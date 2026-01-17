(*
 * Reduce Literals Codesize Pass
 *
 * Port of venom/passes/literals_codesize.py.
 *)

Theory literalsCodesize
Ancestors
  list
  venomState venomInst
  compilerUtils

Definition not_threshold_def:
  not_threshold : num = 1
End

Definition shl_threshold_def:
  shl_threshold : num = 3
End

Definition bit_length_def:
  bit_length n = if n = 0 then 1 else LOG2 n + 1
End

Definition hex_len_def:
  hex_len n = 2 + ((bit_length n + 3) DIV 4)
End

Definition hex_bytes_len_def:
  hex_bytes_len n = hex_len n DIV 2
End

Definition count_trailing_zeros_def:
  count_trailing_zeros (n:num) : num =
    if n = 0 then 0
    else if n MOD 2 = 1 then 0
    else 1 + count_trailing_zeros (n DIV 2)
End

Definition reduce_literal_inst_def:
  reduce_literal_inst inst =
    if inst.inst_opcode <> ASSIGN then inst else
    case inst.inst_operands of
      [Lit w] =>
        let lit_val = (w2n w : num) in
        let not_val = w2n (word_1comp w) in
        let not_benefit =
          (int_of_num (hex_bytes_len lit_val) -
           int_of_num (hex_bytes_len not_val) -
           int_of_num not_threshold) * 8 in
        let ix =
          ((if lit_val = 0 then 2 else count_trailing_zeros lit_val + 1) : num) in
        let shl_benefit =
          int_of_num ix - int_of_num (shl_threshold * 8) in
        if not_benefit <= 0 /\ shl_benefit <= 0 then inst
        else if not_benefit >= shl_benefit then
          inst with <| inst_opcode := NOT;
                       inst_operands := [Lit (word_1comp w)] |>
        else
          let ix' = ix - 1 in
          let shifted = lit_val DIV (pow2 ix') in
          inst with <| inst_opcode := SHL;
                       inst_operands := [Lit (n2w shifted); Lit (n2w ix')] |>
    | _ => inst
End

Definition reduce_literals_codesize_block_def:
  reduce_literals_codesize_block bb =
    bb with bb_instructions := MAP reduce_literal_inst bb.bb_instructions
End

Definition reduce_literals_codesize_function_def:
  reduce_literals_codesize_function fn =
    fn with fn_blocks := MAP reduce_literals_codesize_block fn.fn_blocks
End

Definition reduce_literals_codesize_context_def:
  reduce_literals_codesize_context ctx =
    ctx with ctx_functions := MAP reduce_literals_codesize_function ctx.ctx_functions
End

val _ = export_theory();
