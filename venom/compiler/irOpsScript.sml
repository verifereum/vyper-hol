(*
 * IR Helper Operations for Compiler Passes
 *
 * Functional helpers over Venom IR instructions and blocks.
 *)

Theory irOps
Ancestors
  list alist
  orderedSet
  venomState venomInst
  stringUtils compilerUtils

Definition inst_is_phi_def:
  inst_is_phi inst <=> inst.inst_opcode = PHI
End

Definition inst_is_param_def:
  inst_is_param inst <=> inst.inst_opcode = PARAM
End

Definition inst_is_pseudo_def:
  inst_is_pseudo inst <=>
    inst_is_phi inst \/ inst_is_param inst
End

Definition inst_is_bb_terminator_def:
  inst_is_bb_terminator inst <=> is_terminator inst.inst_opcode
End

Definition inst_is_commutative_def:
  inst_is_commutative inst <=>
    inst.inst_opcode IN {ADD; MUL; OR; XOR; AND; EQ}
End

Definition inst_is_comparator_def:
  inst_is_comparator inst <=>
    inst.inst_opcode IN {GT; LT; SGT; SLT}
End

Definition inst_flippable_def:
  inst_flippable inst <=> inst_is_commutative inst \/ inst_is_comparator inst
End

Definition inst_is_volatile_def:
  inst_is_volatile inst <=>
    inst.inst_opcode IN
     {PARAM; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE;
      SSTORE; ISTORE; TSTORE; MSTORE; CALLDATACOPY; MCOPY; EXTCODECOPY;
      RETURNDATACOPY; CODECOPY; DLOADBYTES; RETURN; RET; JMP; JNZ; DJMP;
      LOG; SELFDESTRUCT; INVALID; REVERT; ASSERT; ASSERT_UNREACHABLE; STOP}
End

Definition inst_no_output_def:
  inst_no_output inst <=>
    inst.inst_opcode IN
    {MSTORE; SSTORE; ISTORE; TSTORE; DLOADBYTES; CALLDATACOPY; MCOPY;
     RETURNDATACOPY; CODECOPY; EXTCODECOPY; RETURN; RET; REVERT;
     ASSERT; ASSERT_UNREACHABLE; SELFDESTRUCT; STOP; INVALID; JMP; DJMP; JNZ; LOG; NOP}
End

Definition inst_get_outputs_def:
  inst_get_outputs inst = inst.inst_outputs
End

Definition inst_num_outputs_def:
  inst_num_outputs inst = LENGTH inst.inst_outputs
End

Definition inst_input_vars_def:
  inst_input_vars inst =
    MAP (λop. case op of Var v => v | _ => "")
      (FILTER (λop. case op of Var _ => T | _ => F) inst.inst_operands)
End

Definition inst_label_operands_def:
  inst_label_operands inst =
    MAP (λop. case op of Label l => l | _ => "")
      (FILTER (λop. case op of Label _ => T | _ => F) inst.inst_operands)
End

Definition inst_non_label_operands_def:
  inst_non_label_operands inst =
    FILTER (\op. case op of Label _ => F | _ => T) inst.inst_operands
End

Definition phi_operands_def:
  phi_operands [] = [] /\
  phi_operands [_] = [] /\
  phi_operands (Label l :: Var v :: rest) = (l,v) :: phi_operands rest /\
  phi_operands (_ :: _ :: rest) = phi_operands rest
End

Definition flip_comparison_opcode_def:
  flip_comparison_opcode GT = LT /\
  flip_comparison_opcode LT = GT /\
  flip_comparison_opcode SGT = SLT /\
  flip_comparison_opcode SLT = SGT /\
  flip_comparison_opcode op = op
End

Definition inst_flip_def:
  inst_flip inst =
    if inst_is_commutative inst then
      inst with inst_operands := REVERSE inst.inst_operands
    else if inst_is_comparator inst then
      inst with <| inst_opcode := flip_comparison_opcode inst.inst_opcode;
                   inst_operands := REVERSE inst.inst_operands |>
    else inst
End

Definition inst_code_size_cost_def:
  inst_code_size_cost inst =
    if inst.inst_opcode IN {RET; PARAM} then (0:num)
    else if inst.inst_opcode IN {ASSIGN; PALLOCA; ALLOCA; CALLOCA} then (1:num)
    else (2:num)
End

Definition inst_make_nop_def:
  inst_make_nop inst =
    inst with <| inst_opcode := NOP; inst_operands := []; inst_outputs := [] |>
End

Definition replace_operands_def:
  replace_operands reps inst =
    let rep = (\op. case ALOOKUP reps op of NONE => op | SOME v => v) in
    inst with inst_operands := MAP rep inst.inst_operands
End

Definition replace_label_operands_def:
  replace_label_operands reps inst =
    let rep = (\op. case op of
                     Label l =>
                       (case ALOOKUP reps l of NONE => op | SOME l' => Label l')
                   | _ => op) in
    inst with inst_operands := MAP rep inst.inst_operands
End

Definition strip_var_prefix_def:
  strip_var_prefix v =
    case strip_percent v of
      NONE => v
    | SOME rest => rest
End

Definition mk_var_operand_def:
  mk_var_operand n = Var (mk_var_name n)
End

Definition mk_label_operand_def:
  mk_label_operand n suffix = Label (mk_label_name n suffix)
End

Definition max_var_id_in_operands_def:
  max_var_id_in_operands ops =
    FOLDL
      (λacc op.
         case op of
           Var v =>
             (case var_id_of_name v of NONE => acc | SOME n => MAX acc n)
         | _ => acc) 0 ops
End

Definition max_var_id_in_inst_def:
  max_var_id_in_inst inst =
    let out_ids = MAP var_id_of_name inst.inst_outputs in
    let in_id = max_var_id_in_operands inst.inst_operands in
    let out_max = FOLDL (λacc opt. case opt of NONE => acc | SOME n => MAX acc n) 0 out_ids in
    MAX in_id out_max
End

Definition max_var_id_in_block_def:
  max_var_id_in_block bb =
    FOLDL (λacc inst. MAX acc (max_var_id_in_inst inst)) 0 bb.bb_instructions
End

Definition max_var_id_in_function_def:
  max_var_id_in_function fn =
    FOLDL (λacc bb. MAX acc (max_var_id_in_block bb)) 0 fn.fn_blocks
End

Definition max_inst_id_in_block_def:
  max_inst_id_in_block bb =
    FOLDL (λacc inst. MAX acc inst.inst_id) 0 bb.bb_instructions
End

Definition max_inst_id_in_function_def:
  max_inst_id_in_function fn =
    FOLDL (λacc bb. MAX acc (max_inst_id_in_block bb)) 0 fn.fn_blocks
End

Definition max_label_id_in_function_def:
  max_label_id_in_function fn =
    let ids = MAP (label_id_of_name) (MAP (\bb. bb.bb_label) fn.fn_blocks) in
    FOLDL (λacc opt. case opt of NONE => acc | SOME n => MAX acc n) 0 ids
End

Definition bb_phi_instructions_def:
  bb_phi_instructions bb =
    TAKE (LENGTH (take_while (λinst. inst.inst_opcode = PHI) bb.bb_instructions))
         bb.bb_instructions
End

Definition bb_param_instructions_def:
  bb_param_instructions bb =
    TAKE (LENGTH (take_while (λinst. inst.inst_opcode = PARAM) bb.bb_instructions))
         bb.bb_instructions
End

Definition bb_pseudo_instructions_def:
  bb_pseudo_instructions bb =
    FILTER inst_is_pseudo bb.bb_instructions
End

Definition bb_non_phi_instructions_def:
  bb_non_phi_instructions bb =
    FILTER (λinst. inst.inst_opcode <> PHI) bb.bb_instructions
End

Definition bb_body_instructions_def:
  bb_body_instructions bb =
    case bb.bb_instructions of
      [] => []
    | insts =>
        let body = BUTLAST insts in
        FILTER (λinst. ~inst_is_pseudo inst) body
End

Definition bb_code_size_cost_def:
  bb_code_size_cost bb =
    FOLDL (λacc inst. acc + inst_code_size_cost inst) 0 bb.bb_instructions
End

Definition fn_code_size_cost_def:
  fn_code_size_cost fn =
    FOLDL (λacc bb. acc + bb_code_size_cost bb) 0 fn.fn_blocks
End

Definition bb_is_terminated_def:
  bb_is_terminated bb =
    case bb.bb_instructions of
      [] => F
    | insts => inst_is_bb_terminator (LAST insts)
End

Definition bb_is_halting_def:
  bb_is_halting bb =
    case bb.bb_instructions of
      [] => F
    | insts =>
        (LAST insts).inst_opcode IN {RETURN; REVERT; STOP; INVALID}
End

Definition bb_out_labels_def:
  bb_out_labels bb =
    case bb.bb_instructions of
      [] => []
    | insts => get_successors (LAST insts)
End

Definition bb_get_assignments_def:
  bb_get_assignments bb =
    FLAT (MAP inst_get_outputs bb.bb_instructions)
End

Definition replace_operands_in_block_def:
  replace_operands_in_block reps bb =
    bb with bb_instructions := MAP (replace_operands reps) bb.bb_instructions
End

Definition replace_operands_in_function_def:
  replace_operands_in_function reps fn =
    fn with fn_blocks := MAP (replace_operands_in_block reps) fn.fn_blocks
End

Definition lookup_inst_in_block_def:
  lookup_inst_in_block iid bb =
    FIND (λinst. inst.inst_id = iid) bb.bb_instructions
End

Definition lookup_inst_in_blocks_def:
  lookup_inst_in_blocks iid [] = NONE /\
  lookup_inst_in_blocks iid (bb::bbs) =
    case lookup_inst_in_block iid bb of
      SOME inst => SOME inst
    | NONE => lookup_inst_in_blocks iid bbs
End

Definition lookup_inst_in_function_def:
  lookup_inst_in_function iid fn = lookup_inst_in_blocks iid fn.fn_blocks
End

Definition update_inst_in_block_def:
  update_inst_in_block iid new_inst bb =
    bb with bb_instructions :=
      MAP (λinst. if inst.inst_id = iid then new_inst else inst) bb.bb_instructions
End

Definition update_inst_in_blocks_def:
  update_inst_in_blocks iid new_inst [] = [] /\
  update_inst_in_blocks iid new_inst (bb::bbs) =
    if MEM iid (MAP (\inst. inst.inst_id) bb.bb_instructions) then
      update_inst_in_block iid new_inst bb :: bbs
    else
      bb :: update_inst_in_blocks iid new_inst bbs
End

Definition update_inst_in_function_def:
  update_inst_in_function iid new_inst fn =
    fn with fn_blocks := update_inst_in_blocks iid new_inst fn.fn_blocks
End

Definition fn_get_param_by_id_def:
  fn_get_param_by_id fn pid =
    FIND (λp. p.param_id = pid) fn.fn_params
End

Definition fn_get_param_by_name_def:
  fn_get_param_by_name fn name =
    FIND (λp. p.param_name = name) fn.fn_params
End

val _ = export_theory();
