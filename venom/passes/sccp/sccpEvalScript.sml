(*
 * SCCP Arithmetic Evaluation
 *
 * Port of venom/passes/sccp/eval.py.
 *)

Theory sccpEval
Ancestors
  list
  venomSem

Definition eval_unop_def:
  eval_unop f ops =
    case ops of
      [x] => SOME (f x)
    | _ => NONE
End

Definition eval_binop_def:
  eval_binop f ops =
    case ops of
      [a; b] => SOME (f b a)
    | _ => NONE
End

Definition eval_ternop_def:
  eval_ternop f ops =
    case ops of
      [a; b; c] => SOME (f c b a)
    | _ => NONE
End

Definition evm_iszero_def:
  evm_iszero x = bool_to_word (x = 0w)
End

Definition evm_shl_def:
  evm_shl sh v =
    if w2n sh >= 256 then 0w else word_lsl v (w2n sh)
End

Definition evm_shr_def:
  evm_shr sh v =
    if w2n sh >= 256 then 0w else word_lsr v (w2n sh)
End

Definition word_is_negative_def:
  word_is_negative w <=> w2i w < 0
End

Definition evm_sar_def:
  evm_sar sh v =
    if w2n sh >= 256 then
      if word_is_negative v then (i2w (-1)) else 0w
    else word_asr v (w2n sh)
End

Definition evm_signextend_def:
  evm_signextend nbytes v =
    let n = w2n nbytes in
    if n > 31 then v
    else
      let shift = n * 8 + 7 in
      let sign_bit = word_lsl (1w:bytes32) shift in
      if word_and v sign_bit <> 0w then
        word_or v (word_1comp (sign_bit - 1w))
      else
        word_and v (sign_bit - 1w)
End

Definition word_pow_def:
  word_pow x 0 = (1w:bytes32) /\
  word_pow x (SUC n) = word_mul x (word_pow x n)
End

Definition eval_arith_def:
  eval_arith op ops =
    case op of
      ADD => eval_binop word_add ops
    | SUB => eval_binop word_sub ops
    | MUL => eval_binop word_mul ops
    | Div => eval_binop safe_div ops
    | SDIV => eval_binop safe_sdiv ops
    | Mod => eval_binop safe_mod ops
    | SMOD => eval_binop safe_smod ops
    | venomInst$EXP =>
        (case ops of
           [a; b] => SOME (word_pow b (w2n a))
         | _ => NONE)
    | EQ => eval_binop (λx y. bool_to_word (x = y)) ops
    | LT => eval_binop (λx y. bool_to_word (w2n x < w2n y)) ops
    | GT => eval_binop (λx y. bool_to_word (w2n x > w2n y)) ops
    | SLT => eval_binop (λx y. bool_to_word (word_lt x y)) ops
    | SGT => eval_binop (λx y. bool_to_word (word_gt x y)) ops
    | OR => eval_binop word_or ops
    | AND => eval_binop word_and ops
    | XOR => eval_binop word_xor ops
    | NOT => eval_unop word_1comp ops
    | SIGNEXTEND => eval_binop evm_signextend ops
    | ISZERO => eval_unop evm_iszero ops
    | SHR => eval_binop evm_shr ops
    | SHL => eval_binop evm_shl ops
    | SAR => eval_binop evm_sar ops
    | ADDMOD => eval_ternop addmod ops
    | MULMOD => eval_ternop mulmod ops
    | _ => NONE
End

val _ = export_theory();
