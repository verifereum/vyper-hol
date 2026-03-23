(*
 * Safe Arithmetic Properties
 *
 * TOP-LEVEL:
 *   compile_safe_add_correct — add with overflow check
 *   compile_safe_sub_correct — sub with underflow check
 *   compile_safe_mul_correct — mul with overflow check (includes int256 MIN_INT)
 *   compile_safe_div_correct — div with division-by-zero check
 *   compile_safe_mod_correct — mod with division-by-zero check
 *   compile_compare_correct  — comparison with signed/unsigned dispatch
 *   compile_clamp_correct    — value clamping to type range
 *
 * Source: arithmetic.py (safe_add/sub/mul/div/mod/pow)
 * Lowering: exprLoweringScript.sml (compile_safe_*, compile_compare, compile_clamp)
 *)

Theory arithmeticProps
Ancestors
  exprLoweringProps
  exprLowering compileEnv
  venomExecSemantics venomState venomInst
  valueEncoding

(* ===== Safe Addition ===== *)

(* Value in range for type: unsigned ⇒ < 2^bits, signed ⇒ in [-2^(bits-1), 2^(bits-1)-1] *)
Definition in_type_range_def:
  in_type_range ty (v:int) =
    let bits = type_bits ty in
    if is_signed_type ty then
      -&(2 ** (bits - 1)) ≤ v ∧ v ≤ &(2 ** (bits - 1) - 1)
    else
      0 ≤ v ∧ v < &(2 ** bits)
End

(* Add: succeeds iff result in range, reverts on overflow *)
Theorem compile_safe_add_correct:
  ∀ x y ty ss st op st' a b.
    compile_safe_add x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME (a + b)) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* Add: if mathematical result is in range, then OK (no revert) *)
Theorem compile_safe_add_in_range:
  ∀ x y ty ss st op st' a b.
    compile_safe_add x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    in_type_range ty (w2i a + w2i b)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (a + b)
Proof
  cheat
QED

(* ===== Safe Subtraction ===== *)

Theorem compile_safe_sub_correct:
  ∀ x y ty ss st op st' a b.
    compile_safe_sub x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME (a - b)) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

Theorem compile_safe_sub_in_range:
  ∀ x y ty ss st op st' a b.
    compile_safe_sub x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    in_type_range ty (w2i a - w2i b)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (a - b)
Proof
  cheat
QED

(* ===== Safe Multiplication ===== *)

Theorem compile_safe_mul_correct:
  ∀ x y ty ss st op st' a b.
    compile_safe_mul x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME (a * b)) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

Theorem compile_safe_mul_in_range:
  ∀ x y ty ss st op st' a b.
    compile_safe_mul x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    in_type_range ty (w2i a * w2i b)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (a * b)
Proof
  cheat
QED

(* ===== Safe Division ===== *)

(* Division by zero → revert *)
Theorem compile_safe_div_by_zero:
  ∀ x y ty ss st op st' a.
    compile_safe_div x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME 0w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* Division with non-zero divisor: result is sdiv or div depending on type *)
Theorem compile_safe_div_correct:
  ∀ x y ty ss st op st' a b.
    compile_safe_div x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    b ≠ 0w
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' =
         SOME (if is_signed_type ty then safe_sdiv a b
               else safe_div a b)) ∨
      (* signed MIN_INT / -1 overflow → revert *)
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Safe Modulo ===== *)

Theorem compile_safe_mod_by_zero:
  ∀ x y ty ss st op st' a.
    compile_safe_mod x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME 0w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* Modulo with non-zero divisor: result is smod or mod depending on type *)
Theorem compile_safe_mod_correct:
  ∀ x y ty ss st op st' a b.
    compile_safe_mod x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    b ≠ 0w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (if is_signed_type ty then safe_smod a b
              else safe_mod a b)
Proof
  cheat
QED

(* ===== Comparison ===== *)

(* Semantic comparison: evaluates cmp_op on two word256 values.
   Signed for all types except uint256 (matching Python). *)
Definition eval_compare_def:
  eval_compare Lt ty a b =
    (if is_uint256 ty then w2n a < w2n b else w2i a < w2i b) ∧
  eval_compare Gt ty a b =
    (if is_uint256 ty then w2n a > w2n b else w2i a > w2i b) ∧
  eval_compare Eq ty a b = (a = b) ∧
  eval_compare NotEq ty a b = (a ≠ b) ∧
  eval_compare LtE ty a b =
    (if is_uint256 ty then w2n a ≤ w2n b else w2i a ≤ w2i b) ∧
  eval_compare GtE ty a b =
    (if is_uint256 ty then w2n a ≥ w2n b else w2i a ≥ w2i b) ∧
  eval_compare _ ty a b = F
End

(* Comparison produces bool_to_word of the semantic comparison *)
Theorem compile_compare_correct:
  ∀ cmp_op x y ty ss st op st' a b.
    compile_compare cmp_op x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    MEM cmp_op [Lt; Gt; Eq; NotEq; LtE; GtE]
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (bool_to_word (eval_compare cmp_op ty a b))
Proof
  cheat
QED

(* ===== Clamping ===== *)

(* Clamp either succeeds (value in range) or reverts *)
Theorem compile_clamp_correct:
  ∀ val_op ty ss st st'.
    compile_clamp val_op ty st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Decimal Division ===== *)

Theorem compile_safe_decimal_div_correct:
  ∀ x y divisor ty ss st op st' a b.
    compile_safe_decimal_div x y divisor ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    b ≠ 0w
    ⇒
    ∃ ss' w.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME w) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED
