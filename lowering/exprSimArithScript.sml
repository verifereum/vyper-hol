(*
 * Expression simulation for the arithmetic operators (#636, part 2)
 *
 * The wrapping operators (UnsafeAdd, UnsafeSub, UnsafeMul, UnsafeDiv)
 * compute the word operation and then truncate it to the type's width:
 * an AND mask for unsigned types, SIGNEXTEND for signed ones
 * (wrap_truncate).  The source reduces the integer result mod 2 ** bits
 * (wrapped_int_op).  The two agree on every integer.
 *
 * The checked operators (Add, Sub, Mul, Div, Mod) on integers check the
 * word result against the type (compile_clamp, or the 256-bit overflow
 * checks) and revert where the source raises a RuntimeError: on overflow,
 * on a zero divisor, and on signed INT_MIN / -1.
 *
 * Decimals are 168-bit signed integers scaled by 10^10.  Add, Sub and Mod
 * emit the int168 code (binop_frag_decimal_transfer).  Mul divides the
 * product by 10^10 with SDIV, which truncates toward zero as the source's
 * SGN p * (ABS p / 10^10) does; Div scales the dividend before the SDIV.
 *
 * Not covered: Exp, blocked on #572.  The type system admits ** with no
 * literal operand, where compile_safe_pow emits an unchecked EXP that
 * wraps while the source reverts.
 *
 * TOP-LEVEL:
 *   unsafe_word_op, unsafe_opcode   — the word operation and opcode of a
 *                                     wrapping operator
 *   compile_unsafe_sim              — binop_frag for the wrapping operators
 *   compile_checked_sim             — binop_frag for Add, Sub, Mul on integers
 *   compile_divmod_sim              — binop_frag for Div, Mod on integers
 *   compile_decimal_add_sub_mod_sim — binop_frag for Add, Sub, Mod on decimals
 *   compile_decimal_mul_div_sim     — binop_frag for Mul, Div on decimals
 *   binop_frag_decimal_transfer     — a decimal operator from its int168 one
 *   compile_safe_add_run, compile_safe_sub_run, compile_safe_mul_run
 *                                   — the checked integer runs, by the bound
 *   bop_result_unsafe, bop_result_checked, bop_result_divmod
 *                                   — the source results
 *   i2w_signed_int_mod_sign_extend  — SIGNEXTEND is signed_int_mod
 *   wrapped_int_op_word             — the word of a wrapped result
 *
 * Helpers: i2w_eq_0_within, compile_binop_unsafe, step_unsafe_opcode,
 *   straight_fresh_unsafe, type_to_int_bound_bits, in_type_range_within,
 *   math_val_i2w, math_val_i2w_word, w2n_i2w_neg,
 *   straight_fresh_compile_clamp, straight_fresh_compile_mul_overflow_check,
 *   straight_fresh_checked, straight_fresh_decimal_div, srem_in_type_range,
 *   decimal_sgn_quot, in_type_range_decimal, w2i_decimal_divisor
 *)

Theory exprSimArith
Ancestors
  arithmetic list rich_list bit integer words fcp integer_word int_bitwise
  intBits fragExec varsExt exprSim freshWrites exprSimOps exprSimCompare
  loweringSlice
  exprLowering emitHelper emitHelperProps exprLoweringProps arithmeticProps
  compileEnv vyperAST vyperInterpreter vyperContext vyperValue
  vyperValueOperation vyperTyping vyperArith valueEncoding
  venomExecSemantics venomInst venomState builtinMath builtinProps
Libs
  intLib pairLib

(* ===== Truncation ===== *)

(* SIGNEXTEND from byte j of a word is signed_int_mod at 8 * (j + 1)
   bits. *)
Theorem i2w_signed_int_mod_sign_extend:
  !j x. j <= 30 ==>
        (i2w (signed_int_mod (8 * (j + 1)) x) : bytes32) =
        sign_extend (n2w j) (i2w x)
Proof
  rpt strip_tac >>
  `w2n (n2w j : bytes32) = j` by simp[w2n_n2w, dimword_def] >>
  simp[sign_extend_def, signed_int_mod_def] >>
  qabbrev_tac `b = 8 * (j + 1)` >>
  `0 < b /\ b < 256 /\ 8 * j + 7 = b - 1 /\ 8 * j + 8 = b` by
    simp[Abbr `b`] >>
  asm_rewrite_tac[] >>
  `(1w:bytes32) << b - 1w = n2w (2 ** b - 1)` by
    (`(1w:bytes32) << b = n2w (2 ** b)` by simp[word_lsl_n2w] >>
     simp[n2w_sub]) >>
  `(i2w x >>> (b - 1) && 1w = (1w:bytes32)) <=> (i2w x : bytes32) ' (b - 1)` by
    (irule lsr_and_1 >> simp[]) >>
  asm_rewrite_tac[] >>
  `(i2w (x % &(2 ** b)) : bytes32) = i2w x && n2w (2 ** b - 1)` by
    (irule i2w_mod_pow2 >> simp[]) >>
  `0 <= x % &(2 ** b) /\ x % &(2 ** b) < &(2 ** b)` by
    (mp_tac (Q.SPECL [`x`, `&(2 ** b)`] INT_MOD_BOUNDS) >> simp[]) >>
  qabbrev_tac `rm = x % &(2 ** b)` >>
  `?tn. rm = &tn` by metis_tac[NUM_POSINT_EXISTS] >>
  `tn < 2 ** b` by fs[] >>
  qpat_x_assum `i2w rm = _` mp_tac >>
  asm_rewrite_tac[i2w_pos] >> strip_tac >>
  `(i2w x : bytes32) ' (b - 1) =
   (i2w x && n2w (2 ** b - 1) : bytes32) ' (b - 1)` by
    simp[word_and_def, FCP_BETA, word_index, BIT_EXP_SUB1] >>
  `(n2w tn : bytes32) ' (b - 1) <=> 2 ** (b - 1) <= tn` by
    (simp[word_index] >> irule bit_top >> simp[]) >>
  `(i2w x : bytes32) ' (b - 1) <=> 2 ** (b - 1) <= tn` by
    (qpat_x_assum `i2w x ' _ <=> (_ && _) ' _` SUBST1_TAC >>
     qpat_x_assum `n2w tn = _` (SUBST1_TAC o SYM) >> asm_rewrite_tac[]) >>
  `&tn >= (&(2 ** (b - 1)) : int) <=> 2 ** (b - 1) <= tn` by
    simp[INT_GE, INT_LE] >>
  qpat_assum `&tn >= _ <=> _` (fn th1 =>
    qpat_assum `i2w x ' _ <=> 2 ** _ <= tn` (fn th2 =>
      ONCE_REWRITE_TAC [th1, th2])) >>
  Cases_on `2 ** (b - 1) <= tn` >> pure_asm_rewrite_tac[COND_CLAUSES]
  >- (REWRITE_TAC[GSYM word_i2w_sub, i2w_pos] >>
      qpat_x_assum `n2w tn = _` SUBST1_TAC >> irule neg_mask >> simp[]) >>
  REWRITE_TAC[i2w_pos] >>
  qpat_x_assum `n2w tn = _` ACCEPT_TAC
QED

(* The word of the source's wrapped result is the lowering's truncation of
   the word of the unwrapped one. *)
Theorem wrapped_int_op_word:
  !ty b rr.
    type_bits ty = b /\ 0 < b /\ b <= 256 /\ b MOD 8 = 0 ==>
    ?z. wrapped_int_op (if is_signed_type ty then Signed b else Unsigned b)
          rr = INL (IntV z) /\
        (i2w z : bytes32) = truncate_to_bits b (is_signed_type ty) (i2w rr)
Proof
  rpt strip_tac >> Cases_on `is_signed_type ty` >>
  simp[wrapped_int_op_def, int_bound_bits_def, truncate_to_bits_def] >>
  Cases_on `b < 256` >> simp[]
  >- (`?k. b = k * 8` by metis_tac[MOD_EQ_0_DIVISOR, DECIDE ``0 < 8n``] >>
      gvs[MULT_DIV] >> Cases_on `k` >> fs[] >>
      qspecl_then [`n`, `rr`] mp_tac i2w_signed_int_mod_sign_extend >>
      simp[ADD1, LEFT_ADD_DISTRIB])
  >- (`b = 256` by decide_tac >> gvs[] >>
      qspec_then `rr` mp_tac
        (INST_TYPE [alpha |-> ``:256``] signed_int_mod_w2i) >>
      simp[i2w_w2i])
  >- (irule i2w_mod_pow2 >> simp[]) >>
  `b = 256` by decide_tac >> gvs[] >>
  `rr % &dimword (:256) = &w2n (i2w rr : bytes32)` by simp[w2n_i2w] >>
  fs[dimword_def, i2w_w2n]
QED

(* ===== The wrapping operators ===== *)

(* The word operation of a wrapping operator, before the truncation. *)
Definition unsafe_word_op_def:
  unsafe_word_op bop ty : bytes32 -> bytes32 -> bytes32 =
    if bop = UnsafeAdd then word_add
    else if bop = UnsafeSub then word_sub
    else if bop = UnsafeMul then word_mul
    else if is_signed_type ty then safe_sdiv
    else safe_div
End

(* An integer within a bound of at most 256 bits whose word is 0 is 0. *)
Theorem i2w_eq_0_within:
  !b signed i.
    within_int_bound (if signed then Signed b else Unsigned b) i /\
    b <= 256 /\ i2w i = (0w : bytes32) ==>
    i = 0
Proof
  rpt gen_tac >> Cases_on `signed` >> rw[]
  >- (drule_all w2i_i2w_within_signed >> simp[word_0_w2i]) >>
  fs[within_int_bound_def] >>
  `?n. i = &n` by metis_tac[NUM_POSINT_EXISTS] >>
  `n < 2 ** 256` by
    (irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** b` >> gvs[]) >>
  gvs[i2w_pos, n2w_11, dimword_def]
QED

(* Close a goal on the result of wrapped_int_op u rr, given the fact
   !rr. ?z. wrapped_int_op u rr = INL (IntV z) /\ i2w z = ... *)
val wrap_tac =
  qmatch_goalsub_abbrev_tac `wrapped_int_op _ rr` >>
  first_x_assum (qspec_then `rr` strip_assume_tac) >>
  qexists_tac `IntV z` >>
  qpat_x_assum `wrapped_int_op _ _ = _` (fn th => rewrite_tac [th]) >>
  qunabbrev_tac `rr` >>
  simp[val_to_w256_def, word_i2w_add, word_i2w_mul, word_i2w_sub];

(* A wrapping operator on two integers of a type of b bits, b a multiple
   of 8, the second within the type's bound: the source's result is the
   truncation of the word operation.  Division by zero gives 0 on both
   sides. *)
Theorem bop_result_unsafe:
  !cx ann bop ty v1 v2 es i1 i2 b.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    v1 = IntV i1 /\ v2 = IntV i2 /\
    type_to_int_bound ann =
      SOME (if is_signed_type ty then Signed b else Unsigned b) /\
    type_bits ty = b /\ 0 < b /\ b <= 256 /\ b MOD 8 = 0 /\
    within_int_bound (if is_signed_type ty then Signed b else Unsigned b) i2 ==>
    ?v. bop_result cx ann bop v1 v2 es = INL (Value v) /\ word_value v /\
        val_to_w256 v =
          truncate_to_bits b (is_signed_type ty)
            (unsafe_word_op bop ty (val_to_w256 v1) (val_to_w256 v2))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `!rr. ?z. wrapped_int_op (if is_signed_type ty then Signed (type_bits ty)
                            else Unsigned (type_bits ty)) rr =
              (INL (IntV z) : value + error) /\
            (i2w z : bytes32) =
              truncate_to_bits (type_bits ty) (is_signed_type ty) (i2w rr)` by
    (gen_tac >> irule wrapped_int_op_word >> simp[]) >>
  simp[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
       val_to_w256_def, unsafe_word_op_def, word_value_def] >>
  TRY (wrap_tac >> NO_TAC) >>
  (* UnsafeDiv *)
  Cases_on `i2 = 0` >> gvs[]
  >- (first_x_assum (qspec_then `0` strip_assume_tac) >>
      qexists_tac `IntV z` >>
      qpat_x_assum `wrapped_int_op _ _ = _` (fn th => rewrite_tac [th]) >>
      Cases_on `is_signed_type ty` >>
      gvs[val_to_w256_def, safe_div_def, safe_sdiv_def, i2w_0]) >>
  `i2w i2 <> (0w : bytes32)` by
    (strip_tac >>
     qspecl_then [`type_bits ty`, `is_signed_type ty`, `i2`] mp_tac
       i2w_eq_0_within >> simp[]) >>
  Cases_on `is_signed_type ty` >> gvs[] >>
  wrap_tac >> simp[safe_div_def, safe_sdiv_def, i2w_w2i]
QED

(* The opcode of a wrapping operator. *)
Definition unsafe_opcode_def:
  unsafe_opcode bop ty =
    if bop = UnsafeAdd then ADD
    else if bop = UnsafeSub then SUB
    else if bop = UnsafeMul then MUL
    else if is_signed_type ty then SDIV
    else Div
End

(* compile_binop lowers a wrapping operator as builtinMath's
   compile_unsafe_binop. *)
Theorem compile_binop_unsafe:
  !bop x y ty bl el.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] ==>
    compile_binop bop x y ty bl el =
      compile_unsafe_binop (unsafe_opcode bop ty) x y (type_bits ty)
        (is_signed_type ty)
Proof
  rw[] >>
  simp[compile_binop_def, compile_unsafe_binop_def, unsafe_opcode_def,
       wrap_truncate_def, LET_THM]
QED

(* The opcode's step computes the word operation. *)
Theorem step_unsafe_opcode:
  !bop ty x y a b id out s.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    eval_operand x s = SOME a /\ eval_operand y s = SOME b ==>
    step_inst_base (mk_inst id (unsafe_opcode bop ty) [x; y] [out]) s =
      OK (update_var out (unsafe_word_op bop ty a b) s)
Proof
  rw[unsafe_opcode_def, unsafe_word_op_def] >>
  FIRST [irule step_ADD, irule step_SUB, irule step_MUL, irule step_SDIV,
         irule step_Div] >>
  simp[]
QED

Theorem straight_fresh_unsafe:
  !bop x y ty bl el.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] ==>
    straight_fresh (compile_binop bop x y ty bl el)
Proof
  rpt strip_tac >> drule compile_binop_unsafe >> simp[] >> strip_tac >>
  simp[compile_unsafe_binop_def, LET_THM] >>
  irule straight_fresh_bind >>
  `fresh_write_op (unsafe_opcode bop ty)` by
    (rw[unsafe_opcode_def] >> simp[fresh_write_op_def]) >>
  simp[straight_fresh_emit_op] >> rw[] >>
  simp[straight_fresh_emit_op, straight_fresh_return, fresh_write_op_def]
QED

(* binop_frag for the wrapping operators on two integers of a type of b
   bits, b a multiple of 8, the second within the type's bound. *)
Theorem compile_unsafe_sim:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0 i1 i2.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    v1 = IntV i1 /\ v2 = IntV i2 /\
    type_to_int_bound ann =
      SOME (if is_signed_type ty then Signed (type_bits ty)
            else Unsigned (type_bits ty)) /\
    0 < type_bits ty /\ type_bits ty <= 256 /\ type_bits ty MOD 8 = 0 /\
    within_int_bound
      (if is_signed_type ty then Signed (type_bits ty)
       else Unsigned (type_bits ty)) i2 ==>
    binop_frag ctx func cenv cx bop ty ann bl el v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `ann`, `bop`, `ty`, `v1`, `v2`, `es0`, `i1`, `i2`,
               `type_bits ty`] mp_tac bop_result_unsafe >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  match_mp_tac binop_frag_straight >> conj_tac
  >- (rpt gen_tac >> irule straight_fresh_unsafe >> first_assum ACCEPT_TAC) >>
  strip_tac >> disj1_tac >> qexists_tac `v` >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `compile_binop _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_binop_unsafe] >> strip_tac >>
  irule compile_unsafe_binop_correct >>
  goal_assum (drule_at (Pat `compile_unsafe_binop`)) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  irule step_unsafe_opcode >> asm_rewrite_tac[]
QED

(* ===== Checked arithmetic: the source's bounds ===== *)

(* An integer type's bound is its width with its signedness. *)
Theorem type_to_int_bound_bits:
  !ty u. type_to_int_bound ty = SOME u ==>
    u = (if is_signed_type ty then Signed (type_bits ty)
         else Unsigned (type_bits ty)) /\ ~is_decimal_type ty
Proof
  Cases >> simp[type_to_int_bound_def] >>
  qmatch_goalsub_rename_tac `BaseT bt` >> Cases_on `bt` >>
  simp[type_to_int_bound_def, is_signed_type_def, type_bits_def,
       is_decimal_type_def]
QED

(* The lowering's range check is the source's bound check. *)
Theorem in_type_range_within:
  !ty v. 0 < type_bits ty ==>
    (in_type_range ty v <=>
     within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                       else Unsigned (type_bits ty)) v)
Proof
  rpt strip_tac >> rw[in_type_range_def, within_int_bound_def] >>
  (Cases_on `v < 0`
   >- (`?n. v = -&n` by
         (irule NUM_NEGINT_EXISTS >> intLib.ARITH_TAC) >>
       gvs[] >>
       `0 < 2 ** (type_bits ty − 1)` by simp[] >>
       simp[INT_SUB] >> intLib.ARITH_TAC) >>
   `?n. v = &n` by (irule NUM_POSINT_EXISTS >> intLib.ARITH_TAC) >>
   gvs[] >>
   `0 < 2 ** (type_bits ty − 1)` by simp[] >>
   simp[INT_SUB] >> intLib.ARITH_TAC)
QED

(* The lowering reads an integer within its type's bound back from its
   word. *)
Theorem math_val_i2w:
  !ty i. type_bits ty <= 256 /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) i ==>
    math_val ty (i2w i : bytes32) = i
Proof
  rw[math_val_def]
  >- (irule w2i_i2w_within_signed >> metis_tac[]) >>
  fs[within_int_bound_def] >>
  `?n. i = &n` by (irule NUM_POSINT_EXISTS >> simp[]) >>
  gvs[i2w_pos] >>
  irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** type_bits ty` >>
  simp[dimword_def]
QED

(* ===== Checked arithmetic: the lowered code ===== *)

(* The checked operations' code writes only fresh variables. *)
val sf_step = FIRST [
  irule straight_fresh_bind >> conj_tac,
  irule straight_fresh_ignore_bind >> conj_tac,
  gen_tac >> BETA_TAC,
  irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
  irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
  MATCH_ACCEPT_TAC straight_fresh_return,
  IF_CASES_TAC];

Theorem straight_fresh_compile_clamp:
  !v ty. straight_fresh (compile_clamp v ty)
Proof
  rw[compile_clamp_def] >> Cases_on `type_bounds ty` >> simp[] >>
  rpt sf_step
QED

Theorem straight_fresh_compile_mul_overflow_check:
  !x y res s b. straight_fresh (compile_mul_overflow_check x y res s b)
Proof
  rw[compile_mul_overflow_check_def, LET_THM] >>
  rpt (FIRST [sf_step, irule straight_fresh_compile_clamp])
QED

Theorem straight_fresh_checked:
  !x y ty.
    straight_fresh (compile_safe_add x y ty) /\
    straight_fresh (compile_safe_sub x y ty) /\
    straight_fresh (compile_safe_mul x y ty) /\
    straight_fresh (compile_safe_div x y ty) /\
    straight_fresh (compile_safe_mod x y ty)
Proof
  rw[compile_safe_add_def, compile_safe_sub_def, compile_safe_mul_def,
     compile_safe_div_def, compile_safe_mod_def, clamp_and_return_def,
     LET_THM] >>
  rpt (FIRST [sf_step, irule straight_fresh_compile_clamp,
              irule straight_fresh_compile_mul_overflow_check])
QED

val wb_ss = [wordsTheory.dimword_def, wordsTheory.INT_MIN_def,
             wordsTheory.INT_MAX_def, integer_wordTheory.INT_MIN_def,
             integer_wordTheory.INT_MAX_def, venomMemPropsTheory.dimindex_256];

(* math_val of the word of an integer within the word's range. *)
Theorem math_val_i2w_word:
  !ty z. type_bits ty <= 256 /\
    (is_signed_type ty ==> INT_MIN (:256) <= z /\ z <= INT_MAX (:256)) /\
    (~is_signed_type ty ==> 0 <= z /\ z < &dimword (:256)) ==>
    math_val ty (i2w z : bytes32) = z
Proof
  rw[math_val_def] >> fs[]
  >- (irule w2i_i2w >> simp[]) >>
  `?n. z = &n` by (irule NUM_POSINT_EXISTS >> simp[]) >>
  gvs[i2w_pos]
QED

Theorem w2n_i2w_neg:
  !n. 0 < n /\ n < dimword (:256) ==>
      w2n (i2w (-&n) : bytes32) = dimword (:256) - n
Proof
  rw[i2w_def] >> simp[word_2comp_n2w]
QED

(* A sum or a difference of two values of a type below 256 bits is within
   the word's range, as math_val reads it. *)
val narrow_range_tac =
  irule math_val_i2w_word >> simp wb_ss >>
  qabbrev_tac `X = 2 ** (type_bits ty − 1)` >>
  qabbrev_tac `Y = 2 ** type_bits ty` >>
  `X ≤ 2 ** 254 ∧ Y ≤ 2 ** 255 ∧ 0 < X` by simp[Abbr `X`, Abbr `Y`] >>
  `&(X − 1) = &X − 1 : int` by simp[INT_SUB] >>
  Cases_on `is_signed_type ty` >> fs[in_type_range_def] >> intLib.ARITH_TAC;

val checked_run_pre_tac =
  rpt gen_tac >> strip_tac >>
  drule type_to_int_bound_bits >> strip_tac >> gvs[] >>
  `math_val ty (i2w i1 : bytes32) = i1 /\ math_val ty (i2w i2 : bytes32) = i2` by
    simp[math_val_i2w] >>
  `in_type_range ty i1 /\ in_type_range ty i2` by simp[in_type_range_within];

(* A checked add of two integers of an integer type: its words sum to the
   integer sum's word when the sum is within the type's bound, and the code
   reverts when it is not. *)
Theorem compile_safe_add_run:
  !x y ty ss st op st' i1 i2 u.
    compile_safe_add x y ty st = (op, st') /\
    eval_operand x ss = SOME (i2w i1) /\ eval_operand y ss = SOME (i2w i2) /\
    fresh_vars_wrt st ss /\ type_to_int_bound ty = SOME u /\
    0 < type_bits ty /\ type_bits ty <= 256 /\
    within_int_bound u i1 /\ within_int_bound u i2 ==>
    (within_int_bound u (i1 + i2) ==>
     ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
           eval_operand op ss' = SOME (i2w (i1 + i2))) /\
    (~within_int_bound u (i1 + i2) ==>
     ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  checked_run_pre_tac >>
  conj_tac
  >- (strip_tac >>
      qspecl_then [`x`, `y`, `ty`, `ss`, `st`, `op`, `st'`, `i2w i1`, `i2w i2`]
        mp_tac compile_safe_add_in_range >>
      simp[in_type_range_within, word_i2w_add]) >>
  strip_tac >> `¬in_type_range ty (i1 + i2)` by simp[in_type_range_within] >>
  Cases_on `type_bits ty < 256`
  >- (qspecl_then [`x`, `y`, `ty`, `ss`, `st`, `op`, `st'`, `i2w i1`, `i2w i2`]
        mp_tac compile_safe_add_out_of_range >>
      simp[word_i2w_add] >>
      `math_val ty (i2w (i1 + i2) : bytes32) = i1 + i2` by narrow_range_tac >>
      simp[]) >>
  `type_bits ty = 256` by decide_tac >> Cases_on `is_signed_type ty`
  >- (qspecl_then [`x`, `y`, `ty`, `ss`, `st`, `op`, `st'`, `i2w i1`, `i2w i2`]
        mp_tac compile_safe_add_overflow_signed_256 >>
      fs[math_val_def]) >>
  qspecl_then [`x`, `y`, `ty`, `ss`, `st`, `op`, `st'`, `i2w i1`, `i2w i2`]
    mp_tac compile_safe_add_overflow >>
  impl_tac >- (fs[math_val_def, in_type_range_def, dimword_def] >>
               fs[GSYM INT_ADD] >> intLib.ARITH_TAC) >>
  simp[]
QED

(* The same for a checked sub; an unsigned difference below 0 wraps to a
   word above the type's range. *)
Theorem compile_safe_sub_run:
  !x y ty ss st op st' i1 i2 u.
    compile_safe_sub x y ty st = (op, st') /\
    eval_operand x ss = SOME (i2w i1) /\ eval_operand y ss = SOME (i2w i2) /\
    fresh_vars_wrt st ss /\ type_to_int_bound ty = SOME u /\
    0 < type_bits ty /\ type_bits ty <= 256 /\
    within_int_bound u i1 /\ within_int_bound u i2 ==>
    (within_int_bound u (i1 - i2) ==>
     ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
           eval_operand op ss' = SOME (i2w (i1 - i2))) /\
    (~within_int_bound u (i1 - i2) ==>
     ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  checked_run_pre_tac >>
  conj_tac
  >- (strip_tac >>
      qspecl_then [`x`, `y`, `ty`, `ss`, `st`, `op`, `st'`, `i2w i1`, `i2w i2`]
        mp_tac compile_safe_sub_in_range >>
      rewrite_tac[word_i2w_sub] >> simp[in_type_range_within]) >>
  strip_tac >> `¬in_type_range ty (i1 - i2)` by simp[in_type_range_within] >>
  Cases_on `type_bits ty < 256`
  >- (qspecl_then [`x`, `y`, `ty`, `ss`, `st`, `op`, `st'`, `i2w i1`, `i2w i2`]
        mp_tac compile_safe_sub_out_of_range >>
      rewrite_tac[word_i2w_sub] >> disch_then irule >> simp[] >>
      Cases_on `is_signed_type ty`
      >- (`math_val ty (i2w (i1 - i2) : bytes32) = i1 - i2` by narrow_range_tac >>
          simp[]) >>
      `i1 - i2 < 0` by (fs[in_type_range_def] >> intLib.ARITH_TAC) >>
      `?n. i1 - i2 = -&n` by (irule NUM_NEGINT_EXISTS >> intLib.ARITH_TAC) >>
      `0 < n ∧ n < 2 ** type_bits ty` by
        (fs[in_type_range_def] >> intLib.ARITH_TAC) >>
      `2 ** type_bits ty ≤ 2 ** 255` by simp[] >>
      `n < dimword (:256)` by
        (irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** type_bits ty` >>
         simp[dimword_def]) >>
      simp[math_val_def, w2n_i2w_neg, in_type_range_def] >>
      qabbrev_tac `Y = 2 ** type_bits ty` >>
      `Y ≤ 57896044618658097711785492504343953926634992332820282019728792003956564819968`
        by fs[] >>
      simp[dimword_def]) >>
  `type_bits ty = 256` by decide_tac >>
  qspecl_then [`x`, `y`, `ty`, `ss`, `st`, `op`, `st'`, `i2w i1`, `i2w i2`]
    mp_tac compile_safe_sub_overflow_256 >>
  simp[]
QED

(* The same for a checked mul of an integer type. *)
Theorem compile_safe_mul_run:
  !x y ty ss st op st' i1 i2 u.
    compile_safe_mul x y ty st = (op, st') /\
    eval_operand x ss = SOME (i2w i1) /\ eval_operand y ss = SOME (i2w i2) /\
    fresh_vars_wrt st ss /\ type_to_int_bound ty = SOME u /\
    0 < type_bits ty /\ type_bits ty <= 256 /\
    within_int_bound u i1 /\ within_int_bound u i2 ==>
    (within_int_bound u (i1 * i2) ==>
     ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
           eval_operand op ss' = SOME (i2w (i1 * i2))) /\
    (~within_int_bound u (i1 * i2) ==>
     ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  checked_run_pre_tac >>
  conj_tac
  >- (strip_tac >>
      qspecl_then [`x`, `y`, `ty`, `ss`, `st`, `op`, `st'`, `i2w i1`, `i2w i2`]
        mp_tac compile_safe_mul_in_range >>
      simp[in_type_range_within, word_i2w_mul]) >>
  strip_tac >>
  qspecl_then [`x`, `y`, `ty`, `ss`, `st`, `op`, `st'`, `i2w i1`, `i2w i2`]
    mp_tac compile_safe_mul_overflow >>
  simp[in_type_range_within]
QED

(* The source's result of a checked add, sub or mul of two integers. *)
Theorem bop_result_checked:
  !cx ann bop v1 v2 es i1 i2 u.
    MEM bop [Add; Sub; Mul] /\ v1 = IntV i1 /\ v2 = IntV i2 /\
    type_to_int_bound ann = SOME u ==>
    bop_result cx ann bop v1 v2 es =
      let r = if bop = Add then i1 + i2 else if bop = Sub then i1 - i2
              else i1 * i2 in
      if within_int_bound u r then INL (Value (IntV r))
      else INR (Error (RuntimeError "bounded_int_op bound"))
Proof
  rw[] >>
  simp[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
       bounded_int_op_def] >>
  rw[]
QED

(* binop_frag for a checked add, sub or mul of two integers of an integer
   type, within its bound: the result when it is within the bound, a revert
   when it is not. *)
Theorem compile_checked_sim:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0 i1 i2 u.
    MEM bop [Add; Sub; Mul] /\ v1 = IntV i1 /\ v2 = IntV i2 /\
    type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
    0 < type_bits ty /\ type_bits ty <= 256 /\
    within_int_bound u i1 /\ within_int_bound u i2 ==>
    binop_frag ctx func cenv cx bop ty ann bl el v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qabbrev_tac `rr = if bop = Add then i1 + i2 else if bop = Sub then i1 - i2
                   else i1 * i2` >>
  `bop_result cx ann bop (IntV i1) (IntV i2) es0 =
     if within_int_bound u rr then INL (Value (IntV rr))
     else INR (Error (RuntimeError "bounded_int_op bound"))` by
    (qspecl_then [`cx`, `ann`, `bop`, `IntV i1`, `IntV i2`, `es0`, `i1`, `i2`,
                  `u`] mp_tac bop_result_checked >> simp[Abbr `rr`]) >>
  `!x y sa sb op ss.
     compile_binop bop x y ty bl el sa = (op, sb) /\
     fresh_vars_wrt sa ss /\ eval_operand x ss = SOME (i2w i1) /\
     eval_operand y ss = SOME (i2w i2) ==>
     (within_int_bound u rr ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
            eval_operand op ss' = SOME (i2w rr)) /\
     (~within_int_bound u rr ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')` by
    (rpt gen_tac >> strip_tac >> fs[] >> gvs[compile_binop_def, Abbr `rr`]
     >- (irule compile_safe_add_run >> metis_tac[])
     >- (irule compile_safe_sub_run >> metis_tac[]) >>
     irule compile_safe_mul_run >> metis_tac[]) >>
  match_mp_tac binop_frag_straight >> conj_tac
  >- (rpt gen_tac >> fs[] >> simp[compile_binop_def, straight_fresh_checked]) >>
  strip_tac >> asm_rewrite_tac[val_to_w256_def] >>
  Cases_on `within_int_bound u rr` >> asm_rewrite_tac[]
  >- (disj1_tac >> qexists_tac `IntV rr` >>
      rewrite_tac[val_to_w256_def, word_value_def] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `"bounded_int_op bound"` >> rewrite_tac[] >>
  metis_tac[]
QED

Theorem srem_in_type_range:
  !ty (A:int) B.
    is_signed_type ty /\ in_type_range ty A /\ in_type_range ty B /\ B <> 0 ==>
    in_type_range ty (A rem B)
Proof
  rpt strip_tac >>
  qspec_then `B` mp_tac integerTheory.INT_REMQUOT >> simp[] >>
  disch_then (qspec_then `A` strip_assume_tac) >>
  qabbrev_tac `rr = A rem B` >>
  qpat_x_assum `A = _` kall_tac >>
  fs[in_type_range_def] >>
  rpt (qpat_x_assum `if is_signed_type _ then _ else _` mp_tac) >>
  simp[] >> rpt strip_tac >>
  qabbrev_tac `X = 2 ** (type_bits ty − 1)` >>
  `0 < X` by simp[Abbr `X`] >>
  `&(X − 1) = &X − 1 : int` by simp[integerTheory.INT_SUB] >>
  qpat_x_assum `ABS rr < ABS B` mp_tac >>
  qpat_x_assum `if 0 < A then _ else _` mp_tac >>
  simp[integerTheory.INT_ABS] >> rw[] >> intLib.ARITH_TAC
QED

(* Source semantics of checked Div/Mod on in-range integers: a zero divisor
   (and, for signed Div, the INT_MIN / -1 overflow) is a runtime error;
   otherwise the result's word image is the EVM safe_* operation. *)
Theorem bop_result_divmod:
  !cx ann bop ty v1 v2 es i1 i2 u.
    MEM bop [Div; Mod] /\ v1 = IntV i1 /\ v2 = IntV i2 /\
    type_to_int_bound ann = SOME u /\ type_to_int_bound ty = SOME u /\
    0 < type_bits ty /\ type_bits ty <= 256 /\
    within_int_bound u i1 /\ within_int_bound u i2 ==>
    ((i2 = 0 \/ (bop = Div /\ is_signed_type ty /\
                 i1 = -&(2 ** (type_bits ty − 1)) /\ i2 = -1)) ==>
     ?m. bop_result cx ann bop v1 v2 es = INR (Error (RuntimeError m))) /\
    (~(i2 = 0 \/ (bop = Div /\ is_signed_type ty /\
                  i1 = -&(2 ** (type_bits ty − 1)) /\ i2 = -1)) ==>
     ?z. bop_result cx ann bop v1 v2 es = INL (Value (IntV z)) /\
         (i2w z : bytes32) =
           (if bop = Div then
              (if is_signed_type ty then safe_sdiv else safe_div)
            else (if is_signed_type ty then safe_smod else safe_mod))
             (i2w i1) (i2w i2))
Proof
  rpt gen_tac >> strip_tac >>
  drule type_to_int_bound_bits >> strip_tac >>
  `math_val ty (i2w i1 : bytes32) = i1 /\ math_val ty (i2w i2 : bytes32) = i2`
    by gvs[math_val_i2w] >>
  `in_type_range ty i1 /\ in_type_range ty i2` by gvs[in_type_range_within] >>
  `i2 = 0 <=> i2w i2 = (0w : bytes32)` by
    (eq_tac >> strip_tac >- simp[integer_wordTheory.i2w_0] >>
     qspecl_then [`type_bits ty`, `is_signed_type ty`, `i2`] mp_tac
       i2w_eq_0_within >> gvs[]) >>
  `bop = Div \/ bop = Mod` by fs[] >>
  Cases_on `is_signed_type ty` >> gvs[math_val_def] >>
  simp[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
       bounded_int_op_def, int_bound_bits_def] >>
  TRY (conj_tac >- (rw[] >> fs[])) >>
  strip_tac >> `i2 <> 0` by fs[]
  >~ [`safe_sdiv`]
  >- ((* signed Div *)

      `i2w i1 / i2w i2 = i2w (i1 quot i2) : bytes32` by
        simp[integer_wordTheory.word_quot] >>
      `in_type_range ty (i1 quot i2)` by
        (irule sdiv_in_type_range >> simp[] >> metis_tac[]) >>
      `w2i (i2w (i1 quot i2) : bytes32) = i1 quot i2` by
        (irule integer_wordTheory.w2i_i2w >>
         qspecl_then [`ty`, `i1 quot i2`] mp_tac in_type_range_signed_256 >>
         simp[]) >>
      `within_int_bound (Signed (type_bits ty)) (i1 quot i2)` by
        (qspecl_then [`ty`, `i1 quot i2`] mp_tac in_type_range_within >>
         simp[]) >>
      qexists_tac `i1 quot i2` >> simp[safe_sdiv_def] >> rw[] >> fs[])
  >~ [`safe_smod`]
  >- ((* signed Mod *)

      `word_rem (i2w i1) (i2w i2) = i2w (i1 rem i2) : bytes32` by
        simp[integer_wordTheory.word_rem] >>
      `in_type_range ty (i1 rem i2)` by
        (irule srem_in_type_range >> simp[]) >>
      `w2i (i2w (i1 rem i2) : bytes32) = i1 rem i2` by
        (irule integer_wordTheory.w2i_i2w >>
         qspecl_then [`ty`, `i1 rem i2`] mp_tac in_type_range_signed_256 >>
         simp[]) >>
      `within_int_bound (Signed (type_bits ty)) (i1 rem i2)` by
        (qspecl_then [`ty`, `i1 rem i2`] mp_tac in_type_range_within >>
         simp[]) >>
      qexists_tac `i1 rem i2` >> simp[safe_smod_def] >> rw[] >> fs[]) >>
  (* unsigned: results are bounded by the dividend / divisor *)
  `0 < w2n (i2w i2 : bytes32)` by
    (Cases_on `w2n (i2w i2 : bytes32)` >> fs[wordsTheory.w2n_eq_0]) >>
  `w2n (i2w i1 : bytes32) < 2 ** type_bits ty /\
   w2n (i2w i2 : bytes32) < 2 ** type_bits ty` by
    (rpt (qpat_x_assum `within_int_bound _ _` mp_tac) >>
     qpat_x_assum `&w2n _ = i1` (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
     qpat_x_assum `&w2n _ = i2` (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
     simp[vyperValueTheory.within_int_bound_def]) >>
  `w2n (i2w i1 : bytes32) < dimword (:256) /\
   w2n (i2w i2 : bytes32) < dimword (:256)` by simp[wordsTheory.w2n_lt]
  >~ [`safe_div`]
  >- ((* unsigned Div *)

      `w2n (i2w i1 // i2w i2 : bytes32) <= w2n (i2w i1 : bytes32)` by
        (simp[wordsTheory.word_div_def] >>
         `w2n (i2w i1 : bytes32) DIV w2n (i2w i2 : bytes32) <=
          w2n (i2w i1 : bytes32)` by simp[arithmeticTheory.DIV_LESS_EQ] >>
         simp[]) >>
      qexists_tac `&w2n (i2w i1 // i2w i2 : bytes32)` >>
      simp[safe_div_def, integer_wordTheory.i2w_w2n,
           vyperValueTheory.within_int_bound_def]) >>
  (* unsigned Mod *)
  `w2n (word_mod (i2w i1) (i2w i2) : bytes32) < w2n (i2w i2 : bytes32)` by
    (simp[wordsTheory.word_mod_def] >>
     `w2n (i2w i1 : bytes32) MOD w2n (i2w i2 : bytes32) <
      w2n (i2w i2 : bytes32)` by simp[arithmeticTheory.MOD_LESS] >>
     simp[]) >>
  qexists_tac `&w2n (word_mod (i2w i1) (i2w i2) : bytes32)` >>
  simp[safe_mod_def, integer_wordTheory.i2w_w2n,
       vyperValueTheory.within_int_bound_def]
QED

(* Checked Div/Mod (non-decimal): both sides fail together on a zero divisor
   or signed INT_MIN / -1, and otherwise agree via the EVM safe_* ops. *)
Theorem compile_divmod_sim:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0 i1 i2 u.
    MEM bop [Div; Mod] /\ v1 = IntV i1 /\ v2 = IntV i2 /\
    type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
    0 < type_bits ty /\ type_bits ty <= 256 /\
    within_int_bound u i1 /\ within_int_bound u i2 ==>
    binop_frag ctx func cenv cx bop ty ann bl el v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qspecl_then [`ty`, `u`] mp_tac type_to_int_bound_bits >> simp[] >>
  strip_tac >>
  `math_val ty (i2w i1 : bytes32) = i1 /\ math_val ty (i2w i2 : bytes32) = i2`
    by gvs[math_val_i2w] >>
  `i2 = 0 <=> i2w i2 = (0w : bytes32)` by
    (eq_tac >> strip_tac >- simp[integer_wordTheory.i2w_0] >>
     qspecl_then [`type_bits ty`, `is_signed_type ty`, `i2`] mp_tac
       i2w_eq_0_within >> gvs[]) >>
  match_mp_tac binop_frag_straight >> conj_tac
  >- (rpt gen_tac >> fs[] >> gvs[compile_binop_def, straight_fresh_checked]) >>
  strip_tac >>
  qspecl_then [`cx`, `ann`, `bop`, `ty`, `IntV i1`, `IntV i2`, `es0`, `i1`,
               `i2`, `u`] mp_tac bop_result_divmod >> impl_tac >- simp[] >>
  qmatch_goalsub_abbrev_tac `(BAD ==> _) /\ _ ==> _` >>
  Cases_on `BAD` >> simp[] >> strip_tac
  >- ((* zero divisor or signed overflow: the lowering reverts *)
      disj2_tac >> qexists_tac `m` >> asm_rewrite_tac[val_to_w256_def] >>
      rpt strip_tac >> fs[markerTheory.Abbrev_def] >>
      gvs[compile_binop_def, integer_wordTheory.i2w_0]
      >- metis_tac[compile_safe_div_by_zero]
      >- (gvs[math_val_def] >> irule compile_safe_div_overflow >>
          simp[] >> metis_tac[]) >>
      metis_tac[compile_safe_mod_by_zero]) >>
  (* defined result: the lowering computes the matching safe_* word *)
  disj1_tac >> qexists_tac `IntV z` >>
  rewrite_tac[val_to_w256_def, word_value_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> fs[markerTheory.Abbrev_def] >>
  `in_type_range ty i1` by gvs[in_type_range_within] >>
  gvs[compile_binop_def]
  >- (qspecl_then [`x`, `y`, `ty`, `ss`, `sa`, `op`, `sb`, `i2w i1`,
                   `i2w i2`] mp_tac compile_safe_div_ok >>
      impl_tac >- (Cases_on `is_signed_type ty` >> gvs[math_val_def]) >>
      Cases_on `is_signed_type ty` >> simp[]) >>
  qspecl_then [`x`, `y`, `ty`, `ss`, `sa`, `op`, `sb`, `i2w i1`, `i2w i2`]
    mp_tac compile_safe_mod_correct >>
  Cases_on `is_signed_type ty` >> gvs[]
QED

(* ===== Decimal arithmetic ===== *)

(* Decimals lower as 168-bit signed integers: where the lowering emits the
   int168 code and the source result differs only in DecimalV vs IntV (with
   runtime errors matched), the int168 operator fragment carries over. *)
Theorem binop_frag_decimal_transfer:
  !ctx func cenv cx bop ann ann' bl el d1 d2 es0.
    binop_frag ctx func cenv cx bop (BaseT (IntT 168)) ann' bl el
      (IntV d1) (IntV d2) es0 /\
    (!x y. compile_binop bop x y (BaseT DecimalT) bl el =
           compile_binop bop x y (BaseT (IntT 168)) bl el) /\
    ((?z. bop_result cx ann' bop (IntV d1) (IntV d2) es0 =
            INL (Value (IntV z)) /\
          bop_result cx ann bop (DecimalV d1) (DecimalV d2) es0 =
            INL (Value (DecimalV z))) \/
     (?m m'. bop_result cx ann' bop (IntV d1) (IntV d2) es0 =
               INR (Error (RuntimeError m)) /\
             bop_result cx ann bop (DecimalV d1) (DecimalV d2) es0 =
               INR (Error (RuntimeError m')))) ==>
    binop_frag ctx func cenv cx bop (BaseT DecimalT) ann bl el
      (DecimalV d1) (DecimalV d2) es0
Proof
  rpt gen_tac >> simp[binop_frag_def] >> strip_tac >> rpt gen_tac >>
  strip_tac >>
  first_x_assum (qspecl_then [`sa`, `sb`, `x`, `y`, `op`, `s0`] mp_tac) >>
  (impl_tac >- gvs[expr_res_ok_def]) >>
  disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >>
  gvs[val_to_w256_def, word_value_def] >>
  Cases >> simp[expr_exit_def]
QED

Theorem compile_decimal_add_sub_mod_sim:
  !ctx func cenv cx bop ann bl el d1 d2 es0.
    MEM bop [Add; Sub; Mod] /\
    within_int_bound (Signed 168) d1 /\ within_int_bound (Signed 168) d2 ==>
    binop_frag ctx func cenv cx bop (BaseT DecimalT) ann bl el
      (DecimalV d1) (DecimalV d2) es0
Proof
  rpt strip_tac >> irule binop_frag_decimal_transfer >>
  conj_tac
  >- (fs[] >> rpt gen_tac >>
      simp[compile_binop_def, compile_safe_add_def, compile_safe_sub_def,
           compile_safe_mod_def, clamp_and_return_def, compile_clamp_def,
           type_bounds_def, type_bits_def, is_signed_type_def]) >>
  qexists_tac `BaseT (IntT 168)` >> conj_tac
  >- (fs[] >>
      simp[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
           bounded_int_op_def, bounded_decimal_op_def, type_to_int_bound_def,
           int_bound_bits_def] >> rw[]) >>
  `bop = Add \/ bop = Sub \/ bop = Mod` by fs[] >>
  FIRST (map (fn th => irule th >>
                       simp[type_to_int_bound_def, type_bits_def] >> NO_TAC)
              [compile_checked_sim, compile_divmod_sim])
QED

Theorem decimal_sgn_quot:
  !p:int. SGN p * (ABS p / 10000000000) = p quot 10000000000
Proof
  gen_tac >> STRUCT_CASES_TAC (Q.SPEC `p` integerTheory.INT_NUM_CASES) >>
  TRY (`-&n quot 10000000000 = -(&n quot 10000000000) : int` by
         simp[integerTheory.INT_QUOT_NEG]) >>
  simp[intExtensionTheory.SGN_def, integerTheory.INT_ABS_NEG,
       integerTheory.INT_ABS_NUM, integerTheory.INT_DIV, integerTheory.INT_QUOT,
       integerTheory.INT_QUOT_0] >>
  intLib.ARITH_TAC
QED

Theorem in_type_range_decimal:
  !v. in_type_range (BaseT DecimalT) v <=> within_int_bound (Signed 168) v
Proof
  simp[in_type_range_def, type_bits_def, is_signed_type_def,
       vyperValueTheory.within_int_bound_def] >> intLib.ARITH_TAC
QED

Theorem w2i_decimal_divisor:
  w2i (n2w 10000000000 : bytes32) = 10000000000
Proof
  irule integer_wordTheory.w2i_n2w_pos >> simp[wordsTheory.INT_MIN_def]
QED

Theorem straight_fresh_decimal_div:
  !x y. straight_fresh
          (compile_safe_decimal_div x y 10000000000 (BaseT DecimalT))
Proof
  rw[compile_safe_decimal_div_def, clamp_and_return_def] >>
  rpt (FIRST [sf_step, irule straight_fresh_compile_clamp])
QED

Theorem compile_decimal_mul_div_sim:
  !ctx func cenv cx bop ann bl el d1 d2 es0.
    MEM bop [Mul; Div] /\
    within_int_bound (Signed 168) d1 /\ within_int_bound (Signed 168) d2 ==>
    binop_frag ctx func cenv cx bop (BaseT DecimalT) ann bl el
      (DecimalV d1) (DecimalV d2) es0
Proof
  rpt strip_tac >> irule binop_frag_straight >> conj_tac
  >- (fs[] >> rpt gen_tac >>
      simp[compile_binop_def, is_decimal_type_def, decimal_divisor_def,
           straight_fresh_checked, straight_fresh_decimal_div]) >>
  strip_tac >>
  `in_type_range (BaseT DecimalT) d1 /\ in_type_range (BaseT DecimalT) d2` by
    simp[in_type_range_decimal] >>
  `bop = Mul \/ bop = Div` by fs[] >>
  simp[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
       decimal_sgn_quot, bounded_decimal_op_def, compile_binop_def,
       is_decimal_type_def, decimal_divisor_def, val_to_w256_def]
  >- ((* Mul: truncating product, bounded to 168 bits *)
      Cases_on `within_int_bound (Signed 168) (d1 * d2 quot 10000000000)` >>
      simp[word_value_def, val_to_w256_def] >> rpt strip_tac >>
      qspecl_then [`x`, `y`, `ss`, `sa`, `op`, `sb`, `d1`, `d2`] mp_tac
        compile_safe_decimal_mul_run >>
      gvs[in_type_range_decimal]) >>
  (* Div: the scaled dividend over the divisor, after the zero check *)
  `w2i (i2w d1 : bytes32) = d1 /\ w2i (i2w d2 : bytes32) = d2` by
    (conj_tac >> irule integer_wordTheory.w2i_i2w >>
     fs[vyperValueTheory.within_int_bound_def, wordsTheory.INT_MIN_def,
        wordsTheory.INT_MAX_def, wordsTheory.dimword_def] >>
     intLib.ARITH_TAC) >>
  `(i2w d1 * n2w 10000000000 : bytes32) = i2w (d1 * 10000000000)` by
    (qspecl_then [`i2w d1 : bytes32`, `n2w 10000000000 : bytes32`] mp_tac
       integer_wordTheory.word_mul_i2w >>
     asm_rewrite_tac[w2i_decimal_divisor] >>
     disch_then (SUBST1_TAC o SYM) >> REFL_TAC) >>
  `(i2w d2 = (0w : bytes32)) <=> d2 = 0` by
    (eq_tac >> strip_tac >> simp[integer_wordTheory.i2w_0] >>
     qpat_x_assum `w2i (i2w d2) = d2` (SUBST1_TAC o SYM) >>
     asm_simp_tac std_ss [integer_wordTheory.word_0_w2i]) >>
  Cases_on `d2 = 0` >> simp[]
  >- (rpt strip_tac >>
      qspecl_then [`x`, `y`, `ss`, `sa`, `op`, `sb`, `i2w d1`, `i2w d2`]
        mp_tac compile_safe_decimal_div_run >> gvs[]) >>
  `safe_sdiv (i2w d1 * n2w 10000000000) (i2w d2) =
     (i2w (d1 * 10000000000) / i2w d2 : bytes32)` by
    asm_simp_tac std_ss [safe_sdiv_def] >>
  Cases_on `within_int_bound (Signed 168)
              (w2i (i2w (d1 * 10000000000) / i2w d2 : bytes32))` >>
  simp[word_value_def, val_to_w256_def, integer_wordTheory.i2w_w2i] >>
  rpt strip_tac >>
  qspecl_then [`x`, `y`, `ss`, `sa`, `op`, `sb`, `i2w d1`, `i2w d2`] mp_tac
    compile_safe_decimal_div_run >>
  gvs[in_type_range_decimal]
QED
