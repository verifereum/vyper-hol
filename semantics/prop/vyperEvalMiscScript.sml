Theory vyperEvalMisc

Ancestors
  vyperInterpreter vyperArray vyperTypeValue

Libs
  intLib wordsLib

val within_int_bound_def = vyperTypeValueTheory.within_int_bound_def;
val evaluate_binop_def = vyperInterpreterTheory.evaluate_binop_def;
val bounded_int_op_def = vyperInterpreterTheory.bounded_int_op_def;
val word_mod_def = wordsTheory.word_mod_def;
val w2n_n2w = wordsTheory.w2n_n2w;
val SIZES_CONV = wordsLib.SIZES_CONV;
val ARITH_TAC = intLib.ARITH_TAC;

Theorem eval_stmts_append:
  ∀cx ss1 ss2. eval_stmts cx (ss1 ++ ss2) = do eval_stmts cx ss1; eval_stmts cx ss2 od
Proof
  Induct_on `ss1` >-
  (simp[Once evaluate_def, return_def, ignore_bind_def] >>
   simp[bind_def, return_def] >> simp[FUN_EQ_THM, bind_def, return_def]) >>
  rpt strip_tac >>
  simp[FUN_EQ_THM, Once evaluate_def] >>
  simp[Once evaluate_def, ignore_bind_def, bind_def] >>
  rpt strip_tac >> Cases_on `eval_stmt cx h x` >> Cases_on `q` >> simp[]
QED

Theorem eval_expr_Name_preserves_state:
  ∀cx n st v st'.
    eval_expr cx (Name n) st = (INL (Value v), st') ==> st' = st
Proof
  simp[Once evaluate_def] >> rpt strip_tac >>
  qpat_x_assum `do _ od _ = _` mp_tac >>
  simp[bind_def, get_scopes_def, return_def, get_immutables_def,
       get_address_immutables_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[raise_def, return_def, lift_sum_def] >>
  Cases_on `exactly_one_option (lookup_scopes (string_to_num n) st.scopes)
                                (FLOOKUP (get_source_immutables NONE x) (string_to_num n))` >>
  gvs[return_def, raise_def]
QED

Theorem eval_base_target_NameTarget_preserves_state:
  ∀cx n st loc sbs st'.
    eval_base_target cx (NameTarget n) st = (INL (loc, sbs), st') ==> st' = st
Proof
  simp[Once evaluate_def] >> rpt strip_tac >>
  gvs[bind_def, get_scopes_def, return_def] >>
  Cases_on `cx.txn.is_creation` >> gvs[return_def] >-
  (gvs[bind_def, get_immutables_def, get_address_immutables_def, lift_option_def] >>
   Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
   gvs[lift_sum_def, bind_def] >>
   Cases_on `exactly_one_option
              (if IS_SOME (lookup_scopes (string_to_num n) st.scopes) then
                 SOME (ScopedVar n)
               else NONE)
              (immutable_target (get_source_immutables NONE x) n
                 (string_to_num n))` >>
   gvs[return_def, raise_def]) >>
  gvs[lift_sum_def, bind_def] >>
  Cases_on `exactly_one_option
             (if IS_SOME (lookup_scopes (string_to_num n) st.scopes) then
                SOME (ScopedVar n)
              else NONE) NONE` >>
  gvs[return_def, raise_def]
QED

(* ===== Binop Helper Lemmas ===== *)

(* Unsigned modulo for uint256 % 3 *)
Theorem evaluate_binop_mod_uint256_3:
  ∀x.
    within_int_bound (Unsigned 256) x ⇒
    evaluate_binop Mod (IntV (Unsigned 256) x) (IntV (Unsigned 256) 3) =
    INL (IntV (Unsigned 256) (x % 3))
Proof
  rpt strip_tac >> gvs[within_int_bound_def] >>
  simp[evaluate_binop_def, bounded_int_op_def, within_int_bound_def] >>
  (* Establish key equation: w2i (word_mod (i2w x) (i2w 3)) = x % 3 *)
  sg `w2i (word_mod ((i2w x):bytes32) (i2w 3)) = x % 3` >- (
    `x = &(Num x)` by gvs[integerTheory.INT_OF_NUM] >>
    pop_assum SUBST_ALL_TAC >>
    simp[integer_wordTheory.i2w_pos, word_mod_def, w2n_n2w] >>
    CONV_TAC (DEPTH_CONV (TRY_CONV SIZES_CONV)) >> fs[] >>
    simp[GSYM integer_wordTheory.i2w_pos] >>
    irule integer_wordTheory.w2i_i2w_pos >>
    CONV_TAC (RAND_CONV (TRY_CONV SIZES_CONV)) >>
    `Num x MOD 3 < 3` by simp[] >> simp[]
  ) >>
  gvs[] >>
  `0 ≤ x % 3 ∧ x % 3 < 3` by (
    `(3:int) ≠ 0` by simp[] >>
    drule integerTheory.INT_MOD_BOUNDS >>
    disch_then (qspec_then `x` mp_tac) >> simp[]
  ) >>
  `x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2` by ARITH_TAC >> gvs[]
QED

(* Bounds on x % 3 *)
Theorem uint256_mod_3_bounds:
  ∀x. 0 ≤ x ⇒ 0 ≤ x % 3 ∧ x % 3 < 3
Proof
  rpt strip_tac >>
  `(3:int) ≠ 0` by simp[] >>
  drule integerTheory.INT_MOD_BOUNDS >>
  disch_then (qspec_then `x` mp_tac) >> simp[]
QED

(* Unsigned subtraction when y ≤ x *)
Theorem evaluate_binop_sub_small_unsigned:
  ∀x y.
    within_int_bound (Unsigned 256) x ∧
    within_int_bound (Unsigned 256) y ∧
    y ≤ x ⇒
    evaluate_binop Sub (IntV (Unsigned 256) x) (IntV (Unsigned 256) y) =
    INL (IntV (Unsigned 256) (x − y))
Proof
  rpt strip_tac >>
  simp[evaluate_binop_def, bounded_int_op_def] >>
  gvs[within_int_bound_def] >>
  `0 ≤ x - y` by ARITH_TAC >> simp[] >>
  `Num (x - y) ≤ Num x` suffices_by simp[] >>
  simp[integerTheory.INT_OF_NUM] >> ARITH_TAC
QED

(* Signed 128 addition when result is in bounds *)
Theorem evaluate_binop_add_int128:
  ∀a b.
    within_int_bound (Signed 128) a ∧
    within_int_bound (Signed 128) b ∧
    within_int_bound (Signed 128) (a + b) ⇒
    evaluate_binop Add (IntV (Signed 128) a) (IntV (Signed 128) b) =
    INL (IntV (Signed 128) (a + b))
Proof
  rpt strip_tac >>
  simp[evaluate_binop_def, bounded_int_op_def]
QED

(* ===== Array Init Properties ===== *)

Definition arr_init_def:
  arr_init = SArrayV (BaseTV (IntT 128)) 3
    [(0, IntV (Signed 128) 10); (1, IntV (Signed 128) 11);
     (2, IntV (Signed 128) 12)]
End

Theorem arr_init_make_array:
  make_array_value (BaseTV (IntT 128)) (Fixed 3)
    [IntV (Signed 128) 10; IntV (Signed 128) 11; IntV (Signed 128) 12] =
  arr_init
Proof
  EVAL_TAC >> simp[arr_init_def]
QED

Theorem arr_init_index_0:
  array_index arr_init 0 = SOME (IntV (Signed 128) 10)
Proof
  EVAL_TAC >> simp[arr_init_def]
QED

Theorem arr_init_index_1:
  array_index arr_init 1 = SOME (IntV (Signed 128) 11)
Proof
  EVAL_TAC >> simp[arr_init_def]
QED

Theorem arr_init_index_2:
  array_index arr_init 2 = SOME (IntV (Signed 128) 12)
Proof
  EVAL_TAC >> simp[arr_init_def]
QED

Theorem arr_init_mutable:
  array_is_mutable arr_init
Proof
  simp[arr_init_def]
QED

Theorem arr_init_length:
  array_length arr_init = 3
Proof
  simp[arr_init_def, array_length_def]
QED

Theorem arr_init_valid_index:
  ∀i. valid_index arr_init i ⇔ 0 ≤ i ∧ i < 3
Proof
  simp[arr_init_def, array_length_def]
QED

(* For any valid index of arr_init, the element is a Signed 128 value between 10 and 12 *)
Theorem arr_init_index_bounds:
  ∀i. valid_index arr_init i ⇒
    ∃a. array_index arr_init i = SOME (IntV (Signed 128) a) ∧ 10 ≤ a ∧ a ≤ 12
Proof
  rpt strip_tac >>
  gvs[arr_init_valid_index] >>
  `i = 0 ∨ i = 1 ∨ i = 2` by ARITH_TAC >>
  gvs[arr_init_index_0, arr_init_index_1, arr_init_index_2]
QED
