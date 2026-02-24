Theory vyperEvalMisc
Ancestors
  vyperMisc vyperContext vyperState vyperInterpreter
  vyperArray vyperValue vyperValueOperation
Libs
  intLib

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
                                (FLOOKUP (get_source_immutables (current_module cx) x) (string_to_num n))` >>
  gvs[return_def, raise_def]
QED

Theorem eval_base_target_NameTarget_preserves_state:
  ∀cx n st loc sbs st'.
    eval_base_target cx (NameTarget n) st = (INL (loc, sbs), st') ==> st' = st
Proof
  simp[Once evaluate_def] >> rpt strip_tac >>
  gvs[bind_def, get_scopes_def, return_def] >>
  Cases_on `cx.txn.is_creation` >> gvs[return_def]
  (* is_creation = T *)
  >> gvs[bind_def, get_immutables_def, get_address_immutables_def,
         lift_option_def, lift_option_type_def,
         option_CASE_rator, sum_CASE_rator, prod_CASE_rator] >>
     gvs[return_def, raise_def, bind_def, check_def, type_check_def,
         ignore_bind_def,
         get_module_code_def, lift_sum_def, exactly_one_option_def,
         sum_CASE_rator, assert_def, AllCaseEqs()]
QED

(* ===== Binop Helper Lemmas ===== *)

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
  `0 ≤ x - y` by intLib.ARITH_TAC >> simp[] >>
  `Num (x - y) ≤ Num x` suffices_by simp[] >>
  simp[integerTheory.INT_OF_NUM] >> intLib.ARITH_TAC
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
