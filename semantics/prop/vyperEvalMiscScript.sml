Theory vyperEvalMisc
Ancestors
  vyperTypeInvariants
  vyperAST vyperMisc vyperContext vyperState vyperInterpreter
  vyperArray vyperBareGlobalName vyperValue vyperValueOperation
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
    eval_expr cx (Name _ n) st = (INL (Value v), st') ==> st' = st
Proof
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def] >>
  rpt strip_tac >>
  Cases_on `lookup_scopes_val (string_to_num n) st.scopes` >>
  gvs[return_def, raise_def]
QED

Theorem eval_base_target_NameTarget_preserves_state:
  ∀cx n st loc sbs st'.
    eval_base_target cx (NameTarget n) st = (INL (loc, sbs), st') ==> st' = st
Proof
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       check_def, type_check_def, assert_def, ignore_bind_def] >>
  rpt strip_tac >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
  gvs[return_def, raise_def]
QED

Theorem eval_base_target_TopLevelNameTarget_preserves_state:
  ∀cx nsid st res st'.
    eval_base_target cx (TopLevelNameTarget nsid) st = (res, st') ==> st' = st
Proof
  Cases_on `nsid` >>
  simp[Once evaluate_def, bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def, LET_THM] >>
  rpt strip_tac >>
  Cases_on `get_module_code cx q` >>
  gvs[return_def, raise_def]
QED

Theorem eval_base_target_TopLevelNameTarget_immutable:
  ∀cx st src id ts.
    get_module_code cx src = SOME ts ∧
    is_immutable_decl (string_to_num id) ts ⇒
    eval_base_target cx (TopLevelNameTarget (src,id)) st =
    (INL (ImmutableVar src id, []), st)
Proof
  simp[Once evaluate_def, bind_def, lift_option_type_def, return_def]
QED

Theorem eval_base_target_TopLevelNameTarget_no_type_error:
  ∀cx st src id res st'.
    (∃ts. get_module_code cx src = SOME ts) ∧
    eval_base_target cx (TopLevelNameTarget (src,id)) st = (res, st') ⇒
    ∀s. res ≠ INR (Error (TypeError s))
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, lift_option_type_def, return_def, raise_def]
QED

(* ===== Binop Helper Lemmas ===== *)

(* Unsigned subtraction when y ≤ x *)
Theorem evaluate_binop_sub_small_unsigned:
  ∀tv x y.
    within_int_bound (Unsigned 256) x ∧
    within_int_bound (Unsigned 256) y ∧
    y ≤ x ⇒
    evaluate_binop (Unsigned 256) tv Sub (IntV x) (IntV y) =
    INL (IntV (x − y))
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
  ∀tv a b.
    within_int_bound (Signed 128) a ∧
    within_int_bound (Signed 128) b ∧
    within_int_bound (Signed 128) (a + b) ⇒
    evaluate_binop (Signed 128) tv Add (IntV a) (IntV b) =
    INL (IntV (a + b))
Proof
  rpt strip_tac >>
  simp[evaluate_binop_def, bounded_int_op_def]
QED

(* Unary negation first validates the already-evaluated operand against the
   annotation bounds. This matches lowering: an out-of-range positive literal
   such as 2^255 for int256 is not reinterpreted as a valid negative literal. *)
Theorem evaluate_builtin_neg_int256_positive_signed_min_rejected:
  evaluate_builtin cx msg (BaseT (IntT 256)) Neg [IntV (&(2 ** 255))] =
  INR (RuntimeError "Neg operand bound")
Proof
  simp[evaluate_builtin_def, type_to_int_bound_def, within_int_bound_def]
QED

(* ===== For Loop Boundedness ===== *)

(* For loop iterator produces at most n elements (issue #87) *)
Theorem for_loop_iterator_bounded:
  ∀cx id typ it n body st st'.
    eval_stmt cx (For id typ it n body) st = (INL (), st') ⇒
    ∀vs st1.
      eval_iterator cx it st = (INL vs, st1) ⇒
      LENGTH vs ≤ n
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, lift_option_type_def, ignore_bind_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> gvs[raise_def, return_def] >>
  gvs[AllCaseEqs()] >>
  rpt strip_tac >> gvs[check_def, type_check_def, assert_def, compatible_bound_def]
QED
