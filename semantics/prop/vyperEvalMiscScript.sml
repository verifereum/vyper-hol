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

Theorem eval_base_target_BareGlobalNameTarget_preserves_state:
  ∀cx id st res st'.
    eval_base_target cx (BareGlobalNameTarget id) st = (res, st') ==> st' = st
Proof
  simp[Once evaluate_def, bind_def, return_def, raise_def,
       get_immutables_def, get_address_immutables_def, get_scopes_def,
       lift_option_def, lift_option_type_def, type_check_def,
       assert_def, check_def, ignore_bind_def, LET_THM] >>
  rpt strip_tac >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[return_def, raise_def] >>
  Cases_on `get_module_code cx (current_module cx)` >>
  gvs[return_def, raise_def] >>
  Cases_on `is_immutable_decl (string_to_num id) x'` >>
  gvs[return_def, raise_def] >>
  Cases_on `IS_SOME (FLOOKUP (get_source_immutables (current_module cx) x) (string_to_num id))` >>
  gvs[return_def, raise_def]
QED

Theorem eval_base_target_BareGlobalNameTarget_non_immutable_type_error[local]:
  ∀cx st id ts imms res st'.
    ALOOKUP st.immutables cx.txn.target = SOME imms ∧
    get_module_code cx (current_module cx) = SOME ts ∧
    ¬is_immutable_decl (string_to_num id) ts ∧
    eval_base_target cx (BareGlobalNameTarget id) st = (res, st') ⇒
      res = INR (Error (TypeError "assign to constant")) ∧ st' = st
Proof
  simp[Once evaluate_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_def, lift_option_type_def,
       type_check_def, assert_def, check_def, ignore_bind_def,
       return_def, raise_def, LET_THM] >>
  rpt strip_tac >> gvs[return_def, raise_def]
QED

Theorem eval_base_target_BareGlobalNameTarget:
  ∀cx st n.
    IS_SOME (lookup_bare_global_name cx st n) ∧
    is_immutable cx n ⇒
    eval_base_target cx (BareGlobalNameTarget n) st =
    (INL (ImmutableVar n, []), st)
Proof
  rpt strip_tac >>
  gvs[is_immutable_def, lookup_bare_global_name_def, lookup_immutable_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[] >>
  Cases_on `get_module_code cx (current_module cx)` >> gvs[] >>
  simp[Once evaluate_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_def, return_def,
       lift_option_type_def, type_check_def, assert_def,
       ignore_bind_def]
QED

(* No-TypeError boundary lemma for BareGlobalNameTarget.
   Uses the SAME precondition shape as well_typed_target_BareGlobalNameTarget_IS_SOME
   and well_typed_target_BareGlobalNameTarget_is_immutable, so imp_res_tac can match.
   The env_consistent global_types clause gives exactly these preconditions. *)
Theorem eval_base_target_BareGlobalNameTarget_no_type_error:
  ∀cx st id res st'.
    IS_SOME (FLOOKUP (get_source_immutables (current_module cx)
        (case ALOOKUP st.immutables cx.txn.target of
           SOME m => m | NONE => [])) (string_to_num id)) ∧
    (∃ts. get_module_code cx (current_module cx) = SOME ts ∧
          is_immutable_decl (string_to_num id) ts) ∧
    eval_base_target cx (BareGlobalNameTarget id) st = (res, st') ⇒
    ∀s. res ≠ INR (Error (TypeError s))
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_def, return_def,
       lift_option_type_def, type_check_def, assert_def,
       check_def, ignore_bind_def, LET_THM] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> simp[] >-
    (rpt strip_tac >> gvs[] >>
     qpat_x_assum `IS_SOME _` mp_tac >>
     simp[get_source_immutables_def]) >>
  simp[lift_option_type_def, return_def, raise_def, LET_THM] >>
  Cases_on `get_module_code cx (current_module cx)` >> simp[] >-
    (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[type_check_def, assert_def, check_def, ignore_bind_def,
       return_def, raise_def] >>
  rpt strip_tac >> gvs[]
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
