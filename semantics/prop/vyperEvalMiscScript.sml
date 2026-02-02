Theory vyperEvalMisc

Ancestors
  vyperInterpreter

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
