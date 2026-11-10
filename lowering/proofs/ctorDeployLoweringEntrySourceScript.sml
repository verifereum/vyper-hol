(* Small source-selection and emitted-cursor boundaries for deploy entry. *)
Theory ctorDeployLoweringEntrySource
Ancestors
  ctorDeployLoweringDefs ctorDeployDefs e2eDeployDefs emitHelperProps compileVyper
  vyperInterpreter vyperTypeContract supportedProgram
  venomInst venomWf venomState
Libs finite_mapLib

Theorem deploy_ctor_start_nonreentrant_false:
  !tops deploy_bc am tx es mut nr body am_c es0.
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) ==>
  nr = F
Proof
  rpt gen_tac >>
  pure_rewrite_tac[deploy_state_rel_def, deploy_ctor_start_def,
                   constructor_args_encode_def] >>
  rpt strip_tac >>
  qpat_x_assum `tx.function_name = _` (fn th =>
    qpat_x_assum `lookup_function NONE tx.function_name _ _ = _`
      (mp_tac o PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `lookup_function NONE "__init__" _ _ = _`
    (fn th => pure_rewrite_tac[th]) >>
  simp_tac bool_ss [optionTheory.SOME_11, pairTheory.PAIR_EQ]
QED

Theorem deploy_ctor_fresh_label_cursor:
  fresh_label prefix st = (lbl, st') ==>
  st'.cs_current_bb = st.cs_current_bb /\
  LENGTH st'.cs_current_insts = LENGTH st.cs_current_insts /\
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_next_id = st.cs_next_id
Proof
  strip_tac >> drule fresh_label_props >> simp[]
QED

Theorem deploy_ctor_fn_pass_fold_append:
  !xs s fn lm fn1 lm1 s1 ys fn2 lm2 s2.
    run_configured_fn_pass_fold runner rp xs unit s fn lm =
      SOME (fn1,lm1,s1) /\
    run_configured_fn_pass_fold runner rp ys unit s1 fn1 lm1 =
      SOME (fn2,lm2,s2) ==>
    run_configured_fn_pass_fold runner rp (xs ++ ys) unit s fn lm =
      SOME (fn2,lm2,s2)
Proof
  Induct_on `xs` >>
  simp[venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED
