(* Small source-selection and emitted-cursor boundaries for deploy entry. *)
Theory ctorDeployLoweringEntrySource
Ancestors
  ctorDeployLoweringDefs e2eDeployDefs emitHelperProps compileVyper
  vyperInterpreter vyperTypeContract

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

(* Adversarial selection check: deployment visibility does not constrain name. *)
Theorem deploy_ctor_noninit_selection_probe:
  function_header_ok Deploy Payable F F "other" [] [] NoneT /\
  vyperInterpreter$lookup_function NONE "__init__" Deploy
    [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]] =
      SOME (Payable,F,[],[],NoneT,[]) /\
  classify_functions
    [FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]] =
      ([],[],NONE,SOME (Payable,F,F,"other",[],[],NoneT,[Return NONE]))
Proof
  EVAL_TAC
QED
