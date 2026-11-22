Theory dispatchedRejectCertificateBoundary
Ancestors
  dispatchedRejectCertificateMods sourceUnitExecutionMods e2eModsDefs
  compileUnit venomInst moduleLoweringProps compileEnv fragExec
  gasShadowUnit vyperInterpreter list

(* The rejection trace is uniform even in the choice of outcome oracle. *)
Theorem linked_installed_reject_certificate_boundary:
  unit.cu_context.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  EVERY (\(s,l). s < 2 ** 32) selectors /\
  compile_selector_dispatch_linear selectors fl ds = ((),de) /\
  fn_has_code ds de fn /\ ds.cs_current_bb = "__entry" /\
  ds.cs_current_insts = [] /\
  compile_entry_checks mc F opened = ((),checked) /\
  fn_has_code opened checked fn /\ opened.cs_current_insts = [] /\
  ~block_is_terminated opened /\
  opened.cs_current_bb = linear_dispatch_target vs.vs_call_ctx.cc_calldata selectors fl /\
  source_typing_ok_mods mods exps am tx /\
  initial_venom_state_rel_mods mods am tx vs /\
  gas_shadow_context unit.cu_context shadow_ctx /\
  tx.value <> 0 /\
  (!os gobs. call_external_trace (SOME os) gobs am tx =
    (INR (Error (RuntimeError "not Payable")),am,[],[])) ==>
  source_unit_execution_correct_with_mods shadow_ctx [] mods exps ret am tx unit vs
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `!os gobs. call_external_trace _ _ _ _ = _`
    (qspec_then `vs.vs_outcomes` assume_tac) >>
  irule linked_installed_reject_certificate >>
  fs[] >>
  qexistsl_tac [`checked`,`de`,`ds`,`fl`,`mc`,`opened`,`selectors`] >>
  simp[]
QED
