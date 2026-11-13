Theory concretizeStageLookup
Ancestors
  o1PassContract o1PassLift venomInst list

Theorem ctx_pass_stage_lookup:
  ctx_pass_stage rpolicy pass view C C' /\
  lookup_function name C.ctx_functions = SOME fn ==>
  ?fn' observed s out.
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_pass_step rpolicy pass observed s fn out /\
    out.fpo_function = fn' /\ fn'.fn_name = fn.fn_name /\
    observed.cu_context.ctx_entry = C.ctx_entry /\
    observed.cu_context.ctx_global_reserved = C.ctx_global_reserved /\
    ctx_fn_names observed.cu_context = ctx_fn_names C /\
    view C' fn observed
Proof
  strip_tac >>
  gvs[ctx_pass_stage_def] >>
  drule list_rel_lookup_function >>
  impl_tac >- (rpt strip_tac >> gvs[fn_pass_step_def]) >>
  disch_then (qspec_then `name` mp_tac) >>
  simp[optionTheory.OPTREL_def] >> strip_tac >> metis_tac[fn_pass_step_def]
QED
