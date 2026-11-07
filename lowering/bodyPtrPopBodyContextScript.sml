Theory bodyPtrPopBodyContext
Ancestors bodyPtrPopRuntimeContext bodyPtrPopContextExclusion bodySim

Theorem pop_body_inv_runtime_context:
  body_inv tops ctx cenv cx /\ ~cx.in_deploy ==>
  EVERY (\f. EVERY (\bb. ~occurs5 pop_guarded5 bb.bb_instructions) f.fn_blocks)
    ctx.ctx_functions
Proof
  simp[body_inv_def] >> rpt strip_tac >> gvs[] >>
  drule_all pop_lower_runtime_context >> simp[]
QED

Theorem pop_body_runtime_storage_exclusion:
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\
  stmt_state_rel ctx fn ce cx es s /\
  compile_dynarray_pop (Var h) 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  fn_has_code si sb fn ==> F
Proof
  rpt strip_tac >> drule_all pop_body_inv_runtime_context >> strip_tac >>
  drule_all pop_clean_context_storage_exclusion >> simp[]
QED
