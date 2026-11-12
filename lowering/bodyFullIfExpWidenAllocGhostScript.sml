Theory bodyFullIfExpWidenAllocGhost
Ancestors
  bodyPtrIfExpAllocCompiler bodyPtrIfExpAllocGhost bodyPtrIfExpAllocKept
  bodyPtrDefs bodyPtrPrecompileBuiltinsAllocationFrame
  loweringPosts compileEnv loweringHalt exprLoweringProps stmtFragPtr
  venomState venomInst finite_map

Theorem compile_alloc_buffer_ghost_frame_at:
  !D lo ctx fn cenv cx es sa sb n buf sc s out u d PG G tn.
    stmt_state_rel ctx fn cenv cx es s /\
    ghost_inv_at D lo d cenv cx es G tn s /\
    local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sb.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
    buf.buf_operand = Var out /\ n < dimword (:256) /\
    step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    ghost_inv_at D lo d cenv cx es
      (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  rpt strip_tac >>
  drule_all compile_alloc_buffer_frame_separation >>
  disch_then (qspec_then `es.scopes` strip_assume_tac) >>
  drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[] >>
  irule alloca_step_ghost_inv_separated_at >> simp[] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  gvs[local_ptrs_reserved_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem compile_alloc_buffer_kept_frame_at:
  !lo ctx fn cenv cx e es sa sb s0 es' tv vv s n buf sc out u PG G0 tn0 G tn.
    vv_post ctx fn cenv cx e es sa sb s0 es' tv vv s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    lo <= s.vs_alloca_next /\
    local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sb.cs_next_var /\
    compile_alloc_buffer n sb = (buf,sc) /\ buf.buf_operand = Var out /\
    n < dimword (:256) /\
    step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    ghost_kept_at lo cenv es sa G0 tn0 s0
      (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)
Proof
  rpt strip_tac >>
  `ghost_kept cenv es sa G0 tn0 s0 G tn` by
    (gvs[ghost_kept_def, ghost_kept_at_def] >> metis_tac[]) >>
  drule_all compile_alloc_buffer_kept_frame >>
  disch_then (qspec_then `PG` assume_tac) >>
  simp[ghost_kept_at_def] >>
  conj_tac >- gvs[ghost_kept_def] >>
  conj_tac >- gvs[ghost_kept_def] >>
  conj_tac >- gvs[ghost_kept_def] >>
  rpt strip_tac >>
  `i < s.vs_alloca_next` by decide_tac >>
  drule_all alloca_step_taint_below_frontier >>
  gvs[ghost_kept_at_def] >> metis_tac[]
QED
