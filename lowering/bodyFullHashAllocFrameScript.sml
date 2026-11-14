Theory bodyFullHashAllocFrame
Ancestors
  bodyFullAllocGeneric bodyPtrIfExpAllocKept bodyPtrDefs
  loweringHalt exprLoweringProps loweringStateRelDefs venomMemDefs
  venomState venomInst ptrDiscipline finite_map compileEnv

Theorem hash_compile_alloc_entry_kept_at:
  !H ctx fn cenv cx es s sa n buf sc out lo u PG G tn.
    stmt_state_rel H ctx fn cenv cx es s /\
    compile_alloc_buffer n sa = (buf,sc) /\ buf.buf_operand = Var out /\
    n < dimword (:256) /\ lo <= s.vs_alloca_next /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    ghost_kept_at lo cenv es sa G tn s
      (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)
Proof
  rpt strip_tac >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (drule compile_alloc_buffer_parts >> strip_tac >> gvs[] >> metis_tac[]) >>
  `!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) ==>
      off + sz <= s.vs_alloca_next` by
    gvs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
  `!name b sz. local_region cenv es.scopes s name b sz ==>
      b + sz <= s.vs_alloca_next` by
    (gvs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
         local_region_def] >> rpt strip_tac >>
     first_x_assum (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
     simp[] >> strip_tac >> gvs[] >> decide_tac) >>
  `ghost_kept cenv es sa G tn s
      (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)` by
    (irule alloca_step_ghost_kept_bounded >> simp[ghost_kept_def] >> metis_tac[]) >>
  fs[ghost_kept_def] >> rewrite_tac[ghost_kept_at_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `i < s.vs_alloca_next` by decide_tac >>
  drule_all alloca_step_taint_below_frontier >> metis_tac[]
QED
