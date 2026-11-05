Theory bodyPtrIfExpAllocCompiler
Ancestors
  bodyPtrIfExpAllocStep bodyPtrIfExpAllocGhost bodyPtrIfExpAllocKept
  compileEnv loweringHalt stmtFragPtr fragExec allocationPtr emitHelperProps exprSimProps loweringPosts exprLoweringProps venomMemDefs bodyPtrDefs ptrDiscipline venomState

(* These are exactly the reserved-variable premises of expr_vv_sim_ptr,
   transported from its starting cutoff to the allocation after the arm. *)
Theorem compile_alloc_buffer_frame_separation:
  !cenv sa sb n buf sc scopes out.
    local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sb.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    compile_alloc_buffer n sb = (buf,sc) /\ buf.buf_operand = Var out ==>
    not_local_ptr cenv scopes out /\
    (!x. not_fresh_at sa x ==> x <> out) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> out) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> out)
Proof
  rpt strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  gvs[not_local_ptr_def, local_ptrs_reserved_def] >>
  metis_tac[not_fresh_at_mono]
QED

(* Allocation is before unwrap: its executable step needs only the state
   relation from vv_post, not the stronger operand-valued expr_post. *)
Theorem compile_alloc_buffer_raw_step:
  !ctx fn cenv cx es sb n buf sc s.
    stmt_state_rel ctx fn cenv cx es s /\
    compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
    n < dimword (:256) ==>
    ?out u. buf.buf_operand = Var out /\
      MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
      step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u
Proof
  rpt strip_tac >> drule compile_alloc_buffer_emission >> strip_tac >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [p]) (fn_insts fn)` by
    (drule_all fn_has_code_split >> strip_tac >>
     drule_all emit_inst_fn_member >> simp[]) >>
  qexists_tac `p` >> simp[] >>
  Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id`
  >- (drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `p` assume_tac) >> metis_tac[]) >>
  rename1 `FLOOKUP s.vs_allocas sb.cs_next_id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `p` assume_tac) >>
  metis_tac[]
QED

Theorem compile_alloc_buffer_counted:
  !D ctx fn PG G tn cenv cx es sb n buf sc s.
    stmt_state_rel ctx fn cenv cx es s /\
    compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
    n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?out u G1 tn1 t.
      buf.buf_operand = Var out /\
      step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
      t = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
      G1 = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u /\
      tn1 = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
      ptr_covers G1 tn1 out t n
Proof
  rpt strip_tac >> drule_all compile_alloc_buffer_raw_step >> strip_tac >>
  drule compile_alloc_buffer_emission >> strip_tac >> gvs[] >>
  drule emit_inst_extends >> strip_tac >> fs[] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx =
       SOME (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out])` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> gvs[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all alloca_counted_step_covers >>
  disch_then (qspecl_then [`D`, `PG`, `G`, `tn`] strip_assume_tac) >>
  gvs[]
QED

Theorem compile_alloc_buffer_ghost_frame:
  !ctx fn cenv cx es sa sb n buf sc s out u d PG G tn.
    stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
    local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sb.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
    buf.buf_operand = Var out /\ n < dimword (:256) /\
    step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  rpt strip_tac >>
  drule_all compile_alloc_buffer_frame_separation >>
  disch_then (qspec_then `es.scopes` strip_assume_tac) >>
  drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[] >>
  irule alloca_step_ghost_inv_separated >> simp[] >> metis_tac[]
QED

Theorem compile_alloc_buffer_kept_frame:
  !ctx fn cenv cx e es sa sb s0 es' tv vv s n buf sc out u PG G0 tn0 G tn.
    vv_post ctx fn cenv cx e es sa sb s0 es' tv vv s /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sb.cs_next_var /\
    compile_alloc_buffer n sb = (buf,sc) /\ buf.buf_operand = Var out /\
    n < dimword (:256) /\
    step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    ghost_kept cenv es sa G0 tn0 s0
      (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)
Proof
  rpt strip_tac >>
  irule alloca_step_ghost_kept_bounded >> simp[] >>
  conj_tac >- suspend "local_bounds" >>
  conj_tac
  >- (drule compile_alloc_buffer_parts >> strip_tac >> gvs[] >>
      metis_tac[not_fresh_at_mono]) >>
  suspend "alloc_bounds"
QED

Resume compile_alloc_buffer_kept_frame[alloc_bounds]:
  rpt strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by gvs[vv_post_def] >>
  gvs[vv_post_def, stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Resume compile_alloc_buffer_kept_frame[local_bounds]:
  rpt strip_tac >>
  `local_region cenv es'.scopes s name b sz` by
    (irule local_region_frame_fwd >> simp[] >>
     qexistsl_tac [`s0`, `sa`, `es.scopes`] >> gvs[vv_post_def]) >>
  gvs[vv_post_def, stmt_state_rel_def, state_rel_def, local_region_def,
      local_ptrs_rel_def] >>
  qpat_x_assum `!name' entry p sz'. _` drule_all >> simp[]
QED

Finalise compile_alloc_buffer_kept_frame

Theorem compile_alloc_buffer_vv_counted_frame:
  !D d ctx fn PG G0 tn0 G tn cenv cx e es sa sb s0 es' tv vv s n buf sc.
    vv_post ctx fn cenv cx e es sa sb s0 es' tv vv s /\
    ghost_inv d cenv cx es' G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
    local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
    n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?out G1 tn1 t.
      buf.buf_operand = Var out /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
      ptr_covers G1 tn1 out t n /\
      ghost_inv d cenv cx es' G1 tn1 t /\
      ghost_kept cenv es sa G0 tn0 s0 G1 tn1
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx fn cenv cx es' s` by gvs[vv_post_def] >>
  drule_all compile_alloc_buffer_counted >>
  disch_then (qspecl_then [`D`, `PG`, `G`, `tn`] strip_assume_tac) >>
  drule_all compile_alloc_buffer_ghost_frame >>
  disch_then (qspec_then `PG` assume_tac) >>
  drule_all compile_alloc_buffer_kept_frame >>
  disch_then (qspec_then `PG` assume_tac) >>
  qexistsl_tac [`out`, `G1`, `tn1`, `t`] >> simp[] >>
  gvs[] >> suspend "position"
QED

Resume compile_alloc_buffer_vv_counted_frame[position]:
  qpat_x_assum `ghost_inv _ _ _ _ _ _ u` mp_tac >>
  rpt (pop_assum kall_tac) >> Cases_on `d`
  >- (simp[ghost_inv_def, ptr_covers_def, stor_taint_ok_def, lookup_var_def,
           return_buf_ptr_def] >> strip_tac >> simp[]) >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  simp[ghost_inv_def, return_buf_ptr_def, ptr_covers_def,
       stor_taint_ok_def, lookup_var_def] >> strip_tac >> simp[]
QED

Finalise compile_alloc_buffer_vv_counted_frame
