Theory bodyFullExtCallEncoderCallerFrames
Ancestors
  bodyPtrBytestringBuiltinsWindowGhost exprSimProps loweringPosts
  bodyPtrDefs loweringStateRelDefs ptrDiscipline finite_map pred_set

(* Packaging does not change the source scopes. The protected windows
   suffice for writeback and ghost transport at the same encoder exit. *)
Theorem extcall_encoder_caller_frames:
  ghost_inv_at D lo d cenv cx ee Gq tq q /\
  local_ptrs_rel func cenv ee.scopes q /\
  local_ptrs_reserved cenv se /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x w. not_fresh_at se x /\ lookup_var x q = SOME w ==>
    lookup_var x t = SOME w) /\
  (!x. not_fresh_at se x ==> FLOOKUP Gf x = FLOOKUP Gq x /\
    op_taint tf (Var x) = op_taint tq (Var x)) /\
  (!aid row. FLOOKUP q.vs_allocas aid = SOME row ==>
    FLOOKUP t.vs_allocas aid = SOME row) /\
  (!name b len. local_region cenv ee.scopes q name b len ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len q.vs_memory /\
    (!i. b <= i /\ i < b+len /\ i IN tf.t_mem ==> i IN tq.t_mem)) /\
  (!aid b len. FLOOKUP q.vs_allocas aid = SOME (b,len) /\ aid < se.cs_next_id ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len q.vs_memory /\
    (!i. b <= i /\ i < b+len /\ i IN tf.t_mem ==> i IN tq.t_mem)) /\
  stor_taint_ok_at D tf t /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo q.vs_memory /\
  (!i. i < lo /\ i IN tf.t_mem ==> i IN tq.t_mem) /\
  allocas_from lo t /\ lo <= t.vs_alloca_next ==>
  wb_frame cenv ee ee se q t /\
  ghost_kept_at lo cenv ee se Gq tq q Gf tf /\
  ghost_inv_at D lo d cenv cx ee Gf tf t
Proof
  strip_tac >> conj_tac
  >- (simp[wb_frame_def] >> conj_tac
      >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
      irule locals_kept_regions >> rpt strip_tac >>
      first_x_assum drule >> simp[]) >>
  conj_tac
  >- (simp[ghost_kept_at_def] >> rpt conj_tac >> rpt strip_tac >>
      first_x_assum drule_all >> simp[]) >>
  qpat_assum `ghost_inv_at D lo d cenv cx ee Gq tq q`
    (mp_then Any irule ghost_inv_at_local_window_transport) >>
  qpat_assum `local_ptrs_rel func cenv ee.scopes q` (irule_at Any) >>
  qpat_assum `local_ptrs_reserved cenv se` (irule_at Any) >>
  simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
