(* Resource adapter for the single guarded arbitrary-place store endpoint. *)
Theory bodyIntCallFamStmtMutationAssignValueStore
Ancestors
  tuplePlaceValueFrame bodyIntCallFamStmtMutationResource
  bodyIntCallJointPurePath exprSimProps exprLoweringProps
  bodyIntCallJointContract intCallFrame loweringPosts compileEnv venomState

Theorem intcall_assign_value_store_path:
  compile_assign_value ce dst_op loc op (is_word_type dty) src_loc dty sty
    (type_memory_bytes ce dty) sa = ((),sb) /\
  eval_operand dst_op s = SOME w /\
  place_ptr_rel ce fp.jc_cx s (PlaceR p) w (SOME loc) (Type dty) /\
  (!x. dst_op = Var x ==> not_fresh_at sa x) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  type_widens_to (get_tenv fp.jc_cx) sty dty /\
  evaluate_type (get_tenv fp.jc_cx) sty = SOME stv /\ value_has_type stv v /\
  expr_val_rel fp.jc_cx sty v op s /\ ce.ce_target CapMcopy /\
  (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
   ~is_bytestring_type dty /\ dty <> sty ==>
   !sw dtv. eval_operand op s = SOME sw /\
     evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv ==>
     type_memory_size stv = 0 \/
     w2n sw + type_memory_size stv <= w2n w \/
     w2n w + type_memory_size dtv <= w2n sw \/ sw = w /\ stv = dtv) /\
  acyclic_struct_metadata ce.ce_struct_fields /\ storage_place_region fp.jc_cx p /\
  (!id path entry t0. p = MemoryPlace id path /\
     lookup_scopes id ee.scopes = SOME entry /\ ce.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv fp.jc_cx) t0 = SOME entry.type) /\
  (~is_word_type sty ==> !sw. eval_operand op s = SOME sw ==>
     w2n sw + type_memory_size stv <= s.vs_alloca_next /\
     !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
       w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
  (loc = LocMemory ==> !dtv. evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv ==>
     w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
  (!dtv. evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv ==> 0 < type_slot_size dtv) /\
  (loc <> LocMemory /\ dty <> sty /\
   ~(is_bytestring_type dty /\ is_bytestring_type sty) ==> type_alloc_ok ce dty) /\
  write_place fp.jc_cx p v ee = (INL (),ff) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env ee sa s /\
  expr_sim_inv ce fp.jc_cx env' ff /\ ce_locals_declared ce env' /\ locals_alloc_ok ce env' /\
  local_ptrs_reserved ce sb /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  MAP FDOM ee.scopes = MAP FDOM ff.scopes /\ ff.immutables = ee.immutables /\
  (!a n dtv. fp.jc_prot a n /\ loc = LocMemory /\
    evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv ==>
    a+n <= w2n w \/ w2n w + type_memory_size dtv <= a) ==>
  ?t. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid b len a n dtv. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= a /\ a+n <= b+len /\
      evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv /\
      (loc = LocMemory ==> a+n <= w2n w \/ w2n w+type_memory_size dtv <= a) ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
    (!a n dtv. evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv /\
      a+n <= s.vs_alloca_next /\
      (!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
        sa.cs_next_id <= aid ==> a+n <= b \/ b+len <= a) /\
      (loc = LocMemory ==> a+n <= w2n w \/
        w2n w+type_memory_size dtv <= a) ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
    intcall_joint_res fp ce env' ff sb t /\
    allocas_above fp.jc_lo t /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee s /\
   expr_sim_inv ce fp.jc_cx env ee /\ local_ptrs_reserved ce sa /\
   allocas_above fp.jc_lo s` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  drule_all tuple_place_value_run_effect >> strip_tac >>
  `allocas_above fp.jc_lo t /\ s.vs_alloca_next <= t.vs_alloca_next` by
    metis_tac[gas_marked_path_allocas_above,gas_marked_path_alloca_next_mono] >>
  `intcall_joint_res fp ce env' ff sb t` by suspend "resources" >>
  qexists_tac `t` >> gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume intcall_assign_value_store_path[resources]:
  markerLib.RESUME_TAC >>
  qpat_assum `intcall_joint_res _ _ _ _ _ _`
    (mp_then Any mp_tac intcall_joint_res_mutation) >>
  disch_then irule >> simp[] >> suspend "landing"
QED

Resume intcall_assign_value_store_path[landing]:
  markerLib.RESUME_TAC >>
  conj_tac >- fs[intcall_joint_res_def,intcall_expr_res_def] >>
  conj_tac >-
    (rpt strip_tac >> irule local_region_frame >>
     fs[stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def] >> metis_tac[]) >>
  conj_tac >-
    (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> strip_tac >>
     rpt strip_tac >>
     qpat_x_assum `!a n dtv. evaluate_type _ _ = SOME dtv /\ _ ==> _`
       irule >>
     fs[intcall_frame_ok_def,allocas_above_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  gen_tac >> strip_tac >>
  `?x ow. op' = Var x /\ lookup_var x fp.jc_oorig = SOME ow` by
    (fs[intcall_frame_ok_def] >> metis_tac[]) >>
  gvs[] >> fs[intcall_joint_res_def,intcall_expr_res_def] >>
  qpat_x_assum `!op. fp.jc_reserved op ==> eval_operand op s = _` drule >>
  simp[eval_operand_def]
QED

Finalise intcall_assign_value_store_path
