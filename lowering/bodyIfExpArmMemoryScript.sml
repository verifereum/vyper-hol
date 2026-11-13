(* Value-post transport at the concrete bytestring adapter copy endpoint. *)
Theory bodyIfExpArmMemory
Ancestors
  exprSimHash exprSimBufferStore exprSimUnwrapProps exprSimMemDefs valueCopy

(* vv_post_allocated_memory_intro for any result that reads to the value. *)
Theorem vv_post_allocated_memory_read_intro[local]:
  read_result cx raw es' = (INL v,es') /\
  post_value_type cenv e = expr_type e /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ val_in_memory tv v (w2n w) s.vs_memory /\
  stmt_state_rel H ctx func cenv cx es' s /\
  storage_well_formed_on cx es' (FST H) /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand s = SOME w /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (!n lb lsz. local_region cenv es'.scopes s n lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b) /\
  wb_frame cenv es es' sa s0 s /\
  (~expr_has_effect e ==> pure_frame cenv func es sa s0 s) ==>
  vv_post H ctx func cenv cx e es sa sb s0 es' raw
    (LocatedValue (expr_type e) p) s
Proof
  strip_tac >>
  `~expr_has_effect e ==>
     vv_storage_live H cx (LocatedValue (expr_type e) p) es' s` by
    simp[vv_storage_live_def] >>
  irule vv_post_frame_intro >>
  simp[loweringPostsTheory.vv_holds_def, loweringPostsTheory.vv_at_def] >>
  disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem ifexp_copy_endpoint:
  post_value_type cenv e = expr_type e /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
  read_result cx raw ee = (INL v,ee) /\
  val_wf tvt v /\ val_in_memory tvt v src s.vs_memory /\
  val_footprint tvt v <= len /\ len <= sz /\
  stmt_state_rel H ctx func cenv cx ee s /\
  storage_well_formed_on cx ee (FST H) /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\ not_local_ptr cenv ee.scopes p /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id /\
  eval_operand op (mcopy (w2n w) src len s) = SOME w /\
  (!n b k. local_region cenv ee.scopes (mcopy (w2n w) src len s) n b k ==>
     w2n w + sz <= b \/ b + k <= w2n w) /\
  wb_frame cenv es ee sa s0 (mcopy (w2n w) src len s) /\
  (~expr_has_effect e ==> pure_frame cenv func es sa s0 (mcopy (w2n w) src len s)) /\
  w2n w + sz <= (mcopy (w2n w) src len s).vs_alloca_next /\
  val_store_size tvt v <= sz /\
  (!ltv. evaluate_type (get_tenv cx) lt = SOME ltv ==> type_memory_size ltv <= sz) ==>
  vv_post H ctx func cenv cx e es sa sb s0 ee raw
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) (mcopy (w2n w) src len s) /\
  expr_post H ctx func cenv cx e es sa sb s0 ee v op (mcopy (w2n w) src len s) /\
  vv_store_bound cx (expr_type e) lt ee raw
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) (mcopy (w2n w) src len s)
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee (mcopy (w2n w) src len s)` by
    (irule stmt_state_rel_mcopy_alloca >> metis_tac[]) >>
  `val_in_memory tvt v (w2n w) (mcopy (w2n w) src len s).vs_memory` by
    (irule mcopy_val_in_memory >> metis_tac[]) >>
  `vv_post H ctx func cenv cx e es sa sb s0 ee raw
     (LocatedValue (expr_type e) (mk_ptr op LocMemory)) (mcopy (w2n w) src len s)` by
    (irule vv_post_allocated_memory_read_intro >>
     simp[contextTheory.mk_ptr_def] >>
     qexistsl_tac [`inst.inst_id`,`w2n w`,`sz`] >>
     gvs[arithmeticTheory.ADD_COMM] >- (first_assum ACCEPT_TAC) >> decide_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (drule_all vv_post_read_result >> strip_tac >>
      drule expr_post_of_vv_post_memory >> simp[contextTheory.mk_ptr_def]) >>
  simp[vv_store_bound_def, contextTheory.mk_ptr_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_MONO_ADD_EQ]
QED
