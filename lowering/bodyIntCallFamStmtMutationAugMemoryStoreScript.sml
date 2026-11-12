(* Resource landing for a word written through an arbitrary nested local place. *)
Theory bodyIntCallFamStmtMutationAugMemoryStore
Ancestors
  bodyIntCallFamStmtMutationResource bodyIntCallAssembly placeStore
  placeMemoryLiveRegion vyperPlaceFrames stmtSimReturn venomMemProofs
  bodyIntCallJointContract compileEnv exprLoweringProps valueEncodingProps
  venomMemDefs venomState loweringPosts loweringStateRelDefs

Theorem intcall_memory_place_word_resources:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  place_ptr_rel ce fp.jc_cx s (PlaceR (MemoryPlace id path)) w
    (SOME LocMemory) (Type ty) /\
  is_word_type ty /\ evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  value_has_type tv v /\
  (!entry t0. lookup_scopes id es.scopes = SOME entry /\
     ce.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv fp.jc_cx) t0 = SOME entry.type) /\
  write_place fp.jc_cx (MemoryPlace id path) v es = (INL (),ee) /\
  expr_sim_inv ce fp.jc_cx env ee /\ local_ptrs_reserved ce sb /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) ==>
  intcall_joint_res fp ce env ee sb
    (mstore (w2n w) (typed_val_to_w256 tv v) s with vs_inst_idx := idx)
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   expr_sim_inv ce fp.jc_cx env es /\ local_ptrs_reserved ce sa` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee
    (mstore (w2n w) (typed_val_to_w256 tv v) s)` by
    (irule place_store_word_memory_state >> metis_tac[]) >>
  `?n b len. local_region ce es.scopes s n b len /\
     b <= w2n w /\ w2n w + type_memory_size tv <= b + len` by
    (drule memory_place_live_region >> simp[] >>
     disch_then drule_all >> simp[]) >>
  `type_memory_size tv = 32` by metis_tac[word_type_sizes] >>
  `!a k. fp.jc_prot a k ==> regions_disjoint a k (w2n w) 32` by
    (rpt strip_tac >>
     `regions_disjoint a k b len` by metis_tac[intcall_local_region_protected] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!a k. fp.jc_prot a k ==>
    mem_bytes_at a k (mstore (w2n w) (typed_val_to_w256 tv v) s).vs_memory =
    mem_bytes_at a k s.vs_memory` by
    (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!n b k. local_region ce ee.scopes s n b k ==>
            local_region ce es.scopes s n b k` by
    metis_tac[expr_inv_local_regions_transport] >>
  `ee.immutables = es.immutables` by metis_tac[write_memory_place_immutables] >>
  irule intcall_joint_res_mutation >> simp[stmt_state_rel_inst_idx] >>
  rpt conj_tac
  >- fs[intcall_joint_res_def,intcall_expr_res_def]
  >- (fs[intcall_joint_res_def,intcall_expr_res_def,mstore_def,
          intCallFrameTheory.allocas_above_def] >> metis_tac[])
  >- fs[intcall_joint_res_def]
  >- fs[intcall_joint_res_def,intcall_expr_res_def]
  >> qexistsl [`env`,`es`,`s`,`sa`] >>
  simp[mstore_def,lookup_var_def,eval_operand_def,local_region_def] >>
  metis_tac[]
QED

Theorem intcall_memory_place_word_store_path:
  emit_void MSTORE [dst; op] sa = ((),sb) /\
  fn_has_code sa sb fp.jc_func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  eval_operand dst s = SOME w /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  place_ptr_rel ce fp.jc_cx s (PlaceR (MemoryPlace id path)) w
    (SOME LocMemory) (Type ty) /\
  is_word_type ty /\ evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  value_has_type tv v /\
  (!entry t0. lookup_scopes id es.scopes = SOME entry /\
     ce.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv fp.jc_cx) t0 = SOME entry.type) /\
  write_place fp.jc_cx (MemoryPlace id path) v es = (INL (),ee) /\
  expr_sim_inv ce fp.jc_cx env ee /\ local_ptrs_reserved ce sb /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      intcall_joint_res fp ce env ee sb u /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. lookup_var x u = lookup_var x s) /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  qspecl_then [`fp.jc_ctx`,`fp.jc_func`,`LocMemory`] mp_tac
    place_store_emit_run >>
  simp[] >>
  disch_then drule_all >> strip_tac >>
  `intcall_joint_res fp ce env ee sb
    (mstore (w2n w) (typed_val_to_w256 tv v) s with
       vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule intcall_memory_place_word_resources >> metis_tac[]) >>
  qexists `mstore (w2n w) (typed_val_to_w256 tv v) s with
       vs_inst_idx := SUC s.vs_inst_idx` >>
  gvs[mstore_def,lookup_var_def]
QED
