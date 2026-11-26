(* Transport the linked ghost and immutable frames at the reached slice endpoint. *)
Theory bodyCalldataSliceLinkedFrameMods
Ancestors
  bodyMethodIdScratchFrameMods bodyShaRegisteredFrameMods
  bodyPtrBytestringBuiltinsWindowGhost bodyFullShadowBodyInv
  bodyPtrDefs loweringStateRelDefs loweringPosts compileEnv venomState
  finite_map pred_set ptrDiscipline valueEncodingDefs

Theorem calldata_slice_linked_frame_mods:
  ghost_inv_at_mods D lo d ce cx mid G tn s /\
  immutable_frame_mods func ce cx mid s /\
  local_ptrs_rel func ce mid.scopes s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
      lookup_var x z = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!nm b len. local_region ce mid.scopes s nm b len ==>
      mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)) /\
  (!i. i < lo /\ i IN tm.t_mem ==> i IN tn.t_mem) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
  z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables /\
  z.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  s.vs_alloca_next <= z.vs_alloca_next /\
  (!aid a len. FLOOKUP z.vs_allocas aid = SOME (a,len) ==>
      FLOOKUP s.vs_allocas aid = SOME (a,len) \/ s.vs_alloca_next <= a) /\
  pure_frame ce func mid sa s z ==>
  ghost_inv_at_mods D lo d ce cx mid HG tm z /\
  immutable_frame_mods func ce cx mid z
Proof
  strip_tac >>
  `ghost_inv_at D 0 d ce cx mid G tn s` by
    (irule method_id_ghost_at_zero >> qexists `lo` >> simp[]) >>
  `stor_taint_ok_at D tm z` by
    (qpat_assum `ghost_inv_at D 0 _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_def]) >>
     fs[stor_taint_ok_at_def]) >>
  `mem_bytes_at 0 0 z.vs_memory = mem_bytes_at 0 0 s.vs_memory` by
    simp[mem_bytes_at_def] >>
  `ghost_inv_at D 0 d ce cx mid HG tm z` by
    (irule ghost_inv_at_local_window_transport >> simp[allocas_from_def] >>
     qexistsl [`G`,`mid`,`func`,`s`,`sa`,`tn`] >> simp[] >>
     first_assum ACCEPT_TAC) >>
  irule sha_registered_frame_mods >> simp[] >>
  qexistsl [`G`,`s`,`sa`,`tn`] >> asm_rewrite_tac[]
QED
