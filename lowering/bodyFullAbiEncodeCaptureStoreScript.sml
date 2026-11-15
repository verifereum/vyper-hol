(* Owned same-type continuation after the successful unwrap endpoint. *)
Theory bodyFullAbiEncodeCaptureStore
Ancestors
  bodyFullAbiEncodeStoreExec bodyFullAbiEncodeStoreFrame bodyPtrDefs
  bodySimFull typedMemoryCopy ptrDiscipline loweringPosts exprSimProps
  venomState valueEncoding valueEncodingDefs finite_map

Theorem abi_encode_capture_store_origin:
  compile_store_memory ce (Var xs) (Var xd) ty ty su = ((),sb) /\
  ty = lowered_value_type ce e /\ ~is_word_type ty /\
  type_memory_bytes ce ty = type_memory_size tv /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  not_fresh_at su xs /\ not_fresh_at su xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_memory_size tv < dimword (:256) /\
  (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  ptr_covers G tn xs s (type_memory_size tv) /\
  FLOOKUP G xd = SOME (w2n dw,type_memory_size tv) /\ op_taint tn (Var xd) = {} /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,type_memory_size tv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  sa.cs_next_var <= su.cs_next_var /\ local_ptrs_reserved ce su /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at su x) /\
  lo <= w2n dw /\
  (!name entry p sz w. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + val_footprint entry.type entry.value <= w2n dw \/
     w2n dw + type_memory_size tv <= w2n w)) /\
  (!aid' off sz. FLOOKUP s0.vs_allocas aid' = SOME (off,sz) /\ aid' < sa.cs_next_id ==>
    off+sz <= w2n dw \/ w2n dw+type_memory_size tv <= off) /\
  (!name b sz. local_region ce es.scopes s0 name b sz ==>
    b+sz <= w2n dw \/ w2n dw+type_memory_size tv <= b) ==>
  ?t Gt tt.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tt)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d ce cx ee Gt tt t /\
       ghost_kept_at lo ce es sa Gi ti s0 Gt tt) /\
    (!mem. mem_agree_outside tt.t_mem t.vs_memory mem ==>
       val_in_memory tv v (w2n dw) mem) /\
    FLOOKUP t.vs_allocas aid = SOME (w2n dw,type_memory_size tv) /\
    lookup_var xd t = SOME dw /\
    FLOOKUP Gt xd = SOME (w2n dw,type_memory_size tv) /\
    ptr_covers Gt tt xd t (type_memory_size tv) /\
    ptr_val_ok cx ty v (Var xd) Gt tt t /\ ptr_buf_ok ce e (Var xd) Gt t /\
    (type_memory_size tv = 0 \/ w2n dw + type_memory_size tv <= t.vs_alloca_next) /\
    typed_copy_state_frame su (w2n dw) (type_memory_size tv) s t /\
    (!p. not_fresh_at su p ==>
       lookup_var p t = lookup_var p s /\ FLOOKUP Gt p = FLOOKUP G p /\
       op_taint tt (Var p) = op_taint tn (Var p)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ptr_covers G tn xd s (type_memory_size tv)` by
    (simp[ptr_covers_def] >> metis_tac[]) >>
  Q.SUBGOAL_THEN `type_memory_size tv = 0 \/ w2n dw + type_memory_size tv <= s.vs_alloca_next` assume_tac
  >- simp[] >>
  drule_all abi_encode_same_type_store_origin >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[] >>
  conj_tac >- (gen_tac >> disch_tac >>
    `ghost_inv_at (DF H) lo d ce cx ee G tn s` by metis_tac[] >>
    drule_all abi_encode_store_exterior_ghost_frame >> simp[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   (!p. not_fresh_at su p ==> lookup_var p t = lookup_var p s)` by
    gvs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `FLOOKUP Gf xd = SOME (w2n dw,type_memory_size tv) /\
   op_taint tnf (Var xd) = {}` by metis_tac[] >>
  simp[] >>
  conj_tac >- (simp[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- suspend "value" >>
  gvs[ptr_buf_ok_def, eval_operand_def]
QED

Resume abi_encode_capture_store_origin[value]:
  `val_store_size tv v <= type_memory_size tv` by metis_tac[val_store_size_le] >>
  simp[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Finalise abi_encode_capture_store_origin
