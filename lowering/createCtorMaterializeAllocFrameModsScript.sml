(* Transport the original expression's value posts across the private ALLOCA.
   The interval of the value stays [sa,sm]; [sm,mid] is the destination's. *)
Theory createCtorMaterializeAllocFrameMods
Ancestors
  createCtorMaterializeAllocFrame createExprSizeExitDefsMods
  abiEncodeMaterialize bodyFullAllocaFresh bodyPtrBopRepresentationFrame
  bodyPtrIfExpAllocSource revertReasonPrefixPtr bodyFullHashKeccakFixed
  bodyMemoryDefs stateRelProj allocaSiteResource logValueFramePtr
  exprSimProps exprSimMemDefs loweringPosts stmtSimDefs loweringStateRelDefs
  exprLoweringProps bodyPtrDefs context ptrDiscipline venomState vyperStorageFootprint words finite_map

Theorem ctor_materialize_alloc_vv_frame_mods:
  read_result cx pv ee = (INL v,ee) /\
  ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\ val_wf rty v /\
  compile_alloc_buffer capacity sm = (buf,mid) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee pv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  ptr_vv_ok cx (post_value_type ce e) pv vv ee G tn s /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx pv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\ return_buf_frame d ce sm s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\
  a with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx |> = s /\
  (!(H':(bool # bytes32 # type_value) list # num list).
    stmt_state_rel H' ctx func ce cx ee s ==> stmt_state_rel H' ctx func ce cx ee a) /\
  allocas_from lo a /\ s.vs_alloca_next <= a.vs_alloca_next /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP a.vs_allocas aid = SOME entry) /\
  (!aid b sz. FLOOKUP a.vs_allocas aid = SOME (b,sz) /\ FLOOKUP s.vs_allocas aid = NONE ==>
     s.vs_alloca_next <= b) /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
  (!i. i IN ta.t_mem <=> i IN tn.t_mem \/
     (s.vs_alloca_next <= i /\ i < w2n w + capacity)) /\
  (!x. not_fresh_at sm x ==> lookup_var x a = lookup_var x s /\
       FLOOKUP Ga x = FLOOKUP G x /\ op_taint ta (Var x) = op_taint tn (Var x)) ==>
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee pv vv a /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta a) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv a /\
  ptr_vv_ok cx (post_value_type ce e) pv vv ee Ga ta a /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op Ga a) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand Ga a) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx pv ee = (INL val,ee) /\
      !rt w0. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) a = SOME w0 ==>
        w2n w0 + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
          val_in_memory rt val (w2n w0) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 Ga ta /\
  return_buf_frame d ce mid a /\ local_ptrs_reserved ce mid /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
  ~a.vs_halted /\ s0.vs_alloca_next <= a.vs_alloca_next /\ a.vs_memory = s.vs_memory /\
  eval_operand (vv_operand vv) a = eval_operand (vv_operand vv) s /\
  ghost_kept_at lo ce ee sm G tn s Ga ta /\ alloca_frame ce ee sm s ce ee a /\
  (!aid off len i. FLOOKUP s.vs_allocas aid = SOME (off,len) /\
    off <= i /\ i < off + len /\ i IN ta.t_mem ==> i IN tn.t_mem)
Proof
  cheat
QED
