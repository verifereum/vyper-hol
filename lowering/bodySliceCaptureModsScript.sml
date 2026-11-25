(* Common ordinary Slice source capture certificate. *)
Theory bodySliceCaptureMods
Ancestors
  bodySliceDynamicCaptureMods bodySliceFixedCaptureMods

Theorem slice_capture_source_mods:
  (compile_bytestring_src op sm = ((limit,data),sc) /\
   fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
   local_ptrs_reserved ce sm /\ (!x. op = Var x ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   return_buf_frame d ce sm s /\ alloca_history func s /\
   expr_type e = BaseT bt /\ is_bytestring_type (BaseT bt) /\
   evaluate_type (get_tenv cx) (BaseT bt) = SOME tv /\ value_has_type tv v /\
   ptr_val_ok cx (BaseT bt) v op G tn s /\
   storage_trace_domain cx st0 es.storage_trace /\
   (!H. valid_horizon cx st0 H es.storage_trace ==>
     expr_post_mods H ctx func ce cx e es0 sa sm s0 es v op s /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv_at_mods (DF H) lo d ce cx es G tn s) /\
   ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
   s.vs_inst_idx = LENGTH sm.cs_current_insts)
   \/
   (compile_alloc_buffer 32 sm = (buf,sb) /\
   emit_void MSTORE [buf.buf_operand;op] sb = ((),sc) /\
   fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
   local_ptrs_reserved ce sm /\ (!x. op = Var x ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   return_buf_frame d ce sm s /\ alloca_history func s /\
   expr_type e = BaseT (BytesT (Fixed m)) /\
   evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
   ptr_val_ok cx (expr_type e) v op G tn s /\
   storage_trace_domain cx st0 es.storage_trace /\
   (!H. valid_horizon cx st0 H es.storage_trace ==>
     expr_post_mods H ctx func ce cx e es0 sa sm s0 es v op s /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv_at_mods (DF H) lo d ce cx es G tn s) /\
   ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
   s.vs_inst_idx = LENGTH sm.cs_current_insts)
  ==>
  ((?t G' tn' lp dp p bs.
     (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
     limit = Var lp /\ data = Var dp /\ not_fresh_at sc lp /\ not_fresh_at sc dp /\
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,G',tn')) /\
     ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
     t.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func t /\
     eval_operand limit t = SOME (n2w (LENGTH bs)) /\
     op_taint tn' limit = {} /\ op_prov G' limit = NONE /\
     lookup_var dp t = SOME p /\ ptr_covers G' tn' dp t (LENGTH bs) /\
     w2n p + LENGTH bs < dimword (:256) /\
     w2n p + LENGTH bs <= t.vs_alloca_next /\
     mem_bytes_at (w2n p) (LENGTH bs) t.vs_memory = bs /\
     (!i. w2n p <= i /\ i < w2n p+LENGTH bs ==> i NOTIN tn'.t_mem) /\
     t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
     t.vs_alloca_next = s.vs_alloca_next /\ tn'.t_mem = tn.t_mem /\
     (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
     return_buf_frame d ce sc t /\
     (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func ce cx es t /\
       immutable_frame_mods func ce cx es t /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at_mods (DF H) lo d ce cx es G' tn' t))
   \/
   (?t G' tn' root p bs.
     v = BytesV bs /\ LENGTH bs = m /\ m <= 32 /\
     buf.buf_operand = Var root /\ not_fresh_at sc root /\
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,G',tn')) /\
     ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
     t.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func t /\
     eval_operand (Lit (n2w m)) t = SOME (n2w (LENGTH bs)) /\
     op_taint tn' (Lit (n2w m)) = {} /\
     op_prov G' (Lit (n2w m)) = NONE /\
     lookup_var root t = SOME p /\ ptr_covers G' tn' root t (LENGTH bs) /\
     w2n p + LENGTH bs < dimword (:256) /\
     w2n p + LENGTH bs <= t.vs_alloca_next /\
     mem_bytes_at (w2n p) (LENGTH bs) t.vs_memory = bs /\
     (!i. w2n p <= i /\ i < w2n p + LENGTH bs ==> i NOTIN tn'.t_mem) /\
     lo <= w2n p /\ s.vs_alloca_next <= t.vs_alloca_next /\
     allocas_from lo t /\
     FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n p,32) /\
     (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
     (!aid b len. aid < sm.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
     (!name b len. local_region ce es.scopes t name b len ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
     (!a len. a+len <= w2n p \/ w2n p+32 <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
     tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
     tn'.t_imm = tn.t_imm /\
     (!i. i < s.vs_alloca_next /\
       ~(w2n p <= i /\ i < w2n p+32) ==>
       (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
     (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
     return_buf_frame d ce sc t /\
     (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func ce cx es t /\
       immutable_frame_mods func ce cx es t /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at_mods (DF H) lo d ce cx es G' tn' t)))
Proof
  strip_tac
  >- (disj1_tac >> irule slice_dynamic_capture_source_mods >>
      rpt conj_tac >> metis_tac[])
  >- (disj2_tac >> irule slice_fixed_capture_source_mods >>
      rpt conj_tac >> metis_tac[])
QED
