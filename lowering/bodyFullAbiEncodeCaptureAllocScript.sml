(* Resources of a successful vv child across the capture allocation. *)
Theory bodyFullAbiEncodeCaptureAlloc
Ancestors
  bodyFullAllocaFresh abiEncodeMaterialize bodyPtrIfExpAllocSource
  bodySimFull robustCopyTransportPtr exprSimMemDefs abiArgsLabelBoundary ptrDiscipline
  bodyPtrDefs loweringPosts exprLoweringProps exprSimProps localPtrsProps
  valueTypingMemoryProps compileEnv exprLowering context venomState arithmetic finite_map
  loweringStateRelDefs venomMemDefs valueEncodingTyping

Theorem capture_alloc_ptr_vv_frame[local]:
  stmt_state_rel H ctx func ce cx ee s /\
  vv_at ce cx ty sa sm ee raw vv s /\ ptr_vv_ok cx ty raw vv ee G tn s /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv) /\
  op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv) /\
  (!x. vv_operand vv = Var x ==> FLOOKUP Ga x = FLOOKUP G x) /\
  u.vs_memory = s.vs_memory /\ u.vs_accounts = s.vs_accounts /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_transient = s.vs_transient /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) ==>
  ptr_vv_ok cx ty raw vv ee Ga ta u
Proof
  strip_tac >>
  `!rt v p. val_wf rt v /\
    (!i. p <= i /\ i < p + val_footprint rt v ==> i < s.vs_alloca_next) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v p mem) ==>
    !mem. mem_agree_outside ta.t_mem u.vs_memory mem ==> val_in_memory rt v p mem` by
    (rpt gen_tac >> strip_tac >> rpt strip_tac >>
     irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`,`u.vs_memory`,`tn.t_mem`,`ta.t_mem`,
       `{i | s.vs_alloca_next <= i}`] >> simp[] >> metis_tac[NOT_LESS_EQUAL]) >>
  Cases_on `vv`
  >- (gvs[vv_operand_def, ptr_vv_ok_def, ptr_val_ok_def] >>
      strip_tac >> gvs[ptr_mem_ok_def] >> rpt strip_tac >>
      `val_wf tv v /\
       (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i < s.vs_alloca_next)` by
        (irule vv_at_memory_footprint >>
         qexistsl_tac [`H`,`ce`,`ctx`,`cx`,`ee`,`func`,`raw`,`sa`,`sm`,`ty`,`StackValue t o'`] >>
         simp[vv_operand_def] >> metis_tac[]) >>
      metis_tac[]) >>
  gvs[vv_operand_def, ptr_vv_ok_def] >>
  strip_tac >> gvs[] >>
  `!tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand p.ptr_operand s = SOME w ==>
    val_wf tv v /\ (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i < s.vs_alloca_next)` by
    (metis_tac[located_vv_at_memory_footprint]) >>
  gvs[ptr_mem_ok_def] >> metis_tac[]
QED

Theorem abi_encode_capture_alloc_resources:
  vv_post (H : (bool # 'a word # type_value) list # num list) ctx func ce cx e es sa sm s0 ee raw vv s /\
  ghost_inv_at D lo d ce cx ee G tn s /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  stmt_state_rel (H0 : (bool # 'a word # type_value) list # num list) ctx func ce cx es s0 /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv s /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx raw ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        value_has_type rt v /\ w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Ga x = FLOOKUP G x /\ op_taint ta (Var x) = op_taint tn (Var x)) /\
  u with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
    vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx |> = s /\
  (!H' : (bool # 'a word # type_value) list # num list. stmt_state_rel H' ctx func ce cx ee s ==> stmt_state_rel H' ctx func ce cx ee u) /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP u.vs_allocas aid = SOME row) /\
  allocas_from lo u /\ lo <= s.vs_alloca_next /\ s.vs_alloca_next <= u.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
  (!i. i IN ta.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < endpos)) ==>
  vv_post H ctx func ce cx e es sa sm s0 ee raw vv u /\
  ghost_inv_at D lo d ce cx ee Ga ta u /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Ga ta /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee Ga ta u /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op Ga u) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand Ga u) /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv u /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx raw ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside ta.t_mem u.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem))
Proof
  strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_accounts = s.vs_accounts /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_transient = s.vs_transient /\
   u.vs_labels = s.vs_labels` by
    (qpat_assum `u with <| vs_vars := _; vs_allocas := _;
      vs_alloca_next := _; vs_inst_idx := _ |> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
   op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv) /\
   op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv)` by
    (Cases_on `vv_operand vv` >> gvs[eval_operand_def, op_taint_def, op_prov_def]) >>
  `stmt_state_rel H ctx func ce cx ee s /\
   vv_at ce cx (post_value_type ce e) sa sm ee raw vv s` by fs[vv_post_def] >>
  conj_tac >- (irule materialize_vv_post_alloc_storage_frame >>
    conj_tac >- (qpat_x_assum `!h. stmt_state_rel h ctx func ce cx ee s ==> stmt_state_rel h ctx func ce cx ee u` (qspec_then `H` mp_tac) >> simp[]) >>
    qexistsl_tac [`s`,`sm`] >> simp[contract_storage_def, contract_transient_def]) >>
  conj_tac >- (irule alloc_buffer_ghost_inv_at >>
    conj_tac >- simp[] >>
    qexistsl_tac [`G`,`H`,`ctx`,`endpos`,`func`,`s`,`sm`,`tn`] >> simp[]) >>
  conj_tac >- suspend "kept" >>
  conj_tac >- (irule capture_alloc_ptr_vv_frame >>
    qexistsl_tac [`G`,`H`,`ce`,`ctx`,`func`,`s`,`sa`,`sm`,`tn`] >> simp[] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> Cases_on `vv` >> gvs[vv_operand_def, ptr_buf_ok_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> Cases_on `vv` >> gvs[vv_operand_def, ptr_buf_ok_def] >> metis_tac[]) >>
  conj_tac >- (Cases_on `vv` >> gvs[vv_store_bound_def, vv_operand_def] >> rpt strip_tac >> metis_tac[LESS_EQ_TRANS]) >>
  suspend "ctor"
QED

Resume abi_encode_capture_alloc_resources[kept]:
  irule alloc_buffer_ghost_kept_at >>
  qexistsl_tac [`G`,`endpos`,`s`,`tn`] >> simp[] >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at sm x` by fs[not_fresh_at_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    `b + sz <= s0.vs_alloca_next` by metis_tac[abi_args_local_region_frontier] >> decide_tac) >>
  rpt strip_tac >>
  `off + sz <= s0.vs_alloca_next` by
    (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >> decide_tac
QED
Resume abi_encode_capture_alloc_resources[ctor]:
  strip_tac >>
  qpat_x_assum `ce.ce_is_ctor /\ _ ==> _` mp_tac >> simp[] >> strip_tac >>
  qexists_tac `v` >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`rt`,`w`] mp_tac) >> simp[] >> strip_tac >>
  rpt strip_tac >>
  irule robust_val_in_memory_exterior_frame >> conj_tac >- metis_tac[value_has_type_val_wf] >>
  qexistsl_tac [`s.vs_memory`,`u.vs_memory`,`tn.t_mem`,`ta.t_mem`,
    `{i | s.vs_alloca_next <= i}`] >> simp[] >>
  `val_wf rt v` by metis_tac[value_has_type_val_wf] >>
  `val_footprint rt v <= type_memory_size rt` by metis_tac[val_footprint_le] >>
  decide_tac
QED
Finalise abi_encode_capture_alloc_resources
