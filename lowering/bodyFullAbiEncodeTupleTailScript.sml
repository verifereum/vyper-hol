(* Output allocation and encoding after native tuple staging. *)
Theory bodyFullAbiEncodeTupleTail
Ancestors
  bodyFullAbiEncodeSetupTail bodyFullAbiEncodeFinish bodyFullAbiEncodeSuffix
  bodyFullAbiEncodeUniformTranslation bodyFullAbiEncodeNonwordWindow
  bodyFullAbiEncodeArgs bodySimFull bodyInvNoDalloca gasOutcomeFullCompose
  abiBuiltinEncodeCode abiBuiltinEncodeWord abiTupleEncodeMemory compileEnv abiEncodeArgsSim
  exprSimAbiEncodeTupleResources abiBuiltinAllocation allocationPtr
  bodyFullUnwrapRun ptrSafetyTransport fragGasSeqPtr fragExecPtr
  instMemFrontier memSafeRun literalAllocPathPtr exprLoweringProps localPtrsProps
  loweringHalt fragExec fragExecMem emitHelperProps rich_list words
  venomMemDefs bodyPtrDefs
  venomExecSemantics venomState venomInst ptrDiscipline finite_map pred_set


Theorem abi_encode_alloc_rows_origin:
  compile_alloc_buffer cap sa = (buf,sc) /\ fn_has_code sa sc func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ alloca_room ctx func s /\ fn_inst_ids_distinct func /\
  cap < dimword(:256) /\
  (!i w p sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?root t b G1 tn1.
    buf.buf_operand = Var root /\ not_fresh_at sc root /\
    (~not_fresh_at sa root) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,G1,tn1)) /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    lookup_var root t = SOME (n2w b) /\ b+cap < dimword(:256) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,cap) /\
    ptr_covers G1 tn1 root t cap /\
    alloca_inv t /\ alloca_room ctx func t /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,sz)) /\
    (!i w p sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) /\
    t.vs_labels = s.vs_labels /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_data_section = s.vs_data_section /\
    t.vs_call_ctx = s.vs_call_ctx /\
    tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule compile_alloc_buffer_emission >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)] [p]) (fn_insts func)` by
    (drule_all fn_has_code_split >> strip_tac >>
     drule_all emit_inst_fn_member >> gvs[]) >>
  drule_at (Pat `MEM (mk_inst _ _ _ _) (fn_insts _)`)
    literal_alloca_step_resources_ptr >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `ptr_covers g1 tn1 _ _ _` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sc.cs_current_insts),g1,tn1)` by
    (gen_tac >> irule emitted_origin_ptr_path >> simp[] >>
     qexists `[mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)] [p]]` >>
     qexists `sa` >>
     simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges, mk_inst_def,
       inst_dload_in_section_def, run_inst_seq_def, is_terminator_def] >>
     conj_tac >- metis_tac[operand_11] >>
     simp[GSYM mk_inst_def, inst_seq_ptr_def, Abbr `g1`, Abbr `tn1`] >>
     irule ptr_inst_ok_lower_bound_transport >>
     simp[] >> qexists `0` >> simp[ptr_inst_ok_alloca]) >>
  qexistsl [`p`,`t with vs_inst_idx := LENGTH sc.cs_current_insts`,`b`,`g1`,`tn1`] >>
  suspend "endpoint"
QED
Resume abi_encode_alloc_rows_origin[endpoint]:
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def,
       AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]) >>
  `p = STRING #"%" (toString sa.cs_next_var)` by metis_tac[operand_11] >>
  `alloca_inv (t with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (qpat_x_assum `alloca_inv t` mp_tac >>
     simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]) >>
  `alloca_room ctx func (t with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (irule alloca_room_fields >> qexists `t` >> simp[]) >>
  `t.vs_labels = s.vs_labels /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_data_section = s.vs_data_section /\
   t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def,
       AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]) >>
  `tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    simp[Abbr `tn1`, step_taint_def, out_taint_def, mk_inst_def,
      adopt_reset_def, store_taint_def, imm_taint_def] >>
  simp[] >>
  fs[ptr_covers_def, eval_operand_def, lookup_var_def] >>
  conj_tac >- metis_tac[optionTheory.SOME_11] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    (strip_tac >> gvs[]) >>
  drule_at (Pat `step_inst_base _ _ = _`) literal_alloca_old_observations >>
  disch_then (qspec_then `x` mp_tac) >>
  simp[Abbr `g1`, Abbr `tn1`, lookup_var_def]
QED
Finalise abi_encode_alloc_rows_origin

(* The physical staging endpoint is fixed before any horizon is inspected. *)
Theorem abi_encode_staged_tuple_full_tail:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  compile_abi_encode_args compile_expr ce args origin = (ops,st) /\
  compile_alloc_buffer (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) st =
    (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0
    (ZIP (ops,MAP (lowered_value_type ce) args)) allocated = ((),staged) /\
  lower_abi_encode ensure (OPTION_MAP bytes_method_id_word mid) buf.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)))
    (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))) staged =
      (out,final_st) /\
  fn_has_code origin st func /\ fn_has_code st allocated func /\
  fn_has_code allocated staged func /\ fn_has_code staged final_st func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce origin /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  return_buf_frame d ce origin s0 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  eval_exprs cx args es = (INL vs,ee) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ?ts. LENGTH ts = LENGTH args /\
    abi_args_post H ctx func ce cx es origin st s0 ee args ops vs initial /\
    (!i. i < LENGTH args ==>
      evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME (EL i ts) /\
      value_has_type (EL i ts) (EL i vs) /\
      type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size (EL i ts) /\
      type_memory_size (EL i ts) < 2**64) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn initial /\
    ghost_kept_at lo ce es origin G0 tn0 s0 G tn /\
    alloca_history func initial /\ s0.vs_alloca_next <= initial.vs_alloca_next) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  LENGTH tvs = LENGTH args /\ LENGTH vs = LENGTH args /\
  (!i. i < LENGTH args ==>
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME (EL i tvs)) /\
  buf.buf_operand = Var root /\ not_fresh_at staged root /\
  lookup_var root prepared = SOME bw /\
  ptr_covers Gp tnp root prepared (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) /\
  w2n bw + abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)) < dimword(:256) /\
  lo <= w2n bw /\
  (!mem. mem_agree_outside tnp.t_mem prepared.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n bw) mem) /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = staged.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH staged.cs_current_insts /\
  prepared.vs_allocas = (abi_builtin_allocate_state st.cs_next_id
    (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) initial).vs_allocas /\
  prepared.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id
    (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) initial).vs_alloca_next /\
  allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\
  alloca_history func prepared /\ local_ptrs_rel func ce ee.scopes prepared /\
  locals_kept ce ee ee initial prepared /\
  prepared.vs_labels = initial.vs_labels /\ prepared.vs_accounts = initial.vs_accounts /\
  prepared.vs_transient = initial.vs_transient /\
  prepared.vs_data_section = initial.vs_data_section /\
  prepared.vs_call_ctx = initial.vs_call_ctx /\
  initial.vs_alloca_next <= prepared.vs_alloca_next /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (initial,G,tn) [] (OK prepared,Gp,tnp)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d ce cx ee Gp tnp prepared /\
    ghost_kept_at lo ce es origin G0 tn0 s0 Gp tnp) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    ((\vs ee. ((case evaluate_type_builtin cx (AbiEncode ensure mid) ty
       (MAP expr_type args) vs of INL w => INL (Value w) | INR err => INR (Error err)),ee)) vs)
    (ee,initial,G,tn)
    (\H res ef Gf tnf t. ?tv. res = INL tv /\
      vv_post H ctx func ce cx (TypeBuiltin ann (AbiEncode ensure mid) ty args)
        es origin final_st s0 ef tv (LocatedValue ann (mk_ptr out LocMemory)) t /\
      vv_store_bound cx (post_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) ty args))
        (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) ty args))
        ef tv (LocatedValue ann (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = final_st.cs_current_bb /\ t.vs_inst_idx = LENGTH final_st.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ef Gf tnf t /\
      ptr_vv_ok cx (post_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) ty args))
        tv (LocatedValue ann (mk_ptr out LocMemory)) ef Gf tnf t /\
      (ce.ce_is_ctor /\ vv_location (LocatedValue ann (mk_ptr out LocMemory)) = SOME LocCode ==>
        ?val. read_result cx tv ef = (INL val,ef) /\
        !rt w. evaluate_type (get_tenv cx)
          (post_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) ty args)) = SOME rt /\
          eval_operand (vv_operand (LocatedValue ann (mk_ptr out LocMemory))) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
      (!t' op. LocatedValue ann (mk_ptr out LocMemory) = StackValue t' op /\
        ~is_word_type (post_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) ty args)) ==>
        ptr_buf_ok ce (TypeBuiltin ann (AbiEncode ensure mid) ty args) op Gf t) /\
      (!t' p. LocatedValue ann (mk_ptr out LocMemory) = LocatedValue t' p /\
        p.ptr_location = LocMemory ==>
        ptr_buf_ok ce (TypeBuiltin ann (AbiEncode ensure mid) ty args) p.ptr_operand Gf t) /\
      ghost_kept_at lo ce es origin G0 tn0 s0 Gf tnf)
    (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> ?ts. _` (drule_then strip_assume_tac) >>
  drule lower_abi_encode_trace >> strip_tac >>
  rename1 `abi_builtin_encode_setup _ _ staged = (setup_ops,ready)` >>
  rename1 `compile_abi_encode_to_buf _ _ _ ready = (len,body_end)` >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  `cs_extends staged ready /\ cs_extends ready body_end /\ cs_extends body_end final_st` by
    (conj_tac >- (irule cs_extends_same_block >> simp[]) >>
     conj_tac >- metis_tac[compile_abi_encode_to_buf_extends] >>
     irule cs_extends_same_block >> simp[]) >>
  `fn_has_code staged ready func /\ fn_has_code ready body_end func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  `local_ptrs_reserved ce st` by
    (irule local_ptrs_reserved_next_var >> qexists `origin` >> simp[] >>
     mp_tac (Q.SPECL [`args`,`ce`,`origin`] abi_args_compile_mono) >>
     simp[ci_mono_def,cs_extends_def]) >>
  drule_at (Pat `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_encode_args_registered_phase_rows >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_abi_tuple _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (qspec_then `prepared` mp_tac) >>
  disch_then (qspec_then `func` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `sb` (qx_choose_then `p`
    (MAP_EVERY assume_tac o CONJUNCTS))) >>
  drule_at (Pat `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_encode_args_tuple_allocation_resources >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `sb0` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `alloca_inv prepared /\ alloca_room ctx func prepared` by
    (conj_tac
     >- (irule alloca_inv_fields >> goal_assum (drule_at Any) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule alloca_room_fields >> goal_assum (drule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule abi_builtin_encode_setup_trace >> strip_tac >>
  rename1 `compile_alloc_buffer _ staged = (output_buf,output_allocated)` >>
  FAIL_TAC "tuple tail output allocation"
QED
