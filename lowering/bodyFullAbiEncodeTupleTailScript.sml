(* Output allocation and encoding after native tuple staging. *)
Theory bodyFullAbiEncodeTupleTail
Ancestors
  bodyFullAbiEncodeSetupTail bodyFullAbiEncodeFinish bodyFullAbiEncodeSuffix
  bodyFullAbiEncodeUniformTranslation bodyFullAbiEncodeNonwordWindow
  bodyFullAbiEncodeArgs bodySimFull bodyInvNoDalloca gasOutcomeFullCompose
  abiBuiltinEncodeCode abiBuiltinEncodeWord abiTupleEncodeMemory compileEnv abiEncodeArgsSim
  exprSimAbiEncodeTupleResources abiBuiltinAllocation allocationPtr
  bodyFullUnwrapRun ptrSafetyTransport fragGasSeqPtr fragExecPtr
  instMemFrontier memSafeRun exprLoweringProps localPtrsProps
  normalizerAllocationFrame allocaSiteResource revertAllocationPtr
  decoderGhostFramePtr stateRelProj
  loweringHalt fragExec fragExecMem emitHelper emitHelperProps rich_list words
  venomMemDefs bodyPtrDefs robustCopyTransportPtr exprSimProps
  bodyFullAbiEncodeSetupSourceFrame
  venomExecSemantics venomState venomInst ptrDiscipline finite_map pred_set


Theorem literal_alloca_step_resources_ptr[local]:
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w cap)] [root]) (fn_insts fn) /\
  cap < dimword(:256) /\
  (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) ==>
  ?t b.
    step_inst_base (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s = OK t /\
    lookup_var root t = SOME (n2w b) /\ b+cap < dimword(:256) /\
    FLOOKUP t.vs_allocas id = SOME (b,cap) /\
    ptr_covers
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w cap)] [root]) t)
      (step_taint (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s t tn)
      root t cap /\
    alloca_inv t /\ alloca_room ctx fn t /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,sz)) /\
    (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w)
Proof
  strip_tac >>
  drule_at (Pat `alloca_room _ _ _`)
    (SRULE [] (Q.INST [`inst` |-> `mk_inst id ALLOCA [Lit (n2w cap)] [root]`,
      `n` |-> `n2w cap`, `out` |-> `root`]
      literal_alloca_structural_resources)) >>
  disch_then (drule_at (Pat `MEM (mk_inst _ _ _ _) (fn_insts _)`)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `step_inst_base (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s = OK t` by
    fs[step_inst_base_opcode_eqs, mk_inst_def] >>
  `FLOOKUP t.vs_allocas id = SOME (b,cap)` by fs[mk_inst_def] >>
  `b+cap < dimword(:256)` by
    (drule_all alloca_site_registered_below >>
     drule alloca_room_next_lt >> simp[]) >>
  qexistsl [`t`,`b`] >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  irule (cj 1 alloca_bounds_ptr_covers) >> simp[] >>
  conj_tac >- metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  strip_tac >>
  `id NOTIN FDOM s.vs_allocas` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  drule_at (Pat `MEM _ (fn_insts _)`) alloca_room_fresh >>
  simp[mk_inst_def, FLOOKUP_DEF] >>
  disch_then (qspecl_then [`s`,`ctx`] mp_tac) >>
  simp[FLOOKUP_DEF]
QED

Theorem literal_alloca_old_observations[local]:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s = OK t /\
  x <> root ==>
  lookup_var x t = lookup_var x s /\
  FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w cap)] [root]) t) x =
    FLOOKUP G x /\
  op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s t tn)
    (Var x) = op_taint tn (Var x)
Proof
  strip_tac >>
  reverse conj_tac
  >- simp[step_prov_other_output, step_taint_other_output, mk_inst_def] >>
  drule alloca_step_operand_preserved >>
  disch_then (qspec_then `Var x` mp_tac) >> simp[eval_operand_def]
QED

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
    (buf.buf_operand = Var root /\ not_fresh_at sc root /\
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
      op_taint tn1 (Var x) = op_taint tn (Var x))) /\
    (t.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id cap s).vs_allocas /\
     t.vs_alloca_next = (abi_builtin_allocate_state sa.cs_next_id cap s).vs_alloca_next /\
     (t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
       vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
     allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
     b + cap <= t.vs_alloca_next /\ lo <= b /\
     (!i. i IN tn1.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b+cap)))
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
  conj_tac >- suspend "endpoint" >> suspend "effects"
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
Resume abi_encode_alloc_rows_origin[effects]:
  simp[Abbr `tn1`] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  qpat_x_assum `cap < dimword (:256)` mp_tac >>
  qpat_x_assum `FLOOKUP t.vs_allocas _ = SOME (b,cap)` mp_tac >>
  qpat_x_assum `alloca_inv s` mp_tac >>
  qpat_x_assum `allocas_from lo s` mp_tac >>
  qpat_x_assum `lo <= s.vs_alloca_next` mp_tac >>
  qpat_x_assum `s.vs_inst_idx = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[step_inst_base_opcode_eqs,mk_inst_def,exec_alloca_def,AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[update_var_def,abi_builtin_allocate_state_def,FLOOKUP_UPDATE] >>
  simp[venom_state_component_equality,allocas_from_def,FLOOKUP_UPDATE] >>
  gvs[allocas_from_def,alloca_inv_def,alloca_next_valid_def,
    step_taint_def,mem_taint_def,step_writes_def,written_taint_def,
    new_site_bytes_def,codegenRelTheory.source_memory_write_ranges_def,range_bytes_def,
    codegenRelTheory.sized_source_write_range_def,codegenRelTheory.fixed_source_write_range_def,FLOOKUP_UPDATE,
    EXTENSION] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- metis_tac[]
  >- (gvs[FLOOKUP_DEF,FAPPLY_FUPDATE_THM] >>
      metis_tac[arithmeticTheory.ADD_COMM])
  >- metis_tac[]
  >- metis_tac[] >>
  `b + cap <= s.vs_alloca_next` by metis_tac[] >> simp[FLOOKUP_DEF] >> metis_tac[]
QED
Finalise abi_encode_alloc_rows_origin

(* Allocate the output and run setup on the supplied staging endpoint. *)
Theorem abi_encode_staged_tuple_ready_origin:
  let tys = MAP (lowered_value_type ce) args in
  let n = abi_tuple_bytes ce (ZIP (ops,tys)) in
  let M = abi_size_bound ce.ce_struct_fields (TupleT tys) in
  let mid' = OPTION_MAP bytes_method_id_word mid in
  let k = case mid' of NONE => 0 | SOME _ => 4 in
  let wlen = case mid' of NONE => 0 | SOME _ => 32 in
  let N = 32+32*word_size (M+k) in
  let ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys) in
  let tv = TupleTV tvs in
  let v = ArrayV (TupleV vs) in
  let cap = val_footprint tv v in
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  eval_exprs cx args es = (INL vs,ee) /\
  vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs /\
  abi_args_post H0 ctx func ce cx es origin st s0 ee args ops vs initial /\
  LENGTH tvs = LENGTH args /\ LENGTH vs = LENGTH args /\
  (!i. i < LENGTH args ==>
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs) /\
    type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size (EL i tvs)) /\
  compile_abi_encode_args compile_expr ce args origin = (ops,st) /\
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 (ZIP (ops,tys)) allocated = ((),staged) /\
  lower_abi_encode ensure mid' buf.buf_operand ei M staged = (out,final_st) /\
  fn_has_code st allocated func /\ fn_has_code staged final_st func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce origin /\
  buf.buf_operand = Var src /\ not_fresh_at staged src /\
  lookup_var src prepared = SOME (n2w sb) /\ ptr_covers Gp tnp src prepared n /\
  sb+n < dimword(:256) /\ lo <= sb /\
  FLOOKUP prepared.vs_allocas st.cs_next_id = SOME (sb,n) /\
  sb+n <= prepared.vs_alloca_next /\
  (!mem. mem_agree_outside tnp.t_mem prepared.vs_memory mem ==>
    val_in_memory tv v sb mem) /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = staged.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH staged.cs_current_insts /\
  prepared.vs_allocas = (abi_builtin_allocate_state st.cs_next_id n initial).vs_allocas /\
  prepared.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id n initial).vs_alloca_next /\
  allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\ alloca_history func prepared ==>
  ?a t Gt tnt u Gu tnu p root dp ct rv ready len body_end output_buf.
    (compile_alloc_buffer N staged = (output_buf,a) /\ output_buf.buf_operand = Var root /\
     abi_builtin_encode_setup mid' M staged = ((Var root,Var dp),ready) /\
     compile_abi_encode_to_buf (Var dp) buf.buf_operand ei ready = (len,body_end) /\
     abi_builtin_encode_finish (Var root) len k body_end = ((),final_st) /\
     out = Var root /\ cs_extends staged a /\ cs_extends a ready /\
     fn_has_code ready body_end func /\ fn_has_code body_end final_st func) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (prepared,Gp,tnp) [] (OK u,Gu,tnu)) /\
    (~u.vs_halted /\ u.vs_current_bb = ready.cs_current_bb /\
     u.vs_inst_idx = LENGTH ready.cs_current_insts /\ alloca_history func u /\
     alloca_inv u /\ alloca_room ctx func u /\ allocas_from lo u /\
     lo <= u.vs_alloca_next /\ p+N <= u.vs_alloca_next /\ p+N < dimword(:256) /\ lo <= p) /\
    (eval_operand buf.buf_operand u = SOME (n2w sb) /\ not_fresh_at ready src /\
     ptr_covers Gu tnu src u cap /\ sb+cap <= u.vs_alloca_next /\ op_taint tnu (Var src) = {} /\
     lookup_var root u = SOME (n2w p) /\ not_fresh_at ready root /\ ptr_covers Gu tnu root u N /\
     eval_operand (Var dp) u = SOME (n2w (p+32+k)) /\ not_fresh_at ready dp /\
     ptr_covers Gu tnu dp u M /\ op_taint tnu (Var dp) = {}) /\
    (FLOOKUP u.vs_allocas st.cs_next_id = SOME (sb,n) /\
     FLOOKUP u.vs_allocas staged.cs_next_id = SOME (p,N) /\
     cap = n /\ venomMemDefs$regions_disjoint (sb,cap) (p,N) /\
     (!mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==>
       abi_encoder_window_input ei ct rv sb cap mem) /\
     enc ct rv = enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP expr_type args))) (ListV avs) /\
     LENGTH (enc ct rv) <= M /\ 32+k+LENGTH (enc ct rv) <= N /\
     (case mid' of NONE => T | SOME w =>
       !mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==> mem_word_at (p+32) mem = w << 224) /\
     (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_id IN frag_ids ready body_end /\ FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
       sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
       venomMemDefs$regions_disjoint (p+32+k,LENGTH (enc ct rv)) (b,sz) /\
       venomMemDefs$regions_disjoint (p+32,k) (b,sz))) /\
    ((!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (prepared,Gp,tnp) [] (OK t,Gt,tnt)) /\
     alloca_history func t /\
     t.vs_allocas = (abi_builtin_allocate_state staged.cs_next_id N prepared).vs_allocas /\
     t.vs_alloca_next = (abi_builtin_allocate_state staged.cs_next_id N prepared).vs_alloca_next /\
     (t with <|vs_vars := prepared.vs_vars; vs_allocas := prepared.vs_allocas;
       vs_alloca_next := prepared.vs_alloca_next; vs_inst_idx := prepared.vs_inst_idx|>) = prepared /\
     prepared.vs_alloca_next <= t.vs_alloca_next /\
     (!x. not_fresh_at staged x ==>
       lookup_var x t = lookup_var x prepared /\ FLOOKUP Gt x = FLOOKUP Gp x /\
       op_taint tnt (Var x) = op_taint tnp (Var x)) /\
     (!i. i IN tnt.t_mem <=> i IN tnp.t_mem \/ (prepared.vs_alloca_next <= i /\ i < p+N)) /\
     tnt.t_stor = tnp.t_stor /\ tnt.t_trans = tnp.t_trans /\ tnt.t_imm = tnp.t_imm) /\
    ((!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,Gt,tnt) [] (OK u,Gu,tnu)) /\
     typed_copy_state_frame a (p+32) wlen t u /\
     u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
     tnu.t_mem = tnt.t_mem DIFF {i | p+32 <= i /\ i < p+32+wlen} /\
     tnu.t_stor = tnt.t_stor /\ tnu.t_trans = tnt.t_trans /\ tnu.t_imm = tnt.t_imm /\
     (!op. (!x. op = Var x ==> not_fresh_at a x) ==>
       eval_operand op u = eval_operand op t /\ op_taint tnu op = op_taint tnt op /\
       op_prov Gu op = op_prov Gt op) /\
     (!D d ce cx es.
       ghost_inv_at D lo d ce cx es Gt tnt t /\ local_ptrs_rel func ce es.scopes t /\
       (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
       (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
       (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
       (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at a x) /\
       (!name b sz. local_region ce es.scopes t name b sz ==>
         loweringStateRelDefs$regions_disjoint (p+32) wlen b sz) ==>
       ghost_inv_at D lo d ce cx es Gu tnu u) /\
     (!ce es origin G0 tn0 s0.
       ghost_kept_at lo ce es origin G0 tn0 s0 Gt tnt /\
       (!x. not_fresh_at origin x ==> not_fresh_at a x) ==>
       ghost_kept_at lo ce es origin G0 tn0 s0 Gu tnu))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  drule_at (Pat `eval_exprs _ _ _ = _`)
    (SIMP_RULE bool_ss [LET_THM] abi_encode_args_numerical_capacity) >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `vyper_to_abi_list _ _ _ = _`)) >>
  disch_then (qspec_then `OPTION_MAP bytes_method_id_word mid` mp_tac) >>
  simp_tac bool_ss [] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
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
  disch_then (qx_choose_then `sbrow` (qx_choose_then `p`
    (MAP_EVERY assume_tac o CONJUNCTS))) >>
  drule_at (Pat `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_encode_args_tuple_allocation_resources >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  (impl_tac >-
    (simp_tac bool_ss [boolTheory.DE_MORGAN_THM] >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
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
  `cs_extends address_st ready` by
    (qpat_x_assum `abi_builtin_encode_method_id _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `OPTION_MAP bytes_method_id_word mid` >>
     simp[abi_builtin_encode_method_id_def,comp_bind_def,comp_ignore_bind_def,
       comp_return_def,emit_op_def,emit_void_def,fresh_var_def,fresh_id_def,emit_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
     simp[cs_extends_def,inst_extends_def,IS_PREFIX_APPEND]) >>
  `fn_has_code staged output_allocated func` by
    (irule (cj 1 fn_has_code_split) >>
     conj_tac >- metis_tac[compile_alloc_buffer_extends] >>
     qexists `ready` >> simp[] >>
     irule cs_extends_trans >> qexists `address_st` >>
     simp[] >>
     qpat_x_assum `emit_op _ _ output_allocated = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     qmatch_asmsub_abbrev_tac `emit_op opc operands output_allocated` >>
     mp_tac (Q.SPECL [`opc`,`operands`,`output_allocated`]
       ci_mono_emit_op) >> simp[ci_mono_def]) >>
  `!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP initial.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w` by
    (qpat_x_assum `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_args_post_def] >>
     disch_then (ACCEPT_TAC o MATCH_MP stmt_state_rel_alloca_size o CONJUNCT1)) >>
  `MEM (mk_inst st.cs_next_id ALLOCA
      [Lit (n2w (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))))]
      [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    (qpat_x_assum `compile_alloc_buffer _ st = _` mp_tac >>
     qpat_x_assum `fn_has_code st allocated func` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule compile_alloc_buffer_emission >> strip_tac >>
     drule compile_alloc_buffer_insts >> strip_tac >>
     drule_all fn_has_code_split >> strip_tac >>
     drule_all emit_inst_fn_member >> gvs[]) >>
  `!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP prepared.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w` by
    (qpat_x_assum `!i w b sz. _` mp_tac >>
     qpat_x_assum `prepared.vs_allocas = _` mp_tac >>
     qpat_x_assum `MEM (mk_inst st.cs_next_id _ _ _) _` mp_tac >>
     qpat_x_assum `fn_inst_ids_distinct func` mp_tac >>
     qpat_x_assum `sb0 + _ < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     qmatch_goalsub_abbrev_tac `abi_builtin_allocate_state site cap initial` >>
     rpt strip_tac >>
     Cases_on `FLOOKUP initial.vs_allocas site = NONE`
     >- (gvs[abi_builtin_allocate_state_def,FLOOKUP_UPDATE] >>
         Cases_on `i.inst_id = site`
         >- (gvs[] >>
             qabbrev_tac `inst = mk_inst i.inst_id ALLOCA [Lit (n2w cap)]
               [STRING #"%" (toString st.cs_next_var)]` >>
             `i = inst` by
               (irule fn_inst_ids_distinct_inj >>
                conj_tac >- simp[Abbr `inst`,mk_inst_def] >>
                qexists `func` >> simp[Abbr `inst`]) >>
             `i.inst_operands = [Lit (n2w cap)]` by
               (qpat_x_assum `i = inst` (pure_once_rewrite_tac o single) >>
                simp[Abbr `inst`,mk_inst_def]) >>
             gvs[w2n_n2w]) >>
         gvs[] >> metis_tac[]) >>
     gvs[abi_builtin_allocate_state_def] >> metis_tac[]) >>
  drule abi_encode_alloc_rows_origin >>
  disch_then (drule_at (Pat `alloca_inv _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`tnp`,`lo`,`explicit`,`ctx`,`PG`,`Gp`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  rename1 `output_buf.buf_operand = Var outroot` >>
  rename1 `lookup_var outroot output_state = SOME (n2w outbase)` >>
  rename1 `ptr_covers Gout tnout outroot output_state _` >>
  `cs_extends output_allocated address_st` by
    (qpat_x_assum `emit_op ADD _ output_allocated = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     qmatch_asmsub_abbrev_tac `emit_op ADD operands output_allocated` >>
     mp_tac (Q.SPECL [`ADD`,`operands`,`output_allocated`] ci_mono_emit_op) >>
     simp[ci_mono_def]) >>
  `fn_has_code output_allocated ready func` by
    (irule (cj 2 fn_has_code_split) >>
     conj_tac
     >- (irule cs_extends_trans >> qexists `address_st` >> simp[]) >>
     qexists `staged` >> simp[] >>
     metis_tac[compile_alloc_buffer_extends]) >>
  qpat_assum `output_buf.buf_operand = Var outroot` (fn th =>
    qpat_x_assum `emit_op ADD _ output_allocated = _`
      (assume_tac o REWRITE_RULE[th]) >>
    qpat_x_assum `abi_builtin_encode_method_id _ _ address_st = _`
      (assume_tac o REWRITE_RULE[th]) >>
    qpat_x_assum `setup_ops = (output_buf.buf_operand,data_ptr)`
      (assume_tac o REWRITE_RULE[th])) >>
  drule_at (Pat `emit_op ADD _ _ = _`) abi_encode_setup_tail_origin >>
  disch_then (drule_at (Pat `abi_builtin_encode_method_id _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code output_allocated _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ outroot _ _`)) >>
  disch_then (qspec_then `(case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME w => 32)` mp_tac) >>
  disch_then (qspecl_then [`outbase`,
    `abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))`,
    `lo`,`explicit`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC])) >>
  strip_tac >>
  rename1 `ptr_covers Gsetup tnsetup dp setup_state _` >>
  `sbrow = sb` by
    (qpat_x_assum `FLOOKUP prepared.vs_allocas st.cs_next_id = SOME (sbrow,_)` mp_tac >>
     qpat_x_assum `FLOOKUP prepared.vs_allocas st.cs_next_id = SOME (sb,_)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  qpat_x_assum `sbrow = sb` SUBST_ALL_TAC >>
  `value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
   type_memory_size (TupleTV tvs) =
     abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))` by
    suspend "source_shape" >>
  `val_wf (TupleTV tvs) (ArrayV (TupleV vs))` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `!mem. mem_agree_outside tnout.t_mem output_state.vs_memory mem ==>
     val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) sb mem` by
    suspend "source_alloc" >>
  `outbase = p` by
    (qpat_x_assum `FLOOKUP output_state.vs_allocas staged.cs_next_id = SOME (outbase,_)` mp_tac >>
     qpat_x_assum `output_state.vs_allocas = _` mp_tac >>
     qpat_x_assum `FLOOKUP (abi_builtin_allocate_state staged.cs_next_id _ prepared).vs_allocas
       staged.cs_next_id = SOME (p,_)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `outbase = p` SUBST_ALL_TAC >>
  `!mem. mem_agree_outside tnsetup.t_mem setup_state.vs_memory mem ==>
     val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) sb mem` by
    suspend "source_setup" >>
  suspend "continuation"
QED
Resume abi_encode_staged_tuple_ready_origin[source_shape]:
  qpat_x_assum `LENGTH tvs = _` mp_tac >>
  qpat_x_assum `LENGTH vs = _` mp_tac >>
  qpat_x_assum `!i. _ ==> evaluate_type _ _ = SOME (EL i tvs) /\ _` mp_tac >>
  qpat_x_assum `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [abi_args_post_def] >> rpt strip_tac
  >- (simp[vyperTypingTheory.value_has_type_def,
        abiTupleValueEncodingTheory.abi_values_have_types,listTheory.LIST_REL_EL_EQN] >>
      metis_tac[]) >>
  `LENGTH ops = LENGTH args` by
    (drule listTheory.LIST_REL_LENGTH >> simp[LENGTH_ZIP]) >>
  simp[abiTuplePropsTheory.abi_tuple_bytes_def,valueEncodingTheory.type_memory_size_def] >>
  simp[listTheory.MAP_ZIP,listTheory.MAP_MAP_o,
    typeLayoutPropsTheory.type_memory_size_list_sum] >>
  AP_TERM_TAC >> irule listTheory.LIST_EQ >> simp[listTheory.EL_MAP] >>
  metis_tac[]
QED
Resume abi_encode_staged_tuple_ready_origin[source_alloc]:
  `output_state.vs_memory = prepared.vs_memory` by
    (qpat_x_assum `(output_state with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|>) = prepared` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  qpat_x_assum `!mem. mem_agree_outside tnp.t_mem _ _ ==> _` mp_tac >>
  qpat_x_assum `val_wf _ _` mp_tac >>
  qpat_x_assum `type_memory_size (TupleTV tvs) = _` mp_tac >>
  qpat_x_assum `sb + _ <= prepared.vs_alloca_next` mp_tac >>
  qpat_x_assum `!i. i IN tnout.t_mem <=> _` mp_tac >>
  qpat_x_assum `output_state.vs_memory = prepared.vs_memory` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`prepared.vs_memory`, `output_state.vs_memory`, `tnp.t_mem`,
    `tnout.t_mem`, `{i | prepared.vs_alloca_next <= i}`] >>
  simp[] >> rpt strip_tac >>
  drule exprSimPropsTheory.val_footprint_le >> strip_tac >> decide_tac
QED
Resume abi_encode_staged_tuple_ready_origin[source_setup]:
  gen_tac >> disch_tac >>
  irule (SIMP_RULE (srw_ss()) [loweringPostsTheory.val_footprint_def]
    (Q.INST [`tv` |-> `TupleTV tvs`, `v` |-> `ArrayV (TupleV vs)`]
      (SPEC_ALL abi_encode_setup_source_robust))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
  qpat_assum `type_memory_size (TupleTV tvs) = _` (pure_once_rewrite_tac o single) >>
  goal_assum (drule_at (Pat `venomMemDefs$regions_disjoint _ _`)) >>
  qexists `tnout` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (POP_ASSUM_LIST (K ALL_TAC) >>
    Cases_on `OPTION_MAP bytes_method_id_word mid` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `tnsetup.t_mem = _` (pure_once_rewrite_tac o single) >>
  REWRITE_TAC[pred_setTheory.DIFF_SUBSET]
QED
Resume abi_encode_staged_tuple_ready_origin[continuation]:
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv)
     (MAP (lowered_value_type ce) args) tvs` by
    (qpat_assum `!i. _ ==> evaluate_type _ _ = SOME (EL i tvs) /\ _` mp_tac >>
     qpat_assum `LENGTH tvs = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[listTheory.LIST_REL_EL_EQN,listTheory.EL_MAP]) >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (MAP (lowered_value_type ce) args) = SOME tvs` by
    (qpat_assum `!i. _ ==> evaluate_type _ _ = SOME (EL i tvs) /\ _` mp_tac >>
     qpat_assum `LENGTH tvs = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> simp[vyperMiscTheory.OPT_MMAP_SOME_IFF] >>
     conj_tac
     >- (simp[listTheory.EVERY_EL,listTheory.EL_MAP] >>
         gen_tac >> disch_then (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >> simp[]) >>
     irule listTheory.LIST_EQ >> simp[listTheory.EL_MAP] >>
     gen_tac >> disch_then (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >> simp[]) >>
  `evaluate_type (get_tenv cx) (TupleT (MAP (lowered_value_type ce) args)) = SOME (TupleTV tvs)` by
    (qpat_assum `type_memory_size (TupleTV tvs) = _` mp_tac >>
     qpat_assum `sb + _ < dimword (:256)` mp_tac >>
     qpat_assum `OPT_MMAP _ _ = SOME tvs` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >>
     simp[vyperValueTheory.evaluate_type_def,vyperValueTheory.evaluate_types_OPT_MMAP] >>
     qpat_x_assum `type_memory_size _ = _` mp_tac >>
     simp[CONJUNCT1 valueEncodingPropsTheory.type_memory_size_slots] >> decide_tac) >>
  `?stvs. LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv)
     (MAP expr_type args) stvs` by
    (drule_all exprSimAbiEncodeRuntimeInputsTheory.abi_encode_body_args_indexed_types >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     qexists `MAP (\e. THE (evaluate_type (get_tenv cx) (expr_type e))) args` >>
     simp[listTheory.LIST_REL_EL_EQN,listTheory.EL_MAP] >>
     rpt strip_tac >>
     rename1 `j < LENGTH vs` >>
     `j < LENGTH args` by decide_tac >>
     qpat_x_assum `!k. _ ==> ?tv. _` (qspec_then `j` mp_tac) >>
     simp[] >> strip_tac >> simp[]) >>
  drule abiEncodeEndpointMetadataTheory.abi_encode_body_arg_types_fit >> strip_tac >>
  drule_all (cj 2 exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_conversion) >>
  disch_then (qspec_then `vs` assume_tac) >>
  drule_all (cj 2 exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_abi_type) >> strip_tac >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    (qpat_assum `expr_body_pre _ _ _ _ _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def,exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  drule exprSimAbiEncodeSourceMetadataTheory.abi_encode_body_evaluated_metadata >> strip_tac >>
  `vyper_to_abi (get_tenv cx) (TupleT (MAP (lowered_value_type ce) args))
       (ArrayV (TupleV vs)) = SOME (ListV avs)` by
    (simp_tac bool_ss [vyperABITheory.vyper_to_abi_def] >>
     qpat_assum `vyper_to_abi_list _ (MAP (lowered_value_type ce) args) vs = _`
       (pure_once_rewrite_tac o single) >>
     qpat_assum `vyper_to_abi_list _ (MAP expr_type args) vs = SOME avs`
       (fn th => simp_tac (srw_ss()) [th])) >>
  `?ct rv. enc ct rv = enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP expr_type args))) (ListV avs) /\
     !mem. mem_agree_outside tnsetup.t_mem setup_state.vs_memory mem ==>
       abi_encoder_window_input
         (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)))
         ct rv sb (val_footprint (TupleTV tvs) (ArrayV (TupleV vs))) mem` by
    suspend "translate" >>
  suspend "join"
QED
Resume abi_encode_staged_tuple_ready_origin[translate]:
  qpat_assum `!tenv. vyper_to_abi_types tenv (MAP (lowered_value_type ce) args) = _`
    (qspec_then `get_tenv cx` (pure_once_rewrite_tac o single o GSYM)) >>
  irule (SIMP_RULE bool_ss [vyperABITheory.vyper_to_abi_type_def]
    (Q.INST [`ty` |-> `TupleT tys`] (SPEC_ALL abi_encode_uniform_translated_footprint_window))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexists `get_tenv cx` >> simp_tac bool_ss [SUBMAP_REFL] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_assum `!ty' tv. evaluate_type _ ty' = SOME tv ==> type_memory_bytes _ _ = _ /\ _`
    (drule_all_then (ACCEPT_TAC o CONJUNCT1))
QED
Resume abi_encode_staged_tuple_ready_origin[join]:
  `alloca_history func output_state` by
    (qpat_assum `!D. gas_origin_ptr_path _ (prepared,_,_) [] _`
       (qspec_then `ARB` assume_tac) >>
     drule_all_then ACCEPT_TAC bodyFullPathHistoryTheory.body_full_path_alloca_history) >>
  qexistsl_tac [`output_allocated`,`output_state`,`Gout`,`tnout`,
    `setup_state`,`Gsetup`,`tnsetup`,`p`,`outroot`,`dp`,`ct`,`rv`,
    `ready`,`len`,`body_end`,`output_buf`] >>
  conj_tac >- suspend "ready_code" >>
  conj_tac >- suspend "ready_path" >>
  conj_tac >- suspend "ready_control" >>
  conj_tac >- suspend "ready_pointers" >>
  conj_tac >- suspend "ready_window" >>
  conj_tac >- suspend "allocation_frame" >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume abi_encode_staged_tuple_ready_origin[ready_code]:
  qpat_assum `setup_ops = (Var outroot,data_ptr)` SUBST_ALL_TAC >>
  qpat_assum `data_ptr = Var dp` SUBST_ALL_TAC >>
  `cs_extends staged output_allocated` by
    (irule compile_alloc_buffer_extends >> goal_assum (drule_at Any)) >>
  `cs_extends output_allocated ready` by
    (irule cs_extends_trans >> qexists `address_st` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `fn_has_code body_end final_st func` by
    (irule (cj 2 fn_has_code_split) >> conj_tac
     >- first_assum ACCEPT_TAC >> qexists `staged` >>
     conj_tac >- metis_tac[cs_extends_trans] >> first_assum ACCEPT_TAC) >>
  qpat_assum `buf.buf_operand = Var src` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `compile_abi_encode_to_buf _ _ _ ready = _`
    (assume_tac o REWRITE_RULE[pairTheory.SND]) >>
  qpat_assum `abi_builtin_encode_finish _ _ _ _ = _`
    (assume_tac o REWRITE_RULE[pairTheory.FST]) >>
  qpat_assum `out = FST _` (assume_tac o REWRITE_RULE[pairTheory.FST]) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC]
QED
Resume abi_encode_staged_tuple_ready_origin[ready_path]:
  qpat_assum `!D. gas_origin_ptr_path _ (prepared,_,_) [] _` mp_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (output_state,_,_) [] _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,listTheory.APPEND]
QED
Resume abi_encode_staged_tuple_ready_origin[ready_control]:
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `fn_inst_ids_distinct func /\ alloca_history func output_state ==> _` irule >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (irule alloca_room_fields >> qexists `output_state` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `setup_state.vs_alloca_next = _` (pure_rewrite_tac o single) >>
  conj_tac >-
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `prepared.vs_alloca_next` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume abi_encode_staged_tuple_ready_origin[ready_pointers]:
  `staged.cs_next_var <= output_allocated.cs_next_var /\
   output_allocated.cs_next_var <= ready.cs_next_var` by
    (qpat_assum `compile_alloc_buffer _ staged = _` mp_tac >>
     qpat_assum `ready.cs_next_var = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule compile_alloc_buffer_emission >> strip_tac >>
     Cases_on `OPTION_MAP bytes_method_id_word mid` >> gvs[]) >>
  `not_fresh_at output_allocated src` by
    (irule stmtFragPtrTheory.not_fresh_at_mono >> qexists `staged` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `not_fresh_at ready src /\ not_fresh_at ready outroot` by
    (conj_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists `output_allocated` >> conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!x. not_fresh_at staged x ==> _`
    (qspec_then `src` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `ptr_covers Gout tnout src output_state
      (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)))` by
    drule_all_then ACCEPT_TAC ptr_covers_frame >>
  qpat_assum `!op. (!x. op = Var x ==> not_fresh_at output_allocated x) ==> _`
    (qspec_then `Var src` mp_tac) >>
  (impl_tac >-
    (simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC)) >>
  REWRITE_TAC[eval_operand_def] >> strip_tac >>
  qpat_assum `data_ptr = Var dp` SUBST_ALL_TAC >>
  qpat_assum `buf.buf_operand = Var src` SUBST_ALL_TAC >>
  simp_tac (srw_ss()) [loweringPostsTheory.val_footprint_def,eval_operand_def] >>
  qpat_assum `type_memory_size (TupleTV tvs) = _` (pure_rewrite_tac o single) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_asm1_tac >-
    (qpat_assum `!x n. not_fresh_at output_allocated x /\ _ ==> _`
       (qspecl_then [`src`,`abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))`] irule) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `setup_state.vs_alloca_next = _` (pure_rewrite_tac o single) >>
     irule arithmeticTheory.LESS_EQ_TRANS >> qexists `prepared.vs_alloca_next` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `ptr_covers Gsetup tnsetup src _ _`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[ptr_covers_def])) >>
  qpat_assum `eval_operand (Var outroot) setup_state = _`
    (assume_tac o REWRITE_RULE[eval_operand_def]) >>
  qpat_assum `eval_operand (Var dp) setup_state = _`
    (assume_tac o REWRITE_RULE[eval_operand_def]) >>
  qpat_assum `ptr_covers Gsetup tnsetup dp _ _`
    (assume_tac o CONJUNCT1 o REWRITE_RULE[ptr_covers_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume abi_encode_staged_tuple_ready_origin[ready_window]:
  conj_tac >-
    (qpat_assum `setup_state.vs_allocas = _` (pure_rewrite_tac o single) >>
     qpat_assum `!aid p sz. FLOOKUP prepared.vs_allocas aid = _ ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  conj_asm1_tac >-
    (qpat_assum `setup_state.vs_allocas = _` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  conj_asm1_tac >-
    (simp_tac (srw_ss()) [loweringPostsTheory.val_footprint_def] >>
     first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `val_footprint (TupleTV tvs) _ = _` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_asm1_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `enc ct rv = _` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  conj_asm1_tac >-
    (qpat_assum `enc ct rv = _` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `sz = 32 /\ venomMemDefs$regions_disjoint
      (sb,abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) (b,sz)` by
    (qpat_assum `FLOOKUP setup_state.vs_allocas inst.inst_id = _` mp_tac >>
     qpat_assum `setup_state.vs_allocas = _` (pure_rewrite_tac o single) >>
     qpat_assum `output_state.vs_allocas = _` (pure_rewrite_tac o single) >>
     strip_tac >>
     qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> _` irule >>
     qexists `inst` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `val_footprint (TupleTV tvs) _ = _` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  suspend "output_scratch_disjoint"
QED
Resume abi_encode_staged_tuple_ready_origin[output_scratch_disjoint]:
  drule_at (Pat `FLOOKUP a.vs_allocas sa.cs_next_id = _`)
    (Q.INST [`a` |-> `setup_state`, `sa` |-> `staged`, `aid` |-> `inst.inst_id`]
      (SPEC_ALL exprSimAbiEncodeNonwordResourcesTheory.abi_encode_setup_scratch_slices)) >>
  disch_then (drule_at (Pat `abi_builtin_encode_setup _ _ staged = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP setup_state.vs_allocas inst.inst_id = _`)) >>
  disch_then (drule_at (Pat `inst.inst_id IN frag_ids _ _`)) >>
  disch_then irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `32 + _ + LENGTH (enc ct rv) <= _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac
QED
Resume abi_encode_staged_tuple_ready_origin[allocation_frame]:
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `(output_state with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|>) = prepared` mp_tac >>
     qpat_assum `prepared.vs_allocas = _` (pure_rewrite_tac o single) >>
     qpat_assum `prepared.vs_alloca_next = _` (pure_rewrite_tac o single) >>
     qpat_assum `prepared.vs_inst_idx = _` (rewrite_tac o single)) >>
  conj_tac >-
    (qpat_assum `prepared.vs_alloca_next = _` (pure_once_rewrite_tac o single o GSYM) >>
     first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `prepared.vs_alloca_next = _` (pure_once_rewrite_tac o single o GSYM) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise abi_encode_staged_tuple_ready_origin
