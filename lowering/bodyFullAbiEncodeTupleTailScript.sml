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
  bodyFullAbiEncodeReadyFinish bodyFullAbiEncodeResultResources bodyFullAbiEncodePureFrame
  exprSimAbiEncodeTupleResult exprSimAbiEncodeRuntimeInputs exprSimAbiEncodeNonwordCase
  exprSimAbiEncodeExecFrame abiCallerAllocation bodyMemoryDefs

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
  compile_alloc_buffer (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 (ZIP (ops,MAP (lowered_value_type ce) args)) allocated = ((),staged) /\
  lower_abi_encode ensure (OPTION_MAP bytes_method_id_word mid) buf.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)))
    (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))) staged = (out,final_st) /\
  fn_has_code st allocated func /\ fn_has_code staged final_st func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce origin /\
  buf.buf_operand = Var src /\ not_fresh_at staged src /\
  lookup_var src prepared = SOME (n2w sb) /\
  ptr_covers Gp tnp src prepared (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) /\
  sb+(abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) < dimword(:256) /\ lo <= sb /\
  FLOOKUP prepared.vs_allocas st.cs_next_id =
    SOME (sb,(abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)))) /\
  sb+(abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) <= prepared.vs_alloca_next /\
  (!mem. mem_agree_outside tnp.t_mem prepared.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) sb mem) /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = staged.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH staged.cs_current_insts /\
  prepared.vs_allocas = (abi_builtin_allocate_state st.cs_next_id
    (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) initial).vs_allocas /\
  prepared.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id
    (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) initial).vs_alloca_next /\
  allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\ alloca_history func prepared ==>
  ?a t Gt tnt u Gu tnu p root dp ct rv ready len body_end output_buf.
    (compile_alloc_buffer
      (32 + 32 * word_size
         (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
          (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4))) staged = (output_buf,a) /\
     output_buf.buf_operand = Var root /\
     abi_builtin_encode_setup (OPTION_MAP bytes_method_id_word mid)
       (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))) staged = ((Var root,Var dp),ready) /\
     compile_abi_encode_to_buf (Var dp) buf.buf_operand
       (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args))) ready = (len,body_end) /\
     abi_builtin_encode_finish (Var root) len
       (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4) body_end = ((),final_st) /\
     out = Var root /\ cs_extends staged a /\ cs_extends a ready /\
     fn_has_code ready body_end func /\ fn_has_code body_end final_st func) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (prepared,Gp,tnp) [] (OK u,Gu,tnu)) /\
    (~u.vs_halted /\ u.vs_current_bb = ready.cs_current_bb /\
     u.vs_inst_idx = LENGTH ready.cs_current_insts /\ alloca_history func u /\
     alloca_inv u /\ alloca_room ctx func u /\ allocas_from lo u /\
     lo <= u.vs_alloca_next /\
     p+(32 + 32 * word_size
        (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
         (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4))) <=
       u.vs_alloca_next /\
     p+(32 + 32 * word_size
        (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
         (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4))) < dimword(:256) /\
     lo <= p) /\
    (eval_operand buf.buf_operand u = SOME (n2w sb) /\ not_fresh_at ready src /\
     ptr_covers Gu tnu src u (val_footprint (TupleTV tvs) (ArrayV (TupleV vs))) /\
     sb+(val_footprint (TupleTV tvs) (ArrayV (TupleV vs))) <= u.vs_alloca_next /\
     op_taint tnu (Var src) = {} /\
     lookup_var root u = SOME (n2w p) /\
     not_fresh_at ready root /\
     ptr_covers Gu tnu root u
       (32 + 32 * word_size
          (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
           (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4))) /\
     eval_operand (Var dp) u =
       SOME (n2w (p+32+(case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4))) /\
     not_fresh_at ready dp /\
     ptr_covers Gu tnu dp u (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))) /\
     op_taint tnu (Var dp) = {}) /\
    (FLOOKUP u.vs_allocas st.cs_next_id =
      SOME (sb,(abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)))) /\
     FLOOKUP u.vs_allocas staged.cs_next_id =
       SOME (p,(32 + 32 * word_size
          (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
           (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4)))) /\
     (val_footprint (TupleTV tvs) (ArrayV (TupleV vs))) =
       (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) /\
     venomMemDefs$regions_disjoint (sb,val_footprint (TupleTV tvs) (ArrayV (TupleV vs)))
       (p,32 + 32 * word_size
         (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
          (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4))) /\
     (!mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==>
       abi_encoder_window_input
         (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args))) ct rv sb
         (val_footprint (TupleTV tvs) (ArrayV (TupleV vs))) mem) /\
     enc ct rv = enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP expr_type args))) (ListV avs) /\
     LENGTH (enc ct rv) <= (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))) /\
     32+(case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4)+LENGTH (enc ct rv) <=
       (32 + 32 * word_size
          (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
           (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4))) /\
     (case OPTION_MAP bytes_method_id_word mid of NONE => T | SOME w =>
       !mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==> mem_word_at (p+32) mem = w << 224) /\
     (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_id IN frag_ids ready body_end /\ FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
       sz = 32 /\
       venomMemDefs$regions_disjoint (sb,(val_footprint (TupleTV tvs) (ArrayV (TupleV vs)))) (b,sz) /\
       venomMemDefs$regions_disjoint
         (p+32+(case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4),
          LENGTH (enc ct rv)) (b,sz) /\
       venomMemDefs$regions_disjoint (p+32,(case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4)) (b,sz))) /\
    ((!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (prepared,Gp,tnp) [] (OK t,Gt,tnt)) /\
     alloca_history func t /\
     t.vs_allocas = (abi_builtin_allocate_state staged.cs_next_id
       (32 + 32 * word_size
          (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
           (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4)))
       prepared).vs_allocas /\
     t.vs_alloca_next = (abi_builtin_allocate_state staged.cs_next_id
       (32 + 32 * word_size
          (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
           (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4)))
       prepared).vs_alloca_next /\
     (t with <|vs_vars := prepared.vs_vars; vs_allocas := prepared.vs_allocas;
       vs_alloca_next := prepared.vs_alloca_next; vs_inst_idx := prepared.vs_inst_idx|>) = prepared /\
     prepared.vs_alloca_next <= t.vs_alloca_next /\
     (!x. not_fresh_at staged x ==>
       lookup_var x t = lookup_var x prepared /\ FLOOKUP Gt x = FLOOKUP Gp x /\
       op_taint tnt (Var x) = op_taint tnp (Var x)) /\
     (!i. i IN tnt.t_mem <=> i IN tnp.t_mem \/ (prepared.vs_alloca_next <= i /\
       i < p+(32 + 32 * word_size
        (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
         (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4))))) /\
     tnt.t_stor = tnp.t_stor /\ tnt.t_trans = tnp.t_trans /\ tnt.t_imm = tnp.t_imm) /\
    ((!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,Gt,tnt) [] (OK u,Gu,tnu)) /\
     typed_copy_state_frame a (p+32)
       (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 32) t u /\
     u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
     tnu.t_mem = tnt.t_mem DIFF {i | p+32 <= i /\
       i < p+32+(case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 32)} /\
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
         loweringStateRelDefs$regions_disjoint (p+32)
           (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 32) b sz) ==>
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
  `ctx_has_dalloca ctx ==> allocas_below_fmp output_state` by simp[] >>
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

(* The argument bind and the tuple staging have already selected their endpoints. *)
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
  (!tail. eval_exprs cx args (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL vs,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    (?ts. LENGTH ts = LENGTH args /\
    abi_args_post H ctx func ce cx es origin st s0 ee args ops vs initial /\
    (!i. i < LENGTH args ==>
      evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME (EL i ts) /\
      value_has_type (EL i ts) (EL i vs) /\
      type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size (EL i ts) /\
      type_memory_size (EL i ts) < 2**64) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn initial /\
    ghost_kept_at lo ce es origin G0 tn0 s0 G tn /\
    alloca_history func initial /\ s0.vs_alloca_next <= initial.vs_alloca_next) /\
    (~expr_has_effect (TypeBuiltin ann (AbiEncode ensure mid) ty args) ==>
      pure_frame ce func es origin s0 initial)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  LENGTH tvs = LENGTH args /\ LENGTH vs = LENGTH args /\
  (!i. i < LENGTH args ==>
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME (EL i tvs)) /\
  buf.buf_operand = Var src /\ not_fresh_at staged src /\
  lookup_var src prepared = SOME bw /\
  ptr_covers Gp tnp src prepared (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) /\
  w2n bw + abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)) < dimword(:256) /\
  lo <= w2n bw /\
  FLOOKUP prepared.vs_allocas st.cs_next_id = SOME
    (w2n bw,abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) /\
  w2n bw + abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)) <=
    prepared.vs_alloca_next /\
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
  initial.vs_alloca_next <= prepared.vs_alloca_next /\
  (!name z k. local_region ce ee.scopes initial name z k ==>
    loweringStateRelDefs$regions_disjoint (w2n bw)
      (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) z k) /\
  (!z k. loweringStateRelDefs$regions_disjoint (w2n bw)
      (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) z k ==>
    mem_bytes_at z k prepared.vs_memory = mem_bytes_at z k initial.vs_memory) /\
  (!i row. FLOOKUP initial.vs_allocas i = SOME row ==>
    FLOOKUP prepared.vs_allocas i = SOME row) /\
  (!x. not_fresh_at st x ==> lookup_var x prepared = lookup_var x initial) /\
  stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee prepared /\
  copy_static prepared = copy_static (abi_builtin_allocate_state st.cs_next_id
    (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) initial) /\
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
  qpat_assum `!H. valid_horizon _ _ _ _ ==> (?ts. _) /\ _` (drule_then strip_assume_tac) >>
  qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` (assume_tac o SRULE [APPEND_NIL])) >>
  `expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all exprSimAbiEncodeRuntimeInputsTheory.abi_encode_body_args_runtime_typed >>
  simp[vyperTypeExprSoundnessTheory.exprs_runtime_typed_def] >> strip_tac >>
  `?avs. vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs` by
    (irule (cj 2 vyperTypeABITheory.vyper_to_abi_total) >>
     qexists `tvs'` >> simp[vyperTypeDefaultsTheory.values_have_types_LIST_REL,
       listTheory.LIST_REL_MAP1, combinTheory.o_DEF] >> fs[]) >>
  `ts = tvs` by
    (simp[listTheory.LIST_EQ_REWRITE] >> qx_gen_tac `i` >> strip_tac >>
     qpat_assum `!j. j < LENGTH args ==> evaluate_type _ _ = SOME (EL j ts) /\ _`
       (qspec_then `i` mp_tac) >>
     qpat_assum `!j. j < LENGTH args ==> evaluate_type _ _ = SOME (EL j tvs)`
       (qspec_then `i` mp_tac) >> simp[]) >>
  qpat_x_assum `ts = tvs` (SUBST_ALL_TAC o SYM) >>
  `abi_args_post (storage_trace_horizon ee.storage_trace) ctx func ce cx
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) origin st s0
     (ee with gas_obs := []) args ops vs initial` by suspend "observed_args" >>
  `lookup_var src prepared = SOME (n2w (w2n bw))` by simp[] >>
  `!i. i < LENGTH args ==>
       evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME (EL i ts) /\
       value_has_type (EL i ts) (EL i vs) /\
       type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size (EL i ts)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i < LENGTH args ==> _ /\ _ /\ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `LENGTH args = 1 ==> ensure` by (strip_tac >> fs[]) >>
  drule_at (Pat `eval_exprs _ _ _ = _`)
    (SIMP_RULE bool_ss [LET_THM] abi_encode_staged_tuple_ready_origin) >>
  disch_then (drule_at (Pat `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then drule_all >>
  strip_tac >>
  pop_assum (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `a` (qx_choose_then `alloc_run`
      (qx_choose_then `Ga` (qx_choose_then `tna`
        (qx_choose_then `ready_run` (qx_choose_then `Gr`
          (qx_choose_then `tnr` strip_assume_tac)))))))) >>
  qmatch_asmsub_abbrev_tac `compile_abi_encode_to_buf (Var dp) (Var src) ei ready = _` >>
  qmatch_asmsub_abbrev_tac `abi_builtin_encode_setup (OPTION_MAP bytes_method_id_word mid) M staged = _` >>
  qmatch_asmsub_abbrev_tac `abi_builtin_encode_finish _ _ k body_end = _` >>
  qmatch_asmsub_abbrev_tac `compile_alloc_buffer N staged = _` >>
  qabbrev_tac `selector = case OPTION_MAP bytes_method_id_word mid of NONE => []
    | SOME w => abi_builtin_encode_method_bytes w` >>
  `LENGTH selector = k` by (simp[Abbr `selector`, Abbr `k`] >>
    Cases_on `OPTION_MAP bytes_method_id_word mid` >>
    simp[abiBuiltinEncodeMethodTheory.abi_builtin_encode_method_bytes_length]) >>
  `!mem. mem_agree_outside tnr.t_mem ready_run.vs_memory mem ==>
    mem_bytes_at (p+32) (LENGTH selector) mem = selector` by suspend "selector" >>
  suspend "protect_ready"
QED

Resume abi_encode_staged_tuple_full_tail[observed_args]:
  `!b. get_storage cx (ee with gas_obs := []) b = get_storage cx ee b` by
    (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  qpat_assum `abi_args_post _ _ _ _ _ es _ _ _ ee _ _ _ _`
    (strip_assume_tac o SRULE [abi_args_post_def]) >>
  pure_rewrite_tac [abi_args_post_def, exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `storage_well_formed_on cx ee _` mp_tac >>
      qpat_assum `!b. get_storage cx (_ with gas_obs := _) b = _`
        (fn th => rewrite_tac [vyperStorageFootprintTheory.storage_well_formed_on_def,th])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `LIST_REL _ ops _` mp_tac >>
      SIMP_TAC (srw_ss()) [loweringPostsTheory.expr_val_at_def]) >>
  qpat_x_assum `wb_frame ce es ee _ _ _` mp_tac >>
  SIMP_TAC (srw_ss()) [loweringPostsTheory.wb_frame_def,
    loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_encode_staged_tuple_full_tail[selector]:
  qpat_assum `(case OPTION_MAP bytes_method_id_word mid of NONE => T | SOME _ => _)` mp_tac >>
  simp[Abbr `selector`, NoAsms] >>
  Cases_on `OPTION_MAP bytes_method_id_word mid`
  >- simp[NoAsms,valueEncodingDefsTheory.mem_bytes_at_def] >>
  simp[NoAsms,abiBuiltinEncodeMethodTheory.abi_builtin_encode_method_bytes_length] >>
  disch_tac >> gen_tac >> strip_tac >>
  `mem_word_at (p+32) mem = x << 224` by
    (qpat_assum `!m. mem_agree_outside _ _ m ==> mem_word_at _ m = _`
       (drule_then ACCEPT_TAC)) >>
  pop_assum mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
  qspecl_then [`p+32`,`0`,`4`,`32`,`mem`] mp_tac
    abiCanonicalHeadSizeTheory.mem_bytes_at_window >>
  simp[NoAsms] >>
  disch_then (SUBST1_TAC o SYM) >>
  rewrite_tac[abiEncoderMemoryTheory.abi_encoder_word_window,
              abiBuiltinEncodeMethodTheory.abi_builtin_encode_method_bytes_def] >>
  disch_then SUBST1_TAC >> REFL_TAC
QED

Resume abi_encode_staged_tuple_full_tail[protect_ready]:
  qpat_assum `abi_args_post _ _ _ _ _ es _ _ _ ee _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_args_post_def]) >>
  qpat_assum `wb_frame ce es ee origin s0 initial`
    (assume_tac o cj 2 o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (qpat_assum `wb_frame ce es ee origin s0 initial` mp_tac >>
     simp[NoAsms, loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def]) >>
  `ci_mono origin st` by
    (mp_tac (Q.SPECL [`args`,`ce`,`origin`] abi_args_compile_mono) >> simp[]) >>
  qpat_assum `ci_mono origin st` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  drule_all_then strip_assume_tac abiTupleEncodePrepareTheory.abi_tuple_encode_stage_shape >>
  drule_then strip_assume_tac abi_builtin_encode_setup_shape >>
  `staged.cs_next_id < ready.cs_next_id /\ staged.cs_next_var <= ready.cs_next_var` by
    (qpat_assum `ready.cs_next_id = _` SUBST1_TAC >>
     qpat_assum `ready.cs_next_var = _` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `OPTION_MAP bytes_method_id_word mid` >> simp[]) >>
  `staged.cs_next_var <= a.cs_next_var` by
    (qpat_assum `compile_alloc_buffer N staged = _` (fn th =>
       mp_tac (REWRITE_RULE [th,pairTheory.SND,ci_mono_def]
         (Q.SPECL [`N`,`staged`] ci_mono_compile_alloc_buffer))) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `st.cs_next_var <= staged.cs_next_var` by
    (qpat_assum `staged.cs_next_var = _` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `local_ptrs_reserved ce st` by
    (irule local_ptrs_reserved_next_var >> qexists `origin` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved ce staged` by
    (irule local_ptrs_reserved_next_var >> qexists `st` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved ce ready` by
    (irule local_ptrs_reserved_next_var >> qexists `staged` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at staged x ==> lookup_var x ready_run = lookup_var x prepared` by
    (rpt strip_tac >>
     `not_fresh_at a x` by
       (irule stmtFragPtrTheory.not_fresh_at_mono >> qexists `staged` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `typed_copy_state_frame a _ _ alloc_run ready_run`
       (drule_then SUBST1_TAC o cj 2 o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
     qpat_assum `!x. not_fresh_at staged x ==> lookup_var x alloc_run = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `!i row. FLOOKUP prepared.vs_allocas i = SOME row ==>
     FLOOKUP ready_run.vs_allocas i = SOME row` by
    (rpt strip_tac >>
     qpat_assum `ready_run.vs_allocas = _` SUBST1_TAC >>
     qpat_assum `alloc_run.vs_allocas = _` SUBST1_TAC >>
     qpat_assum `FLOOKUP prepared.vs_allocas i = SOME row` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abi_builtin_allocate_state_def,FLOOKUP_UPDATE] >>
     Cases_on `FLOOKUP prepared.vs_allocas staged.cs_next_id` >> simp[] >>
     Cases_on `staged.cs_next_id = i`
     >- (qpat_assum `staged.cs_next_id = i` (SUBST1_TAC o SYM) >> simp[]) >>
     simp[FLOOKUP_UPDATE]) >>
  suspend "setup_frames"
QED

Resume abi_encode_staged_tuple_full_tail[setup_frames]:
  `alloc_run with <|vs_vars := prepared.vs_vars; vs_allocas := prepared.vs_allocas;
     vs_alloca_next := prepared.vs_alloca_next; vs_inst_idx := prepared.vs_inst_idx|> = prepared` by
    (qpat_assum `alloc_run with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = prepared` mp_tac >>
     qpat_assum `prepared.vs_allocas = _` (pure_once_rewrite_tac o single o SYM) >>
     qpat_assum `prepared.vs_alloca_next = _` (pure_once_rewrite_tac o single o SYM) >>
     qpat_assum `prepared.vs_inst_idx = _` (pure_once_rewrite_tac o single o SYM) >>
     disch_then ACCEPT_TAC) >>
  `alloc_run.vs_memory = prepared.vs_memory` by
    (qpat_assum `alloc_run with <|vs_vars := _; vs_allocas := prepared.vs_allocas;
          vs_alloca_next := _; vs_inst_idx := _|> = prepared`
        (mp_tac o AP_TERM ``venom_state_vs_memory``) >>
     simp[NoAsms]) >>
  `cs_extends staged ready` by
    (irule cs_extends_trans >> qexists `a` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `cs_extends ready body_end` by
    (qpat_assum `compile_abi_encode_to_buf (Var dp) (Var src) ei ready = (len,body_end)`
       (ACCEPT_TAC o MATCH_MP compile_abi_encode_to_buf_extends)) >>
  `cs_extends body_end final_st` by
    (qpat_assum `abi_builtin_encode_finish _ _ _ body_end = ((),final_st)`
       (strip_assume_tac o MATCH_MP abi_builtin_encode_finish_shape) >>
     irule cs_extends_same_block >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `cs_extends ready final_st` by
    (irule cs_extends_trans >> qexists `body_end` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `fn_has_code staged ready func` by
    (mp_tac (Q.SPECL [`staged`,`ready`,`final_st`,`func`] fn_has_code_split) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  suspend "setup_locals"
QED

Resume abi_encode_staged_tuple_full_tail[setup_locals]:
  `prepared.vs_alloca_next <= alloc_run.vs_alloca_next` by
    (qpat_assum `prepared.vs_alloca_next = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `!i row. FLOOKUP prepared.vs_allocas i = SOME row ==>
     FLOOKUP alloc_run.vs_allocas i = SOME row` by
    (qpat_assum `!i row. FLOOKUP prepared.vs_allocas i = SOME row ==> FLOOKUP ready_run.vs_allocas i = SOME row`
       mp_tac >>
     qpat_assum `ready_run.vs_allocas = alloc_run.vs_allocas` (pure_rewrite_tac o single) >>
     disch_then ACCEPT_TAC) >>
  `!i b sz. FLOOKUP alloc_run.vs_allocas i = SOME (b,sz) /\
     FLOOKUP prepared.vs_allocas i = NONE ==> prepared.vs_alloca_next <= b` by
    (qpat_assum `alloc_run.vs_allocas = _` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_builtin_allocate_state_def] >>
     Cases_on `FLOOKUP prepared.vs_allocas staged.cs_next_id` >> simp[FLOOKUP_UPDATE] >>
     gen_tac >> Cases_on `staged.cs_next_id = i` >> simp[] >>
     rpt strip_tac >> fs[]) >>
  `!name entry x sz. lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
     lookup_var x alloc_run = lookup_var x prepared` by
    (rpt strip_tac >>
     `not_fresh_at staged x` by
       (qpat_assum `local_ptrs_reserved ce staged`
          (mp_tac o cj 2 o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
        qpat_assum `FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     qpat_assum `!x. not_fresh_at staged x ==> lookup_var x alloc_run = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `local_ptrs_rel func ce ee.scopes alloc_run` by
    (irule localPtrsPropsTheory.local_ptrs_rel_mem_agree >> qexists `prepared` >>
     conj_tac >- (qpat_assum `alloc_run.vs_memory = prepared.vs_memory` (rewrite_tac o single)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "setup_disjoint"
QED

Resume abi_encode_staged_tuple_full_tail[setup_disjoint]:
  `fn_has_code staged a func` by
    (mp_tac (Q.SPECL [`staged`,`a`,`ready`,`func`] fn_has_code_split) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `MEM (mk_inst staged.cs_next_id ALLOCA [Lit (n2w N)] [root]) (fn_insts func) /\
   ~not_fresh_at staged root` by
    (qpat_assum `compile_alloc_buffer N staged = (output_buf,a)` mp_tac >>
     qpat_assum `fn_has_code staged a func` mp_tac >>
     qpat_assum `output_buf.buf_operand = Var root` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule compile_alloc_buffer_emission >> strip_tac >>
     drule_all fn_has_code_split >> strip_tac >>
     drule_all emit_inst_fn_member >> gvs[]) >>
  `alloca_inv alloc_run` by
    (irule localPtrsPropsTheory.alloca_inv_fields >> qexists `ready_run` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >> sym_tac >> first_assum ACCEPT_TAC) >>
  `FLOOKUP alloc_run.vs_allocas staged.cs_next_id = SOME (p,N)` by
    (qpat_assum `ready_run.vs_allocas = alloc_run.vs_allocas`
       (pure_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  `not_local_ptr ce ee.scopes root` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >> qexists `staged` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!name b sz. local_region ce ee.scopes alloc_run name b sz ==>
     loweringStateRelDefs$regions_disjoint p N b sz` by
    (rpt strip_tac >>
     qabbrev_tac `inst = mk_inst staged.cs_next_id ALLOCA [Lit (n2w N)] [root]` >>
     `MEM inst (fn_insts func)` by
       (simp[NoAsms,Abbr `inst`] >> first_assum ACCEPT_TAC) >>
     `inst.inst_outputs = [root] /\ inst.inst_id = staged.cs_next_id` by
       simp[NoAsms,Abbr `inst`,mk_inst_def] >>
     `FLOOKUP alloc_run.vs_allocas inst.inst_id = SOME (p,N)` by
       (qpat_assum `inst.inst_id = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`ce`,`func`,`inst`,`name`,`root`,`ee.scopes`,`alloc_run`] >>
     asm_rewrite_tac[]) >>
  suspend "setup_selector_frame"
QED

Resume abi_encode_staged_tuple_full_tail[setup_selector_frame]:
  qabbrev_tac `wlen = case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME v => 32` >>
  `32 + wlen <= N` by
    (simp[NoAsms,Abbr `N`,Abbr `wlen`,Abbr `k`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `OPTION_MAP bytes_method_id_word mid` >>
     simp[] >> mp_tac (Q.SPEC `M + 4` abiBuiltinAllocationTheory.abi_builtin_word_size_capacity) >>
     Cases_on `word_size (M + 4)` >> simp[]) >>
  `!name b sz. local_region ce ee.scopes alloc_run name b sz ==>
     loweringStateRelDefs$regions_disjoint (p+32) wlen b sz` by
    (rpt strip_tac >>
     qpat_assum `!name b sz. local_region ce ee.scopes alloc_run name b sz ==>
           loweringStateRelDefs$regions_disjoint p N b sz` drule >>
     qpat_assum `32 + wlen <= N` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rw[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!z n. z+n <= p+32 \/ p+32+wlen <= z ==>
      mem_bytes_at z n ready_run.vs_memory = mem_bytes_at z n alloc_run.vs_memory` by
    (qpat_assum `typed_copy_state_frame a (p+32) wlen alloc_run ready_run` mp_tac >>
     rewrite_tac[typedMemoryCopyTheory.typed_copy_state_frame_def,
                 typedMemoryCopyTheory.typed_copy_frame_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!name entry x sz. lookup_scopes name ee.scopes = SOME entry /\
      FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
      lookup_var x ready_run = lookup_var x alloc_run` by
    (rpt strip_tac >>
     `not_fresh_at staged x` by
       (qpat_assum `local_ptrs_reserved ce staged`
          (mp_tac o cj 2 o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
        qpat_assum `FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     qpat_assum `!x. not_fresh_at staged x ==> lookup_var x ready_run = _` (drule_then SUBST1_TAC) >>
     qpat_assum `!name entry x sz. _ ==> lookup_var x alloc_run = lookup_var x prepared`
       (drule_all_then (ACCEPT_TAC o SYM))) >>
  `!name b sz. local_region ce ee.scopes alloc_run name b sz ==>
      mem_bytes_at b sz alloc_run.vs_memory = mem_bytes_at b sz ready_run.vs_memory` by
    (rpt strip_tac >> sym_tac >>
     qpat_assum `!z n. z+n <= p+32 \/ _ ==> _` irule >>
     qpat_assum `!name b sz. local_region ce ee.scopes alloc_run name b sz ==>
       loweringStateRelDefs$regions_disjoint (p+32) wlen b sz` drule >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `local_ptrs_rel func ce ee.scopes ready_run` by
    (irule localPtrsPropsTheory.local_ptrs_rel_mem_agree >> qexists `alloc_run` >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     pop_assum mp_tac >> pop_assum mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  suspend "setup_ghost"
QED

Resume abi_encode_staged_tuple_full_tail[setup_ghost]:
  `!x. not_fresh_at origin x ==> not_fresh_at staged x` by
    (gen_tac >> strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists `origin` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     irule arithmeticTheory.LESS_EQ_TRANS >> qexists `st.cs_next_var` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at staged x ==> not_fresh_at a x` by
    (gen_tac >> strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists `staged` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at staged x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at origin x ==> _` irule >>
     qpat_assum `!x sz. ce.ce_return_buf = _ ==> _` (drule_then ACCEPT_TAC)) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at staged x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at origin x ==> _` irule >>
     qpat_assum `!x sz. ce.ce_return_pc = _ ==> _` (drule_then ACCEPT_TAC)) >>
  `!i. i IN tna.t_mem <=> i IN tnp.t_mem \/ (prepared.vs_alloca_next <= i /\ i < p+N)` by
    (qpat_assum `prepared.vs_alloca_next = _` (pure_once_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  `allocas_from lo alloc_run` by
    (qpat_assum `allocas_from lo ready_run` mp_tac >>
     qpat_assum `ready_run.vs_allocas = alloc_run.vs_allocas` (fn th =>
       rewrite_tac [allocas_from_def,th])) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d ce cx ee Ga tna alloc_run` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> ghost_inv_at _ _ _ _ _ _ Gp tnp prepared /\ _`
       (drule_then strip_assume_tac) >>
     drule_at (Pat `ghost_inv_at _ _ _ _ _ _ Gp tnp prepared`)
       (Q.INST [`sa` |-> `staged`, `e` |-> `p+N`, `t` |-> `alloc_run`,
         `G'` |-> `Ga`, `tn'` |-> `tna`]
         (SPEC_ALL bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at_locals)) >>
     disch_then (drule_at (Pat `local_ptrs_rel func ce ee.scopes prepared`)) >>
     disch_then irule >> asm_rewrite_tac[] >>
     conj_tac >- (qexistsl_tac [`N`,`p`] >> REWRITE_TAC[]) >>
     qexists `staged` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "setup_ghost_ready"
QED

Resume abi_encode_staged_tuple_full_tail[setup_ghost_ready]:
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at staged x ==> not_fresh_at a x` irule >>
     qpat_assum `!x sz. ce.ce_return_buf = _ ==> not_fresh_at staged x` (drule_then ACCEPT_TAC)) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at staged x ==> not_fresh_at a x` irule >>
     qpat_assum `!x sz. ce.ce_return_pc = _ ==> not_fresh_at staged x` (drule_then ACCEPT_TAC)) >>
  `local_ptrs_reserved ce a` by
    (irule local_ptrs_reserved_next_var >> qexists `staged` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x` by
    (qpat_assum `local_ptrs_reserved ce a` (mp_tac o cj 2 o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at a x` by
    (rpt strip_tac >> irule local_ptrs_reserved_imm_base >> qexists `ce` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d ce cx ee Gr tnr ready_run` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> ghost_inv_at _ _ _ _ _ _ Ga tna alloc_run`
       (drule_then assume_tac) >>
     qpat_assum `!D d ce cx es. ghost_inv_at _ _ _ _ _ _ Ga tna alloc_run /\ _ ==> _` irule >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "setup_kept"
QED

Resume abi_encode_staged_tuple_full_tail[setup_kept]:
  qpat_assum `stmt_state_rel _ ctx func ce cx ee prepared`
    (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  `!i row. FLOOKUP s0.vs_allocas i = SOME row ==>
       FLOOKUP prepared.vs_allocas i = SOME row` by
    (rpt strip_tac >>
     qpat_assum `!i row. FLOOKUP initial.vs_allocas i = SOME row ==> _` irule >>
     qpat_assum `!i row. FLOOKUP s0.vs_allocas i = SOME row ==> _`
       (drule_then ACCEPT_TAC)) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= prepared.vs_alloca_next` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i row. FLOOKUP s0.vs_allocas i = SOME row ==> FLOOKUP prepared.vs_allocas i = SOME row`
       (drule_then (mp_then (Pat `FLOOKUP _ _ = _`) irule alloca_site_registered_below)) >>
     first_assum ACCEPT_TAC) >>
  `!name b sz. local_region ce es.scopes s0 name b sz ==>
      local_region ce ee.scopes initial name b sz` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `wb_frame ce es ee origin s0 initial`
       (assume_tac o cj 1 o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     qpat_assum `local_region ce es.scopes s0 name b sz` mp_tac >>
     qpat_assum `local_ptrs_reserved ce origin` mp_tac >>
     qpat_assum `MAP FDOM ee.scopes = MAP FDOM es.scopes` mp_tac >>
     qpat_assum `!x w. not_fresh_at origin x /\ lookup_var x s0 = SOME w ==> lookup_var x initial = SOME w` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[exprSimPropsTheory.local_region_frame_fwd]) >>
  `!name b sz. local_region ce es.scopes s0 name b sz ==>
       b+sz <= prepared.vs_alloca_next` by
    (rpt gen_tac >> strip_tac >>
     irule arithmeticTheory.LESS_EQ_TRANS >> qexists `initial.vs_alloca_next` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `stmt_state_rel _ ctx func ce cx ee initial`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule body_local_region_frontier) >>
     qpat_assum `!name b sz. local_region ce es.scopes s0 name b sz ==> local_region ce ee.scopes initial name b sz`
       (drule_then assume_tac) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`))) >>
  suspend "setup_kept_transport"
QED

Resume abi_encode_staged_tuple_full_tail[setup_kept_transport]:
  qpat_assum `!H. valid_horizon _ _ _ _ ==> ghost_inv_at _ _ _ _ _ _ Gp tnp prepared /\ _`
    (drule_then (assume_tac o CONJUNCT2)) >>
  `!x. not_fresh_at origin x ==>
     FLOOKUP Ga x = FLOOKUP Gp x /\ op_taint tna (Var x) = op_taint tnp (Var x)` by
    (qx_gen_tac `oldvar` >> disch_tac >>
     `not_fresh_at staged oldvar` by
       (qpat_assum `!x. not_fresh_at origin x ==> not_fresh_at staged x`
         (qspec_then `oldvar` irule) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at staged x ==> lookup_var x alloc_run = _ /\ _`
       (qspec_then `oldvar` (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
  `ghost_kept_at lo ce es origin G0 tn0 s0 Ga tna` by
    (qpat_assum `ghost_kept_at lo ce es origin G0 tn0 s0 Gp tnp`
       (mp_then (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`) irule
         (Q.INST [`s` |-> `prepared`, `e` |-> `p+N`]
           (SPEC_ALL bodyFullAllocaFreshTheory.alloc_buffer_ghost_kept_at))) >>
     asm_rewrite_tac[] >> qexistsl_tac [`N`,`p`,`prepared`] >> asm_rewrite_tac[]) >>
  `ghost_kept_at lo ce es origin G0 tn0 s0 Gr tnr` by
    (qpat_assum `!ce es origin G0 tn0 s0. ghost_kept_at _ _ _ _ _ _ _ Ga tna /\ _ ==> _` irule >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at staged x ==> not_fresh_at a x` irule >>
     qpat_assum `!x. not_fresh_at origin x ==> not_fresh_at staged x` (drule_then ACCEPT_TAC)) >>
  suspend "ready_protected"
QED

Resume abi_encode_staged_tuple_full_tail[ready_protected]:
  `!name entry x sz. lookup_scopes name ee.scopes = SOME entry /\
      FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
      lookup_var x prepared = lookup_var x initial` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x prepared = _` irule >>
     qpat_assum `local_ptrs_reserved ce st`
       (mp_tac o cj 2 o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
     qpat_assum `FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!name b sz. local_region ce ee.scopes ready_run name b sz <=>
       local_region ce ee.scopes alloc_run name b sz` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     first_assum ACCEPT_TAC) >>
  `!name b sz. local_region ce ee.scopes alloc_run name b sz <=>
       local_region ce ee.scopes prepared name b sz` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     first_assum ACCEPT_TAC) >>
  `!name b sz. local_region ce ee.scopes prepared name b sz <=>
       local_region ce ee.scopes initial name b sz` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     first_assum ACCEPT_TAC) >>
  `!name b sz. local_region ce es.scopes s0 name b sz ==>
       local_region ce ee.scopes ready_run name b sz` by
    (rpt gen_tac >>
     qpat_assum `!name b sz. local_region ce ee.scopes ready_run name b sz <=> _` (rewrite_tac o single) >>
     qpat_assum `!name b sz. local_region ce ee.scopes alloc_run name b sz <=> _` (rewrite_tac o single) >>
     qpat_assum `!name b sz. local_region ce ee.scopes prepared name b sz <=> _` (rewrite_tac o single) >>
     qpat_assum `!name b sz. local_region ce es.scopes s0 name b sz ==> local_region ce ee.scopes initial name b sz`
       MATCH_ACCEPT_TAC) >>
  `!name b sz. local_region ce ee.scopes ready_run name b sz ==>
       loweringStateRelDefs$regions_disjoint p N b sz` by
    (rpt gen_tac >>
     qpat_assum `!name b sz. local_region ce ee.scopes ready_run name b sz <=> _` (rewrite_tac o single) >>
     qpat_assum `!name b sz. local_region ce ee.scopes alloc_run name b sz ==> _`
       MATCH_ACCEPT_TAC) >>
  suspend "scratch_rows"
QED

Resume abi_encode_staged_tuple_full_tail[scratch_rows]:
  `!id. id IN window_alloca_sites func (frag_ids ready body_end) ==>
       ?inst q. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
         inst.inst_id = id /\ inst.inst_id IN frag_ids ready body_end /\
         inst.inst_outputs = [q] /\ not_local_ptr ce ee.scopes q` by
    (simp_tac (srw_ss()) [abiEncoderWindowContractTheory.window_alloca_sites_def] >>
     rpt strip_tac >>
     drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)
       (Q.INST [`func` |-> `func`, `obs` |-> `func`, `earlier` |-> `ready`,
                `scopes` |-> `ee.scopes`, `ce` |-> `ce`]
         (SPEC_ALL exprSimAbiEncodeSiteResourcesTheory.abi_encode_compiled_scratch_site)) >>
     disch_then (drule_at (Pat `MEM i (fn_insts func)`)) >>
     disch_then (qspecl_then [`ee`,`ce`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choose_then `q` strip_assume_tac o CONJUNCT2) >>
     qexistsl_tac [`inst`,`q`] >> asm_rewrite_tac[]) >>
  `!id b sz name z n. id IN window_alloca_sites func (frag_ids ready body_end) /\
       FLOOKUP ready_run.vs_allocas id = SOME (b,sz) /\
       local_region ce ee.scopes ready_run name z n ==>
       loweringStateRelDefs$regions_disjoint b sz z n` by
    (rpt strip_tac >>
     qpat_assum `!id. id IN window_alloca_sites _ _ ==> _`
       (drule_then (qx_choose_then `inst` (qx_choose_then `q` strip_assume_tac))) >>
     `FLOOKUP ready_run.vs_allocas inst.inst_id = SOME (b,sz)` by
       (qpat_assum `inst.inst_id = id` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`ce`,`func`,`inst`,`name`,`q`,`ee.scopes`,`ready_run`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "protected_bytes"
QED

Resume abi_encode_staged_tuple_full_tail[protected_bytes]:
  `origin.cs_next_id <= staged.cs_next_id` by
    (qpat_assum `origin.cs_next_id <= st.cs_next_id` mp_tac >>
     qpat_assum `st.cs_next_id < staged.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!id. id IN window_alloca_sites func (frag_ids ready body_end) ==> staged.cs_next_id < id` by
    (qpat_assum `staged.cs_next_id < ready.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiEncoderWindowContractTheory.window_alloca_sites_def,abiEncoderPropsTheory.frag_ids_def] >>
     rpt strip_tac >> decide_tac) >>
  `!id b sz id' b' sz'. id <> id' /\
      FLOOKUP ready_run.vs_allocas id = SOME (b,sz) /\
      FLOOKUP ready_run.vs_allocas id' = SOME (b',sz') ==>
      b + sz <= b' \/ b' + sz' <= b` by
    (qpat_assum `alloca_inv ready_run` (mp_tac o CONJUNCT1 o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[venomMemDefsTheory.allocas_non_overlapping_def] >> metis_tac[]) >>
  `!id row. FLOOKUP s0.vs_allocas id = SOME row ==> FLOOKUP ready_run.vs_allocas id = SOME row` by
    (rpt strip_tac >>
     qpat_assum `!i row. FLOOKUP prepared.vs_allocas i = SOME row ==> FLOOKUP ready_run.vs_allocas i = SOME row` irule >>
     qpat_assum `!i row. FLOOKUP s0.vs_allocas i = SOME row ==> FLOOKUP prepared.vs_allocas i = SOME row`
       (drule_then ACCEPT_TAC)) >>
  `!name b sz. local_region ce ee.scopes ready_run name b sz ==> b+sz <= ready_run.vs_alloca_next` by
    (rpt gen_tac >>
     qpat_assum `!name b sz. local_region ce ee.scopes ready_run name b sz <=> _` (pure_rewrite_tac o single) >>
     qpat_assum `!name b sz. local_region ce ee.scopes alloc_run name b sz <=> _` (pure_rewrite_tac o single) >>
     strip_tac >>
     `b+sz <= prepared.vs_alloca_next` by
       (qpat_assum `stmt_state_rel _ ctx func ce cx ee prepared`
         (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule body_local_region_frontier) >>
        goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`))) >>
     qpat_assum `ready_run.vs_alloca_next = alloc_run.vs_alloca_next` SUBST1_TAC >>
     irule arithmeticTheory.LESS_EQ_TRANS >> qexists `prepared.vs_alloca_next` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!id b sz. id IN window_alloca_sites func (frag_ids ready body_end) /\
      FLOOKUP ready_run.vs_allocas id = SOME (b,sz) ==>
      venomMemDefs$regions_disjoint (p+32,k) (b,sz)` by
    (rpt strip_tac >>
     qpat_assum `!id. id IN window_alloca_sites _ _ ==> _`
       (drule_then (qx_choose_then `inst` (qx_choose_then `q` strip_assume_tac))) >>
     `FLOOKUP ready_run.vs_allocas inst.inst_id = SOME (b,sz)` by
       (qpat_assum `inst.inst_id = id` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> sz = 32 /\ _`
       (qspecl_then [`inst`,`b`,`sz`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  suspend "protected_set"
QED

Resume abi_encode_staged_tuple_full_tail[protected_set]:
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < origin.cs_next_id ==>
      off+sz <= ready_run.vs_alloca_next /\ (off+sz <= p \/ p+N <= off) /\
      !id b n. id IN window_alloca_sites func (frag_ids ready body_end) /\
        FLOOKUP ready_run.vs_allocas id = SOME (b,n) ==> off+sz <= b \/ b+n <= off` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!id row. FLOOKUP s0.vs_allocas id = SOME row ==> FLOOKUP ready_run.vs_allocas id = SOME row`
       (drule_then assume_tac) >>
     conj_tac >-
       (irule alloca_site_registered_below >> (metis_tac[])) >>
     conj_tac >-
       (`aid <> staged.cs_next_id` by
          (qpat_assum `aid < origin.cs_next_id` mp_tac >>
           qpat_assum `origin.cs_next_id <= staged.cs_next_id` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
        qpat_assum `!id b sz id' b' sz'. _ ==> _`
          (qspecl_then [`aid`,`off`,`sz`,`staged.cs_next_id`,`p`,`N`] mp_tac) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     `aid <> id` by
       (qpat_assum `!id. id IN window_alloca_sites _ _ ==> staged.cs_next_id < id`
          (drule_then mp_tac) >> qpat_assum `aid < origin.cs_next_id` mp_tac >>
        qpat_assum `origin.cs_next_id <= staged.cs_next_id` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     qpat_assum `!id b sz id' b' sz'. _ ==> _`
       (qspecl_then [`aid`,`off`,`sz`,`id`,`b`,`n`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  qabbrev_tac `P = {i | i < lo \/
      (?name b sz. local_region ce ee.scopes ready_run name b sz /\ b <= i /\ i < b+sz) \/
      (?aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < origin.cs_next_id /\ off <= i /\ i < off+sz) \/
      (p+32 <= i /\ i < p+32+k)}` >>
  `!i. i IN P <=> i < lo \/
      (?name b sz. local_region ce ee.scopes ready_run name b sz /\ b <= i /\ i < b+sz) \/
      (?aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < origin.cs_next_id /\ off <= i /\ i < off+sz) \/
      (p+32 <= i /\ i < p+32+k)` by simp[NoAsms, Abbr `P`] >>
  pop_assum (mk_asm "protected_membership") >>
  suspend "protected_bounds"
QED

Resume abi_encode_staged_tuple_full_tail[protected_bounds]:
  `!i. i IN P ==> i < ready_run.vs_alloca_next /\
      (i < p+32+k \/ p+32+k+LENGTH (enc ct rv) <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids ready body_end) /\
        FLOOKUP ready_run.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i)` by
    (asm "protected_membership" (pure_rewrite_tac o single) >>
     qx_gen_tac `j` >> disch_tac >>
     pop_assum (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) >-
     (conj_tac >-
       (qpat_assum `j < lo` mp_tac >> qpat_assum `lo <= ready_run.vs_alloca_next` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
      conj_tac >-
       (qpat_assum `j < lo` mp_tac >> qpat_assum `lo <= p` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `allocas_from lo ready_run` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
      disch_then (drule_then mp_tac) >> qpat_assum `j < lo` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)
     >- suspend "protected_local"
     >- suspend "protected_old"
     >- suspend "protected_selector") >>
  suspend "ready_finish"
QED

Resume abi_encode_staged_tuple_full_tail[protected_local]:
  rename1 `local_region ce ee.scopes ready_run name b sz` >>
  qpat_assum `!name b sz. local_region ce ee.scopes ready_run name b sz ==> b+sz <= _`
    (drule_then assume_tac) >>
  conj_tac >-
    (qpat_assum `j < b+sz` mp_tac >> qpat_assum `b+sz <= ready_run.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  conj_tac >-
    (qpat_assum `!name b sz. local_region ce ee.scopes ready_run name b sz ==> loweringStateRelDefs$regions_disjoint p N b sz`
       (drule_then (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
     qpat_assum `32+k+LENGTH (enc ct rv) <= N` mp_tac >>
     qpat_assum `j < b+sz` mp_tac >> qpat_assum `b <= j` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!id b sz name z n. _ ==> loweringStateRelDefs$regions_disjoint b sz z n`
    (drule_all_then (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
  qpat_assum `j < b+sz` mp_tac >> qpat_assum `b <= j` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac
QED

Resume abi_encode_staged_tuple_full_tail[protected_old]:
  rename1 `FLOOKUP s0.vs_allocas aid = SOME (off,sz)` >>
  qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
    (drule_all_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 (mk_asm "old_out") (mk_asm "old_scratch")))) >>
  conj_tac >-
    (qpat_assum `j < off+sz` mp_tac >> qpat_assum `off+sz <= ready_run.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  conj_tac >-
    (asm "old_out" mp_tac >> qpat_assum `32+k+LENGTH (enc ct rv) <= N` mp_tac >>
     qpat_assum `j < off+sz` mp_tac >> qpat_assum `off <= j` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  asm "old_scratch" (drule_all_then mp_tac) >>
  qpat_assum `j < off+sz` mp_tac >> qpat_assum `off <= j` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac
QED

Resume abi_encode_staged_tuple_full_tail[protected_selector]:
  conj_tac >-
    (qpat_assum `j < p+32+k` mp_tac >> qpat_assum `32+k+LENGTH (enc ct rv) <= N` mp_tac >>
     qpat_assum `p+N <= ready_run.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!id b sz. _ ==> venomMemDefs$regions_disjoint (p+32,k) (b,sz)`
    (drule_all_then (mp_tac o REWRITE_RULE [venomMemDefsTheory.regions_disjoint_def])) >>
  qpat_assum `!id. id IN window_alloca_sites _ _ ==> ?inst q. _`
    (drule_then (qx_choose_then `ins` (qx_choose_then `q` strip_assume_tac))) >>
  rename1 `FLOOKUP ready_run.vs_allocas id = SOME (b,n)` >>
  `FLOOKUP ready_run.vs_allocas ins.inst_id = SOME (b,n)` by
    (qpat_assum `ins.inst_id = id` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> sz = 32 /\ _`
    (qspecl_then [`ins`,`b`,`n`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `j < p+32+k` mp_tac >> qpat_assum `p+32 <= j` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac
QED

Resume abi_encode_staged_tuple_full_tail[ready_finish]:
  qabbrev_tac `cap = val_footprint (TupleTV ts) (ArrayV (TupleV vs))` >>
  `32 <= N /\ p < dimword(:256) /\
   LENGTH (enc ct rv) + k < dimword(:256) /\
   p+32+k+LENGTH (enc ct rv) <= ready_run.vs_alloca_next` by
    (qpat_assum `32+k+LENGTH (enc ct rv) <= N` mp_tac >>
     qpat_assum `p+N < dimword(:256)` mp_tac >>
     qpat_assum `p+N <= ready_run.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `ptr_covers Gr tnr dp ready_run (LENGTH (enc ct rv))` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `M` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `venomMemDefs$regions_disjoint (w2n bw,cap) (p+32+k,LENGTH (enc ct rv))` by
    (qpat_assum `venomMemDefs$regions_disjoint (w2n bw,cap) (p,N)` mp_tac >>
     qpat_assum `32+k+LENGTH (enc ct rv) <= N` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!name b sz. local_region ce ee.scopes ready_run name b sz ==>
     loweringStateRelDefs$regions_disjoint p 32 b sz` by
    (rpt strip_tac >>
     qpat_assum `!name b sz. local_region ce ee.scopes ready_run name b sz ==> loweringStateRelDefs$regions_disjoint p N b sz`
       (drule_then mp_tac) >>
     qpat_assum `32 <= N` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!x. not_fresh_at origin x ==> not_fresh_at ready x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >> qexists `staged` >>
     qpat_assum `!x. not_fresh_at origin x ==> not_fresh_at staged x` (drule_then assume_tac) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ready x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at origin x ==> not_fresh_at ready x` irule >>
     qpat_assum `!x sz. ce.ce_return_buf = _ ==> not_fresh_at origin x` (drule_then ACCEPT_TAC)) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ready x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at origin x ==> not_fresh_at ready x` irule >>
     qpat_assum `!x sz. ce.ce_return_pc = _ ==> not_fresh_at origin x` (drule_then ACCEPT_TAC)) >>
  `abi_encoder_admissible ei` by
    simp[NoAsms, Abbr `ei`, abiEncoderAdmissibleTheory.abi_encoder_translation_admissible] >>
  suspend "finish_apply"
QED

Resume abi_encode_staged_tuple_full_tail[finish_apply]:
  `N < dimword(:256)` by
    (qpat_assum `p+N < dimword(:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!x. not_fresh_at staged x ==> lookup_var x alloc_run = lookup_var x prepared` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at staged x ==> lookup_var x alloc_run = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  drule_all_then (MAP_EVERY assume_tac o CONJUNCTS)
    bodyFullAbiEncodePureFrameTheory.abi_encode_tuple_setup_frames >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp ready_run /\
    ready_run.vs_alloca_next + pending_alloca_size func ready_run <= w2n ready_run.vs_initial_fmp` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx ee prepared`
       (mp_tac o MATCH_MP stmt_state_rel_fmp_room) >>
     qpat_assum `abi_encode_exec_frame func prepared ready_run` mp_tac >>
     qpat_assum `alloca_inv ready_run` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_def,
          exprSimAbiEncodeSemanticTheory.abi_encode_semantic_obs_fields,
          exprLoweringPropsTheory.fmp_room_def, ptrDisciplineTheory.allocas_below_fmp_def,
          venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  qpat_assum `compile_abi_encode_to_buf (Var dp) (Var src) ei ready = (len,body_end)`
    (mp_tac o Q.INST [`fin` |-> `final_st`,
      `site` |-> `staged.cs_next_id`, `sa` |-> `origin`,
      `s` |-> `ready_run`, `G` |-> `Gr`, `tn` |-> `tnr`, `ret` |-> `d`,
      `at` |-> `ct`, `av` |-> `rv`, `sb` |-> `w2n (bw:256 word)`, `dstcap` |-> `M`]
      o PART_MATCH (boolSyntax.lhand o boolSyntax.lhand)
          bodyFullAbiEncodeReadyFinishTheory.abi_encode_ready_finish_origin_split
      o concl) >>
  qpat_assum `LENGTH selector = k` (pure_rewrite_tac o single) >>
  (impl_tac >- suspend "finish_premises") >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu` strip_assume_tac)))))) >>
  suspend "pure_frame_join"
QED

Resume abi_encode_staged_tuple_full_tail[finish_premises]:
  `0 < cap ==> w2n bw + cap <= ready_run.vs_alloca_next /\
      venomMemDefs$regions_disjoint (w2n bw,cap) (p+32+k,LENGTH (enc ct rv)) /\
      ?x. Var src = Var x /\ ptr_covers Gr tnr x ready_run cap` by
    (disch_tac >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists `src` >> REWRITE_TAC[] >> first_assum ACCEPT_TAC) >>
  `0 < LENGTH (enc ct rv) ==> ptr_covers Gr tnr dp ready_run (LENGTH (enc ct rv))` by
    (disch_tac >> first_assum ACCEPT_TAC) >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids ready body_end /\
      FLOOKUP ready_run.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (w2n bw,cap) (b,sz)) /\
      venomMemDefs$regions_disjoint (p+32+k,LENGTH (enc ct rv)) (b,sz)` by
    (rpt strip_tac >>
     qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> sz = 32 /\ _`
       (drule_all_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
     first_assum ACCEPT_TAC) >>
  `!name b sz i. local_region ce ee.scopes ready_run name b sz /\ b <= i /\ i < b+sz ==> i IN P` by
    (rpt strip_tac >> asm "protected_membership" (pure_once_rewrite_tac o single) >>
     disj2_tac >> disj1_tac >> qexistsl_tac [`name`,`b`,`sz`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!name b sz i. local_region ce es.scopes s0 name b sz /\ b <= i /\ i < b+sz ==> i IN P` by
    (rpt strip_tac >>
     qpat_assum `!name b sz i. local_region ce ee.scopes ready_run name b sz /\ _ ==> i IN P`
       (qspecl_then [`name`,`b`,`sz`,`i`] mp_tac) >>
     (impl_tac >-
       (reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
        qpat_assum `!name b sz. local_region ce es.scopes s0 name b sz ==> local_region ce ee.scopes ready_run name b sz`
          (drule_then ACCEPT_TAC))) >>
     disch_then ACCEPT_TAC) >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < origin.cs_next_id /\
      (!n b sz'. local_region ce es.scopes s0 n b sz' ==> off+sz <= b \/ b+sz' <= off) /\
      off <= i /\ i < off+sz ==> i IN P` by
    (rpt gen_tac >> strip_tac >> asm "protected_membership" (pure_once_rewrite_tac o single) >>
     disj2_tac >> disj2_tac >> disj1_tac >> qexistsl_tac [`aid`,`off`,`sz`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!i. i < lo ==> i IN P` by
    (rpt strip_tac >> asm "protected_membership" (pure_once_rewrite_tac o single) >>
     disj1_tac >> first_assum ACCEPT_TAC) >>
  `!i. p+32 <= i /\ i < p+32+k ==> i IN P` by
    (rpt strip_tac >> asm "protected_membership" (pure_once_rewrite_tac o single) >>
     ntac 3 disj2_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `LENGTH selector = k` (fn th =>
    qpat_assum `!mem. _ ==> mem_bytes_at (p+32) (LENGTH selector) mem = selector`
      (assume_tac o PURE_REWRITE_RULE [th])) >>
  `!x. Var src = Var x ==> not_fresh_at ready x` by
    (simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_encode_staged_tuple_full_tail[pure_frame_join]:
  `~expr_has_effect (TypeBuiltin ann (AbiEncode ensure mid) ty args) ==>
   pure_frame ce func es origin s0 t` by suspend "pure_frame_premises" >>
  suspend "result_source"
QED

Resume abi_encode_staged_tuple_full_tail[pure_frame_premises]:
  qpat_assum `LENGTH selector = k` (fn th =>
    qpat_assum `window_strong_result _ _ _ _ _ _ _ _ ready_run u`
      (assume_tac o PURE_REWRITE_RULE [th])) >>
  disch_tac >>
  irule (INST_TYPE [Type.alpha |-> ``:256``]
    bodyFullAbiEncodePureFrameTheory.abi_encode_tuple_pure_frame_join) >>
  qpat_assum `window_strong_result ctx func ready body_end len ct rv
      (p+32+k) ready_run u` (irule_at Any) >>
  qpat_assum `abi_builtin_encode_setup _ M staged = ((Var root,Var dp),ready)` (irule_at Any) >>
  qpat_assum `typed_copy_state_frame a (p+32) wlen alloc_run ready_run` (irule_at Any) >>
  qpat_assum `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee prepared`
    (irule_at Any) >>
  qpat_assum `compile_alloc_buffer _ st = (buf,allocated)` (irule_at Any) >>
  qpat_assum `wb_frame ce es ee origin s0 initial` (irule_at Any) >>
  qpat_assum `~expr_has_effect (TypeBuiltin ann (AbiEncode ensure mid) ty args)` (irule_at Any) >>
  qpat_assum `FLOOKUP prepared.vs_allocas st.cs_next_id = SOME (_,_)` (irule_at Any) >>
  qpat_assum `FLOOKUP ready_run.vs_allocas staged.cs_next_id = SOME (p,N)` (irule_at Any) >>
  qpat_assum `buf.buf_operand = Var src` (pure_rewrite_tac o single) >>
  qpat_assum `compile_abi_encode_to_buf (Var dp) (Var src) ei ready = (len,body_end)`
    (irule_at Any) >>
  `st.cs_next_id <= staged.cs_next_id` by
    (qpat_assum `st.cs_next_id < staged.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!x. not_fresh_at staged x ==> lookup_var x alloc_run = lookup_var x prepared` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at staged x ==> lookup_var x alloc_run = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  asm_rewrite_tac[] >>
  simp[NoAsms, Abbr `N`, Abbr `k`, Abbr `wlen`]
QED

Resume abi_encode_staged_tuple_full_tail[result_source]:
  `well_typed_type_builtin_args (AbiEncode ensure mid) ty (MAP expr_type args)` by
    (qpat_assum `expr_body_pre ce cx env (TypeBuiltin ann _ _ _) es` mp_tac >>
     simp[NoAsms, exprSimHypsDefsTheory.expr_body_pre_def,
       Once vyperTypeSystemTheory.well_typed_expr_def]) >>
  qabbrev_tac `payload = abi_encode_method_id_bytes mid ++ enc ct rv` >>
  `evaluate_type_builtin cx (AbiEncode ensure mid) ty (MAP expr_type args) vs =
    INL (BytesV payload)` by
    (qpat_assum `well_typed_type_builtin_args _ _ _`
       (strip_assume_tac o SRULE [vyperTypeSystemTheory.well_typed_type_builtin_args_def]) >>
     qpat_assum `ty = TupleT _` SUBST1_TAC >>
     qpat_assum `Abbrev (payload = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `enc ct rv = _` SUBST1_TAC >>
     match_mp_tac (PURE_REWRITE_RULE [vyperABITheory.vyper_to_abi_type_def]
       abiBuiltinEncodeSourceTheory.abi_builtin_encode_source_tuple) >>
     reverse conj_tac >- (qpat_assum `vyper_to_abi_list _ _ _ = SOME avs`
       (fn th => simp[NoAsms, vyperABITheory.vyper_to_abi_def, th])) >>
     qpat_assum `args <> []` mp_tac >>
     qpat_assum `LENGTH args = 1 ==> ensure` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `args` >> simp[] >>
     rename1 `1 <= LENGTH rest` >> Cases_on `rest` >> simp[]) >>
  suspend "result_bound"
QED

Resume abi_encode_staged_tuple_full_tail[result_bound]:
  `?limit. expr_type (TypeBuiltin ann (AbiEncode ensure mid) ty args) = BaseT (BytesT (Dynamic limit)) /\
    vyper_abi_size_bound (get_tenv cx) (TupleT (MAP expr_type args)) + abi_encode_method_id_size mid <= limit` by
    (qpat_assum `expr_body_pre ce cx env (TypeBuiltin ann _ _ _) es` mp_tac >>
     qpat_assum `~(LENGTH args = 1 /\ ~ensure)` mp_tac >>
     qpat_assum `env.type_defs = get_tenv cx` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def, Once vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeSystemTheory.type_builtin_result_ok_def, vyperTypeSystemTheory.abi_encode_size_ok_def] >>
     rpt strip_tac >> Cases_on `args` >> gvs[vyperASTTheory.expr_type_def] >>
     rename1 `rest = [] ==> ensure` >> Cases_on `rest` >> gvs[]) >>
  `LENGTH (enc ct rv) <= vyper_abi_size_bound (get_tenv cx) (TupleT (MAP expr_type args))` by
    (qpat_assum `enc ct rv = _` SUBST1_TAC >>
     irule (cj 2 vyperABIValidTheory.vyper_to_abi_enc_le_size_bound) >>
     qpat_assum `vyper_to_abi_list _ _ _ = SOME avs` (irule_at Any) >>
     qexists `tvs'` >>
     qpat_assum `LIST_REL (\e tv. evaluate_type _ (expr_type e) = _) _ _` mp_tac >>
     qpat_assum `LIST_REL value_has_type tvs' vs` mp_tac >>
     qpat_assum `env.type_defs = get_tenv cx` SUBST1_TAC >>
     simp[NoAsms, listTheory.LIST_REL_MAP1, combinTheory.o_DEF,
       vyperTypeDefaultsTheory.values_have_types_LIST_REL]) >>
  `LENGTH payload <= limit` by
    (qpat_assum `LENGTH (enc ct rv) <= vyper_abi_size_bound _ _` mp_tac >>
     qpat_assum `vyper_abi_size_bound _ _ + _ <= limit` mp_tac >>
     simp[NoAsms, Abbr `payload`, vyperTypeSystemTheory.abi_encode_method_id_size_def] >>
     decide_tac) >>
  suspend "byte_resources"
QED

Resume abi_encode_staged_tuple_full_tail[byte_resources]:
  `selector = abi_encode_method_id_bytes mid` by
    (qpat_assum `well_typed_type_builtin_args _ _ _`
       (assume_tac o MATCH_MP abiBuiltinEncodeSourceTheory.abi_builtin_encode_checked_prefix) >>
     qpat_assum `abi_builtin_encode_prefix _ = _` (pure_once_rewrite_tac o single o GSYM) >>
     Cases_on `mid` >> simp[NoAsms, Abbr `selector`, abiBuiltinEncodeRunTheory.abi_builtin_encode_prefix_def]) >>
  `payload = selector ++ enc ct rv` by
    (qpat_assum `selector = _` SUBST1_TAC >> simp[NoAsms, Abbr `payload`]) >>
  `LENGTH payload <= M+k /\ 32+LENGTH payload <= N` by
    (qpat_assum `payload = selector ++ _` (pure_once_rewrite_tac o single) >>
     qpat_assum `LENGTH selector = k` (fn th => rewrite_tac[listTheory.LENGTH_APPEND,th]) >>
     qpat_assum `32+k+LENGTH (enc ct rv) <= N` mp_tac >>
     qpat_assum `LENGTH (enc ct rv) <= M` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic limit))) (BytesV payload) p mem` by
    (qx_gen_tac `mem` >> strip_tac >>
     qpat_assum `!mem. _ ==> mem_word_at p mem = _ /\ _`
       (qspec_then `mem` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `payload = selector ++ _` (fn th =>
       simp_tac (srw_ss()) [th, valueEncodingDefsTheory.val_in_memory_def,listTheory.LENGTH_APPEND]) >>
     conj_tac >-
       (qpat_assum `LENGTH selector = k` (pure_once_rewrite_tac o single) >>
        once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
     once_rewrite_tac[valueEncodingProofsTheory.mem_bytes_at_split_padded] >>
     qpat_assum `LENGTH selector = k` (pure_rewrite_tac o single) >>
     qpat_assum `mem_bytes_at (p+32) k mem = _` (pure_rewrite_tac o single) >>
     qpat_assum `mem_bytes_at (p+32+k) _ mem = _` (pure_rewrite_tac o single) >>
     REFL_TAC) >>
  `p+N <= t.vs_alloca_next` by
    (irule abiEncoderWindowContractTheory.window_alloca_growth_frontier >>
     qexists `ready_run` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `type_memory_bytes ce (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) ty args)) = N` by
    (qpat_assum `~(LENGTH args = 1 /\ ~ensure)` (fn th =>
       simp_tac (srw_ss()) [Once exprLoweringTheory.lowered_value_type_def,LET_THM,EQF_INTRO th]) >>
     Cases_on `mid` >>
     simp[NoAsms, Abbr `N`, Abbr `M`, Abbr `k`, compileEnvTheory.type_memory_bytes_def,
       vfmConstantsTheory.word_size_def, arithmeticTheory.MULT_COMM]) >>
  `val_store_size (BaseTV (BytesT (Dynamic limit))) (BytesV payload) <= N` by
    (`word_size (LENGTH payload) <= word_size (M+k)` by simp[exprSimPropsTheory.word_size_monotone] >>
     qpat_assum `word_size (LENGTH payload) <= word_size (M+k)` mp_tac >>
     simp[NoAsms, exprSimPropsTheory.val_store_size_def, Abbr `N`]) >>
  `eval_operand (Var root) t = SOME (n2w p)` by
    (rewrite_tac[venomStateTheory.eval_operand_def] >> first_assum ACCEPT_TAC) >>
  `w2n (n2w p : 256 word) = p` by simp[wordsTheory.w2n_n2w] >>
  mp_tac (Q.INST [`s` |-> `t`, `q` |-> `root`, `capacity` |-> `N`,
    `w` |-> `(n2w p : 256 word)`, `G` |-> `Gf`, `tn` |-> `tnf`,
    `N` |-> `limit`, `ann` |-> `ann`, `ensure` |-> `ensure`, `target` |-> `ty`,
    `args` |-> `args`, `mid` |-> `mid`, `ce` |-> `ce`, `cx` |-> `cx`,
    `ee` |-> `ee with gas_obs := []`, `payload` |-> `payload`]
      bodyFullAbiEncodeResultResourcesTheory.abi_encode_bytes_full_resources) >>
  (impl_tac >-
    (qpat_assum `w2n (n2w p : 256 word) = p` (pure_rewrite_tac o single) >>
     qpat_assum `type_memory_bytes ce (lowered_value_type ce (TypeBuiltin ann _ _ _)) = N`
       (fn th => rewrite_tac[th, arithmeticTheory.LESS_EQ_REFL]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> suspend "result_outcome"
QED

Resume abi_encode_staged_tuple_full_tail[result_outcome]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (initial,G,tn) [] (OK t,Gf,tnf)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`Gr`,`ready_run`,`tnr`] >> reverse conj_tac
     >- (qpat_assum `!D. gas_origin_ptr_path _ (ready_run,Gr,tnr) [] (OK t,Gf,tnf)`
          (qspec_then `D` ACCEPT_TAC)) >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`Gp`,`prepared`,`tnp`] >> conj_tac
     >- (qpat_assum `!D. gas_origin_ptr_path _ (initial,G,tn) [] (OK prepared,Gp,tnp)`
          (qspec_then `D` ACCEPT_TAC)) >>
     qpat_assum `!D. gas_origin_ptr_path _ (prepared,Gp,tnp) [] (OK ready_run,Gr,tnr)`
       (qspec_then `D` ACCEPT_TAC)) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gf`,`ee`,`INL (Value (BytesV payload))`,`t`,`tnf`] >>
  conj_tac >- (qpat_assum `evaluate_type_builtin _ _ _ _ _ = INL (BytesV payload)`
    (fn th => simp_tac (srw_ss()) [th])) >>
  qx_gen_tac `H` >> strip_tac >>
  conj_tac >- (qpat_assum `!D. gas_origin_ptr_path _ (initial,G,tn) [] (OK t,Gf,tnf)`
    (qspec_then `DF H` ACCEPT_TAC)) >>
  `ghost_inv_at (DF H) lo d ce cx (ee with gas_obs := []) Gf tnf t` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> ghost_inv_at _ _ _ _ _ _ Gr tnr ready_run`
       (drule_then assume_tac) >>
     qpat_assum `!D. ghost_inv_at D _ _ _ _ ee Gr tnr ready_run ==> _`
       (qspec_then `DF H` (drule_then mp_tac)) >>
     simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  BETA_TAC >> qexists `Value (BytesV payload)` >>
  qpat_assum `out = Var root` SUBST1_TAC >>
  conj_tac >- REFL_TAC >>
  suspend "result_post"
QED

Resume abi_encode_staged_tuple_full_tail[result_post]:
  reverse conj_tac >-
    (`alloca_history func t` by
       (qpat_assum `alloca_history func ready_run ==> alloca_history func t`
          (drule_then ACCEPT_TAC)) >>
     `s0.vs_alloca_next <= t.vs_alloca_next` by
       (qpat_assum `window_alloca_growth ready_run t`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [abiEncoderWindowContractTheory.window_alloca_growth_def]) >>
        qpat_assum `ready_run.vs_alloca_next = alloc_run.vs_alloca_next` (rewrite_tac o single) >>
        qpat_assum `prepared.vs_alloca_next <= alloc_run.vs_alloca_next` mp_tac >>
        qpat_assum `initial.vs_alloca_next <= prepared.vs_alloca_next` mp_tac >>
        qpat_assum `s0.vs_alloca_next <= initial.vs_alloca_next` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     qpat_assum `~ctx_has_dalloca ctx` (fn th =>
        simp[NoAsms, th, contextTheory.mk_ptr_def, contextTheory.vv_location_def]) >>
     qpat_assum `vv_store_bound _ _ _ _ _ _ t`
        (assume_tac o SRULE [loweringPostsTheory.post_value_type_def, contextTheory.mk_ptr_def]) >>
     qpat_assum `ptr_vv_ok _ _ _ _ _ Gf tnf t`
        (assume_tac o SRULE [loweringPostsTheory.post_value_type_def, contextTheory.mk_ptr_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "result_vv"
QED

Resume abi_encode_staged_tuple_full_tail[result_vv]:
  `stmt_state_rel H ctx func ce cx (ee with gas_obs := []) t` by
    suspend "result_state" >>
  `wb_frame ce es (ee with gas_obs := []) origin s0 t` by
    suspend "result_writeback" >>
  `!name b sz. local_region ce ee.scopes t name b sz ==> p+N <= b \/ b+sz <= p` by
    suspend "result_disjoint" >>
  `storage_well_formed_on cx (ee with gas_obs := []) (FST H)` by
    suspend "result_storage" >>
  `val_in_memory (BaseTV (BytesT (Dynamic limit))) (BytesV payload) p t.vs_memory` by
    (qpat_assum `!mem. _ ==> val_in_memory _ _ p mem` irule >> simp[NoAsms, mem_agree_outside_def]) >>
  irule (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [vyperASTTheory.expr_type_def,
      Once exprSimUint2StrTheory.vv_post_located_mk_ptr]))
    (Q.INST [`e` |-> `TypeBuiltin ann (AbiEncode ensure mid) ty args`,
             `result` |-> `Value (BytesV payload)`]
       exprSimAbiEncodeNonwordResultTheory.abi_encode_bytes_vv_post)) >>
  qpat_assum `FLOOKUP t.vs_allocas staged.cs_next_id = SOME (p,N)` (irule_at Any) >>
  qpat_assum `val_in_memory _ _ p t.vs_memory` (irule_at Any) >>
  simp_tac (srw_ss()) [vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  qpat_assum `~expr_has_effect (TypeBuiltin ann (AbiEncode ensure mid) ty args) ==> pure_frame ce func es origin s0 t`
    (rewrite_tac o single o SRULE []) >>
  qpat_assum `stmt_state_rel H ctx func ce cx (ee with gas_obs := []) t`
    (rewrite_tac o single o REWRITE_RULE [exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  suspend "result_vv_premises"
QED

Resume abi_encode_staged_tuple_full_tail[result_vv_premises]:
  `p < dimword (:256)` by
    (qpat_assum `p+N < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `staged.cs_next_id < final_st.cs_next_id` by
    (drule_then ACCEPT_TAC exprSimAbiEncodeBytesOwnershipTheory.abi_encode_strict_id_growth) >>
  conj_tac >- qpat_assum `storage_well_formed_on cx _ (FST H)` ACCEPT_TAC >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_encode_staged_tuple_full_tail[result_storage]:
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> (?ts. _) /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!b. get_storage cx (ee with gas_obs := []) b = get_storage cx ee b` by
    (Cases >> simp[NoAsms, vyperStorageBackendTheory.get_storage_def]) >>
  qpat_assum `abi_args_post H _ _ _ _ es _ _ _ ee _ _ _ _`
    (mp_tac o cj 2 o REWRITE_RULE [abi_args_post_def]) >>
  qpat_assum `!b. get_storage cx (_ with gas_obs := _) b = _`
    (fn th => rewrite_tac[vyperStorageFootprintTheory.storage_well_formed_on_def,th])
QED

Resume abi_encode_staged_tuple_full_tail[result_disjoint]:
  rpt gen_tac >> strip_tac >>
  irule (INST_TYPE [Type.alpha |-> ``:256``]
    exprSimAbiEncodeBytesOwnershipTheory.abi_encode_setup_row_local_exclusion) >>
  qpat_assum `stmt_state_rel H ctx func ce cx (ee with gas_obs := []) t` (irule_at Any) >>
  qpat_assum `FLOOKUP t.vs_allocas staged.cs_next_id = SOME (p,N)` (irule_at Any) >>
  qpat_assum `abi_builtin_encode_setup _ M staged = ((Var root,Var dp),ready)` (irule_at Any) >>
  rename1 `local_region ce ee.scopes t nm b sz` >> qexists `nm` >>
  simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_encode_staged_tuple_full_tail[result_writeback]:
  rewrite_tac[exprSimWordArgsTheory.wb_frame_gas_obs] >>
  `!b n. loweringStateRelDefs$regions_disjoint (w2n bw)
          (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) b n /\
        (b+n <= p \/ p+N <= b) /\ (!i. b <= i /\ i < b+n ==> i IN P) ==>
        mem_bytes_at b n t.vs_memory = mem_bytes_at b n initial.vs_memory` by
    suspend "writeback_interval" >>
  qpat_assum `wb_frame ce es ee origin s0 initial`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  rewrite_tac[loweringPostsTheory.wb_frame_def] >>
  conj_tac >- suspend "writeback_vars" >>
  conj_tac >- (rpt strip_tac >>
    irule abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated >>
    qpat_assum `abi_encoder_registered_effect _ _ ready_run t` (irule_at Any) >>
    qpat_assum `!id row. FLOOKUP s0.vs_allocas id = SOME row ==> FLOOKUP ready_run.vs_allocas id = SOME row`
      (drule_then ACCEPT_TAC)) >>
  conj_tac >- suspend "writeback_rows" >>
  irule exprSimPropsTheory.locals_kept_regions_tail >> qexists `initial` >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  suspend "writeback_locals"
QED

Resume abi_encode_staged_tuple_full_tail[writeback_interval]:
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `!z k. loweringStateRelDefs$regions_disjoint (w2n bw) _ z k ==> mem_bytes_at z k prepared.vs_memory = _`
    (drule_then (fn th => rewrite_tac[GSYM th])) >>
  qpat_assum `alloc_run.vs_memory = prepared.vs_memory` (fn th => rewrite_tac[GSYM th]) >>
  `mem_bytes_at b n ready_run.vs_memory = mem_bytes_at b n alloc_run.vs_memory` by
    (qpat_assum `!z n. _ ==> mem_bytes_at z n ready_run.vs_memory = mem_bytes_at z n alloc_run.vs_memory` irule >>
     qpat_assum `b+n <= p \/ p+N <= b` mp_tac >>
     qpat_assum `32+wlen <= N` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >> qx_gen_tac `i` >> strip_tac >>
  `i IN P` by (first_assum irule >> conj_tac >> first_assum ACCEPT_TAC) >>
  `(i:num) < p \/ p+32 <= i` by
    (qpat_assum `b+n <= p \/ p+N <= b` mp_tac >> qpat_assum `32 <= N` mp_tac >>
     qpat_assum `b <= i` mp_tac >> qpat_assum `i < b+n` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qpat_assum `!i. i IN P /\ _ ==> mem_bytes_at i 1 t.vs_memory = _ /\ _`
    (qspec_then `i` mp_tac) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Resume abi_encode_staged_tuple_full_tail[writeback_vars]:
  rpt strip_tac >>
  `not_fresh_at ready x /\ not_fresh_at staged x` by
    (conj_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  `not_fresh_at st x` by
    (qpat_assum `not_fresh_at origin x` mp_tac >>
     qpat_assum `origin.cs_next_var <= st.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  `lookup_var x initial = SOME w` by
    ((qpat_assum `!x w. not_fresh_at origin x /\ lookup_var x s0 = SOME w ==> _`
       (qspecl_then [`x`,`w`] mp_tac) >> asm_rewrite_tac[] >> (simp[]))) >>
  `lookup_var x ready_run = SOME w` by
    (qpat_assum `!x. not_fresh_at staged x ==> lookup_var x ready_run = lookup_var x prepared`
       (drule_then SUBST1_TAC) >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x prepared = lookup_var x initial`
       (drule_then SUBST1_TAC) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!x w. not_fresh_at ready x /\ lookup_var x ready_run = SOME w ==> _`
    irule >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_encode_staged_tuple_full_tail[writeback_rows]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < origin.cs_next_id /\ _ ==> mem_bytes_at off sz initial.vs_memory = _`
    (drule_all_then (fn th => rewrite_tac[GSYM th])) >>
  qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> off+sz <= ready_run.vs_alloca_next /\ _`
    (drule_all_then (assume_tac o cj 2)) >>
  `loweringStateRelDefs$regions_disjoint (w2n bw)
     (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) off sz` by
    (`aid <> st.cs_next_id` by
       (qpat_assum `aid < origin.cs_next_id` mp_tac >> qpat_assum `origin.cs_next_id <= st.cs_next_id` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     qpat_assum `!id b sz id' b' sz'. _ ==> b+sz <= b' \/ b'+sz' <= b`
       (qspecl_then [`aid`,`off`,`sz`,`st.cs_next_id`,`w2n bw`,
          `abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))`] mp_tac) >>
     (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum (drule_then ACCEPT_TAC) >>
       first_assum ACCEPT_TAC)) >>
     rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
     disch_then (DISJ_CASES_THEN assume_tac) >> simp[NoAsms, Once DISJ_COMM] >>
     asm_rewrite_tac[]) >>
  `!i. off <= i /\ i < off+sz ==> i IN P` by
    (rpt strip_tac >> asm "protected_membership" (pure_once_rewrite_tac o single) >>
     disj2_tac >> disj2_tac >> disj1_tac >> qexistsl [`aid`,`off`,`sz`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_encode_staged_tuple_full_tail[writeback_locals]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!name b sz. local_region ce es.scopes s0 name b sz ==> local_region ce ee.scopes initial name b sz`
    (drule_then assume_tac) >>
  qpat_assum `!name b sz. local_region ce es.scopes s0 name b sz ==> local_region ce ee.scopes ready_run name b sz`
    (drule_then assume_tac) >>
  qpat_assum `!name b sz. local_region ce ee.scopes ready_run name b sz ==> loweringStateRelDefs$regions_disjoint p N b sz`
    (drule_then (assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def, Once DISJ_COMM])) >>
  qpat_assum `!name b sz. local_region ce ee.scopes initial name b sz ==> loweringStateRelDefs$regions_disjoint (w2n bw) _ b sz`
    (drule_then assume_tac) >>
  `!i. b <= i /\ i < b+sz ==> i IN P` by
    (rpt strip_tac >> asm "protected_membership" (pure_once_rewrite_tac o single) >>
     disj2_tac >> disj1_tac >> qexistsl [`n`,`b`,`sz`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_encode_staged_tuple_full_tail[result_state]:
  `abi_encode_exec_frame func prepared t` by
    (irule exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_trans >>
     qexists `ready_run` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `t.vs_labels = prepared.vs_labels` by
    (qpat_assum `t.vs_labels = ready_run.vs_labels` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee t` by
    suspend "canonical_state" >>
  suspend "state_horizon"
QED

Resume abi_encode_staged_tuple_full_tail[canonical_state]:
  `staged.cs_next_var <= body_end.cs_next_var` by
    (qpat_assum `compile_abi_encode_to_buf _ _ _ ready = (_,body_end)`
       (mp_tac o MATCH_MP abiEncodeVarFlowTheory.compile_abi_encode_next_var) >>
     qpat_assum `staged.cs_next_var <= ready.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!op v. abi_decoder_operand_live body_end.cs_next_var op /\
      eval_operand op u = SOME v ==> eval_operand op t = SOME v` by
    (gen_tac >> gen_tac >> disch_tac >>
     qpat_assum `!op. (!x. op = Var x ==> _) ==> eval_operand op t = _`
       (qspec_then `op` mp_tac) >>
     pop_assum mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `op` >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
          abiDecoderReentryTheory.abi_decoder_older_vars_def,
          loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[]) >>
  `p <= p+32+k /\ p+32+k+LENGTH (enc ct rv) <= p+N` by
    (qpat_assum `32+k+LENGTH (enc ct rv) <= N` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  irule (cj 1 exprSimAbiEncodeStateTransportTheory.abi_encode_phases_caller_state) >>
  qpat_assum `window_strong_result ctx func ready body_end len ct rv
      (p+32+k) ready_run u` (irule_at Any) >>
  qpat_assum `abi_builtin_encode_setup _ M staged = ((Var root,Var dp),ready)`
    (irule_at Any) >>
  qpat_assum `abi_builtin_encode_setup_frame _ _ N p wlen prepared ready_run`
    (irule_at Any) >>
  simp_tac bool_ss [pairTheory.SND] >>
  qpat_assum `compile_abi_encode_to_buf (Var dp) (Var src) ei ready = (len,body_end)`
    (irule_at Any) >>
  asm_rewrite_tac[] >>
  simp[NoAsms,Abbr `N`,Abbr `k`]
QED

Resume abi_encode_staged_tuple_full_tail[state_horizon]:
  `stmt_state_rel H ctx func ce cx ee initial` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
         (?ts. _ /\ abi_args_post H ctx func ce cx es origin st s0 ee args ops vs initial /\ _) /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     qpat_assum `abi_args_post H ctx func ce cx es origin st s0 ee args ops vs initial`
       (ACCEPT_TAC o cj 1 o REWRITE_RULE [abi_args_post_def])) >>
  `prepared.vs_accounts = initial.vs_accounts /\
   prepared.vs_transient = initial.vs_transient /\
   prepared.vs_requests = initial.vs_requests /\
   prepared.vs_call_ctx = initial.vs_call_ctx` by
    (qpat_assum `copy_static prepared = copy_static _`
       (fn th =>
         mp_tac (MATCH_MP exprSimStorageCopyTheory.copy_static_fields th) >>
         mp_tac (AP_TERM ``venom_state_vs_requests`` th)) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[exprSimStorageCopyTheory.copy_static_def,
          abiBuiltinAllocationTheory.abi_builtin_allocate_state_def] >>
     IF_CASES_TAC >> simp[]) >>
  drule_all_then (MAP_EVERY assume_tac o CONJUNCTS)
    exprSimAbiEncodeStateTransportTheory.abi_encode_caller_world_fields >>
  qpat_assum `abi_encode_exec_frame func prepared t`
    (assume_tac o cj 3 o REWRITE_RULE [exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_def]) >>
  rewrite_tac[exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
  irule (INST_TYPE [Type.alpha |-> ``:256``]
    exprLoweringPropsTheory.stmt_state_rel_fields_transport) >>
  qpat_assum `stmt_state_rel H ctx func ce cx ee initial` (irule_at Any) >>
  qexists `storage_trace_horizon ee.storage_trace` >>
  map_every (fn q => qpat_assum q (pure_once_rewrite_tac o single))
    [`t.vs_call_ctx = prepared.vs_call_ctx`,
     `t.vs_accounts = prepared.vs_accounts`,
     `t.vs_transient = prepared.vs_transient`,
     `t.vs_requests = prepared.vs_requests`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise abi_encode_staged_tuple_full_tail
