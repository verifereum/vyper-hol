(* Output allocation and encoding after native tuple staging. *)
Theory bodyFullAbiEncodeTupleTail
Ancestors
  bodyFullAbiEncodeSetupTail bodyFullAbiEncodeFinish bodyFullAbiEncodeSuffix
  bodyFullAbiEncodeUniformTranslation bodyFullAbiEncodeNonwordWindow
  exprSimAbiEncodeTupleResources abiBuiltinAllocation allocationPtr
  bodyFullUnwrapRun ptrSafetyTransport fragGasSeqPtr fragExecPtr
  instMemFrontier memSafeRun literalAllocPathPtr exprLoweringProps
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
