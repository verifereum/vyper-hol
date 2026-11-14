(* Allocation-only resource boundary for exact registration. *)
Theory defaultBytesAllocationBoundary
Ancestors moduleLowering compileEnv emitHelper
  finite_map words arithmetic ctorDeployMemoryRunPtrPrefixRegisterAlloc
  ctorDeployMemoryRunPtrPrefixRegisterAddress dispatchedDecoderTrace
  ctorDeployLoweringEntryRegisterRun ctorDeployMemoryRunMemEntryRegistration
  abiEncoderProps loweringHalt fragExec context abiDecoderReentry
  loweringStateRelDefs bodyPtrDefs venomState ptrDiscipline localPtrsProps
  ctorDeployLoweringEntryAllocation emitHelperProps venomInst venomExecSemantics
  slotCopyExecution exprLoweringProps rich_list

Theorem default_bytes_allocation_boundary:
  compile_alloc_buffer cap st = (buf,allocated) /\
  0 < cap /\ cap < dimword (:256) /\ fn_has_code st allocated fn /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  fn_inst_ids_distinct fn /\ k + unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  alloca_history fn s /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?a H u p.
    buf.buf_operand = Var p /\
    eval_operand (Var p) a = SOME (n2w s.vs_alloca_next) /\
    abi_decoder_operand_live allocated.cs_next_var (Var p) /\
    not_fresh_at allocated p /\ ptr_covers H u p a cap /\
    FLOOKUP a.vs_allocas st.cs_next_id = SOME (s.vs_alloca_next,cap) /\
    a.vs_alloca_next = s.vs_alloca_next + cap /\
    s.vs_alloca_next + cap < dimword (:256) /\
    alloca_inv a /\ alloca_frontier_inv_from k ctx fn site a /\
    allocas_from lo a /\ lo <= a.vs_alloca_next /\ alloca_history fn a /\
    ~a.vs_halted /\ a.vs_current_bb = allocated.cs_current_bb /\
    a.vs_inst_idx = LENGTH allocated.cs_current_insts /\
    a = (s with <|vs_vars := a.vs_vars; vs_allocas := a.vs_allocas;
      vs_alloca_next := a.vs_alloca_next;
      vs_inst_idx := LENGTH allocated.cs_current_insts|>) /\
    st.cs_next_id < allocated.cs_next_id /\ st.cs_next_var <= allocated.cs_next_var /\
    (!id. id <> st.cs_next_id ==> FLOOKUP a.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op a = eval_operand op s) /\
    (!v. not_fresh_at st v ==> FLOOKUP H v = FLOOKUP G v /\
      op_taint u (Var v) = op_taint tn (Var v)) /\
    u.t_mem = tn.t_mem UNION
      {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+cap} /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    gas_path_mem ctx fn s 0 (OK a) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK a,H,u)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u a) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule_all deploy_ctor_register_alloc_run >> strip_tac >>
  `emit_op ALLOCA [Lit (n2w cap)] st = (buf.buf_operand,allocated)` by
    (gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[]) >>
  drule prefix_register_address_emit_shape >> strip_tac >>
  qabbrev_tac `p = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `H = G |+ (p,(s.vs_alloca_next,cap))` >>
  qabbrev_tac `u = tn with <|t_var := tn.t_var |+ (p,{});
    t_mem := tn.t_mem UNION
      {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+cap}|>` >>
  qmatch_asmsub_abbrev_tac `a = raw with vs_inst_idx := _` >>
  `raw = update_var (STRING #"%" (toString st.cs_next_var))
    (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+
      (st.cs_next_id,(s.vs_alloca_next,cap));
      vs_alloca_next := s.vs_alloca_next+cap|>)` by simp[Abbr `raw`] >>
  drule_all ctor_checked_alloc_buffer_edge >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl [`a`,`H`,`u`,`p`] >>
  pure_rewrite_tac[CONJ_ASSOC] >>
  reverse conj_tac >- suspend "pullback" >>
  reverse conj_tac >- suspend "origin" >>
  reverse conj_tac >- suspend "memory" >>
  suspend "fields"
QED

Resume default_bytes_allocation_boundary[fields]:
  pure_rewrite_tac[GSYM CONJ_ASSOC] >>
  simp[] >>
  conj_tac >- simp[Abbr `raw`, update_var_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    Abbr `p`, ASCIInumbersTheory.toString_11] >>
  conj_tac >- simp[not_fresh_at_def, Abbr `p`, ASCIInumbersTheory.toString_11] >>
  conj_tac >-
    (simp[ptr_covers_def, op_taint_def, Abbr `u`, Abbr `H`, Abbr `raw`,
      update_var_def, lookup_var_def, FLOOKUP_UPDATE, w2n_n2w] >>
     `s.vs_alloca_next < dimword (:256)` by decide_tac >> simp[]) >>
  simp[Abbr `raw`, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >-
    (simp[allocas_from_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     Cases_on `aid = st.cs_next_id` >> gvs[allocas_from_def] >> metis_tac[]) >>
  conj_tac >- gvs[update_var_def] >>
  conj_tac >-
    (Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >>
     `s' <> p` by (simp[Abbr `p`] >> metis_tac[]) >> simp[]) >>
  conj_tac >-
    (rpt strip_tac >>
     `v <> p` by (gvs[not_fresh_at_def, Abbr `p`] >> metis_tac[]) >>
     simp[Abbr `H`, Abbr `u`, FLOOKUP_UPDATE, op_taint_def]) >>
  simp[Abbr `u`]
QED
Resume default_bytes_allocation_boundary[memory]:
  gvs[Abbr `raw`]
QED
Resume default_bytes_allocation_boundary[origin]:
  rpt gen_tac >>
  simp_tac bool_ss [Abbr `H`, Abbr `u`] >>
  qpat_x_assum `a = _` SUBST1_TAC >>
  simp_tac bool_ss [Abbr `raw`, Abbr `p`] >>
  irule prefix_register_address_emit_origin >> simp[] >>
  qexistsl [`ALLOCA`,`[Lit (n2w cap)]`,`buf.buf_operand`,`st`] >>
  qpat_x_assum `s.vs_alloca_next + cap < dimword (:256)` kall_tac >>
  qpat_x_assum `k + unit_alloca_budget ctx < dimword (:256)` kall_tac >>
  drule_all prefix_register_alloc_pair >>
  disch_then (qspecl_then [`STRING #"%" (toString st.cs_next_var)`,
    `tn`,`0`,`fn`,`PG`,`G`,`D`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  simp[run_inst_seq_def, mk_inst_def, is_terminator_def,
    unitTransformDefsTheory.inst_mem_below_frontier_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def]
QED
Resume default_bytes_allocation_boundary[pullback]:
  gen_tac >>
  drule_all prefix_register_alloc_run_continuation >>
  simp[NoAsms, LET_THM] >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] mp_tac) >>
  simp[Abbr `H`, Abbr `u`, Abbr `p`, Abbr `raw`]
QED
Finalise default_bytes_allocation_boundary
