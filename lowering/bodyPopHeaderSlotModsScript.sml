(* The counted storage/transient header load of a linked Pop. *)
Theory bodyPopHeaderSlotMods
Ancestors
  exprSimPopNestedBase stmtAppendStorageRunPtr payloadLoadStorePtr
  fragGasSeqPtr fragExecMem instMemFrontier ptrSafetyTransport
  ghostPcTransportPtr instIdxIndep unitTransformDefs fragExec
  exprLoweringProps memSafeRun
  ptrDiscipline venomExecSemantics venomState venomInst finite_map list

Theorem pop_header_slot_load_mods:
  eval_operand hdr s = SOME slot /\ op_taint tn hdr = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0]]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?q u G' tn'.
    q = update_var x0 (if tr then tload slot s else sload slot s) s /\
    run_inst_seq [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0]] s = OK q /\
    u = (q with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn
      [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0]]
      (s with vs_inst_idx := k) G' tn') /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,G',tn')) /\
    lookup_var x0 u = SOME (if tr then tload slot s else sload slot s) /\
    op_prov G' (Var x0) = NONE /\ op_taint tn' (Var x0) = {} /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
    u.vs_inst_idx = SUC s.vs_inst_idx /\ allocas_from lo u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> x0 ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0]` >>
  qabbrev_tac `q = update_var x0 (if tr then tload slot s else sload slot s) s` >>
  qabbrev_tac `u = q with vs_inst_idx := SUC s.vs_inst_idx` >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   i.inst_opcode <> GAS /\ i.inst_opcode <> DALLOCA` by
    (Cases_on `tr` >> simp[Abbr `i`,mk_inst_def,is_terminator_def]) >>
  `step_inst_base i s = OK q` by simp[Abbr `i`, Abbr `q`, nested_pop_step_load] >>
  `run_inst_seq [i] s = OK q` by simp[run_inst_seq_def] >>
  qabbrev_tac `G' = step_prov PG G i q` >>
  qabbrev_tac `tn' = tn with t_var := tn.t_var |+ (x0,{})` >>
  `step_taint i s q tn = tn'` by
    (simp[Abbr `i`, Abbr `tn'`] >> irule scalar_storage_load_taint >>
     simp[Abbr `q`,update_var_def]) >>
  `!D k. inst_seq_ptr D lo ctx func PG G tn [i] (s with vs_inst_idx := k) G' tn'` by
    (rpt gen_tac >>
     `step_inst_base i (s with vs_inst_idx := k) = OK (q with vs_inst_idx := k)` by
       simp[step_inst_inst_idx_indep, exec_result_map_def] >>
     `allocas_from lo (s with vs_inst_idx := k) /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp (s with vs_inst_idx := k))` by
       (fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
     simp[inst_seq_ptr_def, Abbr `G'`] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists_tac `0` >>
     simp[Abbr `i`] >> irule ptr_inst_ok_storage_load_payload >>
     simp[Abbr `q`, update_var_def]) >>
  `run_inst_seq_mem_ok [i] s` by
    (simp[run_inst_seq_mem_ok_def] >> conj_tac
     >- (irule below_frontier_no_ranges >> Cases_on `tr` >> simp[Abbr `i`,mk_inst_def]) >>
     Cases_on `tr` >> simp[Abbr `i`,inst_dload_in_section_def,mk_inst_def]) >>
  qexistsl_tac [`q`, `u`, `G'`, `tn'`] >> simp[] >>
  conj_tac
  >- (gen_tac >>
      `inst_seq_ptr D lo ctx func PG G tn [i] s G' tn'` by
        (first_x_assum (qspecl_then [`D`, `s.vs_inst_idx`] mp_tac) >> simp[]) >>
      qspecl_then [`[i]`,`s`,`q`] mp_tac run_inst_seq_gas_origin_ptr_path >>
      simp[Abbr `u`, dalloca_no_wrap_def, Once EQ_SYM_EQ, APPEND_EQ_SING, GSYM arithmeticTheory.ADD1] >>
      disch_then irule >> simp[] >> fs[]) >>
  conj_tac >- simp[Abbr `u`, Abbr `q`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (simp[Abbr `G'`, Abbr `i`] >> irule payload_load_provenance >> Cases_on `tr` >> simp[]) >>
  simp[Abbr `u`, Abbr `q`, Abbr `tn'`, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, op_taint_def, allocas_from_def, allocas_below_fmp_def] >>
  rpt strip_tac >> simp[Abbr `G'`, Abbr `i`, scalar_step_old_prov]
QED
