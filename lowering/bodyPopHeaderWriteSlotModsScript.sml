(* The permitted storage/transient header write at the reached Pop cursor. *)
Theory bodyPopHeaderWriteSlotMods
Ancestors
  exprSimPopNestedBase stmtAppendStorageRunPtr ptrSafetyTransport
  fragGasSeqPtr fragExecMem bodyBinopFragMemory instIdxIndep unitTransformDefs
  fragExec memSafeRun instMemFrontier exprLoweringProps contextCodegenRel codegenRel
  allocasBelowFmpUpdatesProps
  ptrDiscipline venomExecSemantics venomState venomInst rich_list list arithmetic

Theorem pop_header_slot_store_mods:
  ~s5.vs_call_ctx.cc_static /\ ~s5.vs_halted /\
  lookup_block s5.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s5.vs_inst_idx =
    SOME (mk_inst id (if tr then TSTORE else SSTORE) [hdr;Var x3] []) /\
  eval_operand hdr s5 = SOME slot /\ lookup_var x3 s5 = SOME w /\
  op_taint tn hdr = {} /\ op_taint tn (Var x3) = {} /\
  allocas_from lo s5 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s5) ==>
  ?q s6 tn6.
    q = (if tr then tstore slot w s5 else sstore slot w s5) /\
    run_inst_seq [mk_inst id (if tr then TSTORE else SSTORE) [hdr;Var x3] []]
      s5 = OK q /\
    s6 = (q with vs_inst_idx := s5.vs_inst_idx + 1) /\
    tn6 = (if tr then tn with t_trans := key_update tn.t_trans slot {}
           else tn with t_stor := key_update tn.t_stor slot {}) /\
    (!D j. inst_seq_ptr D lo ctx func PG G tn
      [mk_inst id (if tr then TSTORE else SSTORE) [hdr;Var x3] []]
      (s5 with vs_inst_idx := j) G tn6) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s5,G,tn) [] (OK s6,G,tn6)) /\
    (if tr then (s6 with <|vs_transient := s5.vs_transient;
                            vs_inst_idx := s5.vs_inst_idx|>) = s5
     else (s6 with <|vs_accounts := s5.vs_accounts;
                      vs_inst_idx := s5.vs_inst_idx|>) = s5) /\
    (!op. eval_operand op s6 = eval_operand op s5 /\ op_taint tn6 op = op_taint tn op) /\
    ~s6.vs_halted /\ s6.vs_current_bb = s5.vs_current_bb /\
    s6.vs_inst_idx = s5.vs_inst_idx + 1 /\ s6.vs_memory = s5.vs_memory /\
    s6.vs_immutables = s5.vs_immutables /\ s6.vs_allocas = s5.vs_allocas /\
    s6.vs_alloca_next = s5.vs_alloca_next /\ s6.vs_fmp = s5.vs_fmp /\
    allocas_from lo s6 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s6) /\
    (alloca_history func s5 ==> alloca_history func s6) /\
    tn6.t_mem = tn.t_mem /\ tn6.t_imm = tn.t_imm /\
    (if tr then s6.vs_accounts = s5.vs_accounts /\ tn6.t_stor = tn.t_stor
     else s6.vs_transient = s5.vs_transient /\ tn6.t_trans = tn.t_trans)
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst id (if tr then TSTORE else SSTORE) [hdr;Var x3] []` >>
  qabbrev_tac `q = if tr then tstore slot w s5 else sstore slot w s5` >>
  qabbrev_tac `s6 = q with vs_inst_idx := s5.vs_inst_idx + 1` >>
  qabbrev_tac `tn6 = if tr then tn with t_trans := key_update tn.t_trans slot {}
                    else tn with t_stor := key_update tn.t_stor slot {}` >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   i.inst_opcode <> GAS /\ i.inst_opcode <> DALLOCA /\ i.inst_opcode <> ALLOCA` by
    (Cases_on `tr` >> simp[Abbr `i`,mk_inst_def,is_terminator_def]) >>
  `step_inst_base i s5 = OK q` by simp[Abbr `i`,Abbr `q`,nested_pop_step_store] >>
  `run_inst_seq [i] s5 = OK q` by simp[run_inst_seq_def] >>
  `step_taint i s5 q tn = tn6` by
    (simp[Abbr `i`,Abbr `tn6`] >> irule scalar_storage_store_taint >>
     Cases_on `tr` >> simp[Abbr `q`,sstore_def,tstore_def]) >>
  `!D j. inst_seq_ptr D lo ctx func PG G tn [i] (s5 with vs_inst_idx := j) G tn6` by
    (rpt gen_tac >>
     `step_inst_base i (s5 with vs_inst_idx := j) = OK (q with vs_inst_idx := j)` by
       simp[step_inst_inst_idx_indep,exec_result_map_def] >>
     `allocas_from lo (s5 with vs_inst_idx := j) /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp (s5 with vs_inst_idx := j))` by
       (conj_tac
        >- (qpat_assum `allocas_from lo s5` mp_tac >> simp[NoAsms,allocas_from_def]) >>
        simp[allocas_below_fmp_updates]) >>
     simp[inst_seq_ptr_def] >>
     simp[Abbr `i`,scalar_void_prov] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists `0` >> simp[] >>
     irule append_scalar_inst_check >>
     `q.vs_requests = s5.vs_requests` by (Cases_on `tr` >> simp[Abbr `q`,sstore_def,tstore_def]) >>
     Cases_on `tr` >> simp[] >> metis_tac[]) >>
  `isPREFIX [i] (DROP s5.vs_inst_idx bb.bb_instructions)` by
    (Cases_on `s5.vs_inst_idx < LENGTH bb.bb_instructions` >>
     fs[get_instruction_def,DROP_CONS_EL]) >>
  `run_inst_seq_mem_ok [i] s5` by
    (Cases_on `tr` >> simp[run_inst_seq_mem_ok_last,Abbr `i`,mk_inst_def,
       inst_mem_below_frontier_def,inst_dload_in_section_def,
       source_memory_read_ranges_def,source_memory_write_ranges_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s5,G,tn) [] (OK s6,G,tn6)` by
    (gen_tac >>
     `inst_seq_ptr D lo ctx func PG G tn [i] s5 G tn6` by
       (qpat_assum `!D j. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
         (qspecl_then [`D`,`s5.vs_inst_idx`] mp_tac) >>
        simp_tac bool_ss [venom_state_fupdselfid]) >>
     qspecl_then [`[i]`,`s5`,`q`] mp_tac run_inst_seq_gas_origin_ptr_path >>
     simp[Abbr `s6`,dalloca_no_wrap_def,Once EQ_SYM_EQ,APPEND_EQ_SING] >>
     disch_then irule >> simp[] >> fs[]) >>
  `(alloca_history func s5 ==> alloca_history func s6)` by
    (strip_tac >> simp_tac bool_ss [Abbr `s6`] >>
     `LENGTH [i] = 1` by simp[] >>
     qpat_assum `LENGTH [i] = 1` (once_rewrite_tac o single o GSYM) >>
     irule alloca_history_no_alloca_slice >>
     `q.vs_allocas = s5.vs_allocas /\ q.vs_current_bb = s5.vs_current_bb` by
       (Cases_on `tr` >> simp[Abbr `q`,sstore_def,tstore_def]) >>
     simp[] >>
     qpat_assum `isPREFIX [i] _` mp_tac >>
     simp_tac bool_ss [IS_PREFIX_APPEND,APPEND]) >>
  qexistsl_tac [`q`,`s6`,`tn6`] >> simp[] >>
  Cases_on `tr` >>
  (simp[Abbr `q`,Abbr `s6`,Abbr `tn6`,sstore_def,tstore_def,
        allocas_from_def,allocas_below_fmp_def] >>
   reverse conj_tac
   >- (conj_tac
       >- (qpat_assum `allocas_from lo s5` mp_tac >> simp[NoAsms,allocas_from_def]) >>
       qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s5` mp_tac >>
       simp[NoAsms,allocas_below_fmp_def] >> metis_tac[]) >>
   Cases >> simp[eval_operand_def,lookup_var_def,op_taint_def])
QED
