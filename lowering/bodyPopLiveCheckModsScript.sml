(* The reached, non-empty Pop check: ASSERT and the scalar decrement. *)
Theory bodyPopLiveCheckMods
Ancestors
  bodyPtrBopAssert bodyPtrPopScalarTransfer ptrSafetyTransport
  exprSimPop exprLoweringProps fragGasSeqPtr fragExecMem bodyBinopFragMemory
  allocasBelowFmpUpdatesProps unitTransformDefs venomState venomInst
  venomExecSemantics codegenRel contextCodegenRel ptrDiscipline
  ptrSafeRun memSafeRun blockPrefixEquiv finite_map list rich_list words arithmetic

Theorem pop_check_sequence[local]:
  lookup_var x2 s = SOME (bool_to_word T) /\
  lookup_var x0 s = SOME n /\
  op_taint tn (Var x2) = {} /\ op_taint tn (Var x0) = {} /\
  op_prov G (Var x0) = NONE /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  let a = mk_inst (id+3) ASSERT [Var x2] [];
      b = mk_inst (id+4) SUB [Var x0; Lit 1w] [x3];
      u = update_var x3 (n-1w) s;
      G5 = DRESTRICT G (COMPL {x3});
      tn5 = tn with t_var := tn.t_var |+ (x3,{})
  in
    run_inst_seq [a;b] s = OK u /\
    (!D j. inst_seq_ptr D lo ctx func PG G tn [a;b]
      (s with vs_inst_idx := j) G5 tn5)
Proof
  strip_tac >> simp[LET_THM] >>
  qabbrev_tac `a = mk_inst (id+3) ASSERT [Var x2] []` >>
  qabbrev_tac `b = mk_inst (id+4) SUB [Var x0; Lit 1w] [x3]` >>
  `!j. step_inst_base a (s with vs_inst_idx := j) = OK (s with vs_inst_idx := j)` by
    simp[Abbr `a`, pop_step_ASSERT, lookup_var_set_inst_idx, bool_to_word_def] >>
  `!j. step_inst_base b (s with vs_inst_idx := j) =
       OK (update_var x3 (n-1w) (s with vs_inst_idx := j))` by
    simp[Abbr `b`, pop_step_SUB_lit, lookup_var_set_inst_idx] >>
  `step_inst_base a s = OK s /\ step_inst_base b s = OK (update_var x3 (n-1w) s)` by
    simp[Abbr `a`, Abbr `b`, pop_step_ASSERT, pop_step_SUB_lit, bool_to_word_def] >>
  conj_tac >- simp[run_inst_seq_def] >>
  gen_tac >>
  `!j. allocas_from lo (s with vs_inst_idx := j) /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp (s with vs_inst_idx := j))` by
    (gen_tac >> conj_tac
     >- (qpat_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
     simp[allocas_below_fmp_updates]) >>
  `!j. ptr_inst_ok D lo 0 ctx func G tn a (s with vs_inst_idx := j)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists `0` >>
     simp[Abbr `a`, bop_assert_ptr_inst_ok]) >>
  `!j. ptr_inst_ok D lo 0 ctx func G tn b (s with vs_inst_idx := j)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists `0` >>
     simp[Abbr `b`] >>
     irule (List.last (IMP_CANON (SIMP_RULE (srw_ss()) []
       (Q.INST [`opc` |-> `SUB`] pop_scalar_binary_step)))) >>
     simp[eval_operand_def, lookup_var_set_inst_idx, op_taint_def]) >>
  `!u. step_prov PG G a u = G /\ step_taint a u u tn = tn` by
    simp[Abbr `a`, bop_assert_ghost] >>
  `!m. step_prov PG G b (update_var x3 (n-1w) m) = DRESTRICT G (COMPL {x3}) /\
   step_taint b m (update_var x3 (n-1w) m) tn = (tn with t_var := tn.t_var |+ (x3,{}))` by
    (gen_tac >> qunabbrev_tac `b` >> irule pop_scalar_binary_ghost >>
     simp[op_prov_def, op_taint_def]) >>
  simp[inst_seq_ptr_def]
QED

Theorem pop_check_path[local]:
  let code = [mk_inst (id+3) ASSERT [Var x2] [];
              mk_inst (id+4) SUB [Var x0; Lit 1w] [x3]] in
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D lo ctx func PG G tn code s G5 tn5 /\
  run_inst_seq code s = OK u ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := s.vs_inst_idx+2),G5,tn5)
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq code s` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[Abbr `code`, mk_inst_def, inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def]) >>
  `!i u. MEM i code ==> dalloca_no_wrap i u` by
    (simp[Abbr `code`] >> rpt gen_tac >>
     disch_then (DISJ_CASES_THEN SUBST1_TAC) >> simp[mk_inst_def, dalloca_no_wrap_def]) >>
  `(ctx_has_dalloca ctx ==> !pre i post u.
     code = pre ++ i::post /\ run_inst_seq pre s = OK u ==> dalloca_no_wrap i u)` by
    (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  drule_all run_inst_seq_gas_origin_ptr_path >>
  simp[Abbr `code`, mk_inst_def]
QED

Theorem pop_live_check_mods:
  let code = [mk_inst (id+3) ASSERT [Var x2] [];
              mk_inst (id+4) SUB [Var x0; Lit 1w] [x3]] in
  s.vs_inst_idx = k+3 /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  alloca_history func s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_var x2 s = SOME (bool_to_word T) /\ op_taint tn (Var x2) = {} /\
  lookup_var x0 s = SOME n /\ n <> 0w /\
  op_taint tn (Var x0) = {} /\ op_prov G (Var x0) = NONE /\
  x3 <> x0 /\ x3 <> x2 ==>
  ?u s5 G5 tn5.
    run_inst_seq code s = OK u /\
    s5 = (u with vs_inst_idx := k+5) /\
    (!D j. inst_seq_ptr D lo ctx func PG G tn code (s with vs_inst_idx := j) G5 tn5) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s5,G5,tn5)) /\
    lookup_var x3 s5 = SOME (n-1w) /\ op_taint tn5 (Var x3) = {} /\
    op_prov G5 (Var x3) = NONE /\
    (!q. q <> x3 ==> lookup_var q s5 = lookup_var q s /\
      FLOOKUP G5 q = FLOOKUP G q /\ op_taint tn5 (Var q) = op_taint tn (Var q)) /\
    (!op. op <> Var x3 ==> eval_operand op s5 = eval_operand op s) /\
    tn5.t_mem = tn.t_mem /\ tn5.t_stor = tn.t_stor /\
    tn5.t_trans = tn.t_trans /\ tn5.t_imm = tn.t_imm /\
    (s5 with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    ~s5.vs_halted /\ s5.vs_current_bb = s.vs_current_bb /\
    s5.vs_allocas = s.vs_allocas /\ s5.vs_alloca_next = s.vs_alloca_next /\
    s5.vs_fmp = s.vs_fmp /\ alloca_history func s5 /\ allocas_from lo s5 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s5)
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  qabbrev_tac `u = update_var x3 (n-1w) s` >>
  qabbrev_tac `s5 = u with vs_inst_idx := s.vs_inst_idx+2` >>
  qabbrev_tac `G5 = DRESTRICT G (COMPL {x3})` >>
  qabbrev_tac `tn5 = tn with t_var := tn.t_var |+ (x3,{})` >>
  `run_inst_seq code s = OK u /\
   (!D j. inst_seq_ptr D lo ctx func PG G tn code (s with vs_inst_idx := j) G5 tn5)` by
    (simp_tac bool_ss [Abbr `code`, Abbr `u`, Abbr `G5`, Abbr `tn5`] >>
     irule (SIMP_RULE bool_ss [LET_THM] pop_check_sequence) >> simp[]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn code s G5 tn5` by
    (gen_tac >>
     qpat_assum `!D j. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >>
     simp_tac bool_ss [venom_state_fupdselfid]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s5,G5,tn5)` by
    (gen_tac >> simp_tac bool_ss [Abbr `s5`] >>
     irule (SIMP_RULE bool_ss [LET_THM] pop_check_path) >>
     conj_tac >- asm_rewrite_tac[] >>
     map_every qexists [`bb`,`id`,`x0`,`x2`,`x3`] >>
     qunabbrev_tac `code` >> asm_rewrite_tac[]) >>
  `alloca_history func s5` by
    (qpat_x_assum `s.vs_inst_idx = k+3` kall_tac >>
     `LENGTH code = 2` by simp[Abbr `code`] >>
     simp_tac bool_ss [Abbr `s5`] >>
     qpat_assum `LENGTH code = 2` (once_rewrite_tac o single o GSYM) >>
     irule alloca_history_no_alloca_slice >>
     simp[Abbr `u`, update_var_def] >>
     conj_tac >- (pure_rewrite_tac [GSYM IS_PREFIX_APPEND] >> asm_rewrite_tac[]) >>
     simp[Abbr `code`, mk_inst_def]) >>
  `s5 = (u with vs_inst_idx := k+5)` by simp[Abbr `s5`] >>
  map_every qexists [`u`,`G5`,`tn5`] >>
  qpat_x_assum `s5 = (u with vs_inst_idx := k+5)` (once_rewrite_tac o single o GSYM) >>
  simp[Abbr `s5`, Abbr `u`, Abbr `G5`, Abbr `tn5`, lookup_var_set_inst_idx,
       lookup_var_update_var_same, lookup_var_update_var_other, FLOOKUP_DRESTRICT,
       op_taint_def, op_prov_def, FLOOKUP_UPDATE, update_var_def,
       allocas_from_def, allocas_below_fmp_updates] >>
  conj_tac >-
    (Cases >> simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  qpat_assum `s.vs_inst_idx = k+3` (pure_once_rewrite_tac o single o GSYM) >>
  simp_tac bool_ss [venom_state_fupdselfid]
QED
