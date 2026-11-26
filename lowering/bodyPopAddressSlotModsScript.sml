(* The three scalar address instructions after the linked Pop header store. *)
Theory bodyPopAddressSlotMods
Ancestors
  exprSimPopNestedBase exprSimPop bodyPtrPopScalarTransfer ptrSafetyTransport
  fragGasSeqPtr fragExecMem exprLoweringProps bodyBinopFragMemory allocasBelowFmpUpdatesProps
  unitTransformDefs venomState venomInst venomExecSemantics codegenRel
  ghostPcTransportPtr
  contextCodegenRel ptrDiscipline ptrSafeRun memSafeRun blockPrefixEquiv
  finite_map list rich_list words arithmetic

Theorem pop_slot_scalar_cons[local]:
  (opc = ADD /\ z = x+y \/ opc = MUL /\ z = x*y) /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
  op_prov G a = NONE /\ op_prov G b = NONE /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  inst_seq_ptr D lo ctx func PG (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{})) tail
    (update_var out z s with vs_inst_idx := SUC s.vs_inst_idx) G' tn' ==>
  inst_seq_ptr D lo ctx func PG G tn (mk_inst id opc [a;b] [out]::tail) s G' tn'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `step_inst_base (mk_inst id opc [a;b] [out]) s = OK (update_var out z s) /\
   ptr_inst_ok D 0 0 ctx func G tn (mk_inst id opc [a;b] [out]) s` by
    (irule pop_scalar_binary_step >> simp[] >> map_every qexists [`x`,`y`] >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn (mk_inst id opc [a;b] [out]) s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists `0` >> simp[]) >>
  `step_prov PG G (mk_inst id opc [a;b] [out]) (update_var out z s) =
      DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id opc [a;b] [out]) s (update_var out z s) tn =
      (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule pop_scalar_binary_ghost >> simp[] >> metis_tac[]) >>
  simp[Once inst_seq_ptr_def]
QED

Theorem pop_slot_address_run[local]:
  eval_operand hdr s = SOME slot /\ lookup_var x3 s = SOME m /\
  ALL_DISTINCT [x3;x4;x5;x6] ==>
  run_inst_seq [mk_inst (id+6) ADD [hdr; Lit 1w] [x4];
                mk_inst (id+7) MUL [Var x3; Lit (n2w esz)] [x5];
                mk_inst (id+8) ADD [Var x4; Var x5] [x6]] s =
  OK (update_var x6 (slot + 1w + m * n2w esz)
       (update_var x5 (m * n2w esz) (update_var x4 (slot + 1w) s)))
Proof
  simp[run_inst_seq_def, nested_pop_step_add, pop_step_MUL_lit,
       pop_step_ADD_var, lookup_var_update_var_same, lookup_var_update_var_other]
QED

Theorem pop_slot_allocas[local]:
  (allocas_from lo (s with vs_inst_idx := j) <=> allocas_from lo s) /\
  (allocas_from lo (update_var x w s) <=> allocas_from lo s)
Proof
  simp[allocas_from_def, update_var_def]
QED

Theorem pop_slot_address_ptr[local]:
  let code = [mk_inst (id+6) ADD [hdr; Lit 1w] [x4];
              mk_inst (id+7) MUL [Var x3; Lit (n2w esz)] [x5];
              mk_inst (id+8) ADD [Var x4; Var x5] [x6]];
      H = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x4})) (COMPL {x5})) (COMPL {x6});
      tm = tn with t_var := tn.t_var |+ (x4,{}) |+ (x5,{}) |+ (x6,{})
  in
    ALL_DISTINCT [x3;x4;x5;x6] /\
    eval_operand hdr s = SOME slot /\ lookup_var x3 s = SOME m /\
    op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
    op_prov G (Var x3) = NONE /\ op_taint tn (Var x3) = {} /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
    !D j. inst_seq_ptr D lo ctx func PG G tn code (s with vs_inst_idx := j) H tm
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >> rpt gen_tac >>
  fs[op_prov_def, op_taint_def] >>
  irule pop_slot_scalar_cons >>
  simp[eval_operand_def, op_prov_def, op_taint_def, pop_slot_allocas,
       allocas_below_fmp_updates] >>
  irule pop_slot_scalar_cons >>
  simp[eval_operand_def, lookup_var_update_var_same, lookup_var_update_var_other,
       lookup_var_set_inst_idx, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       op_prov_def, op_taint_def, pop_slot_allocas, allocas_below_fmp_updates] >>
  irule pop_slot_scalar_cons >>
  simp[eval_operand_def, lookup_var_update_var_same, lookup_var_update_var_other,
       lookup_var_set_inst_idx, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       op_prov_def, op_taint_def, pop_slot_allocas, allocas_below_fmp_updates,
       inst_seq_ptr_def, pred_setTheory.INTER_ASSOC]
QED

Theorem pop_slot_address_path[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MUL) code /\
  inst_seq_ptr D lo ctx func PG G tn code s H tm /\ run_inst_seq code s = OK u ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH code),H,tm)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. MEM i code ==> i.inst_opcode = ADD \/ i.inst_opcode = MUL` by
    fs[EVERY_MEM] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >> first_x_assum drule >>
     disch_then (DISJ_CASES_THEN SUBST1_TAC) >> simp[is_terminator_def]) >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >> simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     qpat_assum `!i. MEM i code ==> _` (qspec_then `i` mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     disch_then (DISJ_CASES_THEN assume_tac) >>
     simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `(ctx_has_dalloca ctx ==> !pre i post u.
     code = pre ++ i::post /\ run_inst_seq pre s = OK u ==> dalloca_no_wrap i u)` by
    (rpt strip_tac >> `MEM i code` by simp[] >>
     qpat_assum `!i. MEM i code ==> _` (qspec_then `i` mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     disch_then (DISJ_CASES_THEN assume_tac) >> simp[dalloca_no_wrap_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> gen_tac >> disch_tac >>
     qpat_assum `!i. MEM i code ==> _` (qspec_then `i` mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >> disch_then (DISJ_CASES_THEN assume_tac) >> simp[]) >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED

Theorem pop_slot_address_code[local]:
  DROP 6 (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) =
    [mk_inst (id+6) ADD [hdr; Lit 1w] [x4];
     mk_inst (id+7) MUL [Var x3; Lit (n2w esz)] [x5];
     mk_inst (id+8) ADD [Var x4; Var x5] [x6]]
Proof
  simp[nested_pop_suffix_def]
QED

Theorem pop_address_slot_mods:
  let code = DROP 6 (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) in
    s.vs_inst_idx = k+6 /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    alloca_history func s /\ allocas_from lo s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    eval_operand hdr s = SOME slot /\ lookup_var x3 s = SOME m /\
    op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
    op_prov G (Var x3) = NONE /\ op_taint tn (Var x3) = {} /\
    ALL_DISTINCT [x3;x4;x5;x6] /\
    (!q. hdr = Var q ==> ~MEM q [x4;x5;x6]) ==>
    ?u s9 G9 tn9.
      run_inst_seq code s = OK u /\ s9 = (u with vs_inst_idx := k+9) /\
      (!D j. inst_seq_ptr D lo ctx func PG G tn code (s with vs_inst_idx := j) G9 tn9) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s9,G9,tn9)) /\
      lookup_var x6 s9 = SOME (slot + 1w + m * n2w esz) /\
      op_prov G9 (Var x6) = NONE /\ op_taint tn9 (Var x6) = {} /\
      (!q. ~MEM q [x4;x5;x6] ==> lookup_var q s9 = lookup_var q s /\
        FLOOKUP G9 q = FLOOKUP G q /\ op_taint tn9 (Var q) = op_taint tn (Var q)) /\
      (!op. ~MEM op [Var x4;Var x5;Var x6] ==> eval_operand op s9 = eval_operand op s) /\
      tn9.t_mem = tn.t_mem /\ tn9.t_stor = tn.t_stor /\
      tn9.t_trans = tn.t_trans /\ tn9.t_imm = tn.t_imm /\
      (s9 with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      ~s9.vs_halted /\ s9.vs_current_bb = s.vs_current_bb /\
      s9.vs_memory = s.vs_memory /\ s9.vs_accounts = s.vs_accounts /\
      s9.vs_transient = s.vs_transient /\
      s9.vs_allocas = s.vs_allocas /\ s9.vs_alloca_next = s.vs_alloca_next /\
      s9.vs_fmp = s.vs_fmp /\ alloca_history func s9 /\ allocas_from lo s9 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s9)
Proof
  simp_tac bool_ss [LET_THM, pop_slot_address_code] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  qabbrev_tac `u = update_var x6 (slot+1w+m*n2w esz)
    (update_var x5 (m*n2w esz) (update_var x4 (slot+1w) s))` >>
  qabbrev_tac `s9 = u with vs_inst_idx := s.vs_inst_idx + LENGTH code` >>
  qabbrev_tac `G9 = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x4})) (COMPL {x5})) (COMPL {x6})` >>
  qabbrev_tac `tn9 = tn with t_var := tn.t_var |+ (x4,{}) |+ (x5,{}) |+ (x6,{})` >>
  `run_inst_seq code s = OK u` by
    (simp_tac bool_ss [Abbr `code`, Abbr `u`] >> irule pop_slot_address_run >> simp[]) >>
  `!D j. inst_seq_ptr D lo ctx func PG G tn code (s with vs_inst_idx := j) G9 tn9` by
    (simp_tac bool_ss [Abbr `code`, Abbr `G9`, Abbr `tn9`] >>
     irule (SIMP_RULE bool_ss [LET_THM] pop_slot_address_ptr) >> simp[]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn code s G9 tn9` by
    (gen_tac >> qpat_assum `!D j. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >> simp_tac bool_ss [venom_state_fupdselfid]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s9,G9,tn9)` by
    (qpat_x_assum `s.vs_inst_idx = k+6` kall_tac >>
     gen_tac >> simp_tac bool_ss [Abbr `s9`] >> irule pop_slot_address_path >>
     asm_simp_tac bool_ss [] >>
     conj_tac >- simp[Abbr `code`, mk_inst_def] >>
     qexists `bb` >> asm_rewrite_tac[]) >>
  `alloca_history func s9` by
    (qpat_x_assum `s.vs_inst_idx = k+6` kall_tac >>
     simp_tac bool_ss [Abbr `s9`] >> irule alloca_history_no_alloca_slice >>
     simp[Abbr `u`, update_var_def] >>
     conj_tac >- (pure_rewrite_tac [GSYM IS_PREFIX_APPEND] >> asm_rewrite_tac[]) >>
     simp[Abbr `code`, mk_inst_def]) >>
  `LENGTH code = 3` by simp[Abbr `code`] >>
  `s9 = (u with vs_inst_idx := k+9)` by simp[Abbr `s9`] >>
  map_every qexists [`u`,`G9`,`tn9`] >>
  qpat_x_assum `s9 = (u with vs_inst_idx := k+9)` (once_rewrite_tac o single o GSYM) >>
  simp[Abbr `s9`, Abbr `u`, Abbr `G9`, Abbr `tn9`, lookup_var_set_inst_idx,
       lookup_var_def, FLOOKUP_DRESTRICT, op_taint_def, op_prov_def,
       FLOOKUP_UPDATE, update_var_def, allocas_from_def, allocas_below_fmp_updates] >>
  conj_tac >- (Cases >> simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  qpat_assum `s.vs_inst_idx = k+6` (pure_once_rewrite_tac o single o GSYM) >>
  simp_tac bool_ss [venom_state_fupdselfid]
QED
