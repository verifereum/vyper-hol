(* Joint Neg simulation: its checked arithmetic suffix. *)
Theory bodyFullBuiltinWordNeg
Ancestors
  bodyFullGhostFrame bodyFullShared bodyFullPreds bodySimFull
  gasOutcomeFullCompose gasOutcomeFullStmts fragGasSeqPtr fragGasEmitCtrl
  exprSimWordBuiltins exprSimUnopProps exprSimSource
  fragExecMem unitTransformDefs memSafeRun fragGasSeqAbort instIdxIndep
  venomInstProofs fragGasOriginPtr fragGasOrigin fragGasPathPtr gasCount
  ptrSafeRun ptrDiscipline exprLowering emitHelper emitHelperProps
  exprLoweringProps compileEnv venomExecSemantics venomInst venomState
  list rich_list finite_map codegenRel contextCodegenRel decoderGhostFramePtr
  freshWrites exprSimHypsDefs vyperTypeSystem vyperTyping vyperValue vyperContext
  exprSimUnopComposeProps gasShadowCompileStmtHelpers

Theorem word_neg_emission:
  !x ty sa op sb.
    compile_neg x ty sa = (op,sb) ==>
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id SGT [x; Lit (FST (type_bounds ty))]
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id+1) ASSERT
         [Var (STRING #"%" (toString sa.cs_next_var))] [];
       mk_inst (sa.cs_next_id+2) SUB [Lit 0w; x]
         [STRING #"%" (toString (sa.cs_next_var+1))]] /\
    op = Var (STRING #"%" (toString (sa.cs_next_var+1)))
Proof
  rpt gen_tac >> Cases_on `type_bounds ty` >>
  simp[compile_neg_def, LET_THM, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
    fresh_var_def, emit_def, emitted_insts_def, DROP_LENGTH_APPEND,
    arithmeticTheory.ADD_ASSOC] >>
  strip_tac >> gvs[listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem word_neg_arithmetic_ptr:
  compile_neg x ty sa = (op,sb) /\
  MEM i [mk_inst sa.cs_next_id SGT [x; Lit (FST (type_bounds ty))]
           [STRING #"%" (toString sa.cs_next_var)];
         mk_inst (sa.cs_next_id+2) SUB [Lit 0w; x]
           [STRING #"%" (toString (sa.cs_next_var+1))]] /\
  op_taint tn x = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn i s
Proof
  strip_tac >> gvs[] >>
  (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  conj_tac >- (gen_tac >> Cases_on `op' = x` >>
    gvs[] >> Cases_on `op'` >> simp[op_taint_def]) >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[])
QED

Theorem word_neg_assert_ptr:
  compile_neg x ty sa = (op,sb) /\
  op_taint tn (Var (STRING #"%" (toString sa.cs_next_var))) = {} /\
  allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn
    (mk_inst (sa.cs_next_id+1) ASSERT
      [Var (STRING #"%" (toString sa.cs_next_var))] []) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  Cases_on `eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) s` >>
  simp[] >> Cases_on `x' = 0w` >> simp[]
QED

Theorem word_neg_inst_seq_ptr:
  compile_neg x ty sa = (op,sb) /\
  op_taint tn x = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?G' tn'. !D. inst_seq_ptr D lo ctx fn PG G tn
    (emitted_insts sa sb) s G' tn'
Proof
  strip_tac >> drule word_neg_emission >> strip_tac >>
  `!D. ptr_inst_ok D lo 0 ctx fn G tn
     (mk_inst sa.cs_next_id SGT [x; Lit (FST (type_bounds ty))]
       [STRING #"%" (toString sa.cs_next_var)]) s` by
    (irule word_neg_arithmetic_ptr >> metis_tac[listTheory.MEM]) >>
  asm_rewrite_tac[] >> simp[Once inst_seq_ptr_def] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
    instruction_accessors, instruction_accfupds, combinTheory.K_THM,
    opcode_case_def] >>
  Cases_on `eval_operand x s` >>
  simp[exec_pure2_def, eval_operand_def] >>
  qmatch_goalsub_abbrev_tac `?G' tn'. !D.
    inst_seq_ptr D lo ctx fn PG G1 tn1 code s1 G' tn'` >>
  `op_taint tn1 x = {} /\
   op_taint tn1 (Var (STRING #"%" (toString sa.cs_next_var))) = {}` by
    (simp[Abbr `tn1`, step_taint_def, op_taint_def, set_var_taint_def,
      out_taint_def, FLOOKUP_UPDATE] >>
     Cases_on `x` >> gvs[op_taint_def, FLOOKUP_UPDATE] >>
     gvs[AllCaseEqs()]) >>
  `allocas_from lo s1 /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s1)` by
    (gvs[Abbr `s1`, allocas_from_def, allocas_below_fmp_def, update_var_def] >>
     metis_tac[]) >>
  `!D. ptr_inst_ok D lo 0 ctx fn G1 tn1
     (mk_inst (sa.cs_next_id+1) ASSERT
       [Var (STRING #"%" (toString sa.cs_next_var))] []) s1` by
    (irule word_neg_assert_ptr >> metis_tac[]) >>
  simp[Abbr `code`, Once inst_seq_ptr_def, GSYM mk_inst_def] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
    instruction_accessors, instruction_accfupds, combinTheory.K_THM,
    opcode_case_def] >>
  namedCases_on `eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) s1`
    ["", "cond"] >> simp[] >> Cases_on `cond = 0w` >> simp[] >>
  qmatch_goalsub_abbrev_tac `?G' tn'. !D.
    inst_seq_ptr D lo ctx fn PG G2 tn2 code2 s2 G' tn'` >>
  `op_taint tn2 x = {}` by
    (Cases_on `x` >>
     gvs[Abbr `tn2`, step_taint_def, op_taint_def, set_var_taint_def,
       finite_mapTheory.DRESTRICT_UNIV]) >>
  `allocas_from lo s2 /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s2)` by
    (gvs[Abbr `s2`, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `!D. ptr_inst_ok D lo 0 ctx fn G2 tn2
     (mk_inst (sa.cs_next_id+2) SUB [Lit 0w; x]
       [STRING #"%" (toString (sa.cs_next_var+1))]) s2` by
    (irule word_neg_arithmetic_ptr >> metis_tac[listTheory.MEM]) >>
  simp[Abbr `code2`, Once inst_seq_ptr_def, GSYM mk_inst_def] >>
  Cases_on `step_inst_base
    (mk_inst (sa.cs_next_id+2) SUB [Lit 0w; x]
      [STRING #"%" (toString (sa.cs_next_var+1))]) s2` >>
  simp[inst_seq_ptr_def, mk_inst_def]
QED

Theorem word_neg_memory_safe:
  compile_neg x ty sa = (op,sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule word_neg_emission >> strip_tac >>
  asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, inst_mem_below_frontier_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    inst_dload_in_section_def]
QED

Theorem word_neg_run_nonfresh:
  compile_neg x ty sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME w ==>
  (w2i (FST (type_bounds ty)) < w2i w ==>
     ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
         eval_operand op t = SOME (0w - w)) /\
  (~(w2i (FST (type_bounds ty)) < w2i w) ==>
     ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >> drule word_neg_emission >> strip_tac >>
  `!z. x = Var z ==> z <> STRING #"%" (toString sa.cs_next_var)` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `!v. eval_operand x (update_var
       (STRING #"%" (toString sa.cs_next_var)) v s) = SOME w` by
    (Cases_on `x` >> gvs[eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE]) >>
  asm_rewrite_tac[] >>
  simp[run_inst_seq_def, step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
    instruction_accessors, instruction_accfupds, combinTheory.K_THM,
    opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    integer_wordTheory.WORD_GTi, integerTheory.int_gt, bool_to_word_def] >>
  strip_tac >>
  qpat_x_assum `!v. eval_operand x (update_var _ v s) = SOME w`
    (qspec_then `1w` mp_tac) >>
  simp[update_var_def] >> strip_tac >> simp[FLOOKUP_UPDATE]
QED

Theorem word_neg_success_origin:
  compile_neg x ty sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME w /\
  w2i (FST (type_bounds ty)) < w2i w /\
  op_taint tn x = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (0w - w) /\
    !D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),
         G',tn')
Proof
  strip_tac >> drule_all word_neg_run_nonfresh >> simp[] >> strip_tac >>
  drule_all word_neg_inst_seq_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `G`] strip_assume_tac) >>
  qexistsl [`t`, `G'`, `tn'`] >> simp[] >> gen_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (drule word_neg_emission >> strip_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  drule word_neg_memory_safe >> strip_tac >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn'` by simp[] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by simp[] >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED

Theorem word_neg_abort_origin:
  compile_neg x ty sa = (op,sb) /\
  op_taint tn x = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts sa sb) s = Abort a t ==>
  ?G' tn'. !D.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort a (t with vs_inst_idx := SUC s.vs_inst_idx),G',tn')
Proof
  strip_tac >> drule_all word_neg_inst_seq_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `G`] strip_assume_tac) >>
  drule word_neg_emission >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa sb = [i;j;k]` >>
  `!t'. step_inst_base i s <> Abort a t'` by
    (simp[Abbr `i`, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, AllCaseEqs()]) >>
  `!u t'. step_inst_base k u <> Abort a t'` by
    (simp[Abbr `k`, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, AllCaseEqs()]) >>
  `isPREFIX [i;j;k] (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base i s` >>
  gvs[run_inst_seq_def, Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base j v` >>
  gvs[AllCaseEqs()] >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   j.inst_opcode <> INVOKE /\ j.inst_opcode <> GAS /\
   ~is_terminator j.inst_opcode` by
    simp[Abbr `i`, Abbr `j`, mk_inst_def, is_terminator_def] >>
  `~v.vs_halted /\ v.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow,
      step_inst_non_invoke] >>
  qabbrev_tac `u = v with vs_inst_idx := SUC s.vs_inst_idx` >>
  `get_instruction bb u.vs_inst_idx = SOME j` by
    (simp[Abbr `u`] >>
     `isPREFIX [j;k] (DROP (SUC s.vs_inst_idx) bb.bb_instructions)` by simp[] >>
     drule instruction_prefix_cursor >> simp[]) >>
  `step_inst_base j u = Abort a (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Abbr `u`, step_inst_inst_idx_indep, exec_result_map_def] >>
  qexistsl [`G'`, `tn'`] >> gen_tac >>
  first_x_assum (qspec_then `D` strip_assume_tac) >>
  gvs[Once inst_seq_ptr_def] >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
   mem_safe_step 0 ctx j u` by
    simp[Abbr `i`, Abbr `j`, mem_safe_step_non_invoke,
      inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def, mk_inst_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK u,step_prov PG G i v,step_taint i s v tn)` by
    (drule_all straight_line_origin_ptr_edge >>
     simp[Abbr `i`, Abbr `u`, mk_inst_def]) >>
  `!fuel. step_inst fuel ctx j u =
     Abort a (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[step_inst_non_invoke] >>
  `~u.vs_halted /\
   lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by simp[Abbr `u`] >>
  `exit_result (Abort a (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    simp[fragExecTheory.exit_result_def] >>
  `gas_events_step 0 ctx func.fn_name j u = [] /\
   gas_count_step 0 ctx j u = 0` by
    simp[gasEventsTheory.gas_events_step_def, gas_count_step_def] >>
  drule_all exit_inst_origin_ptr >> strip_tac >>
  drule (cj 2 gas_origin_ptr_path_rules) >> simp[]
QED

Theorem word_neg_ghost_register_frame:
  compile_neg x ty sa = (op,sb) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' ==>
  !z. not_fresh_at sa z ==>
    FLOOKUP G' z = FLOOKUP G z /\
    op_taint tn' (Var z) = op_taint tn (Var z)
Proof
  strip_tac >> drule word_neg_emission >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa sb = [i;j;k]` >>
  gen_tac >> strip_tac >>
  `~MEM z i.inst_outputs /\ ~MEM z j.inst_outputs /\
   ~MEM z k.inst_outputs` by
    (gvs[Abbr `i`, Abbr `j`, Abbr `k`, mk_inst_def,
       loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  gvs[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base i s` >>
  gvs[step_prov_other_output, step_taint_other_output] >>
  gvs[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base j (v with vs_inst_idx := SUC s.vs_inst_idx)` >>
  gvs[step_prov_other_output, step_taint_other_output] >>
  gvs[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base k (v' with vs_inst_idx := SUC (SUC s.vs_inst_idx))` >>
  gvs[inst_seq_ptr_def, step_prov_other_output, step_taint_other_output]
QED

Theorem word_neg_step_exterior:
  compile_neg x ty sa = (op,sb) /\
  MEM i (emitted_insts sa sb) /\ step_inst_base i s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (step_taint i s t tn).t_mem = tn.t_mem /\
  (step_taint i s t tn).t_stor = tn.t_stor /\
  (step_taint i s t tn).t_trans = tn.t_trans /\
  (step_taint i s t tn).t_imm = tn.t_imm
Proof
  strip_tac >> drule word_neg_emission >> strip_tac >> gvs[] >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
    AllCaseEqs(), update_var_def] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
    step_writes_def, source_memory_write_ranges_def, range_bytes_def,
    written_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
    mk_inst_def, finite_mapTheory.FLOOKUP_DEF] >>
  SET_TAC[]
QED

Theorem word_neg_taint_exterior:
  compile_neg x ty sa = (op,sb) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' ==>
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  `!i u v tn0. MEM i (emitted_insts sa sb) /\
      step_inst_base i u = OK v ==>
      (step_taint i u v tn0).t_mem = tn0.t_mem /\
      (step_taint i u v tn0).t_stor = tn0.t_stor /\
      (step_taint i u v tn0).t_trans = tn0.t_trans /\
      (step_taint i u v tn0).t_imm = tn0.t_imm` by
    metis_tac[word_neg_step_exterior] >>
  drule word_neg_emission >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa sb = [i;j;k]` >>
  `MEM i (emitted_insts sa sb) /\ MEM j (emitted_insts sa sb) /\
   MEM k (emitted_insts sa sb)` by simp[] >>
  gvs[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base i s` >> gvs[] >>
  gvs[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base j (v with vs_inst_idx := SUC s.vs_inst_idx)` >>
  gvs[] >>
  gvs[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base k (v' with vs_inst_idx := SUC (SUC s.vs_inst_idx))` >>
  gvs[inst_seq_ptr_def] >> metis_tac[]
QED

Theorem word_neg_runtime_frame:
  compile_neg x ty sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s) /\
  (!func bb. alloca_history func s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
    alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))
Proof
  strip_tac >> mp_tac straight_fresh_neg >> simp[straight_fresh_def] >>
  disch_then drule >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> simp[lookup_var_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    (drule word_neg_emission >> strip_tac >> simp[mk_inst_def]) >>
  `alloca_history func (s with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (qpat_x_assum `alloca_history func s`
       (strip_assume_tac o REWRITE_RULE [allocaHistoryTheory.alloca_history_def]) >>
     rewrite_tac[allocaHistoryTheory.alloca_history_def] >> conj_tac >- simp[] >>
     rpt strip_tac >>
     rename1 `get_instruction bb2 k = SOME inst` >>
     `lookup_block s.vs_current_bb func.fn_blocks = SOME bb2` by
       (qpat_x_assum `lookup_block (_ with vs_inst_idx := _).vs_current_bb _ = _` mp_tac >> simp[]) >>
     `bb2 = bb` by metis_tac[optionTheory.SOME_11] >>
     qpat_x_assum `bb2 = bb` SUBST_ALL_TAC >>
     `k < s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by
       (qpat_x_assum `k < (_ with vs_inst_idx := _).vs_inst_idx` mp_tac >> simp[]) >>
     Cases_on `k < s.vs_inst_idx` >- (simp[] >> metis_tac[]) >>
     `k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst` by
       (qpat_x_assum `get_instruction bb k = _` mp_tac >> rw[get_instruction_def]) >>
     `k - s.vs_inst_idx + s.vs_inst_idx = k /\
      k - s.vs_inst_idx < LENGTH (emitted_insts sa sb)` by decide_tac >>
     `EL (k - s.vs_inst_idx) (DROP s.vs_inst_idx bb.bb_instructions) = inst` by
       (qspecl_then [`k - s.vs_inst_idx`, `s.vs_inst_idx`, `bb.bb_instructions`]
          mp_tac EL_DROP >> simp[]) >>
     qpat_x_assum `isPREFIX _ _` mp_tac >> rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
     `EL (k - s.vs_inst_idx) (emitted_insts sa sb) = inst` by
       (qpat_x_assum `EL _ (DROP _ _) = _` mp_tac >> simp[EL_APPEND_EQN]) >>
     `MEM inst (emitted_insts sa sb)` by metis_tac[EL_MEM] >>
     gvs[EVERY_MEM]) >>
  irule allocaHistoryTheory.alloca_history_frame >>
  qexists_tac `s with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)` >> simp[]
QED

Theorem word_neg_ghost_frame:
  compile_neg x ty sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
  ghost_inv_at D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
          not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
          not_fresh_at sa z) /\ es'.scopes = es.scopes ==>
  ghost_inv_at D lo d cenv cx es' G' tn' (t with vs_inst_idx := n)
Proof
  strip_tac >>
  drule_all word_neg_runtime_frame >> strip_tac >>
  drule_all word_neg_taint_exterior >> strip_tac >>
  `!z. not_fresh_at sa z ==> FLOOKUP G' z = FLOOKUP G z /\
       op_taint tn' (Var z) = op_taint tn (Var z)` by
    metis_tac[word_neg_ghost_register_frame] >>
  irule ghost_inv_at_exterior_frame >>
  qexistsl [`G`, `es`, `s`, `sa`, `tn`] >>
  simp[] >>
  qpat_x_assum `t = s with vs_vars := _` SUBST_ALL_TAC >>
  fs[lookup_var_def]
QED

Theorem word_neg_result_clean:
  compile_neg x ty sa = (op,sb) /\ op_prov G x = NONE /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' ==>
  op_taint tn' op = {} /\ op_prov G' op = NONE
Proof
  strip_tac >> drule word_neg_emission >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa sb = [i;j;k]` >>
  `~is_terminator i.inst_opcode /\ ~is_terminator j.inst_opcode /\
   ~is_terminator k.inst_opcode` by
    simp[Abbr `i`, Abbr `j`, Abbr `k`, mk_inst_def, is_terminator_def] >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  gvs[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  simp[Abbr `i`, Abbr `j`, Abbr `k`, step_prov_def, out_prov_def,
    set_prov_def, op_prov_def, first_prov_def, FLOOKUP_DRESTRICT,
    step_taint_def, op_taint_def, set_var_taint_def, out_taint_def,
    mk_inst_def, FLOOKUP_UPDATE, eval_operand_def] >>
  Cases_on `x` >> gvs[op_prov_def] >>
  Cases_on `s' = STRING #"%" (toString sa.cs_next_var)` >>
  gvs[FLOOKUP_DRESTRICT]
QED

Theorem word_neg_success_ghost_origin:
  compile_neg x ty sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  op_prov G x = NONE /\ 
  eval_operand x s = SOME w /\
  w2i (FST (type_bounds ty)) < w2i w /\
  op_taint tn x = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
          not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
          not_fresh_at sa z) /\ es'.scopes = es.scopes /\
  (!H. valid_horizon cx st0 H trace ==>
       ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (0w - w) /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    t = s with vs_vars := t.vs_vars /\
    (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s /\
         FLOOKUP G' z = FLOOKUP G z /\
         op_taint tn' (Var z) = op_taint tn (Var z)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !H. valid_horizon cx st0 H trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),
         G',tn') /\
      ghost_inv_at (DF H) lo d cenv cx es' G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))
Proof
  strip_tac >> drule_all word_neg_success_origin >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`] strip_assume_tac) >>
  `inst_seq_ptr (DF (storage_trace_horizon trace)) lo ctx func PG G tn
     (emitted_insts sa sb) s G' tn'` by simp[] >>
  drule_all word_neg_result_clean >> strip_tac >>
  drule_all word_neg_runtime_frame >> strip_tac >>
  drule_all word_neg_taint_exterior >> strip_tac >>
  `!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s /\
       FLOOKUP G' z = FLOOKUP G z /\
       op_taint tn' (Var z) = op_taint tn (Var z)` by
    metis_tac[word_neg_ghost_register_frame] >>
  qexistsl [`t`, `G'`, `tn'`] >> simp[] >> rpt strip_tac >>
  irule word_neg_ghost_frame >> metis_tac[]
QED

Theorem word_neg_continuation_full:
  expr_body_pre cenv cx env (Builtin (expr_type e) Neg [e]) es /\
  expr_body_pre cenv cx env e es /\
  is_numeric_type (expr_type e) /\ ~is_uint_type (expr_type e) /\
  is_word_type (expr_type e) /\
  0 < type_bits (expr_type e) /\ type_bits (expr_type e) <= 256 /\
  compile_neg x (expr_type e) s1 = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
  fn_has_code s1 sb func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (res,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     ?v. res = INL v /\ expr_post H ctx func cenv cx e es sa s1 s0 mid v x t /\
       expr_store_bound cx (expr_type e) v x t /\
       t.vs_current_bb = s1.cs_current_bb /\
       t.vs_inst_idx = LENGTH s1.cs_current_insts /\ alloca_history func t /\
       s0.vs_alloca_next <= t.vs_alloca_next /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
       ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\ ~t.vs_halted) ==>
  ?v. res = INL v /\
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
      (\es. (unop_result cx (expr_type e) Neg [expr_type e] v es,es))
      (mid,t,G1,tn1)
      (\H res ee G tn t.
        ?v. res = INL v /\
          expr_post H ctx func cenv cx (Builtin (expr_type e) Neg [e]) es sa sb s0 ee v op t /\
          expr_store_bound cx (expr_type (Builtin (expr_type e) Neg [e])) v op t /\
          t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          ptr_val_ok cx (expr_type (Builtin (expr_type e) Neg [e])) v op G tn t /\
          (~is_word_type (expr_type (Builtin (expr_type e) Neg [e])) ==>
             ptr_buf_ok cenv (Builtin (expr_type e) Neg [e]) op G t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
      (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  qexists_tac `v` >> asm_rewrite_tac[] >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
        value_has_type tv v` by
    (irule expr_body_pre_word_value >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`cenv`, `env`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `mid with gas_obs := []`] >>
     simp[] >> metis_tac[APPEND_NIL]) >>
  drule_all neg_typed_source >>
  disch_then (qspec_then `mid` mp_tac) >>
  `eval_operand x t = SOME (typed_val_to_w256 tv v) /\ ~t.vs_halted` by
    gvs[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
      loweringPostsTheory.post_value_type_def] >>
  `op_taint tn1 x = {} /\ op_prov G1 x = NONE` by
    gvs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `allocas_from lo t` by
    gvs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `sb.cs_current_bb = s1.cs_current_bb /\
   sb.cs_current_insts = s1.cs_current_insts ++ emitted_insts s1 sb` by
    (mp_tac (Q.SPECL [`x`, `expr_type e`] straight_fresh_neg) >>
     simp[straight_fresh_def] >> metis_tac[]) >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts s1 sb) (DROP t.vs_inst_idx bb.bb_instructions)` by
    (gvs[fragExecTheory.fn_has_code_def] >>
     qpat_x_assum `isPREFIX (_ ++ _) _` mp_tac >>
     rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
     qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, exprLoweringPropsTheory.DROP_PREFIX] >>
     qexists_tac `l` >> rewrite_tac[]) >>
  `local_ptrs_reserved cenv s1 /\
   (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z)` by
    (conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
     conj_tac >> rpt gen_tac >> strip_tac >>
     `not_fresh_at sa z` by metis_tac[] >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  Cases_on `w2i (FST (type_bounds (expr_type e))) < w2i (typed_val_to_w256 tv v)` >>
  simp[] >> strip_tac
  >- (`!H. valid_horizon cx st0 H mid.storage_trace ==>
           ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
        (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> gvs[]) >>
      `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by simp[] >>
      `mid.scopes = mid.scopes` by simp[] >>
      drule_all word_neg_success_ghost_origin >>
      disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
      irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
      qexistsl_tac [`G'`, `mid`, `INL v'`,
        `t' with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts s1 sb)`, `tn'`] >>
      simp[exprSimUnopComposePropsTheory.unop_result_gas_obs] >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> ?v. _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
      qpat_x_assum `INL v = INL _` (SUBST_ALL_TAC o SYM o SRULE [sumTheory.INL_11]) >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
      simp[vyperASTTheory.expr_type_def] >>
      `stmt_state_rel H ctx func cenv cx mid t` by
        gvs[loweringPostsTheory.expr_post_def] >>
      `stmt_state_rel H ctx func cenv cx mid (t with vs_vars := t'.vs_vars)` by
        (irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
         gvs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
      `stmt_state_rel H ctx func cenv cx mid t'` by metis_tac[] >>
      qpat_x_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
      `expr_post H ctx func cenv cx e es sa s1 s0 (mid with gas_obs := []) v x t =
       expr_post H ctx func cenv cx e es sa s1 s0 mid v x t` by
        (`storage_well_formed_on cx (mid with gas_obs := []) (FST H) <=>
          storage_well_formed_on cx mid (FST H)` by
           (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
         qpat_x_assum `storage_well_formed_on _ (_ with gas_obs := _) _ <=> _`
           (fn th => POP_ASSUM_LIST (K all_tac) >> assume_tac th) >>
         simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_at_def,
           loweringPostsTheory.expr_val_own_def, exprLoweringPropsTheory.stmt_state_rel_def,
           loweringStateRelDefsTheory.state_rel_gas_obs,
           loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def]) >>
      conj_tac
      >- (irule exprSimUnopPropsTheory.expr_post_unop >>
          simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
            exprSimWordArgsTheory.stmt_state_rel_gas_obs,
            loweringPostsTheory.expr_val_rel_def, eval_operand_def, lookup_var_def] >>
          qexistsl_tac [`s1`, `t`, `v`, `x`] >>
          simp[] >>
          conj_tac >- metis_tac[lookup_var_def] >>
          `t'.vs_allocas = t.vs_allocas /\ t'.vs_memory = t.vs_memory` by
            (qpat_assum `t' = t with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
          simp[] >>
          simp[]) >>
      simp[exprSimMemDefsTheory.expr_store_bound_word, bodyPtrDefsTheory.ptr_val_ok_def] >>
      `t'.vs_current_bb = t.vs_current_bb /\ t'.vs_alloca_next = t.vs_alloca_next` by
        (qpat_assum `t' = t with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
      simp[] >>
      conj_tac
      >- (drule_all word_neg_runtime_frame >> strip_tac >>
          first_x_assum (qspecl_then [`func`, `bb`] mp_tac) >> simp[]) >>
      conj_tac
      >- (qpat_x_assum `ghost_inv_at _ _ _ _ _ mid _ _ (_ with vs_inst_idx := _)`
            mp_tac >>
          qpat_assum `t.vs_inst_idx = _` mp_tac >>
          qpat_assum `tn'.t_mem = _` mp_tac >>
          qpat_assum `t'.vs_alloca_next = _` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >>
          simp[bodyPtrDefsTheory.ghost_inv_at_def] >>
          rpt strip_tac >> simp[]) >>
      `!z. not_fresh_at sa z ==> not_fresh_at s1 z` by
        (rpt strip_tac >>
         qpat_x_assum `not_fresh_at sa z` mp_tac >>
         qpat_assum `sa.cs_next_var <= s1.cs_next_var` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ G1 tn1` mp_tac >>
      simp[bodyPtrDefsTheory.ghost_kept_at_def] >>
      metis_tac[]) >>
  drule_all word_neg_run_nonfresh >> strip_tac >>
  `?u. run_inst_seq (emitted_insts s1 sb) t = Abort Revert_abort u` by metis_tac[] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by simp[] >>
  drule_all word_neg_abort_origin >>
  disch_then (qspecl_then [`explicit`, `PG`, `G1`] strip_assume_tac) >>
  irule gas_outcome_full_exit >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`, `mid`,
    `Abort Revert_abort (u with vs_inst_idx := SUC t.vs_inst_idx)`,
    `INR (Error (RuntimeError m))`, `tn'`] >>
  simp[exprSimUnopComposePropsTheory.unop_result_gas_obs,
       fragExecTheory.exit_result_def, exprSimDefsTheory.expr_exit_def]
QED

Theorem word_neg_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
       (~is_word_type (expr_type e) ==>
        !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) =
                SOME tvt ==> type_memory_size tvt = 0) /\
       expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx ty e es /\
       (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
       (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
       expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx ty e es) /\
    bt = Neg /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `MAP expr_type args = [a] /\ is_numeric_type a /\ ~is_uint_type a /\
   well_formed_type env.type_defs a` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
        Excl "is_numeric_type_def"] >>
  Cases_on `args` >> gvs[Excl "is_numeric_type_def"] >>
  rename1 `expr_body_pre _ _ _ (Builtin _ Neg [e]) _` >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> conj_tac
     >- gvs[expr_body_pre_def] >>
     qexistsl [`expr_type e`, `[e]`, `Neg`, `es`] >> simp[]) >>
  `0 < type_bits (expr_type e) /\ type_bits (expr_type e) <= 256 /\
   is_word_type (expr_type e)` by
    (Cases_on `expr_type e` >>
     gvs[is_numeric_type_def, is_int_type_def, is_uint_type_def] >>
     rename1 `BaseT b` >> Cases_on `b` >>
     gvs[is_numeric_type_def, is_int_type_def, is_uint_type_def, type_bits_def,
         is_word_type_def, well_formed_type_def, evaluate_type_def,
         expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def]) >>
  (`expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin (expr_type e) Neg [e]) es` suffices_by
    (strip_tac >> gvs[] >> first_x_assum irule >>
     simp[vyperASTTheory.expr_type_def, compile_neg_stack] >>
     metis_tac[eval_expr_builtin_value]) >>
  `expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es` by
    (gvs[builtin_args_length_ok_def, body_exprs_full_ok_def,
         body_expr_full_ok_def] >> metis_tac[]) >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule lower_value_neg >> strip_tac >>
  rename1 `compile_neg x (expr_type e) s1 = (op,sb)` >>
  Cases_on `lower_value compile_expr cenv (expr_type e)
              (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value _ _ _ _ shadow_sa = (shadow_x,shadow_s1)` >>
  `shadow_x = x /\ gas_shadow_state s1 shadow_s1` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e`, `e` |-> `e`]
      gas_shadow_stmt_lower_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >> metis_tac[pairTheory.FST, pairTheory.SND]) >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `compile_neg _ _ _ = _`
       (mp_then Any mp_tac straight_fresh_cs_extends) >>
     simp[CONV_RULE (DEPTH_CONV ETA_CONV) straight_fresh_neg]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code shadow_sa shadow_s1 shadow_func` by
    (qpat_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ Neg _)) _ = _`
       (mp_tac o SIMP_RULE (srw_ss()) [gasShadowTheory.gas_shadow_expr_def,
          gasShadowTheory.gas_shadow_builtin_def]) >>
     disch_then (mp_then Any mp_tac lower_value_neg) >> strip_tac >>
     gvs[] >>
     qpat_assum `compile_neg _ _ _ = (_,shadow_sb)`
       (mp_then Any mp_tac straight_fresh_cs_extends) >>
     simp[CONV_RULE (DEPTH_CONV ETA_CONV) straight_fresh_neg] >>
     strip_tac >>
     qpat_assum `lower_value _ _ _ _ shadow_sa = _`
       (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >>
     qexistsl [`expr_type e`, `Neg`] >>
     simp[builtin_args_length_ok_def, vyperInterpreterTheory.precompile_builtin_def]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `shadow_s1`,
                           `x`, `s0`, `G0`, `tn0`] mp_tac) >>
  simp[] >> disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ NegChildPost _` >>
  simp[eval_expr_unop_action] >>
  irule gas_outcome_full_bind_all >>
  conj_tac
  >- (gen_tac >> simp[vyperStorageTraceTheory.storage_trace_frame_def,
                     unop_result_def]) >>
  conj_tac
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
      simp[]) >>
  conj_tac
  >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G tn t. NegChildPost H res ee G tn t /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (qpat_assum `gas_outcome_full _ _ _ _ _ _ NegChildPost _`
        (mp_then Any mp_tac gas_outcome_full_post_source) >>
      disch_then irule >> simp[] >> rpt gen_tac >>
      Cases_on `res` >> simp[]) >>
  rpt gen_tac >> strip_tac >> disj1_tac >> BETA_TAC >>
  irule word_neg_continuation_full >>
  simp[Abbr `NegChildPost`, NoAsms] >>
  asm_rewrite_tac[] >>
  rpt conj_tac
  >- (qexists_tac `marks` >> asm_rewrite_tac[])
  >- gvs[]
  >- (qexistsl_tac [`s1`, `x`] >> simp[] >> metis_tac[]) >>
  qexists_tac `env` >> asm_rewrite_tac[])
QED
