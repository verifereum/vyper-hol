(* Joint Neg simulation: its checked arithmetic suffix. *)
Theory bodyFullBuiltinWordNeg
Ancestors
  bodyFullGhostFrame bodyFullShared bodyFullPreds bodySimFull
  gasOutcomeFullCompose gasOutcomeFullStmts fragGasSeqPtr fragGasEmitCtrl
  exprSimWordBuiltins exprSimUnopProps exprSimSource
  fragExecMem unitTransformDefs memSafeRun
  ptrSafeRun ptrDiscipline exprLowering emitHelper emitHelperProps
  exprLoweringProps compileEnv venomExecSemantics venomInst venomState
  list rich_list finite_map codegenRel contextCodegenRel

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

Theorem word_neg_success_origin:
  compile_neg x ty sa = (op,sb) /\ fresh_vars_wrt sa s /\
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
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),
       G',tn')
Proof
  strip_tac >> drule_all compile_neg_run >> simp[] >> strip_tac >>
  drule_all word_neg_inst_seq_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `G`] strip_assume_tac) >>
  qexistsl [`ss'`, `G'`, `tn'`] >> simp[] >> gen_tac >>
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
