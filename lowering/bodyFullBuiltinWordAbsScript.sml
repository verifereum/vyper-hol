(* Joint finite-horizon simulation of Abs. *)
Theory bodyFullBuiltinWordAbs
Ancestors
  bodyFullPreds bodySimFull bodyFullGhostFrame gasOutcomeFullCompose
  exprSimWordBuiltins exprSimUnopProps fragGasSeqPtr builtinProps
  fragExecMem instMemFrontier memSafeRun ghostPcTransportPtr
  builtinSimple emitHelper emitHelperProps freshWrites
  exprLoweringProps exprLowering compileEnv venomInst list rich_list

val _ = Parse.hide "body";

Theorem abs_suffix_opcodes:
  !x sa op sb.
    compile_builtin_abs x sa = (op,sb) ==>
    MAP (\i. i.inst_opcode) (emitted_insts sa sb) =
      [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL; XOR]
Proof
  rpt gen_tac >>
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, mk_inst_def,
       emitted_insts_def] >>
  rpt strip_tac >> gvs[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem abs_suffix_mem_ok:
  !x sa op sb s.
    compile_builtin_abs x sa = (op,sb) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> drule abs_suffix_opcodes >> strip_tac >>
  irule run_inst_seq_mem_ok_every >>
  `EVERY (\opc. MEM opc [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL])
     (MAP (\i. i.inst_opcode) (emitted_insts sa sb))` by simp[] >>
  gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[below_frontier_no_ranges, inst_dload_in_section_other]
QED

Theorem abs_suffix_abort_full:
  compile_builtin_abs x sa = (op,sb) /\
  eval_operand x s = SOME INT_MINw /\ fresh_vars_wrt sa s /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)
  ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) []
      (Abort Revert_abort (t with vs_inst_idx := s.vs_inst_idx + 5),G',tn')
Proof
  strip_tac >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
  `?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t` by
    metis_tac[compile_builtin_abs_run] >>
  qpat_x_assum `compile_builtin_abs _ _ = _` mp_tac >>
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, mk_inst_def] >>
  strip_tac >>
  gvs[emitted_insts_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[rich_listTheory.DROP_LENGTH_APPEND] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [i0;i1;i2;i3;i4;i5;i6;i7;i8] s` >>
  `!n. sa.cs_next_var <= n ==> x <> Var (STRING #"%" (toString n))` by
    (rpt strip_tac >>
     drule fresh_vars_wrt_eval_operand >>
     disch_then (qspecl_then [`x`, `INT_MINw`, `STRING #"%" (toString n)`, `n`] mp_tac) >>
     simp[]) >>
  `step_inst_base i0 s =
     OK (update_var (STRING #"%" (toString sa.cs_next_var))
           (0w - INT_MINw) s)` by
    (simp[Abbr `i0`, GSYM mk_inst_def] >>
     irule step_SUB >> simp[eval_operand_lit]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base i0 s = OK s1` >>
  `eval_operand x s1 = SOME INT_MINw` by
    (simp[Abbr `s1`] >> irule eval_operand_update_other_local >>
     simp[] >> metis_tac[]) >>
  `step_inst_base i1 s1 =
     OK (update_var (STRING #"%" (toString (sa.cs_next_var + 1)))
           (bool_to_word (word_lt (INT_MINw:bytes32) 0w)) s1)` by
    (simp[Abbr `i1`, GSYM mk_inst_def] >>
     irule step_SLT >> simp[eval_operand_lit]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base i1 s1 = OK s2` >>
  `eval_operand x s2 = SOME INT_MINw` by
    (simp[Abbr `s2`] >> irule eval_operand_update_other_local >>
     simp[] >> metis_tac[]) >>
  `eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) s2 =
     SOME (0w - INT_MINw)` by
    (simp[Abbr `s2`, Abbr `s1`, eval_operand_update_other,
          eval_operand_update_var]) >>
  `step_inst_base i2 s2 =
     OK (update_var (STRING #"%" (toString (sa.cs_next_var + 2)))
           (bool_to_word ((INT_MINw:bytes32) = 0w - INT_MINw)) s2)` by
    (simp[Abbr `i2`, GSYM mk_inst_def] >> irule step_EQ >> simp[]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base i2 s2 = OK s3` >>
  `eval_operand (Var (STRING #"%" (toString (sa.cs_next_var + 1)))) s3 =
     SOME (bool_to_word (word_lt (INT_MINw:bytes32) 0w))` by
    simp[Abbr `s3`, Abbr `s2`, eval_operand_update_other,
         eval_operand_update_var] >>
  `eval_operand (Var (STRING #"%" (toString (sa.cs_next_var + 2)))) s3 =
     SOME (bool_to_word ((INT_MINw:bytes32) = 0w - INT_MINw))` by
    simp[Abbr `s3`, eval_operand_update_var] >>
  `step_inst_base i3 s3 =
     OK (update_var (STRING #"%" (toString (sa.cs_next_var + 3)))
           (word_and (bool_to_word (word_lt (INT_MINw:bytes32) 0w))
             (bool_to_word ((INT_MINw:bytes32) = 0w - INT_MINw))) s3)` by
    (simp_tac pure_ss [Abbr `i3`, GSYM mk_inst_def] >>
     irule step_AND >> simp[]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base i3 s3 = OK s4` >>
  `eval_operand (Var (STRING #"%" (toString (sa.cs_next_var + 3)))) s4 = SOME 1w` by
    (simp[Abbr `s4`, eval_operand_update_var,
          GSYM wordsTheory.word_msb_neg, wordsTheory.WORD_L_NEG,
          wordsTheory.WORD_SUB_LZERO, wordsTheory.WORD_NEG_L,
          venomExecSemanticsTheory.bool_to_word_def, wordsTheory.WORD_AND_IDEM]) >>
  `step_inst_base i4 s4 =
     OK (update_var (STRING #"%" (toString (sa.cs_next_var + 4))) 0w s4)` by
    (simp[Abbr `i4`, GSYM mk_inst_def] >>
     drule step_ISZERO >> simp[venomExecSemanticsTheory.bool_to_word_def]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base i4 s4 = OK s5` >>
  `step_inst_base i5 s5 =
     Abort Revert_abort (revert_state (set_returndata [] s5))` by
    (simp[Abbr `i5`, GSYM mk_inst_def] >> irule step_ASSERT_revert >>
     simp[Abbr `s5`, eval_operand_update_var]) >>
  qpat_x_assum `run_inst_seq _ s = _` mp_tac >>
  simp[run_inst_seq_def] >> strip_tac >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn i0 s` by
    (gen_tac >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, Abbr `i0`,
          ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          venomExecSemanticsTheory.step_inst_non_invoke] >>
     conj_tac >- (gen_tac >> Cases_on `op = x` >>
       simp[ptrDisciplineTheory.op_taint_def] >>
       Cases_on `op = Lit 0w` >> gvs[ptrDisciplineTheory.op_taint_def]) >>
     simp[Abbr `s1`, venomStateTheory.update_var_def]) >>
  qabbrev_tac `tn1 = step_taint i0 s s1 tn` >>
  `op_taint tn1 x = {} /\
   op_taint tn1 (Var (STRING #"%" (toString sa.cs_next_var))) = {}` by
    (simp[Abbr `tn1`, ptrDisciplineTheory.op_taint_def,
          ptrDisciplineTheory.step_taint_def,
          ptrDisciplineTheory.set_var_taint_def,
          ptrDisciplineTheory.out_taint_def, Abbr `i0`, eval_operand_lit] >>
     Cases_on `x` >>
     gvs[ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `!D G0 k. ptr_inst_ok D lo 0 ctx func G0 tn1 i1 (s1 with vs_inst_idx := k)` by
    (rpt gen_tac >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, Abbr `i1`,
          instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def, is_terminator_def,
          ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          venomExecSemanticsTheory.step_inst_non_invoke] >>
     conj_tac >- (gen_tac >> Cases_on `op = x` >>
       simp[ptrDisciplineTheory.op_taint_def] >>
       Cases_on `op = Lit 0w` >> gvs[ptrDisciplineTheory.op_taint_def]) >>
     simp[Abbr `s2`, Abbr `s1`, venomStateTheory.update_var_def,
          ptrDisciplineTheory.allocas_from_def,
          ptrDisciplineTheory.allocas_below_fmp_def] >>
     gvs[ptrDisciplineTheory.allocas_from_def,
         ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
  qabbrev_tac `tn2 = step_taint i1 s1 s2 tn1` >>
  `op_taint tn2 x = {} /\
   op_taint tn2 (Var (STRING #"%" (toString sa.cs_next_var))) = {} /\
   op_taint tn2 (Var (STRING #"%" (toString (sa.cs_next_var + 1)))) = {}` by
    (simp[Abbr `tn2`, ptrDisciplineTheory.op_taint_def,
          ptrDisciplineTheory.step_taint_def,
          ptrDisciplineTheory.set_var_taint_def,
          ptrDisciplineTheory.out_taint_def, Abbr `i1`, eval_operand_lit,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `x` >>
     gvs[ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  qabbrev_tac `G1 = step_prov PG G i0 s1` >>
  qabbrev_tac `G2 = step_prov PG G1 i1 s2` >>
  `op_prov G1 x = NONE /\
   op_prov G1 (Var (STRING #"%" (toString sa.cs_next_var))) = NONE` by
    (simp[Abbr `G1`, ptrDisciplineTheory.step_prov_def,
          ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.first_prov_def,
          ptrDisciplineTheory.set_prov_def, Abbr `i0`,
          ptrDisciplineTheory.op_prov_def, finite_mapTheory.FLOOKUP_DRESTRICT] >>
     Cases_on `x` >> gvs[ptrDisciplineTheory.op_prov_def]) >>
  `op_prov G2 x = NONE /\
   op_prov G2 (Var (STRING #"%" (toString sa.cs_next_var))) = NONE` by
    (simp[Abbr `G2`, ptrDisciplineTheory.step_prov_def,
          ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.set_prov_def,
          Abbr `i1`, ptrDisciplineTheory.op_prov_def,
          finite_mapTheory.FLOOKUP_DRESTRICT] >>
     Cases_on `x` >> gvs[ptrDisciplineTheory.op_prov_def]) >>
  `(!v. x = Var v ==> v NOTIN FDOM G2) /\
   STRING #"%" (toString sa.cs_next_var) NOTIN FDOM G2` by
    (Cases_on `x` >> gvs[ptrDisciplineTheory.op_prov_def,
         finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]) >>
  `!D k. ptr_inst_ok D lo 0 ctx func G2 tn2 i2 (s2 with vs_inst_idx := k)` by
    (rpt gen_tac >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, Abbr `i2`,
          instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def, is_terminator_def,
          ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          venomExecSemanticsTheory.step_inst_non_invoke] >>
     conj_tac >- (rpt strip_tac >> metis_tac[]) >>
     conj_tac >- (gen_tac >> Cases_on `op = x` >> simp[] >>
       Cases_on `op = Var (STRING #"%" (toString sa.cs_next_var))` >> gvs[]) >>
     simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, venomStateTheory.update_var_def,
          ptrDisciplineTheory.allocas_from_def,
          ptrDisciplineTheory.allocas_below_fmp_def] >>
     gvs[ptrDisciplineTheory.allocas_from_def,
         ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
  qabbrev_tac `tn3 = step_taint i2 s2 s3 tn2` >>
  `op_taint tn3 (Var (STRING #"%" (toString (sa.cs_next_var + 1)))) = {} /\
   op_taint tn3 (Var (STRING #"%" (toString (sa.cs_next_var + 2)))) = {}` by
    (gvs[ptrDisciplineTheory.op_taint_def] >>
     simp[Abbr `tn3`, ptrDisciplineTheory.op_taint_def,
         ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.set_var_taint_def,
         ptrDisciplineTheory.out_taint_def, Abbr `i2`,
         finite_mapTheory.FLOOKUP_UPDATE]) >>
  `!D G0 k. ptr_inst_ok D lo 0 ctx func G0 tn3 i3 (s3 with vs_inst_idx := k)` by
    (rpt gen_tac >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, Abbr `i3`,
          instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def, is_terminator_def,
          ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          venomExecSemanticsTheory.step_inst_non_invoke] >>
     conj_tac >- (gen_tac >>
       Cases_on `op = Var (STRING #"%" (toString (sa.cs_next_var + 1)))` >> simp[] >>
       Cases_on `op = Var (STRING #"%" (toString (sa.cs_next_var + 2)))` >> gvs[]) >>
     simp[Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`, venomStateTheory.update_var_def,
          ptrDisciplineTheory.allocas_from_def, ptrDisciplineTheory.allocas_below_fmp_def] >>
     gvs[ptrDisciplineTheory.allocas_from_def,
         ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
  qabbrev_tac `tn4 = step_taint i3 s3 s4 tn3` >>
  `op_taint tn4 (Var (STRING #"%" (toString (sa.cs_next_var + 3)))) = {}` by
    simp[Abbr `tn4`, ptrDisciplineTheory.op_taint_def,
         ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.set_var_taint_def,
         ptrDisciplineTheory.out_taint_def, Abbr `i3`,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `!D G0 k. ptr_inst_ok D lo 0 ctx func G0 tn4 i4 (s4 with vs_inst_idx := k)` by
    (rpt gen_tac >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, Abbr `i4`,
          instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def, is_terminator_def,
          ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          venomExecSemanticsTheory.step_inst_non_invoke] >>
     simp[Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`, venomStateTheory.update_var_def,
          ptrDisciplineTheory.allocas_from_def, ptrDisciplineTheory.allocas_below_fmp_def] >>
     gvs[ptrDisciplineTheory.allocas_from_def,
         ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
  qabbrev_tac `tn5 = step_taint i4 s4 s5 tn4` >>
  `op_taint tn5 (Var (STRING #"%" (toString (sa.cs_next_var + 4)))) = {}` by
    simp[Abbr `tn5`, ptrDisciplineTheory.op_taint_def,
         ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.set_var_taint_def,
         ptrDisciplineTheory.out_taint_def, Abbr `i4`,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `!D G0 k. ptr_inst_ok D lo 0 ctx func G0 tn5 i5 (s5 with vs_inst_idx := k)` by
    (rpt gen_tac >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, Abbr `i5`,
          instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def, is_terminator_def,
          ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          venomExecSemanticsTheory.step_inst_non_invoke] >>
     simp[Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
          venomStateTheory.update_var_def, venomStateTheory.revert_state_def,
          venomStateTheory.set_returndata_def,
          ptrDisciplineTheory.allocas_from_def, ptrDisciplineTheory.allocas_below_fmp_def] >>
     gvs[ptrDisciplineTheory.allocas_from_def,
         ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
  qabbrev_tac `G3 = step_prov PG G2 i2 s3` >>
  qabbrev_tac `G4 = step_prov PG G3 i3 s4` >>
  qabbrev_tac `G5 = step_prov PG G4 i4 s5` >>
  `i0.inst_opcode = SUB /\ i1.inst_opcode = SLT /\
   i2.inst_opcode = EQ /\ i3.inst_opcode = AND /\ i4.inst_opcode = ISZERO` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, Abbr `i4`] >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [i0;i1;i2;i3;i4] s G5 tn5` by
    (gen_tac >> gvs[Abbr `G1`, Abbr `G2`, Abbr `G3`,
        Abbr `G4`, Abbr `G5`, Abbr `tn1`, Abbr `tn2`, Abbr `tn3`,
        Abbr `tn4`, Abbr `tn5`] >>
     simp[inst_seq_ptr_def, instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def, is_terminator_def]) >>
  `run_inst_seq [i0;i1;i2;i3;i4] s = OK s5` by simp[run_inst_seq_def] >>
  `isPREFIX [i0;i1;i2;i3;i4] (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `run_inst_seq_mem_ok [i0;i1;i2;i3;i4] s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, Abbr `i4`,
          below_frontier_no_ranges, inst_dload_in_section_other]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (s5 with vs_inst_idx := s.vs_inst_idx + 5),G5,tn5)` by
    (gen_tac >>
     drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[is_terminator_def] >>
     disch_then irule >> simp[]) >>
  `get_instruction bb (s.vs_inst_idx + 5) = SOME i5` by
    (`LENGTH (DROP s.vs_inst_idx bb.bb_instructions) =
        LENGTH (i0::i1::i2::i3::i4::i5::i6::i7::i8::l)` by asm_rewrite_tac[] >>
     `EL 5 (DROP s.vs_inst_idx bb.bb_instructions) = i5` by (asm_rewrite_tac[] >> simp[]) >>
     gvs[LENGTH_DROP, EL_DROP, get_instruction_def, arithmeticTheory.ADD_COMM]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s5 with vs_inst_idx := s.vs_inst_idx + 5,G5,tn5) []
      (Abort Revert_abort (t with vs_inst_idx := s.vs_inst_idx + 5),G5,tn5)` by
    (gen_tac >> irule fragGasEmitCtrlTheory.exit_inst_origin_ptr >>
     conj_tac >- simp[fragExecTheory.exit_result_def] >>
     conj_tac >- simp[Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
                        venomStateTheory.update_var_def] >>
     qexistsl_tac [`bb`, `i5`] >>
     simp[Abbr `i5`, venomExecSemanticsTheory.step_inst_non_invoke,
          instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def] >>
     simp[is_terminator_def,
          instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def,
          gasEventsTheory.gas_events_step_def, gasCountTheory.gas_count_step_def,
          mem_safe_step_def] >>
     simp[Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
          venomStateTheory.update_var_def] >>
     simp[below_frontier_no_ranges]) >>
  qexistsl_tac [`G5`, `tn5`] >>
  gen_tac >>
  qpat_x_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspec_then `D` mp_tac) >>
  disch_then (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  simp[] >> metis_tac[]
QED
