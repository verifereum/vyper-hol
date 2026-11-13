(* Joint finite-horizon simulation of Abs. *)
Theory bodyFullBuiltinWordAbs
Ancestors
  bodyFullPreds bodySimFull bodyFullGhostFrame gasOutcomeFullCompose
  exprSimWordBuiltins exprSimUnopProps fragGasSeqPtr builtinProps
  fragExecMem instMemFrontier memSafeRun
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
  `!D. ptr_inst_ok D lo 0 ctx func G tn1 i1 s1` by
    (gen_tac >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, Abbr `i1`,
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
  FAIL_TAC "abs abort five scalar steps"
QED
