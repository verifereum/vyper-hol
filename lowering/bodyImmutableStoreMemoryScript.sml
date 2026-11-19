(* Memory checks for copying one word into an immutable slot. *)
Theory bodyImmutableStoreMemory
Ancestors
  bodyImmutableCopyMemory bodyLiteralBufferMemory immutableDeployOperandTransfer
  immutableCopyExecution ctorAbiActualObservations exprSimMapKey
  instMemFrontier fragExecMem memSafeRun context compileEnv loweringStateRelDefs
  exprLoweringProps emitHelperProps emitHelper venomExecSemantics venomState
  venomInst words arithmetic list finite_map rich_list
  unitTransformDefs[qualified,ignore_grammar]
  contextCodegenRel[qualified,ignore_grammar] codegenRel[qualified,ignore_grammar]

Theorem immutable_store_word_mem_ok:
  compile_imm_store_word imm dst v sa = ((),sb) /\
  eval_operand dst s = SOME a /\ w2n a + 32 <= s.vs_alloca_next /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> namedCases_on `imm` ["", "reg"]
  >- (fs[compile_imm_store_word_def] >>
      drule emitted_insts_emit_void >> simp[] >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_ISTORE,
           inst_dload_in_section_def, mk_inst_def]) >>
  drule compile_imm_store_word_result >> strip_tac >>
  `eval_operand reg s = SOME 0w` by fs[] >>
  `emitted_insts sa sb =
     [mk_inst sa.cs_next_id ADD [reg; dst] ["%" ++ toString sa.cs_next_var];
      mk_inst (sa.cs_next_id + 1) ISTORE
        [Var ("%" ++ toString sa.cs_next_var); v] []]` by
    simp[emitted_insts_def, DROP_APPEND] >>
  conj_tac >- simp[] >>
  simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
       below_frontier_ISTORE] >>
  simp[inst_dload_in_section_def, mk_inst_def,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def] >>
  simp[step_inst_base_opcode_eqs, exec_pure2_def, wordsTheory.WORD_ADD_0,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem immutable_direct_one_mem_ok:
  immutable_store_one imm src dst off sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  w2n a + off + 32 <= s.vs_alloca_next /\
  w2n b + off + 32 <= s.vs_alloca_next /\
  w2n a + off < dimword (:256) /\ w2n b + off < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[immutable_store_one_def, immutable_comp_bind_cases] >> strip_tac >>
  rename1 `compile_lit_byte_offset src off sa = (sp,c1)` >>
  rename1 `emit_op MLOAD [sp] c1 = (loaded,c2)` >>
  rename1 `compile_lit_byte_offset dst off c2 = (dp,c3)` >>
  drule_all immutable_byte_offset_old_execution >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  drule_all emit_MLOAD_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  drule emitted_insts_emit_op >> strip_tac >>
  `s1.vs_alloca_next = s.vs_alloca_next /\ s1.vs_labels = s.vs_labels` by
    (qpat_x_assum `s1 with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `s2.vs_alloca_next = s.vs_alloca_next /\ s2.vs_labels = s.vs_labels` by
    (qpat_x_assum `s2 with vs_vars := _ = s1` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> lookup_var x s2 = lookup_var x s` by
    (rpt strip_tac >> `not_fresh_at c1 x` by fs[not_fresh_at_def] >> simp[]) >>
  `eval_operand dst s2 = SOME b` by
    (irule ctor_actual_old_operand >> qexistsl [`s`,`sa`] >> simp[]) >>
  `!x. dst = Var x ==> not_fresh_at c2 x` by fs[not_fresh_at_def] >>
  qpat_assum `compile_lit_byte_offset dst off c2 = _`
    (mp_then Any mp_tac immutable_byte_offset_old_execution) >>
  disch_then (qspec_then `s2` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `s3.vs_alloca_next = s.vs_alloca_next /\ s3.vs_labels = s.vs_labels` by
    (qpat_x_assum `s3 with vs_vars := _ = s2` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> lookup_var x s3 = lookup_var x s` by
    (rpt strip_tac >> `not_fresh_at c2 x` by fs[not_fresh_at_def] >> simp[]) >>
  `!region. imm = SOME region ==> eval_operand region s3 = SOME 0w` by
    (rpt strip_tac >> irule ctor_actual_old_operand >>
     qexistsl [`s`,`sa`] >> simp[] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts c1 c2) s1` by
    (simp[run_inst_seq_mem_ok_last, below_frontier_MLOAD] >>
     simp[inst_dload_in_section_def, mk_inst_def] >>
     irule body_immutable_copy_offset_range >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts c3 sb) s3` by
    (`w2n (b + n2w off) + 32 <= s3.vs_alloca_next` by
       (irule body_immutable_copy_offset_range >> simp[]) >>
     drule_all immutable_store_word_mem_ok >> simp[]) >>
  `sb.cs_current_insts = c3.cs_current_insts ++ emitted_insts c3 sb` by
    (Cases_on `imm`
     >- (qpat_x_assum `compile_imm_store_word NONE _ _ _ = _` mp_tac >>
         simp[NoAsms, compile_imm_store_word_def] >>
         disch_then (mp_tac o MATCH_MP emit_void_extends) >> simp[NoAsms]) >>
     drule compile_imm_store_word_result >> strip_tac >>
     qpat_assum `sb.cs_current_insts = c3.cs_current_insts ++ _` (fn th =>
       simp[NoAsms, th, emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND])) >>
  `emitted_insts sa sb = emitted_insts sa c1 ++ (emitted_insts c1 c2 ++
       (emitted_insts c2 c3 ++ emitted_insts c3 sb))` by
    (simp[NoAsms, SimpLHS, Once emitted_insts_def] >>
     qpat_assum `sb.cs_current_insts = _` SUBST1_TAC >>
     qpat_assum `c3.cs_current_insts = _` SUBST1_TAC >>
     qpat_assum `emitted_insts c1 c2 = _` SUBST1_TAC >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     REFL_TAC) >>
  pop_assum SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append_run >>
  conj_tac >- (qpat_assum `compile_lit_byte_offset src _ _ = _`
    (mp_then Any MATCH_ACCEPT_TAC body_immutable_byte_offset_mem_ok)) >>
  qexists `s1` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule run_inst_seq_mem_ok_append_run >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `s2` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule run_inst_seq_mem_ok_append_run >>
  conj_tac >- (qpat_assum `compile_lit_byte_offset dst _ _ = _`
    (mp_then Any MATCH_ACCEPT_TAC body_immutable_byte_offset_mem_ok)) >>
  qexists `s3` >> simp[]
QED
