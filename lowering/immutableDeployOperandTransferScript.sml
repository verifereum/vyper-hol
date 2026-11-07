(* Immutable stores whose input operands are syntactically old.
   Generated temporaries may already be populated in the initial state. *)
Theory immutableDeployOperandTransfer
Ancestors
  immutableDeployAssignExecution immutableDeployAssignTransfer
  immutableWordExecution immutableCopyExecution moduleLoweringProps
  exprSimWordBuiltins context compileEnv venomState venomInst
  emitHelperProps exprLoweringProps fragExec venomExecSemantics
  placeMemoryFieldsForward exprSimMapKey typedMemoryCopy ctorAbiActualObservations

Theorem immutable_store_word_old_execution:
  compile_imm_store_word (SOME region) dst value sa = ((),sb) /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  eval_operand region s = SOME 0w /\ eval_operand dst s = SOME a /\
  eval_operand value s = SOME v ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    t.vs_memory = (mstore (w2n a) v s).vs_memory /\
    t.vs_immutables = s.vs_immutables |+ (w2n a,v)
Proof
  strip_tac >>
  `eval_operand value (update_var (STRING #"%" (toString sa.cs_next_var)) a s) = SOME v` by
    (drule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
     disch_then (qspecl_then [`s`,`sa.cs_next_var`,`a`] mp_tac) >> simp[]) >>
  drule_all (SRULE [] compile_imm_store_word_execution) >> strip_tac >>
  qexists_tac `istore (w2n a) v
    (update_var (STRING #"%" (toString sa.cs_next_var)) a s)` >>
  simp[istore_def, mstore_def, update_var_def] >>
  rpt strip_tac >>
  gvs[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem immutable_byte_offset_old_execution:
  compile_lit_byte_offset op off sa = (out,sb) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME a ==>
  sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  (!x. out = Var x ==> not_fresh_at sb x) /\
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME (a + n2w off) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  Cases_on `off = 0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def, emitted_insts_def, same_blocks_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[emitted_insts_def, same_blocks_def, run_inst_seq_def, wordsTheory.WORD_ADD_0]) >>
  Cases_on `?w. op = Lit w`
  >- (strip_tac >> gvs[compile_lit_byte_offset_def, comp_return_def,
                       emitted_insts_def, same_blocks_def, eval_operand_def] >> qexists_tac `s` >>
      simp[emitted_insts_def, same_blocks_def, run_inst_seq_def, eval_operand_def]) >>
  strip_tac >>
  `compile_with_byte_offset op off sa = (out,sb)` by
    (Cases_on `op` >> gvs[compile_lit_byte_offset_def, compile_with_byte_offset_def]) >>
  drule_all compile_with_byte_offset_fresh >> strip_tac >> simp[] >>
  drule_all compile_with_byte_offset_sequence >> strip_tac >>
  simp[] >> qexists_tac `u` >> simp[]
QED

Theorem immutable_store_one_old_execution:
  immutable_store_one (SOME region) src dst off sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. region = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand region s = SOME 0w ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    t.vs_memory = (immutable_word_transfer T T a b off s).vs_memory /\
    t.vs_immutables = (immutable_word_transfer T T a b off s).vs_immutables
Proof
  simp[immutable_store_one_def, immutable_comp_bind_cases] >> strip_tac >>
  rename1 `compile_lit_byte_offset src off sa = (sp,c1)` >>
  rename1 `emit_op MLOAD [sp] c1 = (loaded,c2)` >>
  rename1 `compile_lit_byte_offset dst off c2 = (dp,c3)` >>
  qpat_assum `compile_lit_byte_offset src off sa = _`
    (mp_then Any mp_tac immutable_byte_offset_old_execution) >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  drule emit_MLOAD_frame >>
  disch_then (qspec_then `s1` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule typed_copy_emit_op_fresh >> strip_tac >>
  `!x. dst = Var x ==> not_fresh_at c2 x` by
    fs[not_fresh_at_def] >>
  `eval_operand dst s2 = SOME b /\ eval_operand region s2 = SOME 0w` by
    suspend "old_inputs" >>
  qpat_assum `compile_lit_byte_offset dst off c2 = _`
    (mp_then Any mp_tac immutable_byte_offset_old_execution) >>
  disch_then (qspec_then `s2` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `(!x. loaded = Var x ==> not_fresh_at c3 x) /\
   eval_operand loaded s3 = SOME (mload (w2n (a+n2w off)) s) /\
   eval_operand region s3 = SOME 0w` by suspend "store_inputs" >>
  drule_all immutable_store_word_old_execution >> strip_tac >>
  qexists_tac `t` >> suspend "compose"
QED

Resume immutable_store_one_old_execution[old_inputs]:
  `s1.vs_labels = s.vs_labels` by
    (qpat_x_assum `s1 with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `s2.vs_labels = s1.vs_labels` by
    (qpat_x_assum `s2 with vs_vars := _ = s1` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> lookup_var x s2 = lookup_var x s` by
    (rpt strip_tac >> `not_fresh_at c1 x` by fs[not_fresh_at_def] >> simp[]) >>
  conj_tac >> irule ctor_actual_old_operand >> qexistsl_tac [`s`,`sa`] >>
  simp[] >> metis_tac[]
QED
Resume immutable_store_one_old_execution[store_inputs]:
  `s3.vs_labels = s2.vs_labels` by
    (qpat_x_assum `s3 with vs_vars := _ = s2` mp_tac >>
     simp[venom_state_component_equality]) >>
  `s1.vs_memory = s.vs_memory` by
    (qpat_x_assum `s1 with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  conj_tac >- fs[not_fresh_at_def] >>
  conj_tac >-
    (irule ctor_actual_old_operand >> qexistsl_tac [`s2`,`c2`] >>
     fs[mload_def]) >>
  irule ctor_actual_old_operand >> qexistsl_tac [`s2`,`c2`] >>
  simp[] >> fs[not_fresh_at_def]
QED
Resume immutable_store_one_old_execution[compose]:
  drule compile_imm_store_word_result >> strip_tac >>
  `sb.cs_current_insts = c3.cs_current_insts ++ emitted_insts c3 sb` by
    (qpat_assum `sb.cs_current_insts = _` mp_tac >>
     simp_tac (srw_ss()) [emitted_insts_def, listTheory.DROP_APPEND]) >>
  `emitted_insts sa c2 = emitted_insts sa c1 ++ emitted_insts c1 c2` by
    (irule emitted_insts_append >> simp[]) >>
  `c2.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c2` by
    simp[listTheory.APPEND_ASSOC] >>
  `emitted_insts sa c3 = emitted_insts sa c2 ++ emitted_insts c2 c3` by
    (irule emitted_insts_append >> simp[]) >>
  `c3.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c3` by
    simp[listTheory.APPEND_ASSOC] >>
  `emitted_insts sa sb = emitted_insts sa c3 ++ emitted_insts c3 sb` by
    (irule emitted_insts_append >> simp[]) >>
  conj_tac >-
    (qpat_assum `run_inst_seq (emitted_insts sa c1) s = _`
       (mp_then Any assume_tac run_inst_seq_append) >>
     `run_inst_seq (emitted_insts sa c2) s = OK s2` by metis_tac[] >>
     pop_assum (mp_then Any assume_tac run_inst_seq_append) >>
     `run_inst_seq (emitted_insts sa c3) s = OK s3` by metis_tac[] >>
     pop_assum (mp_then Any assume_tac run_inst_seq_append) >> metis_tac[]) >>
  conj_tac >- decide_tac >>
  conj_tac >-
    (rpt strip_tac >>
     `not_fresh_at c1 x /\ not_fresh_at c2 x /\ not_fresh_at c3 x` by
       fs[not_fresh_at_def] >> simp[]) >>
  qpat_x_assum `s1 with vs_vars := _ = s` mp_tac >>
  qpat_x_assum `s2 with vs_vars := _ = s1` mp_tac >>
  qpat_x_assum `s3 with vs_vars := _ = s2` mp_tac >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s3` mp_tac >>
  simp[venom_state_component_equality, immutable_word_transfer_def,
       immutable_copy_read_def, istore_def, mstore_def]
QED
Finalise immutable_store_one_old_execution
