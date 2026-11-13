(* Memory checks for the concrete constructor immutable writes. *)
Theory immutableAssignStoreMem
Ancestors
  bodyImmutableCopyMemory immutableCopyExecution immutableWordExecution
  fragGasSeqMem typedStoreEndpoint instMemFrontier memSafeRun fragExecMem
  windowSequenceMem abiEncoderWindowSequence abiEncoderSequence memContinuation
  context compileEnv emitHelper emitHelperProps loweringStateRelDefs exprLoweringProps venomExecSemantics
  venomState venomInst words arithmetic list rich_list finite_map

Theorem immutable_store_word_mem_ok:
  compile_imm_store_word (SOME region) dst value sa = ((),sb) /\
  eval_operand region s = SOME 0w /\ eval_operand dst s = SOME b /\
  w2n b + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule compile_imm_store_word_result >> strip_tac >>
  simp[emitted_insts_def, DROP_APPEND, run_inst_seq_mem_ok_cons] >>
  conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[step_inst_base_opcode_eqs, exec_pure2_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_ISTORE,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       WORD_ADD_0]
QED

Theorem immutable_store_word_window:
  compile_imm_store_word (SOME region) dst value sa = ((),sb) /\
  eval_operand region s = SOME 0w /\ eval_operand dst s = SOME b /\
  eval_operand value s = SOME v /\
  (!x. value = Var x ==> not_fresh_at sa x) ==>
  window_seq sa sb s
    (istore (w2n b) v
      (update_var (STRING #"%" (toString sa.cs_next_var)) b s))
Proof
  strip_tac >> drule compile_imm_store_word_result >> strip_tac >>
  `eval_operand value
     (update_var (STRING #"%" (toString sa.cs_next_var)) b s) = SOME v` by
    (Cases_on `value` >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     IF_CASES_TAC >> gvs[not_fresh_at_def]) >>
  `run_inst_seq (emitted_insts sa sb) s =
     OK (istore (w2n b) v
       (update_var (STRING #"%" (toString sa.cs_next_var)) b s))` by
    (irule (SRULE [] compile_imm_store_word_execution) >> metis_tac[]) >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
     simp[compile_imm_store_word_def, emit_op_def, emit_void_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[]) >>
  simp[window_seq_def, inst_extends_def, emitted_insts_def, DROP_APPEND,
       mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  simp[istore_def, mstore_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  IF_CASES_TAC >> gvs[not_fresh_at_def]
QED

Theorem immutable_store_word_mem_cont:
  compile_imm_store_word (SOME region) dst value sa = ((),sb) /\
  eval_operand region s = SOME 0w /\ eval_operand dst s = SOME b /\
  eval_operand value s = SOME v /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  w2n b + 32 <= s.vs_alloca_next /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  mem_cont_sim ctx func s
    ((istore (w2n b) v
      (update_var (STRING #"%" (toString sa.cs_next_var)) b s))
      with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> irule window_seq_mem_cont >> simp[] >>
  qexists_tac `sa` >> simp[] >>
  conj_tac >- (irule immutable_store_word_mem_ok >> metis_tac[]) >>
  irule immutable_store_word_window >> metis_tac[]
QED
