(* Memory-safe immutable word stores with either constructor base form. *)
Theory immutableWordPathMem
Ancestors
  immutableAssignStoreMem abiEncoderWindowSequence windowSequenceMem
  context compileEnv emitHelper emitHelperProps exprLoweringProps fragExecMem
  instMemFrontier memSafeRun loweringStateRelDefs
  venomExecSemantics venomState venomInst valueEncodingProps
  words arithmetic list rich_list finite_map

Theorem immutable_word_store_window:
  compile_imm_store_word ce.ce_imm_alloca (Lit (n2w off)) value sa = ((),sb) /\
  immutable_base_zero ce s /\ eval_operand value s = SOME v /\
  (!x. value = Var x ==> not_fresh_at sa x) /\ off < dimword (:256) /\
  off + 32 <= s.vs_alloca_next ==>
  ?u. window_seq sa sb s u /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb) /\
    ~block_is_terminated sb /\
    u.vs_memory = (mstore off v s).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_immutables := s.vs_immutables|>) = s
Proof
  strip_tac >> Cases_on `ce.ce_imm_alloca`
  >- (gvs[compile_imm_store_word_def, emit_void_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      qexists_tac `istore off v s` >>
      simp[window_seq_def, inst_extends_def, emitted_insts_def, DROP_APPEND,
           run_inst_seq_def, step_inst_base_opcode_eqs, eval_operand_def,
           run_inst_seq_mem_ok_last, SRULE [mk_inst_def] below_frontier_ISTORE,
           mk_inst_def, is_terminator_def, block_is_terminated_def, LAST_APPEND,
           istore_def, mstore_def, lookup_var_def, venom_state_component_equality] >>
      Cases_on `sa.cs_current_insts` >> simp[is_terminator_def,LAST_CONS_cond,LAST_APPEND]) >>
  `eval_operand x s = SOME 0w` by fs[immutable_base_zero_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all immutable_store_word_window >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (mp_tac (Q.INST [`region` |-> `x`, `dst` |-> `Lit (n2w off)`,
       `value` |-> `value`, `b` |-> `n2w off`]
       (SPEC_ALL immutable_store_word_mem_ok)) >> simp[]) >>
  qexists_tac `istore off v
    (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w off) s)` >>
  conj_tac >- gvs[] >> conj_tac >- first_assum ACCEPT_TAC >>
  drule compile_imm_store_word_result >> strip_tac >>
  simp[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def,
       block_is_terminated_def, LAST_APPEND, istore_def, mstore_def,
       update_var_def, venom_state_component_equality] >>
  Cases_on `sa.cs_current_insts` >> simp[is_terminator_def,LAST_CONS_cond,LAST_APPEND]
QED

