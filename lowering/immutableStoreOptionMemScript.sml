(* The constructor store primitive supports both compiler base forms. *)
Theory immutableStoreOptionMem
Ancestors
  immutableAssignStoreMem immutableCopyExecution abiDecoderBytesPrefix
  instMemFrontier memSafeRun fragExecMem context compileEnv emitHelper
  emitHelperProps exprLoweringProps loweringStateRelDefs
  venomExecSemantics venomState venomInst words arithmetic finite_map list rich_list

Theorem immutable_store_option_code:
  compile_imm_store_word imm dst value sa = ((),sb) ==>
  same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb) /\
  (!x. not_fresh_at sa x ==>
    EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts sa sb))
Proof
  Cases_on `imm` >>
  simp[compile_imm_store_word_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  `LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + 1) = 0` by
    decide_tac >>
  simp[same_blocks_def, emitted_insts_def, DROP_APPEND, mk_inst_def,
       not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]
QED

Theorem immutable_store_option_frame:
  compile_imm_store_word imm dst value sa = ((),sb) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  eval_operand dst s = SOME a /\ eval_operand value s = SOME v /\
  fresh_vars_wrt sa s /\ w2n a + 32 <= s.vs_alloca_next ==>
  ?t. immutable_execution_frame sa s sb t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = (mstore (w2n a) v s).vs_memory /\
    t.vs_immutables = s.vs_immutables |+ (w2n a,v)
Proof
  strip_tac >> Cases_on `imm`
  >- (gvs[compile_imm_store_word_def] >>
      mp_tac (Q.INST [`opc` |-> `ISTORE`, `st` |-> `sa`, `st'` |-> `sb`]
        (SPEC_ALL immutable_emit_store_frame)) >> simp[] >> strip_tac >>
      qexists_tac `istore (w2n a) v s` >>
      simp[immutable_execution_frame_def, istore_def, mstore_def] >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_ISTORE]) >>
  `eval_operand x s = SOME 0w` by metis_tac[] >>
  drule_all immutable_store_execution_frame >> strip_tac >>
  rename1 `immutable_execution_frame sa s sb t` >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule immutable_store_word_mem_ok >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (irule abi_decode_nonallocating_sequence_frame >>
     fs[immutable_execution_frame_def] >> goal_assum (drule_at Any) >>
     drule compile_imm_store_word_result >> strip_tac >>
     simp[emitted_insts_def, DROP_APPEND, mk_inst_def,
          is_terminator_def, is_alloca_op_def]) >>
  qexists_tac `t` >> simp[]
QED
