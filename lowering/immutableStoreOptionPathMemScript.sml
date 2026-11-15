(* Counted memory execution for either constructor immutable base form. *)
Theory immutableStoreOptionPathMem
Ancestors
  immutableStoreOptionMem immutableDeployOperandTransfer immutableAssignStoreMem
  immutableCopyExecution bodyDeclMemoryCounted fragGasMode
  instMemFrontier memSafeRun fragExecMem emitHelperProps
  context compileEnv venomState venomInst exprLoweringProps loweringStateRelDefs

Theorem immutable_store_option_path_mem:
  compile_imm_store_word imm dst value sa = ((),sb) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  eval_operand dst s = SOME a /\ eval_operand value s = SOME v /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  w2n a + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_immutables := s.vs_immutables|>) = s /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = (mstore (w2n a) v s).vs_memory /\
    t.vs_immutables = s.vs_immutables |+ (w2n a,v) /\
    gas_marked_path T ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all immutable_store_word_old_execution >> strip_tac >>
  drule immutable_store_option_code >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (Cases_on `imm`
     >- (gvs[compile_imm_store_word_def] >>
         drule emitted_insts_emit_void >> strip_tac >>
         simp[run_inst_seq_mem_ok_last, below_frontier_ISTORE]) >>
     irule immutable_store_word_mem_ok >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _` drule >>
     strip_tac >> gvs[is_terminator_def]) >>
  `gas_marked_path T ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (mp_tac (Q.INST [`sa` |-> `sa`, `sb` |-> `sb`, `s` |-> `s`, `t` |-> `t`]
       (SPEC_ALL body_decl_zero_gas_path)) >>
     impl_tac >- simp[] >> simp[gas_marked_path_def]) >>
  qexists_tac `t` >>
  gvs[venomStateTheory.venom_state_component_equality]
QED
