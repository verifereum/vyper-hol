(* Complete source-instruction interface to the actual regular LOG planner.
   TOP-LEVEL: log_instruction_sim, log_instruction_checked_conditions.
   Helper: log_regular_instruction_sim.
   Input shape comes from inst_wf and successful execution; assembly and
   memory premises come from existing compiler/context checks. *)
Theory logInstructionSim
Ancestors
  logInputs logPlanSim logEmitSim spillWordBounds contextCodegenRelProps
  contextCodegenRel codegenRel stackPlanGen stackPlanTypes stackModel
  venomWf venomInst venomState venomExecSemantics dfgDefs
  asmSem planExec list rich_list arithmetic finite_map

Theorem log_regular_instruction_sim:
  !alloc_base liveness dfg cfg func inst nl is_halting next_is_term bb ps ops post
   initial_fmp fuel ctx lo o2pc prog vs vs' st.
    inst.inst_opcode = LOG /\ inst_wf inst /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!op. MEM op (compute_operands inst) ==> op <> dead_stack_marker /\
      (!at. operand_equiv dfg op at ==> at <> dead_stack_marker)) /\
    (!op. MEM op (compute_operands inst) ==>
      eval_operand op vs = operand_val vs lo op) /\
    residual_budget_wf alloc_base [] ps /\
    (!op1 at. operand_equiv dfg op1 at ==>
      operand_val vs lo op1 = operand_val vs lo at) /\
    generate_regular_inst_plan liveness dfg cfg func inst nl
      is_halting next_is_term bb ps = (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    (!name. MEM (AsmOp name) prog ==> IS_SOME (evm_opcode_byte name)) /\
    venom_asm_rel lo ps vs st /\
    (!i. source_memory_read_byte inst vs i ==>
      ~(post.ps_alloc.sa_spill_base <= i /\ i < post.ps_alloc.sa_next_offset)) /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
    step_inst fuel ctx inst vs = OK vs' ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo post vs' st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`inst`,`fuel`,`ctx`,`vs`,`vs'`] log_instruction_inputs) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `tc` (qx_choose_then `off_op`
    (qx_choose_then `sz_op` (qx_choose_then `topic_ops`
    (qx_choose_then `off` (qx_choose_then `sz`
    (qx_choose_then `topics` strip_assume_tac))))))) >>
  `compute_operands inst = REVERSE (off_op::sz_op::topic_ops)` by
    asm_simp_tac (srw_ss()) [compute_operands_def, LET_THM] >>
  `inst.inst_operands = Lit tc::compute_operands inst` by
    (qpat_assum `inst.inst_operands = _` (fn fields =>
       qpat_assum `compute_operands inst = _` (fn operands =>
         ACCEPT_TAC (REWRITE_RULE [GSYM operands] fields)))) >>
  mp_tac (Q.SPECL [`alloc_base`,`liveness`,`dfg`,`cfg`,`func`,`inst`,`nl`,
    `is_halting`,`next_is_term`,`bb`,`ps`,`ops`,`post`,`tc`,`compute_operands inst`,
    `off_op`,`sz_op`,`topic_ops`,`off`,`sz`,`topics`,`initial_fmp`,`fuel`,`ctx`,
    `lo`,`o2pc`,`prog`,`vs`,`vs'`,`st`] log_regular_plan_sim) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []
QED

Theorem log_instruction_sim:
  !alloc_base liveness dfg cfg func inst nl is_halting next_is_term bb ps ops post
   initial_fmp fuel ctx lo o2pc prog vs vs' st.
    inst.inst_opcode = LOG /\ inst_wf inst /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!op. MEM op (compute_operands inst) ==> op <> dead_stack_marker /\
      (!at. operand_equiv dfg op at ==> at <> dead_stack_marker)) /\
    (!op. MEM op (compute_operands inst) ==>
      eval_operand op vs = operand_val vs lo op) /\
    residual_budget_wf alloc_base [] ps /\
    (!op1 at. operand_equiv dfg op1 at ==>
      operand_val vs lo op1 = operand_val vs lo at) /\
    generate_inst_plan liveness dfg cfg func inst nl
      is_halting next_is_term bb ps = SOME (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    (!name. MEM (AsmOp name) prog ==> IS_SOME (evm_opcode_byte name)) /\
    venom_asm_rel lo ps vs st /\
    (!i. source_memory_read_byte inst vs i ==>
      ~(post.ps_alloc.sa_spill_base <= i /\ i < post.ps_alloc.sa_next_offset)) /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
    step_inst fuel ctx inst vs = OK vs' ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo post vs' st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  `generate_regular_inst_plan liveness dfg cfg func inst nl
    is_halting next_is_term bb ps = (ops,post)` by
    (qpat_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = SOME _`
       (mp_tac o REWRITE_RULE [generate_inst_plan_def]) >>
     asm_simp_tac (srw_ss()) [is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       is_raw_fmp_opcode_def, is_fmp_param_opcode_def, is_param_opcode_def, LET_THM]) >>
  mp_tac (Q.SPECL [`alloc_base`,`liveness`,`dfg`,`cfg`,`func`,`inst`,`nl`,
    `is_halting`,`next_is_term`,`bb`,`ps`,`ops`,`post`,`initial_fmp`,`fuel`,
    `ctx`,`lo`,`o2pc`,`prog`,`vs`,`vs'`,`st`]
    log_regular_instruction_sim) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []
QED

Theorem log_instruction_checked_conditions:
  !rpolicy unit prog Inv ctx cp func inst vs r (post:plan_state).
    codegen_assembly rpolicy unit = SOME prog /\
    codegen_memory_obligations Inv ctx cp /\ Inv ctx func inst vs /\
    MEM func ctx.ctx_functions /\ MEM inst (fn_insts func) /\
    ~in_revert_forward func vs /\ MEM r cp.cp_regions /\
    r.sr_spill_base <= post.ps_alloc.sa_spill_base /\
    post.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    (!name. MEM (AsmOp name) prog ==> IS_SOME (evm_opcode_byte name)) /\
    (!i. source_memory_read_byte inst vs i ==>
      ~(post.ps_alloc.sa_spill_base <= i /\ i < post.ps_alloc.sa_next_offset))
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (drule codegen_assembly_push_sizes >> simp_tac bool_ss [])
  >- (drule codegen_assembly_opcodes >> simp_tac bool_ss []) >>
  rename1 `codegen_memory_obligations Inv ctx memory_plan` >>
  qsuff_tac `codegen_memory_obligations Inv ctx memory_plan /\
    Inv ctx func inst vs /\ MEM func ctx.ctx_functions /\
    MEM inst (fn_insts func) /\ ~in_revert_forward func vs /\
    MEM r memory_plan.cp_regions /\
    r.sr_spill_base <= post.ps_alloc.sa_spill_base /\
    post.ps_alloc.sa_next_offset <= r.sr_spill_end`
  >- (disch_then (mp_tac o MATCH_MP (GEN_ALL codegen_memory_obligations_local_reads)) >>
      simp_tac bool_ss []) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
