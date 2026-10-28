(* LOG operand preparation and opcode execution.
   TOP-LEVEL: log_operand_plan_sim.
   Compiler-checked assembly supplies topic and PUSH bounds. *)
Theory logPlanSim
Ancestors
  logEmitSim operandPreparationSim blockSimHelpers spillWordBounds spillPlanSim allocMono
  stackPlanGen stackPlanOps stackPlanTypes stackModel codegenRel asmSem planExec
  stackOpSim dfgDefs venomInst venomState venomExecSemantics
  contextCodegenRel list rich_list arithmetic finite_map ASCIInumbers

Theorem execute_log_operand_plan:
  !initial_fmp input_ops reorder_ops (tc:bytes32).
    execute_plan initial_fmp
      (input_ops ++ reorder_ops ++ [SOEmit ("LOG" ++ num_to_dec_string (w2n tc))]) =
    execute_plan initial_fmp (input_ops ++ reorder_ops) ++
      [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))]
Proof
  simp[execute_plan_append, execute_plan_def, exec_stack_op_def]
QED

Theorem log_operands_bound:
  !(tc:bytes32) (off_op:operand) sz_op topic_ops prog pc.
    w2n tc = LENGTH topic_ops /\
    (!name. MEM (AsmOp name) prog ==> IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog pc [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))] ==>
    LENGTH (REVERSE (off_op::sz_op::topic_ops)) <= 16
Proof
  rpt gen_tac >> strip_tac >>
  `IS_SOME (evm_opcode_byte ("LOG" ++ num_to_dec_string (w2n tc)))` by
    (first_x_assum irule >> irule asm_block_at_member >>
     qexistsl_tac [`[AsmOp ("LOG" ++ num_to_dec_string (w2n tc))]`,`pc`] >>
     asm_simp_tac (srw_ss()) []) >>
  `w2n tc <= 4` by (drule encodable_log_topic_count >> simp[]) >>
  simp[] >> decide_tac
QED

Theorem log_operand_plan_sim:
  !alloc_base inst tc operands off_op sz_op topic_ops off sz topics
   nl ps input_ops mid dfg reorder_ops prepared
   initial_fmp fuel ctx lo o2pc prog vs vs' st.
    inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc::operands /\
    operands = REVERSE (off_op::sz_op::topic_ops) /\
    w2n tc = LENGTH topic_ops /\
    eval_operand off_op vs = SOME off /\ eval_operand sz_op vs = SOME sz /\
    eval_operands topic_ops vs = SOME topics /\
    (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
    (!op. MEM op operands /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!op. MEM op operands ==> op <> dead_stack_marker /\
      (!at. operand_equiv dfg op at ==> at <> dead_stack_marker)) /\
    (!op. MEM op operands ==> eval_operand op vs = operand_val vs lo op) /\
    residual_budget_wf alloc_base [] ps /\
    (!op1 at. operand_equiv dfg op1 at ==>
      operand_val vs lo op1 = operand_val vs lo at) /\
    emit_input_plan LOG operands nl ps = (input_ops,mid) /\
    reorder_plan dfg operands mid = (reorder_ops,prepared) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    (!name. MEM (AsmOp name) prog ==> IS_SOME (evm_opcode_byte name)) /\
    venom_asm_rel lo ps vs st /\
    (!i. source_memory_read_byte inst vs i ==>
      ~(prepared.ps_alloc.sa_spill_base <= i /\ i < prepared.ps_alloc.sa_next_offset)) /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp
      (input_ops ++ reorder_ops ++ [SOEmit ("LOG" ++ num_to_dec_string (w2n tc))])) /\
    step_inst fuel ctx inst vs = OK vs' ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp
        (input_ops ++ reorder_ops ++ [SOEmit ("LOG" ++ num_to_dec_string (w2n tc))])))
        st = AsmOK st' /\
      venom_asm_rel lo
        (prepared with ps_stack := stack_pop (LENGTH topic_ops + 2) prepared.ps_stack)
        vs' st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp
        (input_ops ++ reorder_ops ++ [SOEmit ("LOG" ++ num_to_dec_string (w2n tc))]))
Proof
  rpt gen_tac >> strip_tac >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp (input_ops ++ reorder_ops)) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops)))
     [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))]` by
    (qpat_assum `asm_block_at prog st.as_pc _` mp_tac >>
     pure_rewrite_tac [execute_log_operand_plan, asm_block_at_append] >>
     simp_tac bool_ss []) >>
  `LENGTH operands <= 16` by
    (mp_tac (Q.SPECL [`tc`,`off_op`,`sz_op`,`topic_ops`,`prog`,
       `st.as_pc + LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops))`]
       log_operands_bound) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  `EVERY (\op. op <> dead_stack_marker) operands` by
    (qpat_assum `!op. MEM op operands ==> _ /\ _`
       (qspec_then `dead_stack_marker` assume_tac) >> fs[EVERY_MEM]) >>
  `LOG <> INVOKE` by simp[] >>
  mp_tac (Q.SPECL [`alloc_base`,`LOG`,`operands`,`nl`,`ps`,`input_ops`,`mid`,
    `dfg`,`reorder_ops`,`prepared`,`initial_fmp`,`lo`,`o2pc`,`prog`,`vs`,`st`]
    prepare_operands_correct) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `st1` strip_assume_tac) >>
  `asm_block_at prog st1.as_pc [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))]` by
    (qpat_assum `st1.as_pc = _` (fn pc => rewrite_tac [pc]) >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`inst`,`tc`,`operands`,`off_op`,`sz_op`,`topic_ops`,`off`,
    `sz`,`topics`,`fuel`,`ctx`,`lo`,`o2pc`,`prog`,`prepared`,`vs`,`vs'`,`st1`]
    log_instruction_prepared_sim) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `st2` strip_assume_tac) >>
  qpat_x_assum `prepared.ps_stack = _` kall_tac >>
  qpat_assum `asm_steps lo o2pc prog
      (LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops))) st = AsmOK st1`
    (fn prefix_th => qpat_assum `asm_steps lo o2pc prog 1 st1 = AsmOK st2`
      (fn log_th => assume_tac (MATCH_MP (GEN_ALL asm_steps_compose_ok)
        (CONJ prefix_th log_th)))) >>
  qexists_tac `st2` >>
  asm_simp_tac std_ss [execute_log_operand_plan, LENGTH_APPEND, LENGTH] >> decide_tac
QED

Theorem log_regular_plan_sim:
  !alloc_base liveness dfg cfg func inst nl is_halting next_is_term bb ps ops post
   tc operands off_op sz_op topic_ops off sz topics initial_fmp fuel ctx lo o2pc
   prog vs vs' st.
    inst.inst_opcode = LOG /\ inst.inst_outputs = [] /\
    inst.inst_operands = Lit tc::operands /\
    operands = REVERSE (off_op::sz_op::topic_ops) /\
    w2n tc = LENGTH topic_ops /\
    eval_operand off_op vs = SOME off /\ eval_operand sz_op vs = SOME sz /\
    eval_operands topic_ops vs = SOME topics /\
    (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
    (!op. MEM op operands /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!op. MEM op operands ==> op <> dead_stack_marker /\
      (!at. operand_equiv dfg op at ==> at <> dead_stack_marker)) /\
    (!op. MEM op operands ==> eval_operand op vs = operand_val vs lo op) /\
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
  Cases_on `emit_input_plan LOG operands nl ps` >>
  rename1 `emit_input_plan _ _ _ _ = (input_ops,mid)` >>
  Cases_on `reorder_plan dfg operands mid` >>
  rename1 `reorder_plan _ _ _ = (reorder_ops,prepared)` >>
  `ops = input_ops ++ reorder_ops ++ [SOEmit ("LOG" ++ num_to_dec_string (w2n tc))] /\
   post = release_dead_spills nl
     (prepared with ps_stack := stack_pop (LENGTH operands) prepared.ps_stack)` by
    (qpat_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`
       (fn actual_th =>
         mp_tac (Q.SPECL [`liveness`,`dfg`,`cfg`,`func`,`inst`,`nl`,
           `is_halting`,`next_is_term`,`bb`,`ps`,`tc`,`operands`,`input_ops`,
           `mid`,`reorder_ops`,`prepared`] log_plan_decompose) >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then (mp_tac o TRANS (SYM actual_th))) >> simp[]) >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  qpat_x_assum `post = _` SUBST_ALL_TAC >>
  `!i. source_memory_read_byte inst vs i ==>
    ~(prepared.ps_alloc.sa_spill_base <= i /\ i < prepared.ps_alloc.sa_next_offset)` by
    (qpat_assum `!i. source_memory_read_byte inst vs i ==> _`
       (mp_tac o SIMP_RULE (srw_ss())
         [release_dead_spills_spill_base, release_dead_spills_next_offset]) >>
     simp_tac bool_ss []) >>
  `LENGTH operands = LENGTH topic_ops + 2` by
    (qpat_assum `operands = _` (fn shape => rewrite_tac [shape]) >>
     simp[] >> decide_tac) >>
  mp_tac (Q.SPECL [`alloc_base`,`inst`,`tc`,`operands`,`off_op`,`sz_op`,
    `topic_ops`,`off`,`sz`,`topics`,`nl`,`ps`,`input_ops`,`mid`,`dfg`,
    `reorder_ops`,`prepared`,`initial_fmp`,`fuel`,`ctx`,`lo`,`o2pc`,`prog`,
    `vs`,`vs'`,`st`] log_operand_plan_sim) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `st'` strip_assume_tac) >>
  qexists_tac `st'` >> asm_rewrite_tac [] >>
  irule venom_asm_rel_release_dead_spills >> asm_rewrite_tac []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed LOG operand-plan proof: " ^ name)
  end) (DB.thms "logPlanSim")
