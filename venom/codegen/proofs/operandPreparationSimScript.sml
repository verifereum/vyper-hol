(* Actual input emission followed by complete operand reordering.
   TOP-LEVEL: prepare_operands_sim.
   Stack-copy and allocator premises are produced by input emission. *)
Theory operandPreparationSim
Ancestors
  inputPlanSim inputMaterialised emitOperandSim reorderCheckedSim
  reorderMaterialised reorderSim planSpillBounds
  stackPlanGen stackPlanOps stackPlanTypes stackModel planWf
  codegenRel asmSem planExec stackOpSim dfgDefs
  list rich_list arithmetic finite_map

Theorem emit_input_plan_layout_wf:
  !operands opc nl ps ops post.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    emit_input_plan opc operands nl ps = (ops,post) ==>
    spill_alloc_layout_wf post.ps_alloc post.ps_spilled
Proof
  Induct >- simp[emit_input_plan_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `emit_one_input opc (operand_vars operands ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops,mid)` >>
  Cases_on `emit_input_plan opc operands nl mid` >>
  rename1 `emit_input_plan opc operands nl mid = (rest_ops,last)` >>
  `ops = step_ops ++ rest_ops /\ post = last` by
    (qpat_x_assum `emit_input_plan opc (h::operands) nl ps = _` mp_tac >>
     simp[Once emit_input_plan_def, LET_THM]) >> gvs[] >>
  `spill_alloc_layout_wf mid.ps_alloc mid.ps_spilled` by
    (drule_all emit_one_input_layout_wf >> simp[]) >>
  first_x_assum (qspecl_then [`opc`,`nl`,`mid`,`rest_ops`,`last`] mp_tac) >>
  asm_rewrite_tac []
QED

Theorem prepare_operands_sim:
  !opc operands nl ps input_ops mid dfg reorder_ops post
   initial_fmp lo o2pc prog vs st.
    opc <> INVOKE /\ LENGTH operands <= 16 /\
    (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
    (!op. MEM op operands /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!op. MEM op operands ==> op <> dead_stack_marker /\
      (!at. operand_equiv dfg op at ==> at <> dead_stack_marker)) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!op1 at. operand_equiv dfg op1 at ==>
      operand_val vs lo op1 = operand_val vs lo at) /\
    emit_input_plan opc operands nl ps = (input_ops,mid) /\
    reorder_plan dfg operands mid = (reorder_ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc
      (execute_plan initial_fmp (input_ops ++ reorder_ops)) ==>
    ?st'. asm_steps lo o2pc prog
      (LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops))) st = AsmOK st' /\
      venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc +
        LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops)) /\
      spill_alloc_layout_wf post.ps_alloc post.ps_spilled /\
      LENGTH operands <= LENGTH post.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `!op. LIST_ELEM_COUNT op operands <= LIST_ELEM_COUNT op mid.ps_stack` by
    (drule_all emit_input_plan_materialised >> simp[]) >>
  `LENGTH operands <= LENGTH mid.ps_stack` by
    (irule materialised_operands_length >> first_assum ACCEPT_TAC) >>
  `spill_alloc_layout_wf mid.ps_alloc mid.ps_spilled` by
    (drule_all emit_input_plan_layout_wf >> simp[]) >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp input_ops) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp input_ops))
     (execute_plan initial_fmp reorder_ops)` by
    fs[execute_plan_append, asm_block_at_append] >>
  mp_tac (Q.SPECL [`operands`,`opc`,`nl`,`ps`,`input_ops`,`mid`,`initial_fmp`,
    `lo`,`o2pc`,`prog`,`vs`,`st`] emit_input_plan_sim) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `st1` strip_assume_tac) >>
  mp_tac (Q.SPECL [`dfg`,`operands`,`mid`,`reorder_ops`,`post`,`initial_fmp`,
    `lo`,`o2pc`,`prog`,`vs`,`st1`] reorder_plan_checked_sim) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      gen_tac >> strip_tac >> CCONTR_TAC >> gvs[]])) >>
  disch_then (qx_choose_then `st2` strip_assume_tac) >> qexists_tac `st2` >>
  asm_simp_tac std_ss [execute_plan_append, LENGTH_APPEND, asm_steps_add,
    ADD_ASSOC] >> asm_simp_tac (srw_ss()) [] >> decide_tac
QED

Theorem prepare_operands_resources:
  !alloc_base opc operands nl ps input_ops mid dfg reorder_ops post.
    residual_budget_wf alloc_base [] ps /\ LENGTH operands <= 16 /\
    (!op. MEM op operands /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    emit_input_plan opc operands nl ps = (input_ops,mid) /\
    reorder_plan dfg operands mid = (reorder_ops,post) ==>
    plan_state_residual_wf alloc_base operands (LENGTH operands) post /\
    post.ps_stack = stack_pop (LENGTH operands) post.ps_stack ++ operands /\
    plan_slots_bounded alloc_base
      (post with ps_stack := stack_pop (LENGTH operands) post.ps_stack) /\
    ALL_DISTINCT (stack_pop (LENGTH operands) post.ps_stack) /\
    DISJOINT (set (stack_pop (LENGTH operands) post.ps_stack)) (FDOM post.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  `!op. LIST_ELEM_COUNT op operands <= LIST_ELEM_COUNT op mid.ps_stack` by
    (drule_all emit_input_plan_materialised >> simp[]) >>
  `LENGTH operands <= LENGTH mid.ps_stack` by
    (irule materialised_operands_length >> first_assum ACCEPT_TAC) >>
  `residual_budget_wf alloc_base operands mid` by
    (mp_tac (Q.SPECL [`operands`,`[]`,`alloc_base`,`opc`,`nl`,`ps`,
       `input_ops`,`mid`] emit_input_plan_residual_budget_wf) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  mp_tac (Q.SPECL [`alloc_base`,`dfg`,`operands`,`mid`,`reorder_ops`,`post`]
    reorder_plan_materialised) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  mp_tac (Q.SPECL [`alloc_base`,`operands`,`post`] plan_state_residual_wf_pop) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem prepare_operands_correct:
  !alloc_base opc operands nl ps input_ops mid dfg reorder_ops post
   initial_fmp lo o2pc prog vs st.
    opc <> INVOKE /\ LENGTH operands <= 16 /\
    (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
    (!op. MEM op operands /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!op. MEM op operands ==> op <> dead_stack_marker /\
      (!at. operand_equiv dfg op at ==> at <> dead_stack_marker)) /\
    residual_budget_wf alloc_base [] ps /\
    (!op1 at. operand_equiv dfg op1 at ==>
      operand_val vs lo op1 = operand_val vs lo at) /\
    emit_input_plan opc operands nl ps = (input_ops,mid) /\
    reorder_plan dfg operands mid = (reorder_ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc
      (execute_plan initial_fmp (input_ops ++ reorder_ops)) ==>
    ?st'. asm_steps lo o2pc prog
      (LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops))) st = AsmOK st' /\
      venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc +
        LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops)) /\
      post.ps_stack = stack_pop (LENGTH operands) post.ps_stack ++ operands /\
      plan_slots_bounded alloc_base
        (post with ps_stack := stack_pop (LENGTH operands) post.ps_stack) /\
      spill_alloc_layout_wf post.ps_alloc post.ps_spilled /\
      ALL_DISTINCT (stack_pop (LENGTH operands) post.ps_stack) /\
      DISJOINT (set (stack_pop (LENGTH operands) post.ps_stack)) (FDOM post.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by fs[residual_budget_wf_def] >>
  mp_tac (Q.SPECL [`alloc_base`,`opc`,`operands`,`nl`,`ps`,`input_ops`,`mid`,
    `dfg`,`reorder_ops`,`post`] prepare_operands_resources) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  mp_tac (Q.SPECL [`opc`,`operands`,`nl`,`ps`,`input_ops`,`mid`,`dfg`,
    `reorder_ops`,`post`,`initial_fmp`,`lo`,`o2pc`,`prog`,`vs`,`st`]
    prepare_operands_sim) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `st'` strip_assume_tac) >>
  qexists_tac `st'` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
