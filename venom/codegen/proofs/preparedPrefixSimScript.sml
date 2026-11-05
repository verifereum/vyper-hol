Theory preparedPrefixSim
Ancestors
  generatedPrefixSim generatedReorderSim genericInputReady sorting
  asmSem planExec codegenRel stackPlanTypes stackPlanGen reorderSim
  stackOpSim blockSimHelpers
  list rich_list arithmetic

Theorem selected_prefix_prepared_sim:
  opc <> INVOKE /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf spillbase [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val vs lo op = operand_val vs lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  plan_state_residual_wf spillbase selected (LENGTH selected) arranged /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (iops ++ rops)))
          st = AsmOK st' /\
    venom_asm_rel lo arranged vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops))
Proof
  strip_tac >>
  `plan_state_residual_wf spillbase selected (LENGTH selected) arranged /\
   arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected` by
    (irule selected_input_arranged >> metis_tac[]) >> simp[] >>
  fs[EVERY_APPEND] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[execute_plan_append, asm_block_at_append] >> strip_tac >>
  drule_all emit_input_plan_prepared_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `asm_steps _ _ _ _ st = AsmOK mid` >>
  `asm_block_at prog mid.as_pc (execute_plan initial_fmp rops)` by
    metis_tac[ADD_COMM] >>
  `residual_budget_wf spillbase selected prepared /\
   pending_inventory_wf selected prepared` by
    metis_tac[residual_budget_wf_perm, pending_inventory_wf_perm] >>
  `LENGTH selected <= 16 /\ LENGTH selected <= LENGTH prepared.ps_stack` by
    metis_tac[PERM_LENGTH] >>
  `EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) selected` by
    (drule PERM_EVERY >> disch_then (qspec_then
      `\op. op <> dead_stack_marker /\ ~operand_equiv dfg op dead_stack_marker`
      mp_tac) >> simp[]) >>
  `!op at. MEM op selected /\
    (MEM at prepared.ps_stack \/ at IN FDOM prepared.ps_spilled) /\
    operand_equiv dfg op at ==>
    operand_val vs lo op = operand_val vs lo at` by
    (drule_at (Pat `emit_input_plan _ _ _ _ = _`)
       emit_input_plan_alias_transport >>
     disch_then (qspecl_then [`selected`, `dfg`, `vs`, `lo`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  drule_all reorder_plan_venom_asm_rel_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo arranged vs endpoint` >>
  qexists `endpoint` >> simp[execute_plan_append] >>
  irule asm_steps_compose_ok >> qexists `mid` >> simp[]
QED
