(*
 * The input-preparation and reorder simulation over a planner state with
 * repeated dead_stack_marker slots.
 *
 * A cleanup elision (clean_stack_plan's mark_dead_stack) leaves the marker
 * in several stack slots.  reorderSim's residual_budget_wf allows each
 * operand at most one stack copy beyond its pending ones, which repeated
 * markers break.  The _marked budgets (deepResidualBudget) exempt the
 * marker from that count, and keep it out of the spill map; the marker is
 * never an operand
 * or a reorder target, and plan_stack_rel doesn't read its slots.  The
 * lemmas are their unmarked namesakes over these budgets; the simulation
 * is the numeric one, which needs no stack depth bound.
 *
 * TOP-LEVEL:
 *   generated_plan_state_wf_marked_residual_nil
 *                                             - the block-level wf gives one
 *   emit_input_plan_prepared_sim_marked       - input emission
 *   reorder_plan_venom_asm_rel_numeric_marked - reorder
 *   selected_input_arranged_marked, selected_prefix_prepared_sim_marked
 *                                             - emission then reorder
 *   materialised_emit_resources_marked        - the state after the emit
 *)

Theory deepResidualSim
Ancestors
  deepResidualBudget fnPlanPrefix preparedPrefixSim generatedPrefixSim
  generatedReorderSim genericInputReady reorderSim doSwapSim codegenRel asmSem planExec
  stackPlanGen stackPlanOps stackPlanTypes stackModel blockSimHelpers
  list rich_list arithmetic

Theorem filter_distinct_elem_count_le_one[local]:
  !l (x : 'a) P.
    ALL_DISTINCT (FILTER P l) /\ P x ==> LIST_ELEM_COUNT x l <= 1
Proof
  Induct >> simp[LIST_ELEM_COUNT_THM] >> rpt strip_tac >>
  Cases_on `h = x`
  >- (gvs[MEM_FILTER, LIST_ELEM_COUNT_THM] >>
      `~(LIST_ELEM_COUNT h l > 0)` by metis_tac[LIST_ELEM_COUNT_MEM] >>
      decide_tac) >>
  simp[LIST_ELEM_COUNT_THM] >> first_x_assum irule >>
  qexists_tac `P` >> Cases_on `P h` >> gvs[]
QED

Theorem generated_plan_state_wf_marked_residual_nil:
  !base ps.
    generated_plan_state_wf_marked base ps ==>
    residual_budget_wf_marked base [] ps
Proof
  rw[generated_plan_state_wf_marked_def, residual_budget_wf_marked_def,
     LIST_ELEM_COUNT_THM]
  >- (irule filter_distinct_elem_count_le_one >>
      qexists_tac `\op. op <> dead_stack_marker` >> simp[]) >>
  `~MEM op ps.ps_stack` by
    (fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
     metis_tac[]) >>
  `~(LIST_ELEM_COUNT op ps.ps_stack > 0)` by
    metis_tac[LIST_ELEM_COUNT_MEM] >>
  decide_tac
QED

(* generatedPrefixSim$emit_input_plan_prepared_sim over the marker-tolerant budget. *)
Theorem emit_input_plan_prepared_sim_marked:
  opc <> INVOKE /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spill_base ps /\
  residual_budget_wf_marked spill_base [] ps /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
  plan_slots_bounded spill_base ps' /\
  residual_budget_wf_marked spill_base operands ps' /\
  pending_inventory_wf operands ps' /\
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  cheat
QED

(* generatedReorderSim$reorder_plan_venom_asm_rel_numeric over the marker-tolerant budget. *)
Theorem reorder_plan_venom_asm_rel_numeric_marked:
  !dfg target_ops ps ops ps' base lo o2pc prog vs st.
    residual_budget_wf_marked base target_ops ps /\
    pending_inventory_wf target_ops ps /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) target_ops /\
    LENGTH target_ops <= LENGTH ps.ps_stack /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    reorder_plan dfg target_ops ps = (ops,ps') /\
    (!op1 at. MEM op1 target_ops /\
              (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
              operand_equiv dfg op1 at ==>
              operand_val vs lo op1 = operand_val vs lo at) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
          venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
          residual_budget_wf_marked base target_ops ps' /\
          pending_inventory_wf target_ops ps'
Proof
  cheat
QED

(* generatedPrefixSim$selected_input_arranged over the marker-tolerant budget. *)
Theorem selected_input_arranged_marked:
  residual_budget_wf_marked spillbase [] ps /\
  (!op. MEM op operands /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  reorder_plan dfg selected prepared = (rops,arranged) ==>
  plan_state_residual_wf_marked spillbase selected (LENGTH selected) arranged /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected
Proof
  cheat
QED

(* preparedPrefixSim$selected_prefix_prepared_sim over the marker-tolerant budget. *)
Theorem selected_prefix_prepared_sim_marked:
  opc <> INVOKE /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps /\
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
  plan_state_residual_wf_marked spillbase selected (LENGTH selected) arranged /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (iops ++ rops)))
          st = AsmOK st' /\
    venom_asm_rel lo arranged vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops))
Proof
  cheat
QED

(* generatedPrefixSim$materialised_emit_resources over the marker-tolerant
   budget; the emitted state is generated_plan_state_wf_marked. *)
Theorem materialised_emit_resources_marked:
  plan_state_residual_wf_marked spillbase selected (LENGTH selected) ps /\
  LENGTH selected = n /\ LENGTH outputs <= 1 /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outputs) /\
  emitted = ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
    (stack_pop n ps.ps_stack) outputs ==>
  generated_plan_state_wf_marked spillbase emitted
Proof
  cheat
QED
