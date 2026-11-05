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
  stackPlanGen stackPlanOps stackPlanTypes stackModel blockSimHelpers planSpillBounds
  stackOpSim sorting list rich_list arithmetic

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
  strip_tac >>
  conj_tac >- metis_tac[emit_input_plan_layout_wf] >>
  conj_tac >- metis_tac[emit_input_plan_slots_bounded] >>
  conj_tac
  >- (drule_all emit_input_plan_residual_budget_wf_marked >> simp[]) >>
  conj_tac >- metis_tac[emit_input_plan_pending_inventory] >>
  irule emit_input_plan_venom_asm_rel_numeric >> simp[] >>
  metis_tac[]
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
  rpt gen_tac >> strip_tac >>
  `EVERY (\(idx,op). idx < LENGTH target_ops /\ MEM op target_ops)
     (MAPi (\i op. (i,op)) target_ops)` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[] >> simp[MEM_EL] >> qexists_tac `p_1` >> simp[]) >>
  `plan_steps (\(idx,op) ps. reorder_one dfg target_ops idx op ps)
     (MAPi (\i op. (i,op)) target_ops) ps = (ops,ps')` by
    (qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
     simp[reorder_plan_eq_plan_steps]) >>
  drule_all plan_steps_reorder_venom_asm_rel_numeric_marked >> simp[]
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
  strip_tac >>
  drule_all emit_input_plan_materialised >> strip_tac >>
  `residual_budget_wf_marked spillbase operands prepared` by
    (drule_all emit_input_plan_residual_budget_wf_marked >> simp[]) >>
  drule perm_operand_counts >> strip_tac >>
  `residual_budget_wf_marked spillbase selected prepared` by
    metis_tac[residual_budget_wf_marked_perm] >>
  `LENGTH selected = LENGTH operands` by metis_tac[PERM_LENGTH] >>
  `!x. LIST_ELEM_COUNT x selected <= LIST_ELEM_COUNT x prepared.ps_stack` by
    metis_tac[] >>
  qspecl_then [`spillbase`, `selected`, `dfg`, `prepared`, `rops`, `arranged`]
    mp_tac reorder_plan_materialised_arranged_marked >>
  impl_tac >- fs[] >> simp[]
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
  strip_tac >>
  `plan_state_residual_wf_marked spillbase selected (LENGTH selected) arranged /\
   arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected` by
    (irule selected_input_arranged_marked >> metis_tac[]) >> simp[] >>
  fs[EVERY_APPEND] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[execute_plan_append, asm_block_at_append] >> strip_tac >>
  drule_all emit_input_plan_prepared_sim_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `asm_steps _ _ _ _ st = AsmOK mid` >>
  `asm_block_at prog mid.as_pc (execute_plan initial_fmp rops)` by
    metis_tac[ADD_COMM] >>
  `residual_budget_wf_marked spillbase selected prepared /\
   pending_inventory_wf selected prepared` by
    metis_tac[residual_budget_wf_marked_perm, pending_inventory_wf_perm] >>
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
  drule_all reorder_plan_venom_asm_rel_numeric_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo arranged vs endpoint` >>
  qexists `endpoint` >> simp[execute_plan_append] >>
  irule asm_steps_compose_ok >> qexists `mid` >> simp[]
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
  strip_tac >> drule plan_state_residual_wf_marked_pop >> strip_tac >>
  simp[generated_plan_state_wf_marked_def] >>
  Cases_on `outputs` >- gvs[] >>
  rename1 `LENGTH (out::rest) <= 1` >>
  `rest = []` by (Cases_on `rest` >> gvs[]) >> gvs[] >>
  `~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled` by
    (fs[EVERY_MEM] >> conj_tac
     >- (qpat_x_assum `!op. MEM op _ ==> _`
           (qspec_then `Var out` mp_tac) >> simp[] >> metis_tac[]) >>
     qpat_x_assum `!op. op IN FDOM _ ==> _`
       (qspec_then `Var out` mp_tac) >> simp[] >> metis_tac[]) >>
  `Var out <> dead_stack_marker` by simp[dead_stack_marker_def] >>
  gvs[stack_push_def, plan_slots_bounded_def, FILTER_SNOC,
      ALL_DISTINCT_SNOC, MEM_FILTER] >>
  fs[pred_setTheory.IN_DISJOINT, stack_pop_def] >>
  metis_tac[rich_listTheory.MEM_TAKE]
QED
