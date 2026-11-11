(*
 * The planner's input preparation and reorder on the symbolic machine:
 * the symbolic twin of selected_prefix_prepared_sim_marked
 * (deepResidualSim), over a planner state with repeated dead_stack_marker
 * slots.  Kinds only: no Venom state, no concrete assembly state.
 *
 * TOP-LEVEL:
 *   sym_selected_prefix_sim_marked
 *)
Theory symPlannerSim
Ancestors
  symShuffleSim symPlannerReorder symPlannerInput codegenSymRel deepResidualSim deepResidualBudget fnPlanPrefix
  doSwapSim planSpillBounds contextCodegenRel unitShapeDefs venomWf
  stackPlanGen stackPlanOps stackPlanTypes planExec asmSymSem asmSem
  dfgDefs

(* Input emission then reorder, from planner state ps to arranged, keeps
   the kinds of the frame's values; spills and restores stay inside the
   function's spill region r, so label bytes outside it are unchanged. *)
Theorem sym_selected_prefix_sim_marked:
  opc <> INVOKE /\
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
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp (iops ++ rops))) ss =
          SymOK ss' /\
        sym_kinds_ok cplan fn ret srest arranged ss' /\
        ss'.sym_base.as_pc =
          ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)) /\
        (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
             FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  drule_all_then assume_tac allocMonoTheory.emit_input_plan_spill_base >>
  drule_all_then assume_tac allocMonoTheory.reorder_plan_next_offset >>
  `prepared.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
  `residual_budget_wf_marked spillbase operands prepared` by
    (drule_all_then mp_tac emit_input_plan_residual_budget_wf_marked >> simp[]) >>
  `residual_budget_wf_marked spillbase selected prepared` by
    metis_tac[residual_budget_wf_marked_perm] >>
  `pending_inventory_wf selected prepared` by
    (drule_all_then assume_tac reorderSimTheory.emit_input_plan_materialised >>
     fs[reorderSimTheory.pending_inventory_wf_def] >>
     metis_tac[genericInputReadyTheory.perm_operand_counts, arithmeticTheory.LESS_EQ_TRANS,
       arithmeticTheory.LESS_EQ_ADD]) >>
  `LENGTH selected <= LENGTH prepared.ps_stack` by
    metis_tac[sortingTheory.PERM_LENGTH] >>
  rule_assum_tac (PURE_REWRITE_RULE [stackOpSimTheory.execute_plan_append,
    stackOpSimTheory.asm_block_at_append, listTheory.EVERY_APPEND]) >>
  rpt (qpat_x_assum `_ /\ _` strip_assume_tac) >>
  drule_all_then (qspec_then `env` (qx_choose_then `mid` strip_assume_tac))
    sym_emit_input_plan >>
  `asm_block_at p mid.sym_base.as_pc (execute_plan initial_fmp rops)`
    by asm_rewrite_tac[] >>
  `r.sr_spill_base <= prepared.ps_alloc.sa_spill_base` by metis_tac[] >>
  drule_all_then (qspec_then `env` (qx_choose_then `last` strip_assume_tac))
    sym_reorder_plan >>
  qexists_tac `last` >>
  pure_rewrite_tac[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  ho_match_mp_tac symPlannerBaseTheory.sym_steps_frame_compose >> asm_rewrite_tac[]
QED
