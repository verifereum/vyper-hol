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
  symShuffleSim codegenSymRel deepResidualSim deepResidualBudget fnPlanPrefix
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
  cheat
QED
