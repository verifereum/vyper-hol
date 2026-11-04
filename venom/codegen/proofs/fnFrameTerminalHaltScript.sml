Theory fnFrameTerminalHalt
Ancestors
  fnFrameTerminalPrep generatedPrefixSim preparedPrefixSim emitSim
  stackPlanGen stackPlanOps allocMono

(* Empty outputs eliminate both postfix phases.  Keep the arranged planner
   as the semantic boundary, so prefix simulation needs no shadow-state
   allocation comparison. *)
Theorem output_free_regular_plan:
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_outputs = [] /\ ~is_commutative inst.inst_opcode /\
  generate_regular_inst_plan liveness dfg cfg fn inst nl halting term label ps =
    (ops, final) ==>
  ?iops prepared rops arranged.
    emit_input_plan inst.inst_opcode (compute_operands inst) nl ps =
      (iops, prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops, arranged) /\
    ops = iops ++ rops ++ [SOEmit name] /\
    final = release_dead_spills nl
      (arranged with ps_stack := stack_pop (LENGTH (compute_operands inst))
        arranged.ps_stack) /\
    arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset = final.ps_alloc.sa_next_offset
Proof
  strip_tac >> drule_all regular_plan_selected_prefix >>
  disch_then (REPEAT_TCL CHOOSE_THEN strip_assume_tac) >>
  gvs[release_dead_spills_spill_base, release_dead_spills_next_offset] >>
  metis_tac[]
QED
