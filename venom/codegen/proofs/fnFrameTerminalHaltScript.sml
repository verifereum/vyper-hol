Theory fnFrameTerminalHalt
Ancestors
  fnFrameTerminalPrep generatedPrefixSim preparedPrefixSim emitSim
  stackPlanGen stackPlanOps allocMono frameViewFacts frameViewMemory
  contextCodegenRel list

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

Theorem ordinary_inst_operand_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
  inst.inst_opcode <> RET /\ inst.inst_opcode <> RETFMP /\
  inst.inst_opcode <> DRET /\ MEM op inst.inst_operands ==>
  eval_operand op (frame_view fn ra vs with vs_memory := m) =
    eval_operand op vs
Proof
  strip_tac >> irule eval_operand_frame_view >> gen_tac >> disch_tac >>
  irule ordinary_operand_not_retpc >> simp[] >> qexists `inst` >> gvs[]
QED

(* A range may be on either side of any spill region.  This interface
   deliberately makes no below-spill-base assumption. *)
Theorem context_memory_read_range:
  !cp inst vs am off size.
  source_memory_reads_disjoint cp inst vs /\
  context_memory_rel cp vs.vs_memory am /\
  MEM (off, size) (source_memory_read_ranges inst vs) ==>
  TAKE size (DROP off am ++ REPLICATE size 0w) =
  TAKE size (DROP off vs.vs_memory ++ REPLICATE size 0w)
Proof
  rpt gen_tac >> strip_tac >> irule padded_memory_read_cong >> rpt strip_tac >>
  fs[context_memory_rel_def] >>
  first_x_assum (irule o GSYM) >>
  simp[context_spill_byte_def] >> gen_tac >> CCONTR_TAC >> gvs[] >>
  qpat_x_assum `source_memory_reads_disjoint _ _ _` mp_tac >>
  simp[source_memory_reads_disjoint_def, EVERY_MEM] >>
  rename1 `MEM (off, len) (source_memory_read_ranges inst vs)` >>
  qexists `(off, len)` >> simp[] >> qexists `r` >> simp[] >> decide_tac
QED
