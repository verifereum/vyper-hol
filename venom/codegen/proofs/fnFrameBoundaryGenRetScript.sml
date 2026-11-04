Theory fnFrameBoundaryGenRet
Ancestors
  genFrameSim frameRel contextCodegenRel codegenRel
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst fcgDefs livenessDefs dfgDefs
  venomWf venomEffects stackPlanOps asmIR

Theorem release_dead_spills_stack:
  (release_dead_spills nl ps).ps_stack = ps.ps_stack
Proof
  simp[release_dead_spills_def] >>
  qspec_tac (`FILTER (\(op,off). case op of Lit v => T | Var v => ~MEM v nl | Label v => T)
    (fmap_to_alist ps.ps_spilled)`, `xs`) >>
  qid_spec_tac `ps` >> Induct_on `xs` >> simp[] >>
  Cases_on `h` >> simp[]
QED

Theorem ret_plan_decompose:
  inst.inst_opcode = RET /\ inst_wf inst /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps =
    SOME (ops, final) ==>
  ?iops prepared rops arranged.
    emit_input_plan RET (compute_operands inst) nl ps = (iops, prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops, arranged) /\
    ops = iops ++ rops ++ [SOEmit "JUMP"] /\
    final.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack
Proof
  strip_tac >>
  `inst.inst_outputs = []` by
    (gvs[inst_wf_def] >> Cases_on `inst.inst_outputs` >> gvs[]) >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
      generate_regular_inst_plan_def, is_commutative_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  gvs[generate_emit_ops_def, venom_to_evm_name_def] >>
  gvs[release_dead_spills_stack] >>
  metis_tac[]
QED
