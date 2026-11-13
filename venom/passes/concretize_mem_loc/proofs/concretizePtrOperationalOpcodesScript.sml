Theory concretizePtrOperationalOpcodes
Ancestors
  concretizePtrOperationalBytes concretizePtrImportOrigins concretizeAllocationFree
  concretizePtrChronologicalDemand concretizePtrChronologicalHistory
  concretizeMemLocTransitionProofs concretizeMemLocDefs passSharedDefs stepWriteFootprintBase opcodeClass calleeTransport
  passSharedProps passSimulationDefs o1PassContract ptrDiscipline venomInst venomExecSemantics list

Theorem ptr_discipline_no_dret:
  ptr_discipline lo ctx vs /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) ==> inst.inst_opcode <> DRET
Proof
  simp[ptr_discipline_def, EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]
QED

Theorem ptr_stage_no_dret:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  ptr_discipline lo C vs ==>
  EVERY (\fn. EVERY (\inst. inst.inst_opcode <> DRET) (fn_insts fn))
    C'.ctx_functions
Proof
  simp[ctx_pass_stage_def, ptr_discipline_def] >> rpt strip_tac >>
  fs[LIST_REL_EL_EQN, EVERY_EL] >>
  qx_gen_tac `n` >> strip_tac >>
  `n < LENGTH C.ctx_functions` by simp[] >>
  qpat_x_assum `!n. _ ==> ?observed s out. _`
    (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> DRET)
     (fn_insts out.fpo_function)` by
    (irule (BETA_RULE (Q.INST [`P` |-> `\op. op <> DRET`]
       (SPEC_ALL concretize_fn_pass_opcode_property))) >> simp[] >>
     qexistsl_tac [`EL n C.ctx_functions`, `observed`, `rpolicy`, `s`] >>
     simp[] >> fs[fn_ptr_ok_def, EVERY_EL] >> metis_tac[MEM_EL]) >>
  gvs[EVERY_MEM] >> metis_tac[MEM_EL]
QED

Theorem ptr_frame_context_membership:
  !vs0 ctx stk PG G tn fn inst s.
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  MEM fn ctx.ctx_functions /\ EVERY (\f. MEM f.cf_fn ctx.ctx_functions) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt strip_tac >>
  gvs[] >> metis_tac[lookup_function_MEM]
QED

Theorem ptr_observation_no_dret:
  ptr_observation_reachable vs ctx a /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DRET) (fn_insts fn)) ctx.ctx_functions ==>
  a.po_inst.inst_opcode <> DRET
Proof
  simp[ptr_observation_reachable_def] >> rpt strip_tac >>
  drule ptr_frame_context_membership >> strip_tac >>
  drule concretizePtrChronologicalDemandTheory.ptr_frame_operand_instructions >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem ptr_intret_no_dret_memory:
  step_inst_base inst s = IntRet ret t /\ inst.inst_opcode <> DRET ==>
  t.vs_memory = s.vs_memory
Proof
  strip_tac >> drule step_inst_base_intret_opcodes >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ptr_return_no_dret_memory:
  step_inst fuel ctx inst s = IntRet ret ended /\ inst.inst_opcode <> DRET /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state saved ended)) = SOME next ==>
  next.vs_memory = s.vs_memory
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[step_inst_def, AllCaseEqs()]) >>
  gvs[step_inst_non_invoke] >>
  drule bind_outputs_shared_fields >> simp[] >> strip_tac >>
  metis_tac[ptr_intret_no_dret_memory]
QED

Theorem ptr_stage_observation_no_dret:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  ptr_discipline lo C vs /\
  (ptr_observation_reachable vs C a \/ ptr_observation_reachable vs C' a) ==>
  a.po_inst.inst_opcode <> DRET
Proof
  strip_tac >> irule ptr_observation_no_dret
  >- (qexistsl_tac [`C`,`vs`] >> simp[EVERY_MEM] >>
      metis_tac[ptr_discipline_no_dret]) >>
  qexistsl_tac [`C'`,`vs`] >> simp[] >>
  metis_tac[ptr_stage_no_dret]
QED
