(*
 * Helpers for fnFrameSteps$phi_prefix_frame_sim: a join block's PHI
 * prefix, run from the lineage entry state of its predecessor, against
 * frameRel$fn_frame_inv.
 *)

Theory fnFrameStepsPhi
Ancestors
  fnPlanLineageJoin genFrameSim fnPlanLineage frameRel contextCodegenRel codegenRel
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst livenessDefs dfgDefs cfgDefs

Theorem phi_delete_spills_domain[local]:
  !xs ps at.
    at IN FDOM (FOLDL (\p (op, off).
      p with <| ps_spilled := p.ps_spilled \\ op;
                ps_alloc := free_spill_slot off p.ps_alloc |>) ps xs).ps_spilled <=>
    at IN FDOM ps.ps_spilled /\ ~MEM at (MAP FST xs)
Proof
  Induct_on `xs` >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >> simp[] >> metis_tac[]
QED

Theorem phi_release_dead_spills_domain:
  !live ps at.
    at IN FDOM (release_dead_spills live ps).ps_spilled <=>
    at IN FDOM ps.ps_spilled /\ (?v. at = Var v /\ MEM v live)
Proof
  rpt gen_tac >>
  simp[stackPlanOpsTheory.release_dead_spills_def, phi_delete_spills_domain,
       listTheory.MEM_MAP, listTheory.MEM_FILTER, pairTheory.EXISTS_PROD,
       alistTheory.MEM_fmap_to_alist] >>
  Cases_on `at` >> simp[] >> metis_tac[]
QED

Theorem phi_regular_plan_spill_support:
  !liveness dfg cfg fn inst next_live halting next_term lbl ps ops ps' at.
    generate_regular_inst_plan liveness dfg cfg fn inst next_live
      halting next_term lbl ps = (ops, ps') /\
    at IN FDOM ps'.ps_spilled ==>
    ?v. at = Var v /\ MEM v next_live
Proof
  rpt gen_tac >>
  simp[generate_regular_inst_plan_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (IF_CASES_TAC >> gvs[LET_THM]) >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[phi_release_dead_spills_domain]
QED

Theorem phi_regular_plan_spill_fresh:
  generate_regular_inst_plan liveness dfg cfg fn inst next_live
    halting next_term lbl ps = (ops, ps') /\
  ~MEM out next_live ==> ~(Var out IN FDOM ps'.ps_spilled)
Proof
  strip_tac >> strip_tac >>
  drule_all phi_regular_plan_spill_support >> simp[]
QED

Theorem phi_jmp_plan_spill_support:
  generate_inst_plan liveness dfg cfg fn inst next_live halting next_term lbl ps =
    SOME (ops, ps') /\ inst.inst_opcode = JMP /\
  at IN FDOM ps'.ps_spilled ==>
  ?v. at = Var v /\ MEM v next_live
Proof
  strip_tac >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def,
      venomInstTheory.is_param_opcode_def, AllCaseEqs()] >>
  drule_all phi_regular_plan_spill_support >> simp[]
QED

Theorem phi_terminal_jmp_spill_support:
  !insts i ps ops ps' at.
    insts <> [] /\ (LAST insts).inst_opcode = JMP /\
    generate_block_insts_plan liveness dfg cfg fn lbl halting n_params
      block_len i insts ps = SOME (ops, ps') /\
    at IN FDOM ps'.ps_spilled ==>
    ?v. at = Var v /\ MEM v (live_vars_at liveness lbl block_len)
Proof
  Induct_on `insts` >- simp[] >>
  rpt gen_tac >> Cases_on `insts = []`
  >- (gvs[generate_block_insts_plan_def, AllCaseEqs()] >>
      metis_tac[phi_jmp_plan_spill_support]) >>
  simp[generate_block_insts_plan_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[listTheory.LAST_DEF] >>
  first_x_assum irule >> goal_assum drule >> simp[]
QED
