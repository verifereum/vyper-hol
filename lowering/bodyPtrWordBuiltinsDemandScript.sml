(* Backward cleanliness demands on the actual normal instruction step.
   Unrelated allocations are allowed: only demanded outputs need a clean writer. *)
Theory bodyPtrWordBuiltinsDemand
Ancestors bodyPtrWordBuiltinsScalar decoderGhostFramePtr ptrSafeRun
  ptrDiscipline finite_map pred_set list

Theorem step_prov_clean_demand:
  (!x. x IN need /\ ~MEM x inst.inst_outputs ==> FLOOKUP G x = NONE) /\
  ((?x. x IN need /\ MEM x inst.inst_outputs) ==>
    out_prov PG G inst s' = NONE) ==>
  (!x. x IN need ==> FLOOKUP (step_prov PG G inst s') x = NONE)
Proof
  rpt strip_tac >> Cases_on `MEM x inst.inst_outputs`
  >- (`out_prov PG G inst s' = NONE` by metis_tac[] >>
      Cases_on `inst.inst_outputs` >>
      gvs[step_prov_def, set_prov_def, FLOOKUP_DRESTRICT]) >>
  drule step_prov_other_output >> metis_tac[]
QED

Theorem ghost_step_clean_demand:
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK s' /\
  (!x. x IN need /\ ~MEM x inst.inst_outputs ==> FLOOKUP G x = NONE) /\
  ((?x. x IN need /\ MEM x inst.inst_outputs) ==>
    out_prov PG G inst s' = NONE) ==>
  (!x. x IN need ==>
    FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) x = NONE)
Proof
  strip_tac >> drule_all ghost_step_non_invoke >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] SUBST1_TAC) >>
  pure_rewrite_tac[pairTheory.FST] >>
  metis_tac[step_prov_clean_demand]
QED

Theorem step_prov_scalar_demand:
  (!x. x IN need /\ ~MEM x inst.inst_outputs ==> FLOOKUP G x = NONE) /\
  ((?x. x IN need /\ MEM x inst.inst_outputs) ==>
    (!x. x IN scalars ==> FLOOKUP G x = NONE) /\
    inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
    inst.inst_opcode <> PARAM /\
    ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
      inst.inst_opcode = ASSIGN) ==>
      (!x. MEM (Var x) inst.inst_operands ==> x IN scalars))) ==>
  (!x. x IN need ==> FLOOKUP (step_prov PG G inst s') x = NONE)
Proof
  strip_tac >>
  `((?x. x IN need /\ MEM x inst.inst_outputs) ==>
    out_prov PG G inst s' = NONE)` by
    (strip_tac >> irule scalar_out_prov_none >> metis_tac[]) >>
  metis_tac[step_prov_clean_demand]
QED
