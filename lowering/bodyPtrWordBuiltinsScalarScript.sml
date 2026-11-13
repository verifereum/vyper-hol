(* Finite-map transfer for definitely scalar variables. *)
Theory bodyPtrWordBuiltinsScalar
Ancestors
  bodyPtrWordBuiltinsProvenance decoderGhostFramePtr ptrSafeRun
  ptrDiscipline finite_map pred_set list

Theorem first_prov_none:
  !ops G. (!x. MEM (Var x) ops ==> FLOOKUP G x = NONE) ==>
    first_prov G ops = NONE
Proof
  Induct >> simp[first_prov_def] >>
  rpt strip_tac >> Cases_on `h` >>
  gvs[op_prov_def, first_prov_def]
QED

Theorem scalar_out_prov_none:
  (!x. x IN scalars ==> FLOOKUP G x = NONE) /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
  inst.inst_opcode <> PARAM /\
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
    inst.inst_opcode = ASSIGN) ==>
   (!x. MEM (Var x) inst.inst_operands ==> x IN scalars)) ==>
  out_prov PG G inst s' = NONE
Proof
  strip_tac >> simp[out_prov_def] >>
  IF_CASES_TAC >- (irule first_prov_none >> metis_tac[]) >> simp[]
QED

Theorem step_prov_scalar_set:
  (!x. x IN scalars ==> FLOOKUP G x = NONE) /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
  inst.inst_opcode <> PARAM /\
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
    inst.inst_opcode = ASSIGN) ==>
   (!x. MEM (Var x) inst.inst_operands ==> x IN scalars)) ==>
  (!x. x IN scalars UNION set inst.inst_outputs ==>
       FLOOKUP (step_prov PG G inst s') x = NONE)
Proof
  strip_tac >>
  `out_prov PG G inst s' = NONE` by (irule scalar_out_prov_none >> metis_tac[]) >>
  Cases_on `inst.inst_outputs` >>
  gvs[step_prov_def, set_prov_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ghost_step_scalar_set:
  (!x. x IN scalars ==> FLOOKUP G x = NONE) /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
  inst.inst_opcode <> PARAM /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst s = OK s' /\
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
    inst.inst_opcode = ASSIGN) ==>
   (!x. MEM (Var x) inst.inst_operands ==> x IN scalars)) ==>
  (!x. x IN scalars UNION set inst.inst_outputs ==>
       FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) x = NONE)
Proof
  strip_tac >> drule_all ghost_step_non_invoke >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] SUBST1_TAC) >>
  pure_rewrite_tac[pairTheory.FST] >>
  metis_tac[step_prov_scalar_set]
QED
