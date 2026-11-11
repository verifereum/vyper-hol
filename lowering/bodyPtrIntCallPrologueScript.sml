Theory bodyPtrIntCallPrologue
Ancestors
  bodyPtrIntCallEntryContracts ptrSafeRun ptrDiscipline venomExecSemantics
  venomState finite_map words list

(* PARAM takes provenance from the actual INVOKE operands' PG, not from
   the caller's variable names.  In particular scalar parameters (NONE)
   clear any pre-existing provenance at the captured output. *)
Theorem intcall_param_capture_ghost:
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\ w2n idx < LENGTH PG /\
  step_inst fuel ctx inst s = OK t ==>
  FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) out = EL (w2n idx) PG /\
  op_taint (SND (ghost_step fuel ctx PG G tn inst s)) (Var out) = {}
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  drule_all ghost_step_non_invoke >> disch_then (qspecl_then [`PG`,`G`,`tn`] SUBST1_TAC) >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def, op_taint_def] >>
  Cases_on `EL (w2n idx) PG` >> simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, eval_operand_def]
QED
