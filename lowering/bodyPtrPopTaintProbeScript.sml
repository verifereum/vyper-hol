Theory bodyPtrPopTaintProbe
Ancestors
  ptrDiscipline venomInst venomState words finite_map pred_set

(* A clean header write cannot seed taint in newly dead storage. *)
Theorem pop_clean_header_store_taint:
  !tn inst s addr v key.
    inst.inst_operands = [addr; v] /\ eval_operand addr s = SOME key /\
    op_taint tn v = {} ==>
    store_taint SSTORE tn inst s tn.t_stor SUBSET tn.t_stor
Proof
  rpt strip_tac >> simp[store_taint_def] >>
  Cases_on `inst.inst_opcode = SSTORE` >> simp[key_update_def] >>
  simp[SUBSET_DEF, IN_DEF] >> metis_tac[]
QED

Theorem pop_clean_header_step_taint:
  !tn inst s s' addr v key.
    inst.inst_operands = [addr; v] /\ eval_operand addr s = SOME key /\
    op_taint tn v = {} ==>
    (step_taint inst s s' tn).t_stor SUBSET tn.t_stor
Proof
  rpt strip_tac >>
  drule_all pop_clean_header_store_taint >>
  simp[step_taint_def, adopt_reset_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem pop_nonstore_step_storage_taint:
  !tn inst s s'.
    inst.inst_opcode <> SSTORE ==>
    (step_taint inst s s' tn).t_stor SUBSET tn.t_stor
Proof
  rpt strip_tac >> simp[step_taint_def, store_taint_def, adopt_reset_def] >>
  IF_CASES_TAC >> simp[]
QED
