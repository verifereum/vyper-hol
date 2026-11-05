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
