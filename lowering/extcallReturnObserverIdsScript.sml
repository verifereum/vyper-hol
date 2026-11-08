(* Only foreign STOP/NOP ids are moved: allocation keys are untouched. *)
Theory extcallReturnObserverIds
Ancestors
  extcallReturnObserverRun exprSimAbiGasBridge venomExecSemantics
  venomExecProofs venomInst venomInstProps unitShapeDefs list rich_list arithmetic localPtrsProps venomWf

Definition return_observer_inst_ids_def:
  return_observer_inst_ids func bound inst =
    if MEM inst (fn_insts func) then inst
    else inst with inst_id := bound + inst.inst_id
End

Definition return_observer_ids_def:
  return_observer_ids func bound obs =
    obs with fn_blocks := MAP
      (\bb. bb with bb_instructions :=
        MAP (return_observer_inst_ids func bound) bb.bb_instructions)
      obs.fn_blocks
End

Theorem return_observer_stop_nop_ids:
  (inst.inst_opcode = STOP \/ inst.inst_opcode = NOP) ==>
  step_inst_base (inst with inst_id := id) s = step_inst_base inst s
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs]
QED

Theorem return_observer_inst_ids_step:
  (inst.inst_opcode <> STOP /\ inst.inst_opcode <> NOP ==>
     MEM inst (fn_insts func)) ==>
  step_inst fuel ctx (return_observer_inst_ids func bound inst) s =
  step_inst fuel ctx inst s
Proof
  strip_tac >> simp[return_observer_inst_ids_def] >>
  IF_CASES_TAC >> simp[] >>
  `inst.inst_opcode = STOP \/ inst.inst_opcode = NOP` by metis_tac[] >>
  simp[step_inst_non_invoke, return_observer_stop_nop_ids]
QED

Theorem return_observer_ids_bound:
  ?bound. !i. MEM i (fn_insts func ++ fn_insts obs) ==> i.inst_id < bound
Proof
  qexists_tac `SUC (MAX_LIST (MAP (\i. i.inst_id) (fn_insts func ++ fn_insts obs)))` >>
  rpt strip_tac >>
  `MEM i.inst_id (MAP (\i. i.inst_id) (fn_insts func ++ fn_insts obs))` by
    (simp[MEM_MAP] >> qexists_tac `i` >> fs[]) >>
  drule MAX_LIST_PROPERTY >> simp[]
QED

Theorem return_observer_ids_insts:
  fn_insts (return_observer_ids func bound obs) =
  MAP (return_observer_inst_ids func bound) (fn_insts obs)
Proof
  simp[return_observer_ids_def, fn_insts_def] >>
  qspec_tac (`obs.fn_blocks`, `bbs`) >> Induct >>
  simp[fn_insts_blocks_def, MAP_APPEND]
QED

Theorem return_observer_inst_ids_agree:
  fn_inst_ids_distinct func /\
  (!i. MEM i (fn_insts func) ==> i.inst_id < bound) /\
  MEM i (fn_insts func) /\
  i.inst_id = (return_observer_inst_ids func bound j).inst_id ==>
  i = return_observer_inst_ids func bound j
Proof
  simp[return_observer_inst_ids_def] >>
  IF_CASES_TAC >> simp[] >> rpt strip_tac
  >- metis_tac[fn_inst_ids_distinct_inj] >>
  `i.inst_id < bound` by metis_tac[] >> gvs[]
QED
