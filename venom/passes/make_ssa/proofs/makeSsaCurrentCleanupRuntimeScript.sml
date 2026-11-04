Theory makeSsaCurrentCleanupRuntime
Ancestors
  list venomExecSemantics venomState stateFrame finite_map

Definition current_cleanup_shape_def:
  current_cleanup_shape inst <=>
    (inst.inst_opcode = NOP /\ inst.inst_operands = [] /\ inst.inst_outputs = []) \/
    (?src dst. inst.inst_opcode = ASSIGN /\
      inst.inst_operands = [Var src] /\ inst.inst_outputs = [dst])
End

Definition current_copies_run_def:
  (current_copies_run [] st = OK st) /\
  (current_copies_run (inst::rest) st =
    case step_inst_base inst st of
      OK mid => current_copies_run rest mid
    | other => other)
End

Theorem current_cleanup_assign_step:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var src] /\
  inst.inst_outputs = [dst] ==>
  step_inst_base inst st =
    case lookup_var src st of
      NONE => Error "undefined operand"
    | SOME value => OK (update_var dst value st)
Proof
  strip_tac >> simp[step_inst_base_def, eval_operand_def]
QED

Theorem current_cleanup_nop_step:
  inst.inst_opcode = NOP ==> step_inst_base inst st = OK st
Proof
  simp[step_inst_base_def]
QED

Theorem current_copies_assign:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var src] /\
  inst.inst_outputs = [dst] ==>
  current_copies_run [inst] st =
    case lookup_var src st of
      NONE => Error "undefined operand"
    | SOME value => OK (update_var dst value st)
Proof
  strip_tac >> drule_all current_cleanup_assign_step >>
  disch_then (qspec_then `st` assume_tac) >>
  simp[current_copies_run_def] >> Cases_on `lookup_var src st` >> simp[]
QED

Theorem current_copies_nop:
  inst.inst_opcode = NOP ==> current_copies_run [inst] st = OK st
Proof
  simp[current_copies_run_def, current_cleanup_nop_step]
QED

Theorem current_cleanup_step_frame:
  current_cleanup_shape inst /\ step_inst_base inst st = OK ready ==>
  execution_frame ready = execution_frame st
Proof
  simp[current_cleanup_shape_def] >> rpt strip_tac
  >- gvs[current_cleanup_nop_step] >>
  drule_all current_cleanup_assign_step >>
  disch_then (qspec_then `st` mp_tac) >>
  Cases_on `lookup_var src st` >> gvs[] >> strip_tac >> gvs[]
QED

Theorem current_cleanup_step_untouched:
  current_cleanup_shape inst /\ step_inst_base inst st = OK ready /\
  ~MEM v inst.inst_outputs ==>
  lookup_var v ready = lookup_var v st
Proof
  simp[current_cleanup_shape_def] >> rpt strip_tac
  >- gvs[current_cleanup_nop_step] >>
  drule_all current_cleanup_assign_step >>
  disch_then (qspec_then `st` mp_tac) >>
  Cases_on `lookup_var src st` >> gvs[] >> strip_tac >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem current_copies_run_frame:
  !copies st ready.
  EVERY current_cleanup_shape copies /\ current_copies_run copies st = OK ready ==>
  execution_frame ready = execution_frame st
Proof
  Induct >> simp[current_copies_run_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h st` >> gvs[] >>
  metis_tac[current_cleanup_step_frame]
QED

Theorem current_copies_run_untouched:
  !copies st ready v.
  EVERY current_cleanup_shape copies /\ current_copies_run copies st = OK ready /\
  (!inst. MEM inst copies ==> ~MEM v inst.inst_outputs) ==>
  lookup_var v ready = lookup_var v st
Proof
  Induct >> simp[current_copies_run_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h st` >> gvs[] >>
  metis_tac[current_cleanup_step_untouched]
QED

Theorem current_copies_read_after_write:
  first.inst_opcode = ASSIGN /\ first.inst_operands = [Var a] /\
  first.inst_outputs = [x] /\
  second.inst_opcode = ASSIGN /\ second.inst_operands = [Var x] /\
  second.inst_outputs = [y] /\ lookup_var a st = SOME value ==>
  current_copies_run [first;second] st =
    OK (update_var y value (update_var x value st))
Proof
  strip_tac >>
  `lookup_var x (update_var x value st) = SOME value` by
    simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[current_copies_run_def, step_inst_base_def, eval_operand_def]
QED

Theorem current_copies_assign_success:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var src] /\
  inst.inst_outputs = [dst] /\ lookup_var src st = SOME value ==>
  current_copies_run [inst] st = OK (update_var dst value st)
Proof
  strip_tac >> drule_all current_copies_assign >>
  disch_then (qspec_then `st` mp_tac) >> simp[]
QED

Theorem current_copies_assign_missing:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var src] /\
  inst.inst_outputs = [dst] /\ lookup_var src st = NONE ==>
  current_copies_run [inst] st = Error "undefined operand"
Proof
  strip_tac >> drule_all current_copies_assign >>
  disch_then (qspec_then `st` mp_tac) >> simp[]
QED
