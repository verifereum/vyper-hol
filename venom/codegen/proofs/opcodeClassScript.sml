(*
 * Opcode result classification helpers
 *
 * Classifies which opcodes can produce Halt/Abort results.
 * Shared by gen_inst_halt_sim and gen_inst_abort_sim.
 *)


Theory opcodeClass
Ancestors
  venomExecSemantics venomInst venomEffects
Libs
  BasicProvers

(* ===== exec_* result type lemmas ===== *)
(* Each exec wrapper only returns OK or Error — never Halt/Abort/IntRet.
   Proving these individually is fast; using them as [simp] makes the
   opcode case split in the main theorems fast. *)

(* Reusable tactic for exec_* not_halt/not_abort proofs *)
val exec_case_tac = rpt gen_tac >> simp[] >> every_case_tac >> simp[];

(* --- Not Halt --- *)

val exec_pure1_not_halt = store_thm("exec_pure1_not_halt[local,simp]",
  ``!f inst s vs'. exec_pure1 f inst s <> Halt vs'``,
  simp[exec_pure1_def] >> exec_case_tac);
val exec_pure2_not_halt = store_thm("exec_pure2_not_halt[local,simp]",
  ``!f inst s vs'. exec_pure2 f inst s <> Halt vs'``,
  simp[exec_pure2_def] >> exec_case_tac);
val exec_pure3_not_halt = store_thm("exec_pure3_not_halt[local,simp]",
  ``!f inst s vs'. exec_pure3 f inst s <> Halt vs'``,
  simp[exec_pure3_def] >> exec_case_tac);
val exec_read0_not_halt = store_thm("exec_read0_not_halt[local,simp]",
  ``!f inst s vs'. exec_read0 f inst s <> Halt vs'``,
  simp[exec_read0_def] >> exec_case_tac);
val exec_read1_not_halt = store_thm("exec_read1_not_halt[local,simp]",
  ``!f inst s vs'. exec_read1 f inst s <> Halt vs'``,
  simp[exec_read1_def] >> exec_case_tac);
val exec_write2_not_halt = store_thm("exec_write2_not_halt[local,simp]",
  ``!f inst s vs'. exec_write2 f inst s <> Halt vs'``,
  simp[exec_write2_def] >> exec_case_tac);
val exec_ext_call_not_halt = store_thm("exec_ext_call_not_halt[local,simp]",
  ``!inst s g a v ao as_ ro rs st vs'.
    exec_ext_call inst s g a v ao as_ ro rs st <> Halt vs'``,
  simp[exec_ext_call_def] >> exec_case_tac);
val exec_delegatecall_not_halt = store_thm(
  "exec_delegatecall_not_halt[local,simp]",
  ``!inst s g a ao as_ ro rs vs'.
    exec_delegatecall inst s g a ao as_ ro rs <> Halt vs'``,
  simp[exec_delegatecall_def] >> exec_case_tac);
val exec_create_not_halt = store_thm("exec_create_not_halt[local,simp]",
  ``!inst s v off sz salt vs'.
    exec_create inst s v off sz salt <> Halt vs'``,
  simp[exec_create_def] >> exec_case_tac);
val exec_alloca_not_halt = store_thm("exec_alloca_not_halt[local,simp]",
  ``!inst s a vs'. exec_alloca inst s a <> Halt vs'``,
  simp[exec_alloca_def] >> exec_case_tac);

(* --- Not Abort --- *)

val exec_pure1_not_abort = store_thm("exec_pure1_not_abort[local,simp]",
  ``!f inst s a vs'. exec_pure1 f inst s <> Abort a vs'``,
  simp[exec_pure1_def] >> exec_case_tac);
val exec_pure2_not_abort = store_thm("exec_pure2_not_abort[local,simp]",
  ``!f inst s a vs'. exec_pure2 f inst s <> Abort a vs'``,
  simp[exec_pure2_def] >> exec_case_tac);
val exec_pure3_not_abort = store_thm("exec_pure3_not_abort[local,simp]",
  ``!f inst s a vs'. exec_pure3 f inst s <> Abort a vs'``,
  simp[exec_pure3_def] >> exec_case_tac);
val exec_read0_not_abort = store_thm("exec_read0_not_abort[local,simp]",
  ``!f inst s a vs'. exec_read0 f inst s <> Abort a vs'``,
  simp[exec_read0_def] >> exec_case_tac);
val exec_read1_not_abort = store_thm("exec_read1_not_abort[local,simp]",
  ``!f inst s a vs'. exec_read1 f inst s <> Abort a vs'``,
  simp[exec_read1_def] >> exec_case_tac);
val exec_write2_not_abort = store_thm("exec_write2_not_abort[local,simp]",
  ``!f inst s a vs'. exec_write2 f inst s <> Abort a vs'``,
  simp[exec_write2_def] >> exec_case_tac);
val exec_ext_call_not_abort = store_thm(
  "exec_ext_call_not_abort[local,simp]",
  ``!inst s g a v ao as_ ro rs st ab vs'.
    exec_ext_call inst s g a v ao as_ ro rs st <> Abort ab vs'``,
  simp[exec_ext_call_def] >> exec_case_tac);
val exec_delegatecall_not_abort = store_thm(
  "exec_delegatecall_not_abort[local,simp]",
  ``!inst s g a ao as_ ro rs ab vs'.
    exec_delegatecall inst s g a ao as_ ro rs <> Abort ab vs'``,
  simp[exec_delegatecall_def] >> exec_case_tac);
val exec_create_not_abort = store_thm("exec_create_not_abort[local,simp]",
  ``!inst s v off sz salt ab vs'.
    exec_create inst s v off sz salt <> Abort ab vs'``,
  simp[exec_create_def] >> exec_case_tac);
val exec_alloca_not_abort = store_thm("exec_alloca_not_abort[local,simp]",
  ``!inst s a ab vs'. exec_alloca inst s a <> Abort ab vs'``,
  simp[exec_alloca_def] >> exec_case_tac);

(* ===== Main classification theorems ===== *)

Theorem step_inst_base_halt_opcodes:
  !inst vs vs'.
    step_inst_base inst vs = Halt vs' ==>
    inst.inst_opcode = STOP \/
    inst.inst_opcode = RETURN \/
    inst.inst_opcode = SINK \/
    inst.inst_opcode = SELFDESTRUCT
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode` >>
  simp[step_inst_base_def] >>
  every_case_tac >> simp[]
QED

Theorem step_inst_halt_opcodes:
  !fuel ctx inst vs vs'.
    step_inst fuel ctx inst vs = Halt vs' ==>
    inst.inst_opcode = STOP \/
    inst.inst_opcode = RETURN \/
    inst.inst_opcode = SINK \/
    inst.inst_opcode = SELFDESTRUCT \/
    inst.inst_opcode = INVOKE
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >- simp[] >>
  `step_inst fuel ctx inst vs = step_inst_base inst vs`
    by fs[step_inst_non_invoke] >>
  fs[] >> imp_res_tac step_inst_base_halt_opcodes >> simp[]
QED

Theorem step_inst_base_abort_opcodes:
  !inst vs a vs'.
    step_inst_base inst vs = Abort a vs' ==>
    inst.inst_opcode = REVERT \/
    inst.inst_opcode = INVALID \/
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = ASSERT_UNREACHABLE \/
    inst.inst_opcode = RETURNDATACOPY
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode` >>
  simp[step_inst_base_def] >>
  every_case_tac >> simp[]
QED

Theorem step_inst_abort_opcodes:
  !fuel ctx inst vs a vs'.
    step_inst fuel ctx inst vs = Abort a vs' ==>
    inst.inst_opcode = REVERT \/
    inst.inst_opcode = INVALID \/
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = ASSERT_UNREACHABLE \/
    inst.inst_opcode = RETURNDATACOPY \/
    inst.inst_opcode = INVOKE
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >- simp[] >>
  `step_inst fuel ctx inst vs = step_inst_base inst vs`
    by fs[step_inst_non_invoke] >>
  fs[] >> imp_res_tac step_inst_base_abort_opcodes >> simp[]
QED
