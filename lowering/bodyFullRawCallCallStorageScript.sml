(* Storage taint follows the specified successful oracle-call execution.
   The dead mask is arbitrary, including constructor immutable masks. *)
Theory bodyFullRawCallCallStorage
Ancestors
  oracleCallStepPtr bodyPtrDefs ptrDiscipline pred_set

Theorem raw_call_exec_stor_taint_at:
  (inst.inst_opcode = CALL \/
   (inst.inst_opcode = STATICCALL /\ stat)) /\
  exec_ext_call inst s gas addr value ao az ro rz stat = OK u /\
  u.vs_immutables = s.vs_immutables /\
  stor_taint_ok_at D tn s ==>
  stor_taint_ok_at D (step_taint inst s u tn) u
Proof
  strip_tac >> drule exec_ext_call_storage_cases >> strip_tac >>
  gvs[stor_taint_ok_at_def, step_taint_def, adopt_reset_def,
      store_taint_def, imm_taint_def] >>
  metis_tac[EMPTY_SUBSET]
QED
