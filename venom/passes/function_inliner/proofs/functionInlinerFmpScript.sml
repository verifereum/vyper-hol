(* Allocation-free execution and the FMP component of caller re-entry. *)
Theory functionInlinerFmp
Ancestors
  functionInlinerReturnTransport venomExecSemantics venomInstProofs1 list

Definition inline_fmp_result_def:
  inline_fmp_result fmp r <=>
    case r of
      OK u => u.vs_fmp = fmp
    | IntRet ir u => u.vs_fmp = fmp /\
        (ir.iret_adopt_fmp = NONE \/ ir.iret_adopt_fmp = SOME fmp)
    | Halt u => u.vs_fmp = fmp
    | Abort a u => u.vs_fmp = fmp
    | Error e => T
End

Theorem inline_setup_callee_fmp:
  setup_callee fn args s = SOME u ==> u.vs_fmp = s.vs_fmp
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]
QED

Theorem inline_bind_outputs_fmp:
  bind_outputs outs vals s = SOME u ==> u.vs_fmp = s.vs_fmp
Proof
  strip_tac >> irule bind_outputs_preserves >>
  simp[venomStateTheory.update_var_def] >> goal_assum (drule_at Any)
QED

Theorem inline_adopt_return_fmp:
  u.vs_fmp = caller.vs_fmp /\
  (ir.iret_adopt_fmp = NONE \/ ir.iret_adopt_fmp = SOME caller.vs_fmp) ==>
  (adopt_return_fmp ir (merge_callee_state caller u)).vs_fmp = u.vs_fmp
Proof
  strip_tac >> simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem inline_clone_exit_fmp_reentry:
  inline_clone_exit p V opaque P outs caller ret ir u (OK v) /\
  inline_fmp_result caller.vs_fmp (IntRet ir u) ==>
  ?caller'. bind_outputs outs ir.iret_values caller = SOME caller' /\
    (adopt_return_fmp ir (merge_callee_state caller' u)).vs_fmp = v.vs_fmp
Proof
  simp[inline_clone_exit_def, inline_fmp_result_def] >> rpt strip_tac >>
  qexists `caller'` >> simp[venomStateTheory.jump_to_def] >>
  drule inline_bind_outputs_fmp >> strip_tac >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem inline_base_ok_fmp:
  step_inst_base inst s = OK u /\
  ~MEM inst.inst_opcode [ALLOCA; DALLOCA; DRET; SETFMP] ==>
  u.vs_fmp = s.vs_fmp
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (drule venomInstTheory.terminator_opcode_cases >> strip_tac >>
      gvs[step_inst_base_opcode_eqs, AllCaseEqs(),
          venomStateTheory.jump_to_def, venomStateTheory.halt_state_def,
          venomStateTheory.revert_state_def]) >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[venomInstTheory.is_alloca_op_def]) >>
  drule step_inst_base_preserves_all >> gvs[]
QED
