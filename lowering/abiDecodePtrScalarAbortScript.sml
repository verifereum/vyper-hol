(* A failed scalar assertion checks the prefix and stops before its suffix. *)
Theory abiDecodePtrScalarAbort
Ancestors
  bodyPtrBopScalarDynamic bodyPtrBopScalarSeq bodyPtrBopScalarOutcome instSeqComposePtr
  exprLoweringProps venomExecSemantics venomInst list rich_list

(* Assertion rejection preserves runtime fields except its exit markers. *)
Theorem scalar_seq_abort_runtime_frame:
  bop_scalar_seq R A code B /\ run_inst_seq code s = Abort a t ==>
  (t with <|vs_vars := s.vs_vars; vs_halted := s.vs_halted;
            vs_returndata := s.vs_returndata|>) = s /\
  (!x. x IN R ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> drule_all bop_scalar_seq_abort_prefix >> strip_tac >>
  drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  Cases_on `opc = ASSERT` >>
  gvs[mk_inst_def] >>
  gvs[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      venomStateTheory.revert_state_def, venomStateTheory.halt_state_def,
      venomStateTheory.set_returndata_def,
      AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED
