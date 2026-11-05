Theory dftOperationalOutcome
Ancestors
  dftOperationalCrossing dftLocalOrdinaryClosure dftMixedCrossing
  dftOrdinaryStop dftOrdinarySwap dftOccurrenceResidual venomExecSemantics venomEffects
  venomInst venomState venomWf list pred_set
Libs
  stepInstBaseLib

Definition dft_restore_ordinary_ready_def:
  dft_restore_ordinary_ready x outs ret cs s t <=>
    inst_wf x /\ ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
    x.inst_opcode <> INVOKE /\ x.inst_opcode <> GAS /\ x.inst_opcode <> ALLOCA /\
    ~MEM x.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
    read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects /\
    (!op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v) /\
    (!v. MEM (Var v) x.inst_operands ==> ~MEM v outs) /\
    dft_restore outs ret cs s = SOME t
End

(* The proposed abort-as-input-state alternative is false: ASSERT clears
   returndata and halts, and ASSERT_UNREACHABLE is also permitted here. *)
Theorem dft_assert_zero_abort_state_probe:
  step_inst_base (mk_inst 1 ASSERT [Lit (words$n2w 0)] [])
    (init_venom_state "entry") =
    Abort Revert_abort
      (revert_state (set_returndata [] (init_venom_state "entry"))) /\
  ~(?a. step_inst_base (mk_inst 1 ASSERT [Lit (words$n2w 0)] [])
    (init_venom_state "entry") = Abort a (init_venom_state "entry"))
Proof
  EVAL_TAC >> simp[]
QED

Theorem dft_assert_unreachable_abort_probe:
  step_inst_base (mk_inst 1 ASSERT_UNREACHABLE [Lit (words$n2w 0)] [])
    (init_venom_state "entry") =
    Abort ExHalt_abort
      (halt_state (set_returndata [] (init_venom_state "entry"))) /\
  inst_wf (mk_inst 1 ASSERT_UNREACHABLE [Lit (words$n2w 0)] []) /\
  ~is_pseudo ASSERT_UNREACHABLE /\ ~is_terminator ASSERT_UNREACHABLE /\
  read_effects ASSERT_UNREACHABLE = empty_effects /\
  write_effects ASSERT_UNREACHABLE = empty_effects /\
  ASSERT_UNREACHABLE <> ASSERT
Proof
  EVAL_TAC >> simp[]
QED

Theorem dft_abort_state_premises_inhabited_probe:
  ?t. dft_restore_ordinary_ready
    (mk_inst 1 ASSERT [Lit (words$n2w 0)] []) []
    <|iret_values := []; iret_adopt_fmp := NONE|>
    (init_venom_state "entry") (init_venom_state "entry") t
Proof
  simp[dft_restore_ordinary_ready_def] >> EVAL_TAC >> simp[eval_operand_def]
QED

Theorem dft_restore_ordinary_abort_iff:
  dft_restore_ordinary_ready x outs ret cs s t ==>
  ((!r. step_inst_base x s = Abort a r ==> ?r'. step_inst_base x t = Abort a r') /\
   (!r. step_inst_base x t = Abort a r ==> ?r'. step_inst_base x s = Abort a r'))
Proof
  strip_tac >>
  fs[dft_restore_ordinary_ready_def] >>
  `!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s` by
    (drule dft_restore_operands >> disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  `x.inst_opcode <> RETURNDATACOPY` by
    (strip_tac >> gvs[read_effects_def, empty_effects_def]) >>
  conj_tac >> rpt strip_tac >>
  irule dft_ordinary_abort_replay >> metis_tac[]
QED
