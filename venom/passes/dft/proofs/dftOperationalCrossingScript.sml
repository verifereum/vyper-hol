Theory dftOperationalCrossing
Ancestors
  dftRecursiveActivePhase dftMixedCrossing dftOrdinarySwap dftOccurrenceFrame
  dftOccurrenceResidual venomEffects venomExecSemantics venomInst venomState
  list pred_set

Definition dft_operational_crossing_ready_def:
  dft_operational_crossing_ready x call s <=>
    call.inst_opcode = INVOKE /\
    ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
    x.inst_opcode <> INVOKE /\ x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
    read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects /\
    (!v. MEM v x.inst_outputs ==>
      ~MEM (Var v) call.inst_operands /\ ~MEM v call.inst_outputs) /\
    (!v. MEM (Var v) x.inst_operands ==> ~MEM v call.inst_outputs) /\
    (?r. step_inst_base x s = OK r)
End

Theorem dft_operational_crossing_updates:
  dft_operational_crossing_ready x call s ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       step_inst_base x s = OK (dft_pending_apply us s)
Proof
  strip_tac >> fs[dft_operational_crossing_ready_def] >>
  `?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
        r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
        step_inst_base x s = OK (FOLDL (\u p. update_var (FST p) (SND p) u) s us)` by
    (irule dft_ordinary_empty_effect_replay >> simp[]) >>
  metis_tac[dft_pending_apply_def]
QED

Theorem dft_operational_crossing_restore:
  dft_operational_crossing_ready x call s /\
  dft_restore call.inst_outputs ret cs s = SOME t ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       step_inst_base x s = OK (dft_pending_apply us s) /\
       step_inst_base x t = OK (dft_pending_apply us t)
Proof
  strip_tac >> fs[dft_operational_crossing_ready_def] >>
  drule_all dft_restored_ordinary_replay >> metis_tac[]
QED

Theorem dft_recursive_crossing_operational:
  dft_recursive_crossing_ready f b q pre x call post s /\
  x.inst_opcode <> INVOKE /\
  (!v. MEM (Var v) x.inst_operands ==> ~MEM v call.inst_outputs) ==>
  dft_operational_crossing_ready x call s
Proof
  strip_tac >>
  drule dft_recursive_crossing_partner_success >> strip_tac >>
  drule dft_recursive_partner_disjoint >> strip_tac >>
  fs[dft_recursive_crossing_ready_def] >>
  drule_all dft_invoke_inversion_disjoint >>
  simp[dft_operational_crossing_ready_def]
QED

Theorem dft_assert_operational_crossing:
  dft_operational_crossing_ready
    (mk_inst 1 ASSERT [Lit (words$n2w 1)] [])
    (mk_inst 0 INVOKE [Label "callee"] []) s
Proof
  simp[dft_operational_crossing_ready_def, mk_inst_def, is_pseudo_def,
       is_terminator_def, read_effects_def, write_effects_def] >>
  EVAL_TAC >> simp[]
QED
