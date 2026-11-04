(* Local call framing, independent of whether a callee ever returns. *)
Theory dftOccurrenceFrame
Ancestors
  dftOccurrenceReplay dftScheduleOrder dftCommutation venomExecSemantics
  venomState venomInst venomEffects list pred_set

Theorem dft_invoke_inversion_disjoint:
  ~dft_must_order x y /\ y.inst_opcode = INVOKE ==>
  DISJOINT (set (inst_defs x)) (set (inst_uses y)) /\
  write_effects x.inst_opcode = empty_effects /\
  read_effects x.inst_opcode = empty_effects
Proof
  strip_tac >>
  gvs[dft_must_order_def, read_effects_def, write_effects_def,
      all_effects_def, empty_effects_def, DISJOINT_DEF, EXTENSION] >>
  conj_tac >> gen_tac >> Cases_on `x'` >> metis_tac[]
QED

Theorem dft_setup_callee_update:
  setup_callee fn args (update_var v w s) = setup_callee fn args s
Proof
  simp[setup_callee_def, update_var_def]
QED

Theorem dft_setup_callee_fold:
  !us s. setup_callee fn args
    (FOLDL (\u p. update_var (FST p) (SND p) u) s us) =
    setup_callee fn args s
Proof
  Induct >> simp[dft_setup_callee_update]
QED

Theorem dft_eval_operands_fold:
  !us s. EVERY (\p. ~MEM (Var (FST p)) ops) us ==>
  eval_operands ops (FOLDL (\u p. update_var (FST p) (SND p) u) s us) =
  eval_operands ops s
Proof
  Induct >> simp[eval_operands_update_var]
QED
