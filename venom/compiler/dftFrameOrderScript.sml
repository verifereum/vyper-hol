(* Checked boundary probe: compatible fallibles can cross under DFT. *)
Theory dftFrameOrder
Ancestors
  dftScheduleOrder dftDefs venomWf venomInst venomEffects venomState

Theorem dft_compatible_unordered_fallible_pair:
  let x = mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 0w] [];
      y = mk_inst 1 ASSERT_UNREACHABLE [Lit 1w] []
  in inst_wf x /\ inst_wf y /\
     abort_compatible x.inst_opcode y.inst_opcode /\
     ~dft_must_order x y /\ is_fallible x /\ is_fallible y
Proof
  EVAL_TAC >> simp[]
QED

Theorem dft_unordered_compatible_fallibles:
  inst_wf x /\ inst_wf y /\
  abort_compatible x.inst_opcode y.inst_opcode /\
  ~dft_must_order x y /\ is_fallible x /\ is_fallible y ==>
  x.inst_opcode = RETURNDATACOPY /\
  y.inst_opcode = ASSERT_UNREACHABLE
Proof
  strip_tac >> Cases_on `x.inst_opcode` >>
  gvs[is_fallible_def, opcode_fail_class_def] >>
  gvs[inst_wf_def, dft_must_order_def, read_effects_def,
      write_effects_def, empty_effects_def] >>
  Cases_on `y.inst_opcode` >>
  gvs[is_fallible_def, opcode_fail_class_def, abort_compatible_def,
      is_terminator_def, read_effects_def, write_effects_def,
      empty_effects_def, all_effects_def]
QED
