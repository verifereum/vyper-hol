Theory dftReverseExclusionProbe
Ancestors
  dftPositionalProvenance dftPositionalOrientation dftScheduleOrder
  dftPositionalSchedule dftScheduleEdits dftDefs
  venomEffects venomInst venomWf pred_set list

Theorem dft_reverse_exclusion_conditional:
  ~dft_must_order call x /\ ~is_terminator call.inst_opcode /\
  DISJOINT (set (inst_defs x)) (set (inst_uses call)) /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) ==>
  ~dft_must_order x call
Proof
  simp[dft_must_order_def, DISJOINT_DEF, EXTENSION, IN_UNION] >>
  metis_tac[]
QED

(* A legal ordinary ASSERT realizes the asymmetric root clause. This is
   a local ordering obstruction, not a counterexample to the task. *)
Theorem dft_assert_reverse_exclusion_obstruction:
  ~dft_must_order (mk_inst 0 INVOKE [Label "callee"] [])
    (mk_inst 1 ASSERT [Lit (words$n2w 1)] []) /\
  dft_must_order (mk_inst 1 ASSERT [Lit (words$n2w 1)] [])
    (mk_inst 0 INVOKE [Label "callee"] []) /\
  inst_wf (mk_inst 1 ASSERT [Lit (words$n2w 1)] []) /\
  ~is_pseudo ASSERT /\ ~is_terminator ASSERT /\
  ASSERT <> GAS /\ ASSERT <> INVOKE /\ ASSERT <> ALLOCA
Proof
  EVAL_TAC >> simp[]
QED

Theorem dft_assert_residual_root:
  x.inst_opcode = ASSERT /\ x.inst_outputs = [] ==>
  dft_must_order x call
Proof
  simp[dft_must_order_def, read_effects_def, write_effects_def]
QED

Theorem dft_probe_before_nil[local,simp]:
  ~id_before [] a b
Proof
  simp[id_before_def]
QED

(* Even retaining the guard's original order does not eliminate the
   ASSERT root obstruction. Full function provenance is not asserted. *)
Theorem dft_assert_schedule_guard_obstruction:
  b.bb_instructions =
    [mk_inst 0 INVOKE [Label "callee"] []; mk_inst 1 ASSERT [Lit (words$n2w 1)] []] /\
  dest.bb_instructions =
    [mk_inst 1 ASSERT [Lit (words$n2w 1)] []; mk_inst 0 INVOKE [Label "callee"] []] ==>
  dft_pos_schedule_guard b dest dft_must_order fi bi []
    (mk_inst 0 INVOKE [Label "callee"] [])
    (mk_inst 1 ASSERT [Lit (words$n2w 1)] []) []
Proof
  simp[dft_pos_schedule_guard_def, schedule_edges_def,
       id_before_cons] >>
  EVAL_TAC >> simp[]
QED
