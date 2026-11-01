(* dft_schedule_safe, the premise of dft_pass_correct, is false.

   In MSTORE %p %v; ASSERT %x; RETURN %p 32 the plain EDA that dft_block
   schedules from gives ASSERT no edges, so it is a DFS entry and is emitted
   first. build_full_eda's barrier chain makes ASSERT depend on the earlier
   MSTORE, so the schedule is not topologically sorted w.r.t. full_dep.

   This swap is harmless (a failing ASSERT rolls the MSTORE back), but the
   same mechanism also hoists ASSERT above INVOKE, which is observable: a
   callee that reverts with data is replaced by ASSERT's empty revert. *)
Theory dftScheduleSafeCounterexample
Ancestors dftDefs dftCorrectness venomInst venomWf dftWf dftPermSim dftTopoSort

Definition assert_hoist_block_def:
  assert_hoist_block =
    <| bb_label := "entry";
       bb_instructions :=
         [<|inst_id := 1; inst_opcode := MSTORE;
            inst_operands := [Var "p"; Var "v"]; inst_outputs := []|>;
          <|inst_id := 2; inst_opcode := ASSERT;
            inst_operands := [Var "x"]; inst_outputs := []|>;
          <|inst_id := 3; inst_opcode := RETURN;
            inst_operands := [Var "p"; Lit 32w]; inst_outputs := []|>] |>
End

Theorem assert_hoist_schedule:
  (dft_block [] assert_hoist_block).bb_instructions =
  [EL 1 assert_hoist_block.bb_instructions;
   EL 0 assert_hoist_block.bb_instructions;
   EL 2 assert_hoist_block.bb_instructions]
Proof
  EVAL_TAC
QED

Theorem assert_hoist_full_dep:
  full_dep (build_full_eda assert_hoist_block.bb_instructions)
    (EL 1 assert_hoist_block.bb_instructions)
    (EL 0 assert_hoist_block.bb_instructions)
Proof
  simp[full_dep_def, eda_dep_def] >> EVAL_TAC >> simp[]
QED

Theorem lt3[local]:
  (n:num) < 3 <=> n = 0 \/ n = 1 \/ n = 2
Proof
  decide_tac
QED

Theorem dft_schedule_safe_false:
  ~dft_schedule_safe
Proof
  simp[dft_schedule_safe_def] >>
  qexistsl [`assert_hoist_block`, `[]`] >> rpt conj_tac
  >- simp[bb_well_formed_def, assert_hoist_block_def, is_terminator_def,
          lt3, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, DISJ_IMP_THM,
          FORALL_AND_THM]
  >- EVAL_TAC
  >- simp[non_pseudo_defs_before_uses_def, np_defs_before_uses_def,
          assert_hoist_block_def, producing_inst_def,
          lt3, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, DISJ_IMP_THM,
          FORALL_AND_THM]
  >- EVAL_TAC
  >- (simp[assert_hoist_schedule, topo_sorted_def] >> disj1_tac >>
      qexistsl [`0`, `1`] >>
      EVAL_TAC >> simp[])
QED

Definition assert_invoke_block_def:
  assert_invoke_block =
    <| bb_label := "entry";
       bb_instructions :=
         [<|inst_id := 1; inst_opcode := INVOKE;
            inst_operands := [Label "bar"; Var "y"]; inst_outputs := []|>;
          <|inst_id := 2; inst_opcode := ASSERT;
            inst_operands := [Var "c"]; inst_outputs := []|>;
          <|inst_id := 3; inst_opcode := RETURN;
            inst_operands := [Var "p"; Lit 32w]; inst_outputs := []|>] |>
End

Theorem assert_invoke_schedule:
  MAP (λi. i.inst_id) (dft_block [] assert_invoke_block).bb_instructions =
  [2; 1; 3]
Proof
  EVAL_TAC
QED

Theorem assert_invoke_full_dep:
  full_dep (build_full_eda assert_invoke_block.bb_instructions)
    (EL 1 assert_invoke_block.bb_instructions)
    (EL 0 assert_invoke_block.bb_instructions)
Proof
  simp[full_dep_def, eda_dep_def] >> EVAL_TAC >> simp[]
QED
