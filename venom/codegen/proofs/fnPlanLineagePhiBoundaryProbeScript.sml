Theory fnPlanLineagePhiBoundaryProbe
Ancestors
  fnPlanLineageEntryProbe fnPlanLineageTargetProbe fnPlanLineageNativeResources
  codegenReadyCompute stackPlanGen livenessDefs
Libs wordsLib

(* Shared incoming PHIs are rejected by repeated_target_disjoint_obstruction
   in TargetProbe. Selected input live-through is rejected by
   entry_live_input_rejected in EntryProbe. Neither is a task counterexample. *)
Definition phi_boundary_dead_fn_def:
  phi_boundary_dead_fn = entry_probe_fn with fn_blocks :=
    LUPDATE ((EL 3 entry_probe_fn.fn_blocks) with bb_instructions :=
      [mk_inst 5 PHI [Label "L"; Var "a"; Label "R"; Var "b"] ["x"];
       mk_inst 7 JMP [Label "exit"] []]) 3 entry_probe_fn.fn_blocks
End

Theorem phi_boundary_dead_ready:
  codegen_ready_fn phi_boundary_dead_fn
Proof
  EVAL_TAC >> simp[]
QED

Theorem phi_boundary_dead_plan:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze phi_boundary_dead_fn) (dfg_build_function phi_boundary_dead_fn)
    (cfg_analyze phi_boundary_dead_fn) NONE [] phi_boundary_dead_fn 0 0)
Proof
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC)
QED

Definition phi_boundary_step_def:
  phi_boundary_step n ps = generate_block_plan
    (liveness_analyze phi_boundary_dead_fn) (dfg_build_function phi_boundary_dead_fn)
    (cfg_analyze phi_boundary_dead_fn) phi_boundary_dead_fn
    (EL n phi_boundary_dead_fn.fn_blocks) ps
End

Definition phi_boundary_incoming_def:
  phi_boundary_incoming side = SND (THE (phi_boundary_step side
    (SND (THE (phi_boundary_step 0 (init_cleanup_plan_state NONE [] 0 0))))))
End

Definition phi_boundary_setup_def:
  phi_boundary_setup side = SND (prepare_params_plan
    (liveness_analyze phi_boundary_dead_fn) phi_boundary_dead_fn
    (SND (clean_stack_plan (liveness_analyze phi_boundary_dead_fn)
      (cfg_analyze phi_boundary_dead_fn) phi_boundary_dead_fn
      (EL 3 phi_boundary_dead_fn.fn_blocks) (phi_boundary_incoming side))))
End

Definition phi_boundary_written_def:
  phi_boundary_written side = SND (generate_phi_plan
    (HD (EL 3 phi_boundary_dead_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze phi_boundary_dead_fn) "J" 1) F
    (phi_boundary_setup side))
End

Theorem phi_boundary_dead_frontiers:
  live_vars_at (liveness_analyze phi_boundary_dead_fn) "J" 0 = ["a";"b"] /\
  live_vars_at (liveness_analyze phi_boundary_dead_fn) "J" 1 = [] /\
  (phi_boundary_incoming 1).ps_stack = [Var "a"] /\
  (phi_boundary_incoming 2).ps_stack = [Var "b"] /\
  EVERY (\side.
    phi_boundary_setup side = phi_boundary_incoming side /\
    (phi_boundary_incoming side).ps_spilled = FEMPTY /\
    (phi_boundary_written side).ps_stack = [] /\
    (phi_boundary_written side).ps_spilled = FEMPTY) [1;2]
Proof
  simp_tac bool_ss [listTheory.EVERY_DEF] >> rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- (EVAL_TAC >> simp[])
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- (EVAL_TAC >> simp[])
  >- EVAL_TAC
  >- EVAL_TAC
  >> EVAL_TAC
QED

Theorem phi_boundary_dead_native_calls:
  IS_SOME (phi_boundary_step 0 (init_cleanup_plan_state NONE [] 0 0)) /\
  EVERY (\side.
    IS_SOME (phi_boundary_step side
      (SND (THE (phi_boundary_step 0 (init_cleanup_plan_state NONE [] 0 0)))))) [1;2] /\
  EVERY (\side. IS_SOME (phi_boundary_step 3 (phi_boundary_incoming side))) [1;2] /\
  EVERY (\side. prepare_params_plan (liveness_analyze phi_boundary_dead_fn)
    phi_boundary_dead_fn (phi_boundary_incoming side) =
    ([],phi_boundary_incoming side)) [1;2] /\
  EVERY (\side. clean_stack_plan (liveness_analyze phi_boundary_dead_fn)
    (cfg_analyze phi_boundary_dead_fn) phi_boundary_dead_fn
    (EL 3 phi_boundary_dead_fn.fn_blocks) (phi_boundary_incoming side) =
    ([],phi_boundary_incoming side)) [1;2]
Proof
  simp_tac bool_ss [listTheory.EVERY_DEF] >> rpt conj_tac >>
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC) >> simp[]
QED

Theorem phi_boundary_dead_counts:
  MAP (\v. LIST_ELEM_COUNT (Var v) (phi_boundary_setup 1).ps_stack)
    ["a";"b";"x"] = [1;0;0] /\
  MAP (\v. LIST_ELEM_COUNT (Var v) (phi_boundary_setup 2).ps_stack)
    ["a";"b";"x"] = [0;1;0] /\
  EVERY (\side. MAP (\v. LIST_ELEM_COUNT (Var v) (phi_boundary_written side).ps_stack)
    ["a";"b";"x"] = [0;0;0]) [1;2] /\
  ~native_live_boundary phi_boundary_dead_fn (EL 3 phi_boundary_dead_fn.fn_blocks)
    0 (phi_boundary_setup 1) /\
  ~native_live_boundary phi_boundary_dead_fn (EL 3 phi_boundary_dead_fn.fn_blocks)
    0 (phi_boundary_setup 2) /\
  EVERY (\side. native_live_boundary phi_boundary_dead_fn
    (EL 3 phi_boundary_dead_fn.fn_blocks) 1 (phi_boundary_written side)) [1;2]
Proof
  mp_tac phi_boundary_dead_frontiers >>
  simp_tac (srw_ss()) [listTheory.EVERY_DEF] >> strip_tac >>
  simp[native_live_boundary_def, rich_listTheory.LIST_ELEM_COUNT_DEF] >>
  EVAL_TAC >>
  conj_tac >- (disj1_tac >> qexists `"b"` >> EVAL_TAC) >>
  conj_tac >- (disj1_tac >> qexists `"a"` >> EVAL_TAC) >>
  simp[]
QED
