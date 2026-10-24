(* Focused cleanup partition, promise, and cycle witnesses for issue #545. *)
Theory cleanupPromiseWitness
Ancestors
  stackPlanGen stackPlanTypes venomInst cfgDefs livenessDefs dfAnalyzeDefs
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset;

Definition cleanup_probe_fn_def:
  cleanup_probe_fn = mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 JNZ [Var "cond"; Label "halt"; Label "other"] []] |>;
     <| bb_label := "halt"; bb_instructions := [mk_inst 1 STOP [] []] |>;
     <| bb_label := "other"; bb_instructions := [mk_inst 2 STOP [] []] |>]
End

Definition cleanup_probe_live_def:
  cleanup_probe_live = <|
    ds_inst := FEMPTY |+ (("entry",1), ["live"; "dead"; "ghost"])
                      |+ (("halt",0), ["live"]);
    ds_boundary := FEMPTY |>
End

Definition cleanup_probe_state_def:
  cleanup_probe_state = (init_plan_state 0) with <|
    ps_stack := [Var "dead"; Var "live"]; ps_cleanup_promised := T |>
End

Theorem cleanup_inherited_promise_retains_only_physical_dead:
  clean_stack_plan cleanup_probe_live (cfg_analyze cleanup_probe_fn)
    cleanup_probe_fn (EL 1 cleanup_probe_fn.fn_blocks) cleanup_probe_state =
  ([], cleanup_probe_state with ps_stack := [dead_stack_marker; Var "live"])
Proof
  EVAL_TAC
QED

Theorem cleanup_without_bound_pops_dead:
  (SND (clean_stack_plan cleanup_probe_live (cfg_analyze cleanup_probe_fn)
    cleanup_probe_fn (EL 1 cleanup_probe_fn.fn_blocks)
    (cleanup_probe_state with ps_cleanup_promised := F))).ps_stack = [Var "live"]
Proof
  EVAL_TAC
QED

Theorem cleanup_halt_establishes_promise:
  (SND (clean_stack_plan cleanup_probe_live (cfg_analyze cleanup_probe_fn)
    cleanup_probe_fn (EL 1 cleanup_probe_fn.fn_blocks)
    (cleanup_probe_state with <| ps_cleanup_promised := F;
                                ps_cleanup_height := SOME 0 |>))).ps_cleanup_promised
Proof
  EVAL_TAC
QED

Definition cleanup_cycle_fn_def:
  cleanup_cycle_fn = mk_raw_function "loop"
    [<| bb_label := "loop"; bb_instructions :=
         [mk_inst 3 JMP [Label "loop"] []] |>]
End

Theorem cleanup_reachable_cycle_has_no_growth_bound:
  cleanup_region_growth [] (cfg_analyze cleanup_cycle_fn) cleanup_cycle_fn "loop" = NONE /\
  cleanup_region_growth [("loop",NONE)] (cfg_analyze
    (mk_raw_function "caller" [<| bb_label := "call"; bb_instructions :=
      [mk_inst 4 INVOKE [Label "loop"] []; mk_inst 5 STOP [] []] |>]))
    (mk_raw_function "caller" [<| bb_label := "call"; bb_instructions :=
      [mk_inst 4 INVOKE [Label "loop"] []; mk_inst 5 STOP [] []] |>]) "call" = NONE
Proof
  EVAL_TAC
QED
