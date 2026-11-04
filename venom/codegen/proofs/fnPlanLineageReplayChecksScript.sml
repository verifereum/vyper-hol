(* Concrete boundary checks; no dependency from the reusable replay theory. *)
Theory fnPlanLineageReplayChecks
Ancestors
  fnPlanLineageReplay cleanupPromiseWitness
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset;

Theorem cleanup_empty_inputs_elision:
  clean_stack_plan (cleanup_probe_live with ds_inst := FEMPTY)
    (cfg_analyze cleanup_probe_fn) cleanup_probe_fn
    (EL 1 cleanup_probe_fn.fn_blocks) cleanup_probe_state =
  ([], cleanup_probe_state with ps_stack :=
     [dead_stack_marker; dead_stack_marker])
Proof
  EVAL_TAC
QED

Theorem cleanup_empty_inputs_no_elision:
  clean_stack_plan (cleanup_probe_live with ds_inst := FEMPTY)
    (cfg_analyze cleanup_probe_fn) cleanup_probe_fn
    (EL 1 cleanup_probe_fn.fn_blocks)
    (cleanup_probe_state with <| ps_cleanup_height := NONE;
                                ps_cleanup_promised := F |>) =
  ([], cleanup_probe_state with <| ps_cleanup_height := NONE;
                                 ps_cleanup_promised := F |>)
Proof
  EVAL_TAC
QED

Theorem cleanup_nonretained_is_popped:
  (SND (clean_stack_plan cleanup_probe_live (cfg_analyze cleanup_probe_fn)
    cleanup_probe_fn (EL 1 cleanup_probe_fn.fn_blocks)
    (cleanup_probe_state with ps_stack := [Var "live"; Var "dead"]))).ps_stack =
  [Var "live"]
Proof
  EVAL_TAC
QED
