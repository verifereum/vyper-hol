(* Concrete boundary checks; no dependency from the reusable replay theory. *)
Theory fnPlanLineageReplayChecks
Ancestors
  fnPlanLineageReplay cleanupPromiseWitness pred_set
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset;
val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY]);

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

Definition replay_phi_def:
  replay_phi = mk_inst 10 PHI
    [Label "left"; Var "a"; Label "right"; Var "b"] ["p"]
End

Definition replay_diamond_def:
  replay_diamond = mk_raw_function "diamond"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 ASSIGN [Lit 1w] ["c"];
          mk_inst 1 JNZ [Var "c"; Label "left"; Label "right"] []] |>;
     <| bb_label := "left"; bb_instructions :=
         [mk_inst 2 ASSIGN [Lit 2w] ["a"];
          mk_inst 3 JMP [Label "join"] []] |>;
     <| bb_label := "right"; bb_instructions :=
         [mk_inst 4 ASSIGN [Lit 3w] ["b"];
          mk_inst 5 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
         [replay_phi; mk_inst 11 ISZERO [Var "p"] ["q"];
          mk_inst 12 STOP [] []] |>]
End

Theorem replay_diamond_entries_and_order:
  block_entries_ready (cfg_analyze replay_diamond) replay_diamond /\
  input_vars_from "left" [replay_phi] ["b"; "a"] = ["a"] /\
  input_vars_from "right" [replay_phi] ["b"; "a"] = ["b"] /\
  input_vars_from "left" [replay_phi] ["x"; "a"; "b"; "z"] =
    ["x"; "a"; "z"]
Proof
  EVAL_TAC
QED

Theorem replay_phi_same_slot_code:
  generate_phi_plan replay_phi ["p"] F
    ((init_plan_state 0) with ps_stack := [Var "a"]) =
    ([SOPoke 0 (Var "p")],
     (init_plan_state 0) with ps_stack := [Var "p"]) /\
  generate_phi_plan replay_phi ["p"] F
    ((init_plan_state 0) with ps_stack := [Var "b"]) =
    ([SOPoke 0 (Var "p")],
     (init_plan_state 0) with ps_stack := [Var "p"])
Proof
  EVAL_TAC
QED


Theorem replay_diamond_jump_layout:
  (SND (generate_regular_inst_plan (liveness_analyze replay_diamond)
    (dfg_build_function replay_diamond) (cfg_analyze replay_diamond)
    replay_diamond (mk_inst 3 JMP [Label "join"] []) ["a"; "b"] F F "left"
    ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = [Var "a"] /\
  (SND (generate_regular_inst_plan (liveness_analyze replay_diamond)
    (dfg_build_function replay_diamond) (cfg_analyze replay_diamond)
    replay_diamond (mk_inst 5 JMP [Label "join"] []) ["a"; "b"] F F "right"
    ((init_plan_state 0) with ps_stack := [Var "b"]))).ps_stack = [Var "b"]
Proof
  EVAL_TAC
QED

Definition replay_loop_phi_def:
  replay_loop_phi = mk_inst 20 PHI
    [Label "entry"; Var "a"; Label "back"; Var "b"] ["p"]
End

Definition replay_loop_def:
  replay_loop = mk_raw_function "loop"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 ASSIGN [Lit 1w] ["a"];
          mk_inst 1 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
         [replay_loop_phi;
          mk_inst 2 JNZ [Var "p"; Label "back"; Label "exit"] []] |>;
     <| bb_label := "back"; bb_instructions :=
         [mk_inst 3 ASSIGN [Lit 2w] ["b"];
          mk_inst 4 JMP [Label "join"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 5 STOP [] []] |>]
End

Theorem replay_loop_entries_and_phi:
  block_entries_ready (cfg_analyze replay_loop) replay_loop /\
  input_vars_from "entry" [replay_loop_phi] ["a"; "b"] = ["a"] /\
  input_vars_from "back" [replay_loop_phi] ["a"; "b"] = ["b"] /\
  generate_phi_plan replay_loop_phi ["p"] F
    ((init_plan_state 0) with ps_stack := [Var "b"]) =
    ([SOPoke 0 (Var "p")],
     (init_plan_state 0) with ps_stack := [Var "p"])
Proof
  EVAL_TAC
QED
