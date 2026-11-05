(* Small checked interfaces for the RET residual-inventory investigation. *)
Theory fnBlockPlanStaticRet
Ancestors
  fnPlanLineage stackPlanGen stackPlanTypes venomInst venomWf livenessDefs
  dfgDefs cfgDefs
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset;
val () = computeLib.add_persistent_funs ["stackModel.stack_find_def"];

Definition ret_probe_bb_def:
  ret_probe_bb = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 OFFSET [Lit 0w; Label "entry"] ["x"];
     mk_inst 1 ASSERT [Var "x"] [];
     mk_inst 2 RET [Lit 0w] []] |>
End

Definition ret_probe_fn_def:
  ret_probe_fn = mk_raw_function "f" [ret_probe_bb]
End

Theorem ret_probe_offset_consumed:
  ?ops ps'.
    generate_block_plan (liveness_analyze ret_probe_fn)
      (dfg_build_function ret_probe_fn) (cfg_analyze ret_probe_fn)
      ret_probe_fn ret_probe_bb (init_cleanup_plan_state NONE [] 0 0) =
        SOME (ops, ps') /\ ps'.ps_stack = []
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Definition ret_cleanup_probe_fn_def:
  ret_cleanup_probe_fn = mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 JNZ [Var "cond"; Label "ret"; Label "other"] []] |>;
     <| bb_label := "ret"; bb_instructions := [mk_inst 1 RET [Lit 0w] []] |>;
     <| bb_label := "other"; bb_instructions := [mk_inst 2 STOP [] []] |>]
End

Definition ret_cleanup_probe_live_def:
  ret_cleanup_probe_live = <|
    ds_inst := FEMPTY |+ (("entry",1), ["dead"]);
    ds_boundary := FEMPTY |>
End

Definition ret_cleanup_probe_state_def:
  ret_cleanup_probe_state = (init_plan_state 0) with ps_stack := [Var "dead"]
End

Theorem ret_probe_cleanup_observable:
  clean_stack_plan ret_cleanup_probe_live (cfg_analyze ret_cleanup_probe_fn)
    ret_cleanup_probe_fn (EL 1 ret_cleanup_probe_fn.fn_blocks)
    ret_cleanup_probe_state =
      ([SOPop 1], ret_cleanup_probe_state with ps_stack := []) /\
  clean_stack_plan ret_cleanup_probe_live (cfg_analyze ret_cleanup_probe_fn)
    ret_cleanup_probe_fn (EL 1 ret_cleanup_probe_fn.fn_blocks)
    (ret_cleanup_probe_state with ps_cleanup_promised := T) =
      ([], ret_cleanup_probe_state with
        <| ps_stack := [dead_stack_marker]; ps_cleanup_promised := T |>)
Proof
  EVAL_TAC
QED
