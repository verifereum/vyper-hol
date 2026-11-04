(* Concrete reachable-spill candidate. No dependency on the admitted target. *)
Theory fnPlanLineageDiamondChecks
Ancestors
  stackPlanGen venomWf callLayoutDefs passSharedDefs codegenReadyCompute
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset;
val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY]);

Definition diamond_vars_def:
  diamond_vars = ["x0"; "x1"; "x2"; "x3"; "x4"; "x5"; "x6"; "x7";
    "x8"; "x9"; "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"]
End

Definition diamond_fn_def:
  diamond_fn = mk_raw_function "diamond_spill"
    [<| bb_label := "E"; bb_instructions :=
        MAPi (\i v. mk_inst i PARAM [Lit (n2w i)] [v])
          (["z"] ++ diamond_vars ++ ["c"]) ++
        [mk_inst 19 JNZ [Var "c"; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions :=
        [mk_inst 20 MSTORE [Lit 0w; Var "z"] [];
         mk_inst 21 JMP [Label "J"] []] |>;
     <| bb_label := "B"; bb_instructions :=
        [mk_inst 22 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        MAPi (\i v. mk_inst (23+i) MSTORE [Lit 0w; Var v] []) diamond_vars ++
        [mk_inst 40 STOP [] []] |>]
End

Theorem diamond_static_ready:
  codegen_ready_fn diamond_fn
Proof
  EVAL_TAC
QED

Theorem diamond_no_marker:
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) diamond_fn.fn_blocks
Proof
  EVAL_TAC
QED

Definition diamond_live_def:
  diamond_live = liveness_analyze diamond_fn
End
Definition diamond_dfg_def:
  diamond_dfg = dfg_build_function diamond_fn
End
Definition diamond_cfg_def:
  diamond_cfg = cfg_analyze diamond_fn
End

Theorem diamond_operand_order:
  compute_operands (mk_inst 20 MSTORE [Lit 0w; Var "z"] []) =
    [Var "z"; Lit 0w]
Proof
  EVAL_TAC
QED

Theorem diamond_live_J:
  live_vars_at diamond_live "J" 0 = REVERSE diamond_vars
Proof
  EVAL_TAC
QED

Theorem diamond_cfg_edges:
  cfg_succs_of diamond_cfg "E" = ["B"; "A"] /\
  cfg_succs_of diamond_cfg "A" = ["J"] /\
  cfg_succs_of diamond_cfg "B" = ["J"] /\
  cfg_succs_of diamond_cfg "J" = [] /\
  cfg_preds_of diamond_cfg "J" = ["A"; "B"]
Proof
  EVAL_TAC
QED

Theorem diamond_live_edges:
  live_vars_at diamond_live "A" 0 = REVERSE diamond_vars ++ ["z"] /\
  live_vars_at diamond_live "B" 0 = REVERSE diamond_vars /\
  live_vars_at diamond_live "A" 1 = REVERSE diamond_vars /\
  live_vars_at diamond_live "E" 20 = REVERSE diamond_vars ++ ["z"]
Proof
  EVAL_TAC
QED
