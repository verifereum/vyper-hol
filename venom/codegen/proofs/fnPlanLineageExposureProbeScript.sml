Theory fnPlanLineageExposureProbe
Ancestors
  codegenReadyCompute stackPlanGen livenessDefs venomInst cfgTransform list
Libs wordsLib

(* Directed temporal-exposure candidate: retain the incoming base x through
   a cyclic PHI, then query x in the body.  Before adding selective-spill
   pressure, check the required PHI boundary.  This is a diagnostic only,
   not a counterexample to lineage_state_block_plan. *)
Definition exposure_probe_fn_def:
  exposure_probe_fn = mk_raw_function "exposure_probe"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit 1w] ["seed"];
         mk_inst 1 JMP [Label "H"] []] |>;
     <| bb_label := "H"; bb_instructions :=
        [mk_inst 2 PHI [Label "entry"; Var "seed"; Label "latch"; Var "x"] ["x"];
         mk_inst 3 JNZ [Lit 1w; Label "body"; Label "exit"] []] |>;
     <| bb_label := "body"; bb_instructions :=
        [mk_inst 4 ISZERO [Var "x"] ["out"];
         mk_inst 5 JMP [Label "latch"] []] |>;
     <| bb_label := "latch"; bb_instructions :=
        [mk_inst 6 JMP [Label "H"] []] |>;
     <| bb_label := "exit"; bb_instructions :=
        [mk_inst 7 STOP [] []] |>]
End

Theorem exposure_probe_live_base:
  MEM "x" (live_vars_at (liveness_analyze exposure_probe_fn) "H" 1)
Proof
  EVAL_TAC
QED

Theorem exposure_probe_phi_input:
  MEM "x" (inst_uses (HD (EL 1 exposure_probe_fn.fn_blocks).bb_instructions))
Proof
  EVAL_TAC
QED

Theorem exposure_probe_readiness_obstruction:
  ~phi_block_ready (liveness_analyze exposure_probe_fn)
    (EL 1 exposure_probe_fn.fn_blocks)
Proof
  EVAL_TAC
QED

Theorem exposure_probe_not_ready:
  ~codegen_ready_fn exposure_probe_fn
Proof
  EVAL_TAC
QED
