Theory concretizePtrSingletonOriginProbe
Ancestors concretizeMemLocDefs frameOriginReachable venomWf cfgWf words
Libs wordsLib

Definition sop_callee_def:
  sop_callee = mk_raw_function "leaf"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 100 PARAM [Lit 0w] ["p"];
       mk_inst 101 ALLOCA [Lit 32w] ["b"];
       mk_inst 102 MSTORE [Var "p"; Lit 7w] [];
       mk_inst 103 MSTORE [Var "b"; Lit 9w] [];
       mk_inst 104 RET [Lit 0w] []] |>]
End

Definition sop_caller_def:
  sop_caller = mk_raw_function "main"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 1 ALLOCA [Lit 32w] ["a"];
       mk_inst 2 MSTORE [Var "a"; Lit 1w] [];
       mk_inst 3 INVOKE [Label "leaf"; Var "a"] [];
       mk_inst 4 INVOKE [Label "leaf"; Var "a"] [];
       mk_inst 5 MLOAD [Var "a"] ["r"];
       mk_inst 6 STOP [] []] |>]
End

Definition sop_ctx_def:
  sop_ctx = mk_venom_context [sop_callee; sop_caller] (SOME "main")
End

Definition sop_bp_def:
  sop_bp fn = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn
End

Theorem sop_production_bp:
  bp_get_ptrs (sop_bp sop_callee) "b" = [Ptr (Allocation 101) (SOME 0)] /\
  bp_get_ptrs (sop_bp sop_callee) "p" = [] /\
  SND (bp_one_pass sop_callee (cfg_analyze sop_callee).cfg_dfs_pre
    (sop_bp sop_callee)) = sop_bp sop_callee
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Definition sop_initial_def:
  sop_initial = (init_venom_state "entry") with vs_alloca_next := 256
End

Theorem sop_decode_call:
  decode_invoke (EL 2 (HD sop_caller.fn_blocks).bb_instructions) =
    SOME ("leaf", [Var "a"])
Proof
  EVAL_TAC
QED

Theorem sop_shape_checks:
  ssa_form sop_caller /\ ssa_form sop_callee /\
  all_reachable sop_caller /\ all_reachable sop_callee
Proof
  EVAL_TAC >> simp[relationTheory.RTC_REFL]
QED

Theorem sop_entry:
  origin_frame_reachable sop_initial sop_ctx [] [] FEMPTY entry_taint
    sop_caller (HD (HD sop_caller.fn_blocks).bb_instructions)
    sop_initial [] FEMPTY
Proof
  irule origin_frame_reachable_entry >>
  conj_tac >- (qexists `"main"` >> EVAL_TAC) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  qexists `"entry"` >> EVAL_TAC >>
  simp[venomExecSemanticsTheory.eval_phis_def,
       venomExecSemanticsTheory.phi_prefix_length_def]
QED
