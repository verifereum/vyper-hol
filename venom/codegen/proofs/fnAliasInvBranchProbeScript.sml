Theory fnAliasInvBranchProbe
Ancestors
  stackPlanGen frameRel codegenRel unitShapeDefs codegenReadyCompute

Definition alias_branch_probe_fn_def:
  alias_branch_probe_fn = mk_raw_function "branch_probe"
    [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 CALLDATASIZE [] ["e"];
         mk_inst 1 JMP [Label "header"] []]|>;
     <|bb_label := "header"; bb_instructions :=
        [mk_inst 2 PHI [Label "entry"; Var "e"; Label "body"; Var "q"] ["r"];
         mk_inst 3 JMP [Label "body"] []]|>;
     <|bb_label := "body"; bb_instructions :=
        [mk_inst 4 ASSIGN [Var "r"] ["a"];
         mk_inst 5 ISZERO [Var "a"] ["z"];
         mk_inst 6 CALLDATASIZE [] ["q"];
         mk_inst 7 JNZ [Var "z"; Label "header"; Label "exit"] []]|>;
     <|bb_label := "exit"; bb_instructions :=
        [mk_inst 8 ISZERO [Var "a"] ["w"]; mk_inst 9 STOP [] []]|>]
End

Theorem alias_branch_probe_not_ready:
  ~codegen_ready_fn alias_branch_probe_fn
Proof
  EVAL_TAC
QED

Theorem alias_branch_probe_critical_edge:
  ~cfg_is_normalized (cfg_analyze alias_branch_probe_fn) alias_branch_probe_fn
Proof
  EVAL_TAC
QED
