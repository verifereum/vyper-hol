Theory fnLineageInvFanoutProbe
Ancestors
  fnLineageInvTerminal fnPlanLineage codegenReadyCompute cfgTransform
  stackPlanGen livenessDefs venomInst
Libs wordsLib

Definition fanout_vars_def:
  fanout_vars = ["p0"; "p1"; "p2"; "p3"; "p4"; "p5"; "p6"; "p7";
    "p8"; "p9"; "p10"; "p11"; "p12"; "p13"; "p14"; "p15"; "p16"; "p17"]
End

Definition fanout_fn_def:
  fanout_fn = mk_raw_function "fanout"
    [<| bb_label := "E"; bb_instructions :=
        [mk_inst 0 ADD [Lit 1w; Lit 2w] ["x"];
         mk_inst 1 JNZ [Lit 1w; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions :=
        [mk_inst 2 JMP [Label "J"] []] |>;
     <| bb_label := "B"; bb_instructions :=
        [mk_inst 3 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        MAPi (\i v. mk_inst (4+i) PHI
          [Label "A"; Var "x"; Label "B"; Var "x"] [v]) fanout_vars ++
        MAPi (\i v. mk_inst (22+i) ADD [Var v; Lit 1w] ["u" ++ v]) fanout_vars ++
        [mk_inst 40 STOP [] []] |>]
End

(* Repeated incoming x is forbidden by readiness, before any plan runs. *)
Theorem fanout_readiness_obstruction:
  ~phi_uses_disjoint
    (collect_phis (EL 3 fanout_fn.fn_blocks).bb_instructions) /\
  ~phi_operands_ready fanout_fn /\ ~codegen_ready_fn fanout_fn
Proof
  EVAL_TAC
QED
