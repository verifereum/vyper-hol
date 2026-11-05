Theory fnLineageInvReadinessProbe
Ancestors stackPlanGen venomInst cfgTransform

(* The earlier residual diagnostic predates offset_outputs_used.  Keep its
   concrete value inline so this check does not depend on its stale proof. *)
Theorem residual_literal_not_offset_ready:
  ~offset_outputs_used (mk_raw_function "residual"
    [<| bb_label := "E"; bb_instructions :=
        [mk_inst 0 PARAM [Lit 0w] ["c"];
         mk_inst 1 PARAM [Lit 1w] ["v"];
         mk_inst 2 JNZ [Var "c"; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions :=
        [mk_inst 3 OFFSET [Lit 0w; Label "J"] ["r"];
         mk_inst 4 JMP [Label "J"] []] |>;
     <| bb_label := "B"; bb_instructions :=
        [mk_inst 5 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        [mk_inst 6 RETURN [Var "v"; Lit 0w] []] |>])
Proof
  EVAL_TAC
QED

Theorem residual_literal_not_codegen_ready:
  ~codegen_ready_fn (mk_raw_function "residual"
    [<| bb_label := "E"; bb_instructions :=
        [mk_inst 0 PARAM [Lit 0w] ["c"];
         mk_inst 1 PARAM [Lit 1w] ["v"];
         mk_inst 2 JNZ [Var "c"; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions :=
        [mk_inst 3 OFFSET [Lit 0w; Label "J"] ["r"];
         mk_inst 4 JMP [Label "J"] []] |>;
     <| bb_label := "B"; bb_instructions :=
        [mk_inst 5 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        [mk_inst 6 RETURN [Var "v"; Lit 0w] []] |>])
Proof
  pure_rewrite_tac [codegen_ready_fn_def, residual_literal_not_offset_ready,
             AND_CLAUSES, NOT_CLAUSES]
QED
