Theory singleUseExpansionSupplyChecks
Ancestors singleUseExpansionDefs irSupply venomInst finite_map list

Theorem sue_supply_two_literals_witness:
  MAP (\i. i.inst_operands)
    (FST (sue_expand_inst_supply dfg
      <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
         irs_used_inst_ids := []; irs_used_vars := []; irs_used_labels := [] |>
      <| inst_id := 1; inst_opcode := ADD;
         inst_operands := [Lit 3w; Lit 4w]; inst_outputs := ["out"] |>)) =
    [[Lit 3w]; [Lit 4w]; [Var "formal_var_1"; Var "formal_var_0"]]
Proof
  EVAL_TAC
QED

Theorem sue_supply_phi_witness:
  sue_expand_inst_supply dfg s
    <| inst_id := 1; inst_opcode := PHI;
       inst_operands := [Label "pred"; Var "x"]; inst_outputs := ["y"] |> =
  ([<| inst_id := 1; inst_opcode := PHI;
       inst_operands := [Label "pred"; Var "x"]; inst_outputs := ["y"] |>],s)
Proof
  simp[sue_expand_inst_supply_def, sue_should_skip_def]
QED

Theorem sue_supply_ignored_operand_witness:
  MAP (\i. i.inst_operands)
    (FST (sue_expand_inst_supply
      (dfg_empty with dfg_uses := FEMPTY |+ ("x",
        [<| inst_id := 1; inst_opcode := CALLER;
            inst_operands := [Var "x"]; inst_outputs := ["y"] |>;
         <| inst_id := 2; inst_opcode := CALLER;
            inst_operands := [Var "x"]; inst_outputs := ["z"] |>]))
      <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
         irs_used_inst_ids := [1;2]; irs_used_vars := ["x";"y";"z"];
         irs_used_labels := [] |>
      <| inst_id := 1; inst_opcode := CALLER;
         inst_operands := [Var "x"]; inst_outputs := ["y"] |>)) =
    [[Var "x"]; [Var "formal_var_0"]]
Proof
  EVAL_TAC
QED

Theorem sue_supply_repeated_variable_witness:
  MAP (\i. i.inst_operands)
    (FST (sue_expand_inst_supply
      (dfg_empty with dfg_uses := FEMPTY |+ ("x",
        [<| inst_id := 1; inst_opcode := ADD;
            inst_operands := [Var "x"; Var "x"]; inst_outputs := ["y"] |>;
         <| inst_id := 2; inst_opcode := STOP;
            inst_operands := [Var "x"]; inst_outputs := [] |>]))
      <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
         irs_used_inst_ids := [1;2]; irs_used_vars := ["x";"y"];
         irs_used_labels := [] |>
      <| inst_id := 1; inst_opcode := ADD;
         inst_operands := [Var "x"; Var "x"]; inst_outputs := ["y"] |>)) =
    [[Var "x"]; [Var "x"]; [Var "formal_var_1"; Var "formal_var_0"]]
Proof
  EVAL_TAC
QED

Theorem sue_supply_skip_opcodes:
  sue_should_skip PHI /\ sue_should_skip PARAM /\
  sue_should_skip FMP_PARAM /\ sue_should_skip RETPC_PARAM
Proof
  EVAL_TAC
QED

Theorem sue_supply_alloca_literal_witness:
  MAP (\i. i.inst_operands)
    (FST (sue_expand_inst_supply dfg
      <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
         irs_used_inst_ids := []; irs_used_vars := []; irs_used_labels := [] |>
      <| inst_id := 1; inst_opcode := ALLOCA;
         inst_operands := [Lit 32w]; inst_outputs := ["out"] |>)) =
    [[Lit 32w]; [Var "formal_var_0"]]
Proof
  EVAL_TAC
QED
