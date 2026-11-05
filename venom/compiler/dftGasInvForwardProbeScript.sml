Theory dftGasInvForwardProbe
Ancestors
  dftDefs contextCodegenRel

Definition forwarding_literal_def:
  forwarding_literal = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
     mk_inst 1 REVERT [Lit 0w; Lit 1w] []] |>
End

Theorem forwarding_literal_source:
  revert_forward_pair forwarding_literal 0 1
Proof
  EVAL_TAC >> simp[]
QED

Theorem forwarding_literal_schedule:
  MAP (\i. i.inst_id) (dft_block [] forwarding_literal).bb_instructions = [0;1]
Proof
  EVAL_TAC >> simp[]
QED

Theorem forwarding_literal_target:
  revert_forward_pair (dft_block [] forwarding_literal) 0 1
Proof
  EVAL_TAC >> simp[]
QED

Definition forwarding_alias_def:
  forwarding_alias = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ASSIGN [Lit 0w] ["addr"];
     mk_inst 1 ASSIGN [Lit 1w] ["len"];
     mk_inst 2 ASSIGN [Lit 0w] ["src"];
     mk_inst 3 RETURNDATACOPY [Var "addr"; Var "src"; Var "len"] [];
     mk_inst 4 ASSIGN [Var "addr"] ["addr2"];
     mk_inst 5 ASSIGN [Var "len"] ["len2"];
     mk_inst 6 REVERT [Var "addr2"; Var "len2"] []] |>
End

Theorem forwarding_alias_source:
  revert_forward_pair forwarding_alias 3 6
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >>
  `k = 4 \/ k = 5` by decide_tac >> gvs[]
QED

Theorem forwarding_alias_schedule:
  MAP (\i. i.inst_id) (dft_block [] forwarding_alias).bb_instructions =
  [1;2;0;3;5;4;6]
Proof
  EVAL_TAC >> simp[]
QED

Theorem forwarding_alias_target:
  revert_forward_pair (dft_block [] forwarding_alias) 3 6
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >>
  `k = 4 \/ k = 5` by decide_tac >> gvs[]
QED

Definition forwarding_producer_def:
  forwarding_producer = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ADD [Lit 2w; Lit 3w] ["unused"];
     mk_inst 1 ADD [Lit 0w; Lit 0w] ["addr"];
     mk_inst 2 RETURNDATACOPY [Var "addr"; Lit 0w; Lit 1w] [];
     mk_inst 3 ASSIGN [Var "addr"] ["addr2"];
     mk_inst 4 REVERT [Var "addr2"; Lit 1w] []] |>
End

Theorem forwarding_producer_source:
  revert_forward_pair forwarding_producer 2 4
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >>
  `k = 3` by decide_tac >> gvs[]
QED

Theorem forwarding_producer_schedule:
  MAP (\i. i.inst_id) (dft_block [] forwarding_producer).bb_instructions =
  [0;1;2;3;4]
Proof
  EVAL_TAC >> simp[]
QED

Theorem forwarding_producer_target:
  revert_forward_pair (dft_block [] forwarding_producer) 2 4
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >>
  `k = 3` by decide_tac >> gvs[]
QED
