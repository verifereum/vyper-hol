Theory simplifyCfgStalePhiProbe
Ancestors
  simplifyCfgStruct unitShapeDefs codegenReadyCompute

Definition stale_phi_input_def:
  stale_phi_input = mk_raw_function "A"
    [<| bb_label := "A"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit 1w] ["v"];
         mk_inst 1 JNZ [Label "X"; Label "B"; Label "B"] []] |>;
     <| bb_label := "B"; bb_instructions :=
        [mk_inst 2 JMP [Label "C"] []] |>;
     <| bb_label := "C"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit 2w] ["w"]; mk_inst 4 JMP [Label "X"] []] |>;
     <| bb_label := "X"; bb_instructions :=
        [mk_inst 5 PHI [Label "A"; Var "v"; Label "C"; Var "w"] ["z"];
         mk_inst 6 STOP [] []] |>]
End

Theorem stale_phi_input_antecedent:
  wf_ssa stale_phi_input /\ wf_function stale_phi_input /\
  fn_inst_wf stale_phi_input /\ first_block_no_preds stale_phi_input /\
  EVERY (\inst. inst.inst_opcode <> PHI)
    (HD stale_phi_input.fn_blocks).bb_instructions
Proof
  EVAL_TAC
QED

Theorem stale_phi_output_not_wf_ssa:
  ~wf_ssa (simplify_cfg_fn stale_phi_input)
Proof
  EVAL_TAC
QED

Definition stale_phi_output_def:
  stale_phi_output = mk_raw_function "A"
    [<| bb_label := "A"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit 1w] ["v"];
         mk_inst 3 ASSIGN [Lit 2w] ["w"]; mk_inst 4 JMP [Label "X"] []] |>;
     <| bb_label := "X"; bb_instructions :=
        [mk_inst 5 PHI [Label "A"; Var "v"; Label "A"; Var "w"] ["z"];
         mk_inst 6 STOP [] []] |>]
End

Theorem stale_phi_full_pass_result:
  simplify_cfg_fn stale_phi_input = stale_phi_output
Proof
  EVAL_TAC
QED

Theorem stale_phi_duplicate_predecessors:
  ~ALL_DISTINCT (MAP FST
    (phi_pairs (HD (EL 1 stale_phi_output.fn_blocks).bb_instructions).inst_operands))
Proof
  EVAL_TAC
QED

(* Exact frozen obligation refuted by the checked concrete witness above.
   A narrow exclusion of Label-valued JNZ conditions blocks this example;
   universal sufficiency of that additional condition is not asserted. *)
Theorem simplify_cfg_preserves_wf_ssa_counterexample:
  ?fn. wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
    first_block_no_preds fn /\
    EVERY (\inst. inst.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
    ~wf_ssa (simplify_cfg_fn fn)
Proof
  qexists `stale_phi_input` >>
  simp[stale_phi_input_antecedent, stale_phi_output_not_wf_ssa]
QED
