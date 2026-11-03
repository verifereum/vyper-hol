Theory simplifyCfgChainProbe
Ancestors
  simplifyCfgChainDataflow unitShapeDefs codegenReadyCompute

(* An extra, non-edge PHI input acquires a genuine edge after contraction.
   Initial fix_all_phis removes this input, but the unrestricted local
   chain-merge preservation interface must not assume that implicitly. *)
Definition chain_extra_phi_fn_def:
  chain_extra_phi_fn = mk_raw_function "a"
    [<| bb_label := "a"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit 0w] ["x"]; mk_inst 1 JMP [Label "b"] []] |>;
     <| bb_label := "b"; bb_instructions := [mk_inst 2 JMP [Label "c"] []] |>;
     <| bb_label := "c"; bb_instructions :=
        [mk_inst 3 PHI [Label "b"; Var "x"; Label "a"; Var "z"] ["y"];
         mk_inst 4 STOP [] []] |>]
End

Definition chain_extra_phi_out_def:
  chain_extra_phi_out = chain_extra_phi_fn with fn_blocks :=
    update_succ_phi_labels "b" "a"
      (replace_block "a"
        (merge_blocks (EL 0 chain_extra_phi_fn.fn_blocks) (EL 1 chain_extra_phi_fn.fn_blocks))
        (remove_block "b" chain_extra_phi_fn.fn_blocks)) ["c"]
End

Theorem chain_extra_phi_edge_probe:
  wf_function chain_extra_phi_fn /\ fn_inst_wf chain_extra_phi_fn /\
  first_block_no_preds chain_extra_phi_fn /\
  can_merge_blocks chain_extra_phi_fn
    (EL 0 chain_extra_phi_fn.fn_blocks) (EL 1 chain_extra_phi_fn.fn_blocks) /\
  ~fn_cfg_edge chain_extra_phi_fn "a" "c" /\
  fn_cfg_edge chain_extra_phi_out "a" "c" /\
  MEM ("a", "z") (phi_pairs (EL 0 (EL 2 chain_extra_phi_fn.fn_blocks).bb_instructions).inst_operands) /\
  MEM ("a", "z") (phi_pairs (EL 0 (EL 1 chain_extra_phi_out.fn_blocks).bb_instructions).inst_operands)
Proof
  EVAL_TAC >> simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC >>
  rpt strip_tac >> spose_not_then strip_assume_tac >> gvs[] >>
  qpat_x_assum `_ ==> _ ==> bb = _`
    (strip_assume_tac o REWRITE_RULE [IMP_DISJ_THM]) >>
  gvs[venomInstTheory.is_terminator_def, venomStateTheory.get_label_def, listTheory.REV_DEF]
QED

Theorem chain_extra_phi_endpoint_probe:
  ~def_on_all_paths chain_extra_phi_out (EL 0 chain_extra_phi_out.fn_blocks) NONE "z"
Proof
  simp[venomWfTheory.def_on_all_paths_def] >> qexists `["a"]` >> EVAL_TAC >>
  simp[] >> gen_tac >> `i = 0 \/ i = 1 \/ 2 <= i` by decide_tac >> gvs[]
QED
