Theory makeSsaCurrentPrefixContract
Ancestors
  makeSsaCurrentPrefixCompatibility makeSsaCurrentWfSsa venomWf venomInst

Definition current_prefix_shared_phi_fn_def:
  current_prefix_shared_phi_fn = <|
    fn_name := "probe";
    fn_blocks := [<|bb_label := "join"; bb_instructions :=
      [mk_inst 0 PHI [Label "left"; Var "src"; Label "right"; Var "src"] ["dst1"];
       mk_inst 1 PHI [Label "left"; Var "src"; Label "right"; Var "src"] ["dst2"]]|>];
    fn_call_abi := default_internal_call_abi;
    fn_noinline := F; fn_forced_alloc_positions := FEMPTY;
    fn_eom := NONE; fn_mems_used := []; fn_fmp_signature := NONE
  |>
End

Theorem current_prefix_shared_phi_rejected:
  ~fn_phis_non_degenerate current_prefix_shared_phi_fn
Proof
  simp[fn_phis_non_degenerate_def, current_prefix_shared_phi_fn_def,
    fn_insts_def, mk_inst_def, phi_pairs_def] >>
  qexistsl_tac [`mk_inst 0 PHI
    [Label "left"; Var "src"; Label "right"; Var "src"] ["dst1"]`, `"dst1"`] >>
  simp[mk_inst_def, phi_pairs_def] >> EVAL_TAC >> metis_tac[]
QED
