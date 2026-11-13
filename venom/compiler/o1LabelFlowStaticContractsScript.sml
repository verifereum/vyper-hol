Theory o1LabelFlowStaticContracts
Ancestors
  o1PassContract o1ComposeSupport o1ContractLowerDloadStage
  o1ContractLowerDload o1ContractMakeSsaStep concretizeStepContract
  fmpStepContract o1DftStepAt o1ContractSimplifyCfg o1ContractSue
  o1ContractCfgNorm venomPassSchedule

Theorem label_flow_lower_dload_static[local]:
  o1_step_contract_at 1 rp (CFP_Simple VP_LowerDload)
Proof
  irule o1_step_contract_at_preserve >>
  simp[lower_dload_step_contract] >> metis_tac[lower_dload_fn_row]
QED

Theorem o1_label_flow_static_steps:
  o1_step_contracts_from rp 0 o1_fn_passes
Proof
  simp[o1_fn_passes_def, o1_step_contracts_from_def,
    make_ssa_step_contract_at, label_flow_lower_dload_static,
    concretize_step_contract_at, fmp_step_contract_at,
    o1_contract_simplify_cfg, o1_contract_sue,
    dft_step_contract_at, o1_contract_cfg_normalization]
QED

(* Publication check: structural contracts must not inherit dynamic oracles. *)
val _ = List.app (fn (n, th) =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in print ("LABEL_FLOW_AUDIT " ^ n ^ ": " ^
       String.concatWith "," (ors @ axs) ^ "\n") end)
  [("static_steps", o1_label_flow_static_steps),
   ("make_ssa", make_ssa_step_contract_at),
   ("lower_dload", label_flow_lower_dload_static),
   ("concretize", concretize_step_contract_at),
   ("fmp", fmp_step_contract_at),
   ("simplify_cfg", o1_contract_simplify_cfg),
   ("sue", o1_contract_sue),
   ("dft", dft_step_contract_at),
   ("cfg_norm", o1_contract_cfg_normalization)];
