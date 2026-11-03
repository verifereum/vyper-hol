Theory simplifyCfgPhiPredsProbe
Ancestors
  list venomInst venomWf cfgTransform simplifyCfgDefs simplifyCfgPhiPreds
  simplifyCfgChainProbe unitShapeDefs codegenReadyCompute

(* Repair removes the ignored nonedge pair before any contraction. *)
Theorem chain_extra_phi_repair_probe:
  (EL 0 (EL 2 (fix_all_phis chain_extra_phi_fn).fn_blocks).bb_instructions).inst_opcode = ASSIGN /\
  (EL 0 (EL 2 (fix_all_phis chain_extra_phi_fn).fn_blocks).bb_instructions).inst_operands = [Var "x"] /\
  ~MEM ("a", "z")
    (phi_pairs (EL 0 (EL 2 (fix_all_phis chain_extra_phi_fn).fn_blocks).bb_instructions).inst_operands)
Proof
  EVAL_TAC
QED

Theorem chain_extra_phi_repaired_preds:
  scfg_phi_preds (fix_all_phis chain_extra_phi_fn)
Proof
  irule fix_all_phis_phi_preds >>
  metis_tac[chain_extra_phi_edge_probe]
QED
