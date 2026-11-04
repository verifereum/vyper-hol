(* Definite assignment transport for the exact chain contraction. *)
Theory simplifyCfgMergeAvailability
Ancestors
  simplifyCfgMergePaths simplifyCfgStaticInterface simplifyCfgDefs
  venomWf venomInst venomExecSemantics cfgTransform list rich_list

Theorem scfg_chain_old_pred_not_a:
  scfg_chain_hyp fn a b /\ fn_cfg_edge fn p l /\ l <> b.bb_label ==>
  p <> a.bb_label
Proof
  strip_tac >> strip_tac >> fs[fn_cfg_edge_def] >>
  `bb = a` by metis_tac[scfg_chain_hyp_def, scfg_chain_old_wf,
    venomExecProofsTheory.same_label_same_block, lookup_block_member_label] >>
  gvs[scfg_chain_hyp_def, can_merge_blocks_def]
QED

Theorem scfg_phi_pair_label:
  !ops p v. MEM (p,v) (phi_pairs ops) ==> MEM (Label p) ops
Proof
  recInduct phi_pairs_ind >> simp[phi_pairs_def] >> rpt strip_tac >> metis_tac[]
QED
