(* Definite-assignment transport through PHI fixup. *)
Theory simplifyCfgFixupClosure
Ancestors
  simplifyCfgFixupStatic simplifyCfgRestriction simplifyCfgPhiBlockSemantics
  simplifyCfgPhiSemantics simplifyCfgLabelProps simplifyCfgDefs venomWf venomInst
  venomExecProofs venomExecSemantics analysisSimProofsBase cfgTransform arithmetic list rich_list
  simplifyCfgStruct simplifyCfgReachuses simplifyCfgRepairDataflow simplifyCfgPhiRepair simplifyCfgDataflow cfgWf

Theorem scfg_restriction_fix_phis_wf:
  wf_function fn ==> wf_function (fix_all_phis (remove_unreachable_blocks fn))
Proof
  metis_tac[fix_all_phis_wf, remove_unreachable_blocks_wf]
QED

Theorem scfg_restriction_fix_phis_inst_wf:
  fn_inst_wf fn ==> fn_inst_wf (fix_all_phis (remove_unreachable_blocks fn))
Proof
  metis_tac[simplifyCfgReachusesTheory.fix_all_phis_fn_inst_wf,
            simplifyCfgDefsTheory.remove_unreachable_blocks_fn_inst_wf]
QED

Theorem scfg_fix_phi_retained_opcode:
  (fix_phi_inst actual_preds inst).inst_opcode = PHI ==> inst.inst_opcode = PHI
Proof
  Cases_on `inst.inst_opcode = PHI` >> simp[fix_phi_inst_def]
QED

Theorem scfg_restriction_fix_phis_ok:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn ==>
  simplify_cfg_fn_ok (fix_all_phis (remove_unreachable_blocks fn))
Proof
  rewrite_tac[simplify_cfg_fn_ok_phi_safe] >> strip_tac >>
  qabbrev_tac `r = remove_unreachable_blocks fn` >>
  `wf_function r /\ fn_inst_wf r /\ all_reachable r /\ scfg_phi_safe r /\
   fn_defs_reach_uses r` by
    simp[Abbr `r`, remove_unreachable_blocks_wf,
         simplifyCfgDefsTheory.remove_unreachable_blocks_fn_inst_wf,
         remove_unreachable_blocks_reachable, remove_unreachable_blocks_phi_safe,
         remove_unreachable_blocks_defs_reach_uses] >>
  simp[fix_all_phis_phi_safe, fix_all_phis_defs_reach_uses]
QED
