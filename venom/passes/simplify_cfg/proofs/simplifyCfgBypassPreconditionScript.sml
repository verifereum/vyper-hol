(* Preservation of the guarded pass contract under elementary bypass. *)
Theory simplifyCfgBypassPrecondition
Ancestors
  simplifyCfgBypassPhiClosure simplifyCfgBypassShape
  simplifyCfgBypassClosure simplifyCfgBypassPhi simplifyCfgBypassStatic
  simplifyCfgStaticInterface simplifyCfgMergeAvailability simplifyCfgDefs
  venomWf venomInst venomExecProofs venomExecProps cfgTransform list rich_list
  simplifyCfgPhiSemantics unitShapeDefs

Theorem scfg_bypass_normalized:
  scfg_bypass_hyp fn a b fn' ==> scfg_normalized fn'
Proof
  strip_tac >> drule scfg_bypass_base_hyp >> strip_tac >>
  rewrite_tac[scfg_normalized_def, scfg_static_def,
    simplifyCfgPhiRepairTheory.simplify_cfg_fn_ok_phi_safe] >>
  rpt conj_tac
  >- metis_tac[simplifyCfgStructTheory.do_merge_jump_wf]
  >- metis_tac[simplifyCfgReachusesTheory.do_merge_jump_fn_inst_wf]
  >- metis_tac[scfg_bypass_fn_shape, scfg_bypass_old_static, scfg_static_shape]
  >- metis_tac[simplifyCfgStructTheory.do_merge_jump_first_block_no_preds]
  >- metis_tac[simplifyCfgReachusesTheory.do_merge_jump_phi_safe]
  >- metis_tac[simplifyCfgBypassDataflowTheory.do_merge_jump_defs_reach_uses]
  >- metis_tac[scfg_bypass_all_reachable] >>
  metis_tac[scfg_bypass_phi_support]
QED
