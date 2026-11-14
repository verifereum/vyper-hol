(* PHI fixup introduces ASSIGNs, but all other observations retain the
   identical instruction and state. This covers DLOAD and code_end ADDs. *)
Theory o1CodeEndCfgCleanup
Ancestors
  simplifyCfgFrameRf simplifyCfgRestrictionSemantics simplifyCfgFixupFrames
  simplifyCfgCleanup o1CodeEndCfgBoundary simplifyCfgStruct
  simplifyCfgFramePrefixes simplifyCfgFixupRuns simplifyCfgFixupSemantics
  simplifyCfgFragments simplifyCfgRestriction simplifyCfgDefs venomWf
  o1PassLift venomInst

Theorem o1_code_end_fix_all_phis_reach_back:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s0 /\ frame_reach C (fix_all_phis fn) s0 j t /\
  j.inst_opcode <> ASSIGN ==>
  frame_reach C fn s0 j t
Proof
  strip_tac >>
  `wf_function (fix_all_phis fn)` by metis_tac[fix_all_phis_wf] >>
  drule_all scfg_frame_reach_decompose >> strip_tac >>
  `scfg_bprefix C fn s0 s` by
    (irule scfg_fix_all_phis_bprefix_backward >> simp[] >>
     metis_tac[scfg_bprefix_rules]) >>
  qpat_x_assum `lookup_block _ _ = _` mp_tac >>
  rewrite_tac[scfg_fix_all_phis_lookup] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  strip_tac >> gvs[] >>
  irule scfg_rooted_fix_phis_nonassign_reach >> simp[] >> metis_tac[]
QED

Theorem o1_code_end_cleanup_reach_back:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  fn_entry_state fn s0 /\
  frame_reach C (fix_all_phis (remove_unreachable_blocks fn)) s0 j t /\
  j.inst_opcode <> ASSIGN ==>
  frame_reach C fn s0 j t
Proof
  strip_tac >>
  `frame_reach C (remove_unreachable_blocks fn) s0 j t` by
    (irule o1_code_end_fix_all_phis_reach_back >>
     simp[remove_unreachable_blocks_wf,
       simplifyCfgDefsTheory.remove_unreachable_blocks_fn_inst_wf,
       scfg_restriction_ok] >> conj_tac
     >- (rpt strip_tac >> irule scfg_restriction_blocks_reachable >>
         Cases_on `fn.fn_blocks` >>
         fs[wf_function_def, fn_has_entry_def, fn_entry_label_def,
            entry_block_def] >> metis_tac[]) >>
     gvs[fn_entry_state_def, remove_unreachable_blocks_entry]) >>
  irule scfg_restriction_frame_reach_back >> simp[] >>
  fs[wf_function_def]
QED
