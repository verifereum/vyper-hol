(* Collapse observations retain payload through each recursive transformation. *)
Theory o1CodeEndCfgCollapse
Ancestors
  o1CodeEndCfgMerge o1CodeEndCfgBypass simplifyCfgCollapseSemantics
  simplifyCfgBypassWrapper simplifyCfgBypassPrecondition simplifyCfgLabelProps
  simplifyCfgDefs cfgTransform list rich_list simplifyCfgControl o1PassLift
  simplifyCfgSimTools simplifyCfgMergeSemantics simplifyCfgMergeClosure
  simplifyCfgMergePaths

Theorem scfg_frame_observation_refl[local]:
  !C s0 j t. fn_entry_state fn s0 /\ frame_reach C fn s0 j t /\
    j.inst_opcode <> PHI /\ ~is_terminator j.inst_opcode ==>
    ?s. frame_reach C fn s0 j s /\ scfg_payload s t
Proof
  rpt strip_tac >> qexists_tac `t` >> simp[]
QED

Theorem scfg_try_bypass_frame_observation[local]:
  scfg_normalized fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  try_bypass fn lm bb candidates = (fn',lm',changed) ==>
  !C s0 j t. fn_entry_state fn s0 /\ frame_reach C fn' s0 j t /\
    j.inst_opcode <> PHI /\ ~is_terminator j.inst_opcode ==>
    ?s. frame_reach C fn s0 j s /\ scfg_payload s t
Proof
  strip_tac >> drule_all scfg_try_bypass_choice >> strip_tac
  >- (gvs[] >> metis_tac[scfg_payload_refl]) >>
  metis_tac[scfg_bypass_frame_observation, ctx_bisim_refl]
QED

Theorem scfg_collapse_frame_observation_joint:
  (!fn lm visited lbl. scfg_normalized fn ==>
    !C s0 j t. fn_entry_state fn s0 /\
    frame_reach C (FST (collapse_dfs fn lm visited lbl)) s0 j t /\
    j.inst_opcode <> PHI /\ ~is_terminator j.inst_opcode ==>
    ?s. frame_reach C fn s0 j s /\ scfg_payload s t) /\
  (!fn lm visited succs. scfg_normalized fn ==>
    !C s0 j t. fn_entry_state fn s0 /\
    frame_reach C (FST (collapse_dfs_succs fn lm visited succs)) s0 j t /\
    j.inst_opcode <> PHI /\ ~is_terminator j.inst_opcode ==>
    ?s. frame_reach C fn s0 j s /\ scfg_payload s t)
Proof
  ho_match_mp_tac collapse_dfs_ind >> rpt conj_tac
  >- suspend "dfs"
  >- suspend "nil"
  >> suspend "succs"
QED

Resume scfg_collapse_frame_observation_joint[dfs]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[NoAsms, Once collapse_dfs_def] >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- (simp[] >> rpt strip_tac >> qexists_tac `t` >> simp[]) >>
  rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_member_label] >>
  namedCases_on `bb_succs bb` ["", "s1 rest"]
  >- (Cases_on `MEM lbl visited`
      >- simp[try_bypass_def, scfg_frame_observation_refl] >>
      gvs[try_bypass_def]) >>
  namedCases_on `rest` ["", "s2 rest2"]
  >- (Cases_on `lookup_block s1 fn.fn_blocks`
      >- (Cases_on `MEM lbl visited` >> simp[scfg_frame_observation_refl]) >>
      rename1 `lookup_block s1 fn.fn_blocks = SOME next_bb` >>
      Cases_on `can_merge_blocks fn bb next_bb`
      >- suspend "merge" >>
      Cases_on `MEM lbl visited`
      >- simp[scfg_frame_observation_refl] >> gvs[]) >>
  suspend "bypass"
QED

Resume scfg_collapse_frame_observation_joint[merge]:
  gvs[] >>
  `next_bb.bb_label = s1` by metis_tac[lookup_block_member_label] >>
  `scfg_chain_hyp fn bb next_bb` by
    (simp[scfg_chain_hyp_def] >> metis_tac[]) >>
  `scfg_normalized (scfg_chain fn bb next_bb)` by
    metis_tac[scfg_chain_normalized] >>
  `fn_entry_label (scfg_chain fn bb next_bb) = fn_entry_label fn` by
    metis_tac[scfg_chain_entry_eq] >>
  gvs[GSYM scfg_chain_def] >>
  rpt strip_tac >>
  `fn_entry_state (scfg_chain fn bb next_bb) s0` by
    fs[fn_entry_state_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all scfg_merge_frame_observation >>
  metis_tac[scfg_payload_trans]
QED

Resume scfg_collapse_frame_observation_joint[bypass]:
  Cases_on `try_bypass fn lm bb (s1::s2::rest2)` >> PairCases_on `r` >>
  `scfg_collapse_contract fn q` by
    (irule scfg_collapse_bypass >> simp[] >>
     qexistsl_tac [`bb`, `s1::s2::rest2`, `r1`, `lm`, `r0`] >> simp[]) >>
  `scfg_normalized q /\ fn_entry_label q = fn_entry_label fn` by
    fs[scfg_collapse_contract_def] >>
  `!C s0 j t. fn_entry_state fn s0 /\ frame_reach C q s0 j t /\
     j.inst_opcode <> PHI /\ ~is_terminator j.inst_opcode ==>
     ?s. frame_reach C fn s0 j s /\ scfg_payload s t` by
    (rpt strip_tac >> irule scfg_try_bypass_frame_observation >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  Cases_on `r1` >> gvs[]
  >- suspend "bypass_changed" >>
  Cases_on `MEM bb.bb_label visited` >> gvs[] >>
  suspend "bypass_succs"
QED

Resume scfg_collapse_frame_observation_joint[bypass_changed]:
  rpt strip_tac >>
  `fn_entry_state q s0` by fs[fn_entry_state_def] >>
  qpat_x_assum `!C s0 j t. _ /\ frame_reach C (FST _) _ _ _ /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  first_x_assum drule_all >>
  metis_tac[scfg_payload_trans]
QED

Resume scfg_collapse_frame_observation_joint[bypass_succs]:
  rpt strip_tac >>
  `fn_entry_state q s0` by fs[fn_entry_state_def] >>
  qpat_x_assum `!C s0 j t. _ /\ frame_reach C (FST _) _ _ _ /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  first_x_assum drule_all >>
  metis_tac[scfg_payload_trans]
QED

Resume scfg_collapse_frame_observation_joint[nil]:
  simp[collapse_dfs_def, scfg_frame_observation_refl]
QED

Resume scfg_collapse_frame_observation_joint[succs]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once collapse_dfs_def] >>
  Cases_on `collapse_dfs fn lm visited lbl` >> PairCases_on `r` >>
  gvs[] >>
  `scfg_collapse_contract fn q` by metis_tac[scfg_collapse_joint, pairTheory.FST] >>
  `scfg_normalized q /\ fn_entry_label q = fn_entry_label fn` by
    fs[scfg_collapse_contract_def] >>
  rpt strip_tac >>
  `fn_entry_state q s0` by fs[fn_entry_state_def] >>
  qpat_x_assum `scfg_normalized q ==> _`
    (drule_all_then strip_assume_tac) >>
  first_x_assum drule_all >>
  metis_tac[scfg_payload_trans]
QED

Finalise scfg_collapse_frame_observation_joint
