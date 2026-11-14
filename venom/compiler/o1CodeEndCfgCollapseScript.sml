(* Collapse observations retain payload through each recursive transformation. *)
Theory o1CodeEndCfgCollapse
Ancestors
  simplifyCfgMergeSemantics o1CodeEndCfgBypass simplifyCfgCollapseSemantics
  simplifyCfgBypassWrapper simplifyCfgBypassPrecondition simplifyCfgLabelProps
  simplifyCfgDefs cfgTransform list rich_list simplifyCfgControl o1PassLift
  simplifyCfgSimTools simplifyCfgMergeClosure
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
  mp_tac (Q.INST [`R` |-> `\f g. scfg_collapse_contract f g /\
    !C s0 j t. fn_entry_state f s0 /\ frame_reach C g s0 j t /\
      j.inst_opcode <> PHI /\ ~is_terminator j.inst_opcode ==>
      ?s. frame_reach C f s0 j s /\ scfg_payload s t`]
    scfg_collapse_joint_relation) >> BETA_TAC >>
  (impl_tac >-
    (rpt conj_tac
     >- metis_tac[scfg_collapse_contract_refl, scfg_frame_observation_refl]
     >- (qx_genl_tac [`f`,`g`,`h`] >> strip_tac >> conj_tac
         >- metis_tac[scfg_collapse_contract_trans] >>
         rpt strip_tac >>
         `fn_entry_state g s0` by fs[fn_entry_state_def, scfg_collapse_contract_def] >>
         metis_tac[scfg_payload_trans])
     >- simp[scfg_collapse_contract_def]
     >- metis_tac[scfg_collapse_chain, scfg_merge_frame_observation]
     >> metis_tac[scfg_collapse_bypass, scfg_try_bypass_frame_observation])) >>
  metis_tac[]
QED
