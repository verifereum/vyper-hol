(* Rooted PHI entry is the only boundary exposing entry implementation. *)
Theory simplifyCfgBypassRootedEntry
Ancestors
  simplifyCfgBypassRuns simplifyCfgBypassEntry simplifyCfgBypassClosure
  simplifyCfgBypassPrecondition simplifyCfgStaticInterface simplifyCfgFragments
  simplifyCfgAvailability simplifyCfgDefs contextCodegenRel
  simplifyCfgControl simplifyCfgSimTools venomExecSemantics venomExecProps
  venomExecProofs venomWf venomState venomInst cfgTransform o1PassLift list

Theorem scfg_bypass_rooted_entry_iff[local]:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 ==>
  (enters_block fn' t y <=> ?x. enters_block fn s x /\ scfg_bypass_aligned a b x y)
Proof
  strip_tac >> irule scfg_bypass_enters_block >> simp[] >>
  `wf_function fn /\ fn_inst_wf fn` by
    metis_tac[scfg_bypass_old_static, scfg_static_wf, scfg_static_inst_wf] >>
  drule_all scfg_bprefix_incoming >> strip_tac >> gvs[fn_entry_state_def] >>
  metis_tac[lookup_block_member_label]
QED

Theorem scfg_rooted_entry_info:
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  enters_block fn s x ==>
  x.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
  bb.bb_label = x.vs_current_bb /\
  (!i. get_instruction bb x.vs_inst_idx = SOME i ==> frame_reach C fn s0 i x)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_member_label] >>
  `x.vs_current_bb = s.vs_current_bb /\
   x.vs_inst_idx = phi_prefix_length bb.bb_instructions` by
    (gvs[enters_block_def] >> drule eval_phis_preserves_current_bb >> simp[]) >>
  simp[] >> rpt strip_tac >> irule scfg_bprefix_enter_reach >>
  reverse conj_tac >- (qexists_tac `s` >> simp[]) >>
  simp[active_inst_def] >> qexists_tac `bb` >> gvs[get_instruction_def]
QED

Theorem scfg_bypass_rooted_entry_forward:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 /\ enters_block fn s x ==>
  ?y. enters_block fn' t y /\ scfg_bypass_aligned a b x y /\
    x.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
    y.vs_inst_idx = phi_prefix_length (scfg_bypass_block a b bb).bb_instructions /\
    bb.bb_label = x.vs_current_bb /\
    (!i. get_instruction bb x.vs_inst_idx = SOME i ==> frame_reach C fn s0 i x)
Proof
  strip_tac >>
  `x.vs_current_bb <> b.bb_label` by
    (fs[enters_block_def, scfg_bypass_aligned_def] >>
     metis_tac[eval_phis_preserves_current_bb]) >>
  `?y. scfg_bypass_aligned a b x y` by
    (simp[scfg_bypass_aligned_def]) >>
  `enters_block fn' t y` by
    (drule_all scfg_bypass_rooted_entry_iff >> metis_tac[]) >>
  drule_all scfg_rooted_entry_info >> strip_tac >>
  qexists_tac `y` >> simp[scfg_bypass_phi_prefix_length] >>
  fs[scfg_bypass_aligned_def, scfg_ctrl_def]
QED

Theorem scfg_bypass_rooted_entry_backward:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 /\ enters_block fn' t y ==>
  ?x. enters_block fn s x /\ scfg_bypass_aligned a b x y /\
    x.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
    y.vs_inst_idx = phi_prefix_length (scfg_bypass_block a b bb).bb_instructions /\
    bb.bb_label = x.vs_current_bb /\
    (!i. get_instruction bb x.vs_inst_idx = SOME i ==> frame_reach C fn s0 i x)
Proof
  strip_tac >> drule_all scfg_bypass_rooted_entry_iff >>
  disch_then (drule o iffLR) >> strip_tac >>
  drule_all scfg_rooted_entry_info >> strip_tac >>
  qexists_tac `x` >> simp[scfg_bypass_phi_prefix_length] >>
  fs[scfg_bypass_aligned_def, scfg_ctrl_def]
QED

Theorem scfg_enters_block_run_block:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ enters_block fn s x ==>
  run_block k C bb s = exec_block k C bb x
Proof
  strip_tac >> gvs[enters_block_def, run_block_def]
QED

Theorem scfg_run_block_entry:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block k C bb s = r /\ (!e. r <> Error e) ==>
  ?x. enters_block fn s x /\ exec_block k C bb x = r
Proof
  strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  gvs[run_block_def] >>
  rename1 `eval_phis s bb.bb_instructions = OK p` >>
  qexists_tac `p with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  simp[enters_block_def] >> metis_tac[]
QED
