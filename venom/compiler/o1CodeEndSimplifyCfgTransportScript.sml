Theory o1CodeEndSimplifyCfgTransport
Ancestors
  o1CodeEndCfgRounds o1CodeEndCfgCollapse o1LabelFlowSimplifyPreservation
  o1LabelFlowLateSimplify o1LabelFlowSimplifyChain o1LabelFlowSimplifyJump o1LabelFlowRetention
  o1ContractSimplifyCfg o1PassContract o1PassLift codegenSymRel simplifyCfgStruct
  simplifyCfgDefs simplifyCfgRoundSemantics simplifyCfgShape simplifyCfgFixupShape simplifyCfgInvariant
  simplifyCfgBypassDataflow simplifyCfgWfssa simplifyCfgSimTools cfgTransform venomInst list
  simplifyCfgCorrectness simplifyCfgProof simplifyCfgStaticInterface simplifyCfgShapeCore
  simplifyCfgPhiRepair o1ContractCfgNorm venomWfProps simplifyCfgControl

Theorem code_end_fix_phis_uses[local]:
  (!x i. code_end_var f x /\ MEM i (fn_insts f) /\
    MEM (Var x) i.inst_operands ==> i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) ==>
  !x i. code_end_var (fix_all_phis f) x /\ MEM i (fn_insts (fix_all_phis f)) /\
    MEM (Var x) i.inst_operands ==> i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY
Proof
  rpt strip_tac >>
  `!inst x. MEM inst (fn_insts f) /\ inst.inst_opcode = PHI /\
     code_end_var f x ==> ~MEM (Var x) inst.inst_operands` by
    (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  `code_end_var f x` by metis_tac[simplify_fix_phis_code_end_backward_no_phi] >>
  drule scfg_fix_all_phis_inst_mem >>
  disch_then (qx_choosel_then [`inst`,`actual_preds`] strip_assume_tac) >> gvs[] >>
  `fix_phi_inst actual_preds inst = inst` by
    (irule fix_phi_inst_code_end_identity >> qexistsl_tac [`f`,`x`] >> simp[]) >>
  metis_tac[]
QED

Theorem code_end_unreachable_uses[local]:
  wf_function f /\
  (!x i. code_end_var f x /\ MEM i (fn_insts f) /\
    MEM (Var x) i.inst_operands ==> i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) ==>
  !x i. code_end_var (remove_unreachable_blocks f) x /\
    MEM i (fn_insts (remove_unreachable_blocks f)) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY
Proof
  metis_tac[code_end_var_instruction_subset, simplify_unreachable_inst_subset]
QED

Theorem code_end_chain_uses[local]:
  wf_function f /\ fn_inst_wf f /\ MEM a f.fn_blocks /\ MEM b f.fn_blocks /\
  can_merge_blocks f a b /\
  (!x i. code_end_var f x /\ MEM i (fn_insts f) /\
    MEM (Var x) i.inst_operands ==> i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) /\
  g = (f with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks))
    (bb_succs (merge_blocks a b))) ==>
  !x i. code_end_var g x /\ MEM i (fn_insts g) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY
Proof
  rpt strip_tac >>
  `code_end_var f x` by metis_tac[chain_code_end_backward] >>
  Cases_on `i.inst_opcode = PHI`
  >- (`?j. MEM j (fn_insts f) /\ j.inst_opcode = PHI /\ MEM (Var x) j.inst_operands` by
        (irule chain_phi_var_source >> metis_tac[]) >>
      first_x_assum drule_all >> simp[]) >>
  `MEM i (fn_insts f)` by metis_tac[chain_nonphi_source] >> metis_tac[]
QED

Theorem code_end_jump_uses[local]:
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') /\
  (!x i. code_end_var f x /\ MEM i (fn_insts f) /\
    MEM (Var x) i.inst_operands ==> i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) ==>
  !x i. code_end_var g x /\ MEM i (fn_insts g) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY
Proof
  strip_tac >>
  `EVERY (\i. !x. MEM (Var x) i.inst_operands /\ code_end_var f x ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) (fn_insts g)` suffices_by
    (simp[EVERY_MEM] >> metis_tac[jump_code_end_backward]) >>
  irule do_merge_jump_every >> conj_tac
  >- (simp[] >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `MEM (Var x) i.inst_operands` by metis_tac[update_phi_bypass_var_subset] >>
      `i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY` by metis_tac[] >>
      gvs[update_phi_bypass_def]) >>
  conj_tac
  >- (simp[] >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `MEM (Var x) i.inst_operands` by
        metis_tac[canon_jnz_inst_var_subset, subst_label_inst_use_source] >>
      `i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY` by metis_tac[] >>
      gvs[is_terminator_def]) >>
  qexistsl_tac [`a`, `b`, `f`, `lm`, `lm'`] >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem code_end_collapse_static[local]:
  !f lm vis lbl.
  wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ first_block_no_preds f /\
  scfg_phi_safe f /\ fn_defs_reach_uses f /\
  EVERY label_positions_ok (fn_insts f) /\ all_reachable f /\
  (!x i. code_end_var f x /\ MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) /\
  (!x. code_end_var f x ==> code_end_var original x) ==>
  wf_ssa (FST (collapse_dfs f lm vis lbl)) /\
  wf_function (FST (collapse_dfs f lm vis lbl)) /\
  fn_inst_wf (FST (collapse_dfs f lm vis lbl)) /\
  first_block_no_preds (FST (collapse_dfs f lm vis lbl)) /\
  scfg_phi_safe (FST (collapse_dfs f lm vis lbl)) /\
  fn_defs_reach_uses (FST (collapse_dfs f lm vis lbl)) /\
  EVERY label_positions_ok (fn_insts (FST (collapse_dfs f lm vis lbl))) /\
  all_reachable (FST (collapse_dfs f lm vis lbl)) /\
  (!x i. code_end_var (FST (collapse_dfs f lm vis lbl)) x /\
    MEM i (fn_insts (FST (collapse_dfs f lm vis lbl))) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) /\
  (!x. code_end_var (FST (collapse_dfs f lm vis lbl)) x ==> code_end_var original x)
Proof
  ho_match_mp_tac collapse_dfs_preserves_predicate >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all do_merge_jump_ssa_invariant >> strip_tac >> simp[] >>
      conj_tac >- (rpt strip_tac >> irule code_end_jump_uses >> metis_tac[]) >>
      metis_tac[jump_code_end_backward]) >>
  rpt gen_tac >> strip_tac >>
  `a.bb_label = lbl /\ b.bb_label = next /\ MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  qmatch_goalsub_abbrev_tac `wf_ssa merged` >>
  `merged = f with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks))
    (bb_succs (merge_blocks a b))` by simp[Abbr `merged`] >>
  drule_all chain_merge_ssa_invariant >> strip_tac >>
  ntac 8 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> irule code_end_chain_uses >> metis_tac[]) >>
  metis_tac[chain_code_end_backward]
QED

Theorem code_end_cleanup_static[local]:
  wf_function f /\
  (!x i. code_end_var f x /\ MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) ==>
  (!x i. code_end_var (fix_all_phis (remove_unreachable_blocks f)) x /\
    MEM i (fn_insts (fix_all_phis (remove_unreachable_blocks f))) /\
    MEM (Var x) i.inst_operands ==> i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) /\
  (!x. code_end_var (fix_all_phis (remove_unreachable_blocks f)) x ==> code_end_var f x)
Proof
  strip_tac >>
  `PHI <> ASSIGN /\ PHI <> CODECOPY` by simp[] >>
  `!x i. code_end_var (remove_unreachable_blocks f) x /\
    MEM i (fn_insts (remove_unreachable_blocks f)) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY` by
    metis_tac[code_end_unreachable_uses] >>
  conj_tac >- metis_tac[code_end_fix_phis_uses] >>
  metis_tac[simplify_fix_phis_code_end_backward_no_phi, code_end_var_instruction_subset,
    simplify_unreachable_inst_subset]
QED

Theorem code_end_round_static[local]:
  wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ first_block_no_preds f /\
  scfg_phi_safe f /\ fn_defs_reach_uses f /\ EVERY label_positions_ok (fn_insts f) /\
  (!x i. code_end_var f x /\ MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) ==>
  (!x i. code_end_var (FST (simplify_cfg_round_with_labels f)) x /\
    MEM i (fn_insts (FST (simplify_cfg_round_with_labels f))) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) /\
  (!x. code_end_var (FST (simplify_cfg_round_with_labels f)) x ==> code_end_var f x)
Proof
  strip_tac >> Cases_on `fn_entry_label f`
  >- (simp[simplify_cfg_round_with_labels_def] >> metis_tac[]) >>
  rename1 `fn_entry_label f = SOME entry_lbl` >>
  drule_all simplify_cfg_round_entry_ssa_invariant >> strip_tac >>
  drule_all code_end_cleanup_static >> strip_tac >>
  qabbrev_tac `start = fix_all_phis (remove_unreachable_blocks f)` >>
  Cases_on `collapse_dfs start [] [] entry_lbl` >>
  rename1 `collapse_dfs start [] [] entry_lbl = (collapsed_fn,collapse_tail)` >>
  PairCases_on `collapse_tail` >>
  rename1 `collapse_dfs start [] [] entry_lbl = (collapsed_fn,label_map,new_visited)` >>
  qspecl_then [`start`, `[]`, `[]`, `entry_lbl`] mp_tac
    (Q.INST [`original` |-> `f`] code_end_collapse_static) >> simp[] >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `subst_block_labels_fn label_map collapsed_fn = collapsed_fn` by
    (drule_at (Pat `collapse_dfs _ _ _ _ = _`) collapse_dfs_subst_identity >> simp[]) >>
  `(!x i. code_end_var (fix_all_phis (remove_unreachable_blocks collapsed_fn)) x /\
    MEM i (fn_insts (fix_all_phis (remove_unreachable_blocks collapsed_fn))) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) /\
    (!x. code_end_var (fix_all_phis (remove_unreachable_blocks collapsed_fn)) x ==> code_end_var collapsed_fn x)` by
    (irule code_end_cleanup_static >> conj_tac >> first_assum ACCEPT_TAC) >>
  fs[Abbr `start`] >> simp[simplify_cfg_round_with_labels_def] >> metis_tac[]
QED

Theorem code_end_iter_static[local]:
  !fuel f.
  scfg_static f /\ wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ first_block_no_preds f /\
  scfg_phi_safe f /\ fn_defs_reach_uses f /\ EVERY label_positions_ok (fn_insts f) /\
  (!x i. code_end_var f x /\ MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) ==>
  (!x i. code_end_var (FST (simplify_cfg_iter_with_labels fuel f)) x /\
    MEM i (fn_insts (FST (simplify_cfg_iter_with_labels fuel f))) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) /\
  (!x. code_end_var (FST (simplify_cfg_iter_with_labels fuel f)) x ==> code_end_var f x)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `P = \f. wf_ssa f /\ wf_function f /\ fn_inst_wf f /\
    first_block_no_preds f /\ scfg_phi_safe f /\ fn_defs_reach_uses f /\
    EVERY label_positions_ok (fn_insts f) /\
    (!x i. code_end_var f x /\ MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==>
      i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY)` >>
  `P f` by (simp[Abbr `P`] >> metis_tac[]) >>
  mp_tac (Q.INST [`R` |-> `\a b. P a ==>
    P b /\ (!x. code_end_var b x ==> code_end_var a x)`]
    scfg_iter_relation) >> BETA_TAC >> impl_tac
  >- (conj_tac >- simp[] >> conj_tac
      >- (rpt gen_tac >> rpt strip_tac >> metis_tac[]) >>
      gen_tac >> strip_tac >> simp[Abbr `P`] >> strip_tac >>
      drule_all simplify_cfg_round_ssa_invariant >> strip_tac >>
      drule_all code_end_round_static >> simp[] >> metis_tac[]) >>
  disch_then (qspecl_then [`fuel`,`f`] mp_tac) >> simp[] >>
  simp[Abbr `P`] >> metis_tac[]
QED

Theorem code_end_fn_static[local]:
  scfg_static f /\ wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ first_block_no_preds f /\
  scfg_phi_safe f /\ fn_defs_reach_uses f /\ EVERY label_positions_ok (fn_insts f) /\
  (!x i. code_end_var f x /\ MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) ==>
  (!x i. code_end_var (simplify_cfg_fn f) x /\ MEM i (fn_insts (simplify_cfg_fn f)) /\
    MEM (Var x) i.inst_operands ==> i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) /\
  (!x. code_end_var (simplify_cfg_fn f) x ==> code_end_var f x)
Proof
  simp[NoAsms, simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def] >>
  metis_tac[code_end_iter_static]
QED

Theorem code_end_fn_reach_back[local]:
  scfg_static f /\ fn_entry_state f s0 /\
  frame_reach C (simplify_cfg_fn f) s0 j t /\ j.inst_opcode = CODECOPY ==>
  ?s. frame_reach C f s0 j s /\ scfg_payload s t
Proof
  strip_tac >> irule o1_code_end_iter_reach_back >>
  conj_tac >- metis_tac[scfg_collapse_frame_observation_joint] >>
  simp[is_terminator_def] >>
  qexists_tac `LENGTH f.fn_blocks` >>
  fs[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def, is_terminator_def]
QED

Theorem code_end_origin_payload[local]:
  ctx_bisim C Ct /\
  (!nm f g. lookup_function nm C.ctx_functions = SOME f /\
    lookup_function nm Ct.ctx_functions = SOME g ==> g = simplify_cfg_fn f /\ scfg_static f) /\
  frame_origin vs C Ct g j t /\ j.inst_opcode = CODECOPY ==>
  ?f s. raw_reachable vs C f j s /\ MEM f C.ctx_functions /\ g = simplify_cfg_fn f /\ scfg_payload s t
Proof
  strip_tac >>
  qpat_x_assum `frame_origin _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[frame_origin_def] >>
  disch_then (qx_choosel_then [`fn`,`s0`] strip_assume_tac) >>
  `g = simplify_cfg_fn fn /\ scfg_static fn` by metis_tac[] >>
  `frame_reach C g s0 j t` by metis_tac[frame_reach_ctx_bisim] >>
  `?s. frame_reach C fn s0 j s /\ scfg_payload s t` by
    (irule code_end_fn_reach_back >> metis_tac[]) >>
  metis_tac[frame_reach_raw_reachable, venomInstTheory.lookup_function_MEM]
QED

Theorem code_end_stage_origins[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) view C Ct /\
  o1_ctx_shape C /\ EVERY simplify_cfg_fn_ok C.ctx_functions /\
  o1_run_state_ok vs /\ raw_reachable vs Ct g j t ==>
  frame_origin vs C Ct g j t /\
  (!nm f g. lookup_function nm C.ctx_functions = SOME f /\
    lookup_function nm Ct.ctx_functions = SOME g ==> g = simplify_cfg_fn f /\ scfg_static f)
Proof
  strip_tac >> drule simplify_cfg_stage_functions >> strip_tac >>
  `ctx_bisim C Ct` by metis_tac[simplify_cfg_stage_bisim] >>
  `LIST_REL (\f g. g.fn_name = f.fn_name /\ fn_entry_label g = fn_entry_label f /\
    frame_sim vs.vs_labels C Ct f g /\ g = simplify_cfg_fn f /\ scfg_static f)
    C.ctx_functions Ct.ctx_functions` by
    (simp[LIST_REL_MAP2, LIST_REL_EL_EQN] >> rpt gen_tac >> strip_tac >> simp[EL_MAP] >>
     `MEM (EL n C.ctx_functions) C.ctx_functions` by metis_tac[MEM_EL] >>
     `o1_fn_shape C (EL n C.ctx_functions) /\ simplify_cfg_fn_ok (EL n C.ctx_functions)` by
       fs[o1_ctx_shape_def, EVERY_MEM] >>
     `fn_bisim (EL n C.ctx_functions) (simplify_cfg_fn (EL n C.ctx_functions))` by
       (irule simplify_cfg_fn_correct >> fs[o1_fn_shape_def]) >>
     fs[fn_bisim_def] >> conj_tac
     >- (irule simplify_cfg_frame_sim >> fs[o1_fn_shape_def]) >>
     fs[scfg_static_def, o1_fn_shape_def] >> metis_tac[fn_shape_ok_scfg_shape]) >>
  conj_tac
  >- (irule frame_sim_raw_origins >>
      fs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def, ctx_pass_stage_def] >>
      qpat_x_assum `LIST_REL (\fn fn'. ?observed s out. _) _ _` kall_tac >>
      qpat_x_assum `LIST_REL _ _ _` mp_tac >>
      qpat_x_assum `Ct.ctx_functions = _` mp_tac >>
      rpt (pop_assum kall_tac) >> strip_tac >>
      simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  drule list_rel_lookup_function >> simp[] >>
  disch_then (qspec_then `nm` mp_tac) >> simp[optionTheory.OPTREL_def] >>
  strip_tac >> gvs[]
QED

Theorem code_end_ssa_fn_static[local]:
  o1_fn_shape C f /\ wf_ssa f /\
  (!x i. code_end_var f x /\ MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) ==>
  (!x i. code_end_var (simplify_cfg_fn f) x /\ MEM i (fn_insts (simplify_cfg_fn f)) /\
    MEM (Var x) i.inst_operands ==> i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) /\
  (!x. code_end_var (simplify_cfg_fn f) x ==> code_end_var f x)
Proof
  strip_tac >> irule code_end_fn_static >>
  `EVERY label_positions_ok (fn_insts f)` by metis_tac[o1_fn_shape_label_positions_ok] >>
  `scfg_phi_safe f` by
    (irule wf_ssa_phi_safe >> fs[o1_fn_shape_def, first_block_no_phi_def]) >>
  `simplify_cfg_fn_ok f` by
    (irule simplify_cfg_fn_ok_ssa >> fs[o1_fn_shape_def]) >>
  fs[o1_fn_shape_def, scfg_static_def] >>
  metis_tac[wf_ssa_defs_reach_uses, fn_shape_ok_scfg_shape]
QED

Theorem code_end_stage_preserves[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) view C Ct /\
  o1_ctx_shape C /\ o1_ssa_inv C vs /\ o1_run_state_ok vs /\
  code_end_offset_ok (raw_reachable vs) C /\
  EVERY (\f. !x i. code_end_var f x /\ MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) C.ctx_functions ==>
  code_end_offset_ok (raw_reachable vs) Ct /\
  EVERY (\f. !x i. code_end_var f x /\ MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) Ct.ctx_functions
Proof
  strip_tac >>
  `EVERY simplify_cfg_fn_ok C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_ssa_inv_def, EVERY_MEM] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_ssa >> metis_tac[o1_fn_shape_def]) >>
  `!f. MEM f C.ctx_functions ==>
    (!x i. code_end_var (simplify_cfg_fn f) x /\ MEM i (fn_insts (simplify_cfg_fn f)) /\
      MEM (Var x) i.inst_operands ==> i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) /\
    (!x. code_end_var (simplify_cfg_fn f) x ==> code_end_var f x)` by
    (gen_tac >> disch_tac >> irule code_end_ssa_fn_static >>
     fs[o1_ctx_shape_def, o1_ssa_inv_def, EVERY_MEM] >> metis_tac[]) >>
  reverse conj_tac
  >- (drule simplify_cfg_stage_functions >> strip_tac >>
      simp[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  simp[code_end_offset_ok_def] >> rpt gen_tac >> strip_tac >>
  drule_all code_end_stage_origins >> strip_tac >>
  `ctx_bisim C Ct` by metis_tac[simplify_cfg_stage_bisim] >>
  drule_all code_end_origin_payload >>
  disch_then (qx_choosel_then [`f`,`s`] strip_assume_tac) >>
  `code_end_var f x` by metis_tac[] >>
  qpat_x_assum `code_end_offset_ok _ _` mp_tac >>
  simp[code_end_offset_ok_def] >>
  `eval_operand (Var x) s = SOME w` by metis_tac[scfg_payload_operand] >>
  `s.vs_labels = vs'.vs_labels` by
    (qpat_x_assum `scfg_payload _ _` mp_tac >>
     pure_rewrite_tac[scfg_payload_def] >> strip_tac >>
     qpat_x_assum `vs' = _` SUBST1_TAC >> simp[scfg_ctrl_def]) >>
  metis_tac[]
QED

Theorem simplify_cfg_code_end_run_contract:
  o1_stage_contract rpolicy D (EL 5 o1_fn_passes)
    (o1_walk_view rpolicy 5) (o1_pre 5)
    (\C s. o1_inv D 5 C s /\ code_end_offset_ok (raw_reachable s) C /\
      EVERY (\f. !x i. code_end_var f x /\ MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==>
        i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) C.ctx_functions)
    (\C s. o1_inv D 6 C s /\ code_end_offset_ok (raw_reachable s) C /\
      EVERY (\f. !x i. code_end_var f x /\ MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==>
        i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) C.ctx_functions)
Proof
  mp_tac simplify_cfg_stage_walk >>
  simp[o1_run_contract_def, o1_stage_contract_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `ctx_sim_fuel (pass_fuel (EL 5 o1_fn_passes) C') D C C' s s /\
   o1_inv D 6 C' s` by (first_x_assum irule >> simp[]) >>
  simp[] >>
  `EL 5 o1_fn_passes = CFP_Simple VP_SimplifyCFG` by EVAL_TAC >>
  fs[o1_inv_def] >> metis_tac[code_end_stage_preserves]
QED
