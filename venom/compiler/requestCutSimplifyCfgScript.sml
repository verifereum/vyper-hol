Theory requestCutSimplifyCfg
Ancestors
  o1ContractSimplifyCfg o1PassContract o1PassLift
  simplifyCfgProof simplifyCfgFrameRf simplifyCfgFramePrefixes simplifyCfgFragments
  simplifyCfgMergeClosure finite_map
  simplifyCfgRestrictionSemantics simplifyCfgRestriction simplifyCfgStruct
  simplifyCfgBypassSemantics
  simplifyCfgBypassPrefix simplifyCfgBypassShape simplifyCfgBypassEntry
  simplifyCfgBypassClosure
  simplifyCfgComposeGasEvents simplifyCfgRoundSemantics simplifyCfgCollapseSemantics
  simplifyCfgControlExec simplifyCfgControl simplifyCfgSimTools
  simplifyCfgStaticInterface simplifyCfgShapeCore simplifyCfgMergeSemantics
  simplifyCfgMergePaths simplifyCfgMergeEntry simplifyCfgMergeExec
  simplifyCfgLabelProps simplifyCfgGeneratedSubst simplifyCfgDefs
  lowerDloadRequestObservation unitShapeDefs venomState venomInst
  venomExecSemantics venomWf list pair

(* A recording instruction survives CFG simplification with the same operands
   and state payload. Its block and instruction index can change. *)
val recording_origins = ``\C f g.
  fn_entry_label g = fn_entry_label f /\
  !s0 i t. fn_entry_state f s0 /\ frame_reach C g s0 i t /\
    MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] ==>
    ?s. frame_reach C f s0 i s /\ scfg_payload s t``;

Theorem scfg_recording_merge[local]:
  scfg_chain_hyp f a b ==> ^recording_origins C f (scfg_chain f a b)
Proof
  BETA_TAC >> strip_tac >> conj_tac >- metis_tac[scfg_chain_entry_eq] >>
  qx_genl_tac [`s0`, `i`, `t`] >> strip_tac >>
  `wf_function (scfg_chain f a b)` by metis_tac[scfg_chain_wf] >>
  drule_all scfg_frame_reach_decompose >>
  disch_then (qx_choosel_then [`s`, `bb`, `v`, `e`] strip_assume_tac) >>
  `scfg_chain_exit a b s0 s0` by metis_tac[scfg_chain_initial_exit] >>
  `~s0.vs_halted` by fs[fn_entry_state_def] >>
  `?u. scfg_bprefix C f s0 u /\ ~u.vs_halted /\ scfg_chain_exit a b u s` by
    (irule scfg_chain_bprefix_backward >>
     goal_assum (drule_at Any) >> simp[scfg_bprefix_rules] >>
     conj_tac >- (qexists_tac `s0` >> simp[scfg_bprefix_rules]) >>
     qexists_tac `s0` >> simp[]) >>
  `i.inst_opcode <> PHI` by fs[MEM] >>
  qpat_x_assum `e = _` SUBST_ALL_TAC >>
  drule_all scfg_chain_rooted_segment_observation >> metis_tac[]
QED

Theorem scfg_recording_bypass[local]:
  scfg_bypass_hyp f a b g ==> ^recording_origins C f g
Proof
  BETA_TAC >> strip_tac >> conj_tac >- metis_tac[scfg_bypass_entry_eq] >>
  rpt strip_tac >>
  `scfg_bypass_aligned a b s0 s0` by metis_tac[scfg_bypass_initial_aligned] >>
  `ctx_bisim C C` by simp[ctx_bisim_refl] >>
  drule_all (Q.INST [`C` |-> `C`, `C'` |-> `C`,
    `t0` |-> `s0`] scfg_bypass_rooted_observe) >>
  simp[ctx_bisim_refl] >> rpt strip_tac >>
  `i.inst_opcode <> PHI /\ ~is_terminator i.inst_opcode` by
    (fs[MEM] >> simp[is_terminator_def]) >>
  gvs[scfg_bypass_image_ordinary_inv] >>
  qexists_tac `u` >> fs[scfg_bypass_aligned_def, scfg_payload_def, scfg_ctrl_def]
QED

Theorem scfg_recording_cleanup[local]:
  scfg_static f ==> ^recording_origins C f (fix_all_phis (remove_unreachable_blocks f))
Proof
  BETA_TAC >> strip_tac >> conj_tac >- metis_tac[scfg_static_cleanup_entry] >>
  rpt strip_tac >>
  `wf_function f /\ fn_inst_wf f /\ simplify_cfg_fn_ok f` by fs[scfg_static_def] >>
  `i.inst_opcode <> ASSIGN` by fs[MEM] >>
  `frame_reach C (remove_unreachable_blocks f) s0 i t` by
    (irule scfg_fix_all_phis_frame_reach_back >>
     simp[remove_unreachable_blocks_wf, remove_unreachable_blocks_fn_inst_wf,
          scfg_restriction_ok, fn_entry_state_def, remove_unreachable_blocks_entry] >>
     rpt strip_tac >> fs[wf_function_def, fn_entry_state_def] >>
     metis_tac[scfg_restriction_blocks_reachable]) >>
  qexists_tac `t` >> simp[] >>
  metis_tac[scfg_restriction_frame_reach_back, wf_function_def]
QED

Theorem scfg_recording_trans[local]:
  ^recording_origins C f g /\ ^recording_origins C g h ==>
  ^recording_origins C f h
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- metis_tac[] >>
  qx_genl_tac [`s0`,`i`,`t`] >> strip_tac >>
  `fn_entry_state g s0` by fs[fn_entry_state_def] >>
  `?m. frame_reach C g s0 i m /\ scfg_payload m t` by
    (first_x_assum (irule o Q.SPECL [`s0`,`i`,`t`]) >> simp[]) >>
  `?s. frame_reach C f s0 i s /\ scfg_payload s m` by
    (qpat_assum `!s0 i t. _ /\ frame_reach C g s0 i t /\ _ ==> _`
       (irule o Q.SPECL [`s0`,`i`,`m`]) >> simp[]) >>
  qexists_tac `s` >> simp[] >> metis_tac[scfg_payload_trans]
QED

Theorem scfg_recording_collapse[local]:
  scfg_normalized f ==> ^recording_origins C f (FST (collapse_dfs f lm visited lbl))
Proof
  mp_tac (Q.INST [`R` |-> `^recording_origins C`] scfg_collapse_relation) >>
  BETA_TAC >> impl_tac
  >- (rpt conj_tac
      >- metis_tac[scfg_payload_refl]
      >- (rpt gen_tac >> MATCH_ACCEPT_TAC (BETA_RULE scfg_recording_trans))
      >- (rpt gen_tac >> MATCH_ACCEPT_TAC (BETA_RULE scfg_recording_merge))
      >> rpt gen_tac >> MATCH_ACCEPT_TAC (BETA_RULE scfg_recording_bypass)) >>
  disch_then (mp_tac o Q.SPECL [`f`,`lm`,`visited`,`lbl`] o CONJUNCT1) >>
  simp[]
QED

Theorem scfg_recording_round[local]:
  scfg_static f ==> ^recording_origins C f (FST (simplify_cfg_round_with_labels f))
Proof
  strip_tac >> Cases_on `fn_entry_label f`
  >- (fs[scfg_static_def, wf_function_def, fn_has_entry_def,
         fn_entry_label_def, entry_block_def] >> Cases_on `f.fn_blocks` >> gvs[]) >>
  qabbrev_tac `clean = fix_all_phis (remove_unreachable_blocks f)` >>
  `scfg_normalized clean` by metis_tac[Abbr `clean`, scfg_normalized_cleanup] >>
  Cases_on `collapse_dfs clean [] [] x` >> PairCases_on `r` >>
  `scfg_collapse_contract clean q` by metis_tac[scfg_collapse_joint, pairTheory.FST] >>
  `scfg_normalized q` by fs[scfg_collapse_contract_def] >>
  `scfg_static q` by metis_tac[scfg_normalized_static] >>
  `ALL_DISTINCT (fn_labels clean)` by
    fs[scfg_normalized_def, scfg_static_def, wf_function_def] >>
  `subst_block_labels_fn r0 q = q` by metis_tac[scfg_collapse_subst_identity] >>
  `^recording_origins C f clean` by
    (qunabbrev_tac `clean` >>
     MATCH_ACCEPT_TAC (MATCH_MP scfg_recording_cleanup (ASSUME ``scfg_static f``))) >>
  `^recording_origins C clean q` by
    (mp_tac (Q.INST [`f` |-> `clean`, `lm` |-> `[]`,
       `visited` |-> `[]`, `lbl` |-> `x`] scfg_recording_collapse) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     pure_asm_rewrite_tac[pairTheory.FST] >> disch_then ACCEPT_TAC) >>
  `^recording_origins C q (fix_all_phis (remove_unreachable_blocks q))` by
    MATCH_ACCEPT_TAC (MATCH_MP scfg_recording_cleanup (ASSUME ``scfg_static q``)) >>
  `^recording_origins C f q` by
    (mp_tac (Q.INST [`C` |-> `C`, `f` |-> `f`, `g` |-> `clean`, `h` |-> `q`]
       scfg_recording_trans) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `^recording_origins C f (fix_all_phis (remove_unreachable_blocks q))` by
    (mp_tac (Q.INST [`C` |-> `C`, `f` |-> `f`, `g` |-> `q`,
       `h` |-> `fix_all_phis (remove_unreachable_blocks q)`] scfg_recording_trans) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `FST (simplify_cfg_round_with_labels f) = fix_all_phis (remove_unreachable_blocks q)` by
    (Cases_on `r0 = []` >> fs[simplify_cfg_round_with_labels_def, Abbr `clean`]) >>
  pure_asm_rewrite_tac[] >> first_assum ACCEPT_TAC
QED

Theorem scfg_recording_origin[local]:
  scfg_static f ==> ^recording_origins C f (simplify_cfg_fn f)
Proof
  mp_tac (Q.INST [`R` |-> `^recording_origins C`] scfg_iter_relation) >>
  BETA_TAC >> impl_tac
  >- (rpt conj_tac
      >- metis_tac[scfg_payload_refl]
      >- (rpt gen_tac >> MATCH_ACCEPT_TAC (BETA_RULE scfg_recording_trans))
      >> rpt gen_tac >> MATCH_ACCEPT_TAC (BETA_RULE scfg_recording_round)) >>
  disch_then (mp_tac o Q.SPECL [`LENGTH f.fn_blocks`, `f`]) >>
  PURE_REWRITE_TAC[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def] >>
  disch_then ACCEPT_TAC
QED

Theorem simplify_cfg_stage_recording_step:
  ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) view C CT /\
  o1_ctx_shape C /\ EVERY simplify_cfg_fn_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  raw_reachable vs CT g i t /\ i.inst_opcode <> INVOKE /\
  step_inst fuel CT i t = OK t' /\ LENGTH t.vs_requests < LENGTH t'.vs_requests ==>
  ?f s s'. raw_reachable vs C f i s /\ step_inst fuel C i s = OK s' /\
    s.vs_requests = t.vs_requests /\ s.vs_outcomes = t.vs_outcomes /\
    s'.vs_requests = t'.vs_requests
Proof
  strip_tac >>
  `MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]` by
    (irule ld_request_growth_external >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`CT`, `fuel`, `t`, `t'`] >> simp[]) >>
  `ctx_bisim C CT /\ CT.ctx_entry = C.ctx_entry /\
   CT.ctx_functions = MAP simplify_cfg_fn C.ctx_functions` by
    metis_tac[simplify_cfg_stage_bisim, ctx_pass_stage_def, simplify_cfg_stage_functions] >>
  `!f. MEM f C.ctx_functions ==> scfg_static f` by
    (fs[o1_ctx_shape_def, EVERY_MEM, scfg_static_def] >> rpt strip_tac >>
     `o1_fn_shape C f /\ simplify_cfg_fn_ok f` by metis_tac[] >>
     fs[o1_fn_shape_def, fn_shape_ok_scfg_shape]) >>
  `!f. (simplify_cfg_fn f).fn_name = f.fn_name` by
    metis_tac[simplify_cfg_fn_metadata, fn_identity_metadata_eq_def] >>
  `frame_origin vs C CT g i t` by
    (irule frame_sim_raw_origins >> simp[LIST_REL_MAP2, LIST_REL_EL_EQN] >>
     gen_tac >> strip_tac >>
     `scfg_static (EL n C.ctx_functions)` by metis_tac[EL_MEM] >>
     `o1_fn_shape C (EL n C.ctx_functions)` by
       metis_tac[o1_ctx_shape_def, EVERY_MEM, EL_MEM] >>
     simp[EL_MAP] >>
     conj_tac >- metis_tac[BETA_RULE scfg_recording_origin] >>
     irule simplify_cfg_frame_sim >>
     fs[scfg_static_def, scfg_shape_def, o1_fn_shape_def]) >>
  qpat_x_assum `frame_origin _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[frame_origin_def] >>
  disch_then (qx_choosel_then [`f`,`entry`] strip_assume_tac) >>
  rename1 `lookup_function name C.ctx_functions = SOME f` >>
  `g = simplify_cfg_fn f` by
    (mp_tac (Q.SPECL [`name`, `C.ctx_functions`, `simplify_cfg_fn`] lookup_function_map) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `lookup_function name CT.ctx_functions = SOME g` mp_tac >>
     qpat_assum `CT.ctx_functions = _` (fn th => PURE_REWRITE_TAC[th]) >>
     qpat_assum `lookup_function name C.ctx_functions = SOME f`
       (fn th => PURE_REWRITE_TAC[th]) >>
     simp[] >> metis_tac[]) >>
  `scfg_static f` by metis_tac[lookup_function_MEM] >>
  `frame_reach C g entry i t` by metis_tac[frame_reach_ctx_bisim] >>
  qpat_x_assum `g = simplify_cfg_fn f` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`C` |-> `C`, `f` |-> `f`] scfg_recording_origin) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o Q.SPECL [`entry`,`i`,`t`] o CONJUNCT2 o BETA_RULE) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `s` strip_assume_tac) >>
  `step_inst fuel C i t = OK t'` by gvs[step_inst_non_invoke] >>
  `?u. step_inst fuel C i s = OK u /\ scfg_payload u t'` by
    (mp_tac (Q.INST [`s` |-> `s`, `t` |-> `t`, `k` |-> `fuel`,
      `C` |-> `C`, `i` |-> `i`] scfg_payload_step) >>
     asm_rewrite_tac[] >> Cases_on `step_inst fuel C i s` >> simp[scfg_result_def]) >>
  qexistsl_tac [`f`,`s`,`u`] >>
  simp[] >> conj_tac >- metis_tac[frame_reach_raw_reachable] >>
  fs[scfg_payload_def, scfg_ctrl_def] >>
  qpat_assum `t = _` (fn th =>
    mp_tac (AP_TERM ``\q:venom_state. q.vs_requests`` th) >>
    mp_tac (AP_TERM ``\q:venom_state. q.vs_outcomes`` th)) >>
  qpat_assum `t' = _` (mp_tac o AP_TERM ``\q:venom_state. q.vs_requests``) >>
  simp[]
QED
