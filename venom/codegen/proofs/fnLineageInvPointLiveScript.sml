Theory fnLineageInvPointLive
Ancestors venomWfProps fnPlanLineagePath fnPlanLineagePhiActivation fnPlanLineageLiveness livenessAnalysisProps
  venomWf venomInst venomExecProps codegenReadyCompute list rich_list pred_set
  stackPlanGen cfgAnalysisProps removeUnusedSsaProofs livenessTransferProofs
  fnPlanLineageDemandSupport fnPlanLineagePhiMaps relation

Theorem analyzed_output_live_point_to_after:
  !fn d bb j v p pb k.
    codegen_ready_fn fn /\ lookup_block d fn.fn_blocks = SOME bb /\
    j < LENGTH bb.bb_instructions /\ MEM v (EL j bb.bb_instructions).inst_outputs /\
    fn_dominates fn d p /\ lookup_block p fn.fn_blocks = SOME pb /\
    LENGTH (collect_phis pb.bb_instructions) <= k /\ k <= LENGTH pb.bb_instructions /\
    (d = p ==> j < k) /\
    MEM v (live_vars_at (liveness_analyze fn) p k) ==>
    MEM v (live_vars_at (liveness_analyze fn) d (j+1))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn /\ ssa_form fn` by gvs[codegen_ready_fn_def] >>
  drule_all dominates_analyzed_path_no_revisit >> strip_tac >>
  `MEM d (cfg_analyze fn).cfg_dfs_pre` by gvs[] >>
  Cases_on `d = p`
  >- (gvs[] >>
      drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
      disch_then (qspecl_then [`d`, `bb`, `j+1`, `k`, `v`] mp_tac) >>
      simp[] >> disch_then irule >> simp[] >>
      rpt strip_tac >> gvs[inst_defs_def] >>
      `j < LENGTH bb.bb_instructions /\ k' < LENGTH bb.bb_instructions` by decide_tac >>
      `k' = j` by metis_tac[ssa_output_position_unique] >> decide_tac) >>
  suspend "different_blocks"
QED

Resume analyzed_output_live_point_to_after[different_blocks]:
  `tail <> []` by (Cases_on `tail` >> gvs[]) >>
  `?pre. tail = pre ++ [p]` by
    (qexists_tac `FRONT tail` >>
     `LAST tail = p` by (Cases_on `tail` >> gvs[]) >>
     metis_tac[APPEND_FRONT_LAST]) >>
  gvs[] >>
  `is_fn_path fn (SNOC p (d::pre))` by simp[SNOC_APPEND] >>
  drule venomWfPropsTheory.is_fn_path_init >> strip_tac >>
  drule venomWfPropsTheory.is_fn_path_last_edge >> simp[] >> strip_tac >>
  `EVERY (\inst. ~MEM v (inst_defs inst)) pb.bb_instructions` by
    (simp[EVERY_EL, inst_defs_def] >> rpt strip_tac >>
     `p = d` by metis_tac[ssa_output_position_unique] >> gvs[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) p
      (LENGTH (collect_phis pb.bb_instructions)))` by
    (drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
     disch_then (qspecl_then [`p`, `pb`, `LENGTH (collect_phis pb.bb_instructions)`, `k`, `v`] mp_tac) >>
     simp[] >> disch_then irule >> gvs[EVERY_EL]) >>
  `EVERY (phi_block_ready (liveness_analyze fn)) fn.fn_blocks` by
    (`phi_operands_ready fn` by gvs[codegen_ready_fn_def] >>
     fs[phi_operands_ready_def] >>
     gvs[EVERY_MEM] >> qx_gen_tac `b` >> strip_tac >>
     qpat_x_assum `!bb. MEM bb fn.fn_blocks ==> NULL _`
       (qspec_then `b` mp_tac) >> simp[] >>
     Cases_on `collect_phis b.bb_instructions` >>
     simp[phi_block_ready_def, phi_uses_disjoint_def]) >>
  `pb.bb_label = p` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `MEM v (input_vars_from (LAST (d::pre)) pb.bb_instructions
      (live_vars_at (liveness_analyze fn) p 0))` by
    (irule analyzed_ready_phi_live_through_edge >> simp[] >>
     reverse conj_tac
     >- (fs[EVERY_MEM] >> first_x_assum irule >>
         metis_tac[venomExecPropsTheory.lookup_block_MEM]) >>
     qspec_then `pb.bb_instructions` strip_assume_tac collect_phis_prefix >>
     qpat_x_assum `EVERY (\inst. ~MEM v (inst_defs inst)) pb.bb_instructions` mp_tac >>
     qpat_x_assum `pb.bb_instructions = _` (fn th => rewrite_tac[Once th, EVERY_APPEND]) >>
     simp[]) >>
  `EVERY (\lbl. cfg_reachable_of (cfg_analyze fn) lbl /\
      MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
      ?b. lookup_block lbl fn.fn_blocks = SOME b) (d::pre)` by
    (simp[] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `cfg_reachable_of (cfg_analyze fn) (LAST (d::pre)) /\
   ?eb. lookup_block (LAST (d::pre)) fn.fn_blocks = SOME eb` by
    (qpat_assum `EVERY _ (d::pre)`
       (mp_tac o PURE_REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `LAST (d::pre)` mp_tac) >>
     simp[LAST_MEM]) >>
  `MEM p (cfg_succs_of (cfg_analyze fn) (LAST (d::pre)))` by
    metis_tac[fn_cfg_edge_cfg_analyze] >>
  `MEM v (live_vars_at (liveness_analyze fn) (LAST (d::pre))
      (LENGTH eb.bb_instructions))` by
    (drule_all analyzed_live_out_edge_subset >>
     simp[SUBSET_DEF] >> disch_then irule >> simp[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) d (LENGTH bb.bb_instructions))` by
    (irule analyzed_live_backward_no_kill_path >> simp[] >>
     qexistsl_tac [`eb`, `pre`] >> simp[] >>
     simp[EVERY_MEM] >> reverse conj_tac >- (gvs[EVERY_MEM] >> metis_tac[]) >>
     qx_gen_tac `lbl` >> strip_tac >>
     qx_gen_tac `b` >> strip_tac >> conj_tac
     >- metis_tac[venomExecPropsTheory.lookup_block_MEM, EVERY_MEM] >>
     `lbl <> d` by metis_tac[] >>
     simp[inst_defs_def] >> rpt strip_tac >>
     qpat_x_assum `MEM inst b.bb_instructions` mp_tac >>
     pure_rewrite_tac[MEM_EL] >> strip_tac >> gvs[] >>
     `lbl = d` by metis_tac[ssa_output_position_unique] >> gvs[]) >>
  drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
  disch_then (qspecl_then [`d`, `bb`, `j+1`, `LENGTH bb.bb_instructions`, `v`] mp_tac) >>
  simp[] >> disch_then irule >> simp[] >> rpt strip_tac >>
  gvs[inst_defs_def] >>
  `j < LENGTH bb.bb_instructions` by decide_tac >>
  `k' = j` by metis_tac[ssa_output_position_unique] >> decide_tac
QED

Finalise analyzed_output_live_point_to_after

Theorem analyzed_offset_output_live_after:
  !fn d bb j v.
    codegen_ready_fn fn /\ lookup_block d fn.fn_blocks = SOME bb /\
    j < LENGTH bb.bb_instructions /\
    (EL j bb.bb_instructions).inst_opcode = OFFSET /\
    MEM v (EL j bb.bb_instructions).inst_outputs ==>
    MEM v (live_vars_at (liveness_analyze fn) d (j+1))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\ offset_outputs_used fn` by
    gvs[codegen_ready_fn_def] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = d` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `MEM (EL j bb.bb_instructions) (fn_insts fn)` by
    (simp[venomInstTheory.fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     qexists_tac `bb.bb_instructions` >> simp[] >>
     metis_tac[EL_MEM]) >>
  `?use. MEM use (fn_insts fn) /\ MEM (Var v) use.inst_operands` by
    (fs[offset_outputs_used_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `?ub. MEM ub fn.fn_blocks /\ MEM use ub.bb_instructions` by
    (gvs[venomInstTheory.fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `lookup_block ub.bb_label fn.fn_blocks = SOME ub` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  Cases_on `use.inst_opcode = PHI`
  >- suspend "phi_use" >>
  suspend "ordinary_use"
QED

Resume analyzed_offset_output_live_after[ordinary_use]:
  `def_available_at fn ub (SOME use) v` by
    (fs[def_dominates_uses_def] >>
     qpat_x_assum `!b inst. _` (qspecl_then [`ub`, `use`] mp_tac) >> simp[]) >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  `def_bb = bb /\ def_inst = EL j bb.bb_instructions` by
    metis_tac[ssa_unique_output_block, EL_MEM] >> gvs[] >>
  `?u. u < LENGTH ub.bb_instructions /\ EL u ub.bb_instructions = use /\
        (bb = ub ==> j < u)` by
    (Cases_on `bb = ub`
     >- (gvs[] >> `i = j` by
           (`i < LENGTH bb.bb_instructions` by decide_tac >>
            metis_tac[ssa_output_position_unique]) >>
         metis_tac[]) >>
     metis_tac[MEM_EL]) >>
  `MEM ub.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (`fn_reachable fn ub.bb_label` by gvs[fn_dominates_def] >>
     drule fn_reachable_cfg_analyze >>
     drule cfg_analyze_reachable_sets >> simp[EXTENSION] >> metis_tac[]) >>
  `LENGTH (collect_phis ub.bb_instructions) <= u` by
    (spose_not_then assume_tac >>
     `u < LENGTH (collect_phis ub.bb_instructions)` by decide_tac >>
     qspec_then `ub.bb_instructions` strip_assume_tac collect_phis_prefix >>
     `EL u ub.bb_instructions = EL u (collect_phis ub.bb_instructions)` by
       metis_tac[EL_APPEND1] >>
     metis_tac[livenessTransferProofsTheory.collect_phis_mem, EL_MEM]) >>
  `MEM v (live_vars_at (liveness_analyze fn) ub.bb_label u)` by
    (`MEM v (inst_uses use)` by
       (irule venomWfPropsTheory.operand_var_in_inst_uses >> simp[]) >>
     drule livenessAnalysisPropsTheory.live_vars_at_uses >>
     disch_then (qspecl_then [`ub.bb_label`, `ub`, `u`, `v`] mp_tac) >> simp[]) >>
  irule analyzed_output_live_point_to_after >> simp[] >>
  qexistsl_tac [`u`, `ub.bb_label`, `ub`] >> simp[] >>
  strip_tac >> `bb = ub` by metis_tac[optionTheory.SOME_11] >> simp[]
QED

Resume analyzed_offset_output_live_after[phi_use]:
  `phi_edge_uses_wf fn ub use` by
    (fs[def_dominates_uses_def] >>
     qpat_x_assum `!b inst. _` (qspecl_then [`ub`, `use`] mp_tac) >> simp[]) >>
  `phi_well_formed use.inst_operands` by fs[phi_edge_uses_wf_def] >>
  drule_all phi_well_formed_var_pair >> strip_tac >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = lbl /\
        fn_cfg_edge fn lbl ub.bb_label /\ def_available_at fn pb NONE v` by
    (fs[phi_edge_uses_wf_def] >> metis_tac[]) >>
  `lookup_block pb.bb_label fn.fn_blocks = SOME pb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  `def_bb = bb /\ def_inst = EL j bb.bb_instructions` by
    metis_tac[ssa_unique_output_block, EL_MEM] >> gvs[] >>
  `fn_reachable fn pb.bb_label` by gvs[fn_dominates_def] >>
  `cfg_reachable_of (cfg_analyze fn) pb.bb_label` by
    metis_tac[fn_reachable_cfg_analyze] >>
  `?entry. fn_entry_label fn = SOME entry` by gvs[fn_reachable_def] >>
  `fn_reachable fn ub.bb_label` by
    (gvs[fn_reachable_def] >> metis_tac[RTC_SINGLE, RTC_TRANS]) >>
  `MEM ub.bb_label (cfg_succs_of (cfg_analyze fn) pb.bb_label)` by
    metis_tac[fn_cfg_edge_cfg_analyze] >>
  `MEM use (collect_phis ub.bb_instructions)` by
    (`bb_well_formed ub` by
       (gvs[wf_function_def, EVERY_MEM] >> metis_tac[]) >>
     `?u. u < LENGTH ub.bb_instructions /\ EL u ub.bb_instructions = use` by
       metis_tac[MEM_EL] >>
     gvs[] >> drule_all block_phi_mem_collect >> simp[]) >>
  `?i. i < LENGTH (collect_phis ub.bb_instructions) /\
       EL i (collect_phis ub.bb_instructions) = use` by metis_tac[MEM_EL] >>
  `FIND (\(l,w). l = pb.bb_label) (phi_pairs use.inst_operands) = SOME (pb.bb_label,v)` by
    (qspec_then `FST : string # string -> string`
       (qspecl_then [`phi_pairs use.inst_operands`, `(pb.bb_label,v)`] mp_tac)
       distinct_key_FIND_member >>
     fs[phi_edge_uses_wf_def] >> simp[pairTheory.LAMBDA_PROD]) >>
  `ub.bb_label <> entry` by
    (strip_tac >>
     `MEM pb.bb_label (cfg_preds_of (cfg_analyze fn) entry)` by
       metis_tac[cfg_edge_symmetry_uncond] >>
     `?eb. entry_block fn = SOME eb /\ eb.bb_label = entry` by
       gvs[fn_entry_label_def, AllCaseEqs()] >>
     gvs[codegen_ready_fn_def, block_entries_ready_def, NULL_EQ]) >>
  `MEM v (live_vars_at (liveness_analyze fn) pb.bb_label (LENGTH pb.bb_instructions))` by
    (irule reachable_phi_incoming_live_out >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`ub`, `i`, `ub.bb_label`] >> simp[]) >>
  irule analyzed_output_live_point_to_after >> simp[] >>
  qexistsl_tac [`LENGTH pb.bb_instructions`, `pb.bb_label`, `pb`] >> simp[] >>
  reverse conj_tac
  >- (strip_tac >> `bb = pb` by metis_tac[optionTheory.SOME_11] >> gvs[]) >>
  qspec_then `pb.bb_instructions` strip_assume_tac collect_phis_prefix >>
  qpat_x_assum `pb.bb_instructions = _`
    (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]
QED

Finalise analyzed_offset_output_live_after
