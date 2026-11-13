Theory fmpStageFmpStepsRestoreBounds
Ancestors
  fmpStageFmpStepsRestoreControl fmpStepLayout fmpLowerIndexedProps
  fmpLowerDefs fmpStageRel finite_map list rich_list venomInst arithmetic

Theorem fmp_restore_inst_nonempty:
  fmp_lower_inst infos ctx runner sp inst = SOME (code,sp') ==>
  code <> []
Proof
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem fmp_restore_indexed_nonempty:
  fmp_lower_indexed infos ctx runner lbl idx sp restores (inst::insts) =
    SOME (code,leftover,sp') ==> code <> []
Proof
  simp[fmp_lower_indexed_cons, AllCaseEqs()] >> rpt strip_tac >>
  drule fmp_restore_inst_nonempty >> gvs[]
QED

Theorem fmp_restore_postroot_bound:
  fmp_stage_lowered infos ctx runner fn fn' /\ MEM bb fn.fn_blocks /\
  fn.fn_fmp_signature = NONE /\
  (?info. FLOOKUP infos fn.fn_name = SOME info /\
          (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  idx < LENGTH bb.bb_instructions /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
           bb.bb_label = rl ==> rp <= idx) ==>
  ?bb'. lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) bb.bb_label bb.bb_instructions idx <
      LENGTH bb'.bb_instructions
Proof
  rpt strip_tac >>
  drule fmpStageControlTheory.fmp_stage_tidx_code >>
  disch_then (qspecl_then [`idx`, `bb`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `DROP idx bb.bb_instructions <> []` by simp[DROP_EQ_NIL] >>
  Cases_on `DROP idx bb.bb_instructions` >> gvs[] >>
  drule fmp_restore_indexed_nonempty >> strip_tac >>
  CCONTR_TAC >> gvs[DROP_EQ_NIL]
QED


Theorem fmp_restore_sum_one[local]:
  (!j. j < n ==> f j = 1) ==> SUM (GENLIST f n) = n
Proof
  Induct_on `n` >> simp[GENLIST, SUM_SNOC] >> rpt strip_tac >>
  `SUM (GENLIST f n) = n` by (first_x_assum irule >> simp[]) >>
  `f n = 1` by simp[] >> simp[]
QED

Theorem fmp_restore_preroot_bound:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  FLOOKUP infos fn.fn_name = SOME info /\
  (info.fi_needs_fmp \/ info.fi_publishes_fmp) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  fmp_stage_root infos ctx fn = SOME (lbl,rp) /\ idx < rp ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx <
      LENGTH bb'.bb_instructions
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  drule_all fmpStageControlLayoutTheory.fmp_control_rewrite >> strip_tac >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  drule_all fmpStageControlLayoutTheory.fmp_control_root_layout >> strip_tac >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  drule fmp_lower_blocks_preserves_labels >> simp[] >> strip_tac >>
  `root <> NONE` by gvs[] >>
  `lbl = entry.bb_label /\ rp = LENGTH users + LENGTH (OPTION_TO_LIST oldpc)` by gvs[] >>
  `bb = entry` by gvs[lookup_block_def, FIND_thm] >>
  `!j. j < rp ==> FLOOKUP plan (lbl,j) = NONE` by
    metis_tac[fmpStageControlLayoutTheory.fmp_control_prefix_plan_absent] >>
  drule split_fmp_entry_parameter_prefix >> strip_tac >>
  qpat_x_assum `blocks = _` SUBST_ALL_TAC >>
  `entry'.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  drule_all fmp_install_root_exact_prefix >> strip_tac >>
  qpat_x_assum `!s'' root rest fn ctx. _` (qspecl_then [`s2`, `root`, `rest'`, `fn`, `ctx`] assume_tac) >>
  fs[] >>
  `!j. j < idx ==> ~((entry.bb_label,j) IN FDOM plan) /\
       (EL j entry.bb_instructions).inst_opcode <> DALLOCA` by
    (rpt strip_tac >- (gvs[FLOOKUP_DEF] >> metis_tac[LESS_TRANS]) >>
     `j < LENGTH (users ++ OPTION_TO_LIST oldpc)` by simp[] >>
     `MEM (EL j (users ++ OPTION_TO_LIST oldpc)).inst_opcode
          [PARAM; RETPC_PARAM; FMP_PARAM]` by
       (drule split_fmp_entry_parameter_prefix >>
        pure_rewrite_tac[EVERY_EL] >>
        disch_then (qspec_then `j` mp_tac) >>
        fs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
     Cases_on `j < LENGTH users` >>
     gvs[callLayoutDefsTheory.OPTION_TO_LIST_def, EL_APPEND_EQN]) >>
  `fmp_stage_tidx plan (SOME (entry.bb_label,rp)) entry.bb_label entry.bb_instructions idx = idx` by
    (simp[fmp_stage_tidx_def] >> irule fmp_restore_sum_one >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `oldpc` >> Cases_on `newpc` >>
  gvs[callLayoutDefsTheory.OPTION_TO_LIST_def, lookup_block_def, FIND_thm] >>
  Cases_on `fn_is_context_entry ctx fn` >> simp[]
QED

Theorem fmp_restore_active_bound:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\ pre_fmp_ops fn /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ idx < LENGTH bb.bb_instructions ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx <
      LENGTH bb'.bb_instructions
Proof
  rpt strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    (fs[lookup_block_def] >>
     drule venomInstTheory.FIND_MEM >> drule venomInstTheory.FIND_P >> simp[]) >>
  Cases_on `?info. FLOOKUP infos fn.fn_name = SOME info /\
                  (info.fi_needs_fmp \/ info.fi_publishes_fmp)`
  >- (Cases_on `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
                       bb.bb_label = rl ==> rp <= idx`
      >- (drule_all fmp_restore_postroot_bound >> simp[]) >>
      gvs[NOT_FORALL_THM] >>
      metis_tac[fmp_restore_preroot_bound, NOT_LESS_EQUAL]) >>
  `no_raw_fmp_ops fn` by
    (fs[fmp_stage_lowered_def] >>
     gvs[fmp_lower_function_with_info_def, AllCaseEqs()] >>
     irule fmpLowerPropsTheory.fmp_no_need_input_no_raw >> metis_tac[]) >>
  drule fmpStageControlTheory.fmp_stage_unlowered >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qexists_tac `bb` >> simp[fmp_stage_tidx_def] >>
  irule LESS_EQ_LESS_TRANS >> qexists_tac `idx` >> simp[] >>
  `SUM (GENLIST (\j. if (EL j bb.bb_instructions).inst_opcode = DALLOCA
                         then 4 else 1) idx) = idx` suffices_by simp[] >>
  irule fmp_restore_sum_one >> rpt strip_tac >>
  `MEM (EL j bb.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def] >> irule fmp_fn_insts_blocks_intro >>
     qexists_tac `bb` >> simp[] >> irule EL_MEM >> decide_tac) >>
  fs[no_raw_fmp_ops_def] >>
  first_x_assum drule >>
  Cases_on `(EL j bb.bb_instructions).inst_opcode = DALLOCA` >>
  simp[is_raw_fmp_opcode_def]
QED
