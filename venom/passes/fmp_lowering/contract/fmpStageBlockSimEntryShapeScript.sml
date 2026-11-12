Theory fmpStageBlockSimEntryShape
Ancestors
  fmpStageControl fmpStageOpBase venomExecProofs venomWfProps
  cfgWf cfgHelpers livenessProofs fmpStepRewrite makeSsaCurrentLiveTransport
  venomExecSemantics venomState venomInst frameCfgBoundary list

Theorem fmp_entry_jump_successor:
  MEM bi.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst k C bi s = OK (jump_to lbl s) ==>
  MEM lbl (get_successors bi)
Proof
  strip_tac >>
  `bi.inst_opcode <> INVOKE` by gvs[] >>
  gvs[step_inst_non_invoke] >>
  gvs[step_inst_base_def, get_successors_def, AllCaseEqs(),
      jump_to_def] >>
  first_x_assum (mp_tac o AP_TERM ``\s:venom_state. s.vs_current_bb``) >>
  simp[] >> strip_tac >>
  gvs[is_terminator_def, get_label_def] >>
  all_tac
  >- (IF_CASES_TAC >> simp[])
  >- (IF_CASES_TAC >> simp[]) >>
  drule extract_labels_filtered >> strip_tac >>
  IF_CASES_TAC >> simp[] >> metis_tac[EL_MEM]
QED

Theorem fmp_entry_jump_edge:
  wf_function fn /\ first_block_no_preds fn /\ active_inst fn bi s /\
  MEM bi.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst k C bi s = OK (jump_to lbl s) ==>
  ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    SUC s.vs_inst_idx = LENGTH bb.bb_instructions /\
    MEM lbl (bb_succs bb) /\
    fn_cfg_edge fn s.vs_current_bb lbl /\
    lbl <> (HD fn.fn_blocks).bb_label
Proof
  strip_tac >> drule_all fmp_entry_jump_successor >> strip_tac >>
  qpat_x_assum `active_inst _ _ _` mp_tac >>
  simp[contextCodegenRelTheory.active_inst_def] >> strip_tac >>
  `bb_well_formed bb` by metis_tac[venomWfTheory.wf_function_def] >>
  `is_terminator bi.inst_opcode` by gvs[is_terminator_def] >>
  `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[venomWfTheory.bb_well_formed_def] >>
  `bi = LAST bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[LAST_EL]) >>
  `MEM lbl (bb_succs bb)` by
    (Cases_on `bb.bb_instructions` >> gvs[bb_succs_def, MEM_nub, MEM_REVERSE]) >>
  qexists_tac `bb` >> simp[] >>
  conj_tac
  >- (irule MEM_lookup_block >>
      gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  conj_tac >- (simp[venomWfTheory.fn_cfg_edge_def] >> metis_tac[]) >>
  gvs[unitShapeDefsTheory.first_block_no_preds_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem fmp_entry_indexed_phis:
  !insts k s restores out leftover s'.
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') /\
  (!n base. n < phi_prefix_length insts ==>
    ~MEM ((label,k+n),base) restores) ==>
  collect_phis out = collect_phis insts /\
  phi_prefix_length out = phi_prefix_length insts
Proof
  Induct
  >- simp[fmpLowerDefsTheory.fmp_lower_indexed_def,
          livenessDefsTheory.collect_phis_def, phi_prefix_length_def] >>
  rpt gen_tac >>
  simp[fmpLowerIndexedPropsTheory.fmp_lower_indexed_cons] >>
  strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`bases = []` by
        (drule fmpLowerIndexedPropsTheory.fmp_select_point_restores_once >> strip_tac >>
         qpat_x_assum `!n base. _` (qspec_then `0` mp_tac) >>
         simp[phi_prefix_length_def] >>
         Cases_on `bases` >> gvs[] >> metis_tac[]) >>
      gvs[fmpLowerDefsTheory.fmp_emit_restores_def] >>
      drule fmp_lower_inst_phi >> simp[] >> strip_tac >> gvs[] >>
      simp[livenessDefsTheory.collect_phis_def, phi_prefix_length_def] >>
      first_x_assum irule >> goal_assum (drule_at Any) >>
      rpt strip_tac >>
      drule fmpLowerIndexedPropsTheory.fmp_select_point_restores_once >> strip_tac >>
      qpat_x_assum `!n base. _` (qspec_then `SUC n` mp_tac) >>
      gvs[phi_prefix_length_def, arithmeticTheory.ADD_CLAUSES,
          arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  drule fmp_lower_inst_phi >> simp[] >> strip_tac >>
  drule fmp_lower_inst_terminal >> strip_tac >>
  drule fmp_emit_restores_not_phi >> strip_tac >>
  Cases_on `prefix` >> Cases_on `head` >>
  gvs[livenessDefsTheory.collect_phis_def, phi_prefix_length_def]
QED

Theorem fmp_entry_root_label:
  fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
  rl = (HD fn.fn_blocks).bb_label
Proof
  simp[fmpStageRelTheory.fmp_stage_root_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem fmp_entry_phi_plan_absent:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  n < phi_prefix_length bb.bb_instructions ==>
  ~((lbl,n) IN FDOM (fmp_stage_plan infos ctx fn))
Proof
  strip_tac >> strip_tac >>
  drule_all fmp_stage_plan_point >> strip_tac >>
  ` (EL n bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[phi_prefix_length_el_phi] >>
  gvs[fmpReclaimDefsTheory.fmp_is_reclaim_point_def,
      fmpReclaimDefsTheory.fmp_callee_info_def,
      fmpAnalysisDefsTheory.fmp_invoke_target_def]
QED

Theorem fmp_entry_phi_tidx:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lbl <> (HD fn.fn_blocks).bb_label /\
  n <= phi_prefix_length bb.bb_instructions ==>
  fmp_stage_tidx (fmp_stage_plan infos ctx fn)
    (fmp_stage_root infos ctx fn) lbl bb.bb_instructions n = n
Proof
  Induct_on `n`
  >- (rpt strip_tac >>
      `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) ==> lbl <> rl` by
        metis_tac[fmp_entry_root_label] >>
      Cases_on `fmp_stage_root infos ctx fn` >>
      simp[fmpStageRelTheory.fmp_stage_tidx_def] >>
      rename1 `SOME x` >> PairCases_on `x` >> gvs[]) >>
  rpt strip_tac >>
  `n < phi_prefix_length bb.bb_instructions` by decide_tac >>
  `~((lbl,n) IN FDOM (fmp_stage_plan infos ctx fn))` by
    metis_tac[fmp_entry_phi_plan_absent] >>
  `(EL n bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[phi_prefix_length_el_phi] >>
  `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\ lbl = rl ==>
    rp <> SUC n` by metis_tac[fmp_entry_root_label] >>
  `(EL n bb.bb_instructions).inst_opcode <> DALLOCA` by simp[] >>
  drule_all fmp_stage_tidx_suc >> simp[]
QED

Theorem fmp_entry_block_phis:
  fmp_stage_lowered infos ctx runner fn fn' /\
  MEM bb fn.fn_blocks /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  bb.bb_label <> (HD fn.fn_blocks).bb_label ==>
  ?bb'. lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
    collect_phis bb'.bb_instructions = collect_phis bb.bb_instructions /\
    phi_prefix_length bb'.bb_instructions = phi_prefix_length bb.bb_instructions
Proof
  strip_tac >>
  Cases_on `fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
      (info.fi_needs_fmp \/ info.fi_publishes_fmp)`
  >- (`!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
        bb.bb_label = rl ==> rp <= 0` by metis_tac[fmp_entry_root_label] >>
      `0 <= LENGTH bb.bb_instructions` by simp[] >>
      drule fmp_stage_tidx_code >>
      disch_then (qspecl_then [`0`, `bb`] mp_tac) >> simp[] >> strip_tac >>
      `fmp_stage_tidx (fmp_stage_plan infos ctx fn)
        (fmp_stage_root infos ctx fn) bb.bb_label bb.bb_instructions 0 = 0` by
        (irule fmp_entry_phi_tidx >> simp[]) >>
      gvs[] >>
      drule fmp_entry_indexed_phis >>
      (impl_tac >- (rpt strip_tac >>
        `~((bb.bb_label,n) IN FDOM (fmp_stage_plan infos ctx fn))` by
          metis_tac[fmp_entry_phi_plan_absent] >>
        gvs[finite_mapTheory.FLOOKUP_DEF])) >>
      simp[]) >>
  drule_all fmp_stage_unlowered >> strip_tac >>
  qexists_tac `bb` >> simp[]
QED

Theorem fmp_entry_jump_dfs:
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  active_inst fn bi s /\ MEM bi.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst k C bi s = OK (jump_to lbl s) ==>
  MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre
Proof
  strip_tac >> drule_all fmp_entry_jump_edge >> strip_tac >>
  `MEM s.vs_current_bb (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `MEM lbl (fn_labels fn)` by
    metis_tac[venomWfTheory.wf_function_def, venomWfTheory.fn_succs_closed_def] >>
  metis_tac[current_all_labels_dfs_pre]
QED
