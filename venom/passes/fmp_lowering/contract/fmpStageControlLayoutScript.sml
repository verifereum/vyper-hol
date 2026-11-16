(* Layout boundaries for the stage control map. *)
Theory fmpStageControlLayout
Ancestors
  fmpStageRel fmpStepLayout fmpLowerIndexedProps fmpLowerProps fmpLowerDefs
  fmpStageControlWalk fmpStepOpaque
  fmpReclaimDefs fmpWfDefs venomInst venomWf list rich_list finite_map

Theorem fmp_control_fresh_runner[local]:
  fresh_ir_var s = (v,s') ==>
  MEM v s'.irs_used_vars /\
  !x. MEM x s.irs_used_vars ==> MEM x s'.irs_used_vars
Proof
  strip_tac >> drule irSupplyTheory.fresh_ir_var_contract >> simp[]
QED

Theorem fmp_control_rewrite:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  FLOOKUP infos fn.fn_name = SOME info /\
  (info.fi_needs_fmp \/ info.fi_publishes_fmp) ==>
  ?plan users oldpc suffix root newpc s0 s1 s2 blocks out.
    analyze_fmp_reclaims infos ctx fn = SOME plan /\
    fmp_reclaim_input fn plan /\
    fmp_stage_plan infos ctx fn = plan /\
    split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
    fmp_make_root_layout ctx fn info runner s0 =
      SOME (FmpRootLayout (LENGTH users) root newpc s1) /\
    fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
      SOME (FmpBlocksResult blocks [] s2) /\
    fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s2) blocks =
      SOME (out,s2) /\
    fn'.fn_blocks = out /\ (newpc = NONE <=> oldpc = NONE) /\
    MEM runner s1.irs_used_vars /\
    (!v. MEM v (fn_ir_vars fn) ==> MEM v s1.irs_used_vars)
Proof
  simp[fmp_stage_lowered_def] >> rpt strip_tac >>
  gvs[fmp_lower_function_with_info_def, AllCaseEqs()] >>
  qpat_x_assum `fresh_ir_var _ = _`
    (fn th => assume_tac th >>
              strip_assume_tac (MATCH_MP fmp_control_fresh_runner th)) >>
  Cases_on `root_layout` >> gvs[] >>
  drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def] >>
  `?users oldpc suffix. split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix)` by
    (gvs[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule fmp_install_root_supply >> strip_tac >> gvs[] >>
  drule fmp_make_root_layout_used_vars >> strip_tac >>
  gvs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
      venomFnScheduleRunnerTheory.list_subset_def, EVERY_MEM] >>
  simp[fmp_stage_plan_def] >> metis_tac[]
QED

Theorem fmp_control_point_keys[local]:
  !n. ALL_DISTINCT (MAP FST (FLAT (GENLIST (\k.
    case FLOOKUP plan (lbl,k) of NONE => [] | SOME b => [((lbl,k),b)]) n)))
Proof
  Induct >> simp[GENLIST, FLAT_SNOC, MAP_APPEND, ALL_DISTINCT_APPEND] >>
  Cases_on `FLOOKUP plan (lbl,n)` >> simp[] >>
  simp[MEM_MAP] >> rpt strip_tac >>
  gvs[MEM_FLAT, MEM_GENLIST, AllCaseEqs()]
QED

Theorem fmp_control_plan_keys:
  !bbs. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
  ALL_DISTINCT (MAP FST (fmp_plan_to_alist (fn with fn_blocks := bbs) plan))
Proof
  Induct >> simp[fmp_plan_to_alist_def, MAP_FLAT, MAP_MAP_o,
    combinTheory.o_DEF, ALL_DISTINCT_APPEND] >> rpt strip_tac
  >- (rewrite_tac[GSYM MAP_FLAT] >> irule fmp_control_point_keys)
  >- gvs[fmp_plan_to_alist_def, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  gvs[MEM_MAP, MEM_FLAT, MEM_GENLIST, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem fmp_control_leftover_keys:
  !xs k s rs out left s'.
  fmp_lower_indexed infos ctx runner lbl k s rs xs = SOME (out,left,s') /\
  ALL_DISTINCT (MAP FST rs) ==> ALL_DISTINCT (MAP FST left)
Proof
  Induct >- simp[fmp_lower_indexed_def] >>
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >> gvs[] >>
  drule_all fmp_control_select_distinct >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem fmp_control_blocks_walk:
  !bbs s rs out left s' bb.
  fmp_lower_blocks infos ctx runner s rs bbs = SOME (FmpBlocksResult out left s') /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  ALL_DISTINCT (MAP FST rs) /\ MEM bb bbs ==>
  ?code rs0 s0 left0 s1.
    (!v. MEM v s.irs_used_vars ==> MEM v s0.irs_used_vars) /\
    lookup_block bb.bb_label out = SOME (bb with bb_instructions := code) /\
    ALL_DISTINCT (MAP FST rs0) /\
    (!j b. MEM ((bb.bb_label,j),b) rs0 <=> MEM ((bb.bb_label,j),b) rs) /\
    fmp_lower_indexed infos ctx runner bb.bb_label 0 s0 rs0 bb.bb_instructions =
      SOME (code,left0,s1)
Proof
  Induct >- simp[] >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- (qexistsl [`insts`, `rs`, `s`, `later`, `s2`] >>
      simp[lookup_block_def, FIND_thm]) >>
  drule_all fmp_control_leftover_keys >> strip_tac >>
  first_x_assum drule >> simp[] >> disch_then drule >> strip_tac >>
  qexistsl [`code`, `rs0`, `s0`, `left0`, `s1`] >> simp[] >>
  conj_tac >- metis_tac[fmp_control_indexed_vars_mono] >>
  conj_tac
  >- (gvs[lookup_block_def, FIND_thm, MEM_MAP] >> metis_tac[]) >>
  qpat_assum `fmp_lower_indexed _ _ _ h.bb_label _ _ _ _ = _`
    (mp_then Any mp_tac fmp_lower_indexed_leftover) >> strip_tac >>
  rpt gen_tac >> first_x_assum (qspecl_then [`(bb.bb_label,j)`, `b`] mp_tac) >>
  simp[] >> `bb.bb_label <> h.bb_label` by (gvs[MEM_MAP] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem fmp_control_analyzed_labels:
  analyze_fmp_reclaims infos ctx fn = SOME plan ==>
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)
Proof
  simp[analyze_fmp_reclaims_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[wf_function_def, fn_labels_def]
QED

Theorem fmp_control_checked_walk:
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_reclaim_input fn plan /\
  fmp_lower_blocks infos ctx runner s (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks left s') /\ MEM bb fn.fn_blocks ==>
  ?code rs0 s0 left0 s1.
    (!v. MEM v s.irs_used_vars ==> MEM v s0.irs_used_vars) /\
    lookup_block bb.bb_label blocks = SOME (bb with bb_instructions := code) /\
    ALL_DISTINCT (MAP FST rs0) /\
    (!j b. MEM ((bb.bb_label,j),b) rs0 <=> FLOOKUP plan (bb.bb_label,j) = SOME b) /\
    fmp_lower_indexed infos ctx runner bb.bb_label 0 s0 rs0 bb.bb_instructions =
      SOME (code,left0,s1)
Proof
  strip_tac >> drule fmp_control_analyzed_labels >> strip_tac >>
  `ALL_DISTINCT (MAP FST (fmp_plan_to_alist fn plan))` by
    (mp_tac fmp_control_plan_keys >>
     simp[fmp_plan_to_alist_def]) >>
  drule_all fmp_control_blocks_walk >> strip_tac >>
  qexistsl [`code`, `rs0`, `s0`, `left0`, `s1`] >>
  simp[] >> metis_tac[MEM_fmp_plan_to_alist_FLOOKUP]
QED

Theorem fmp_control_install_suffix:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  (newpc = NONE <=> oldpc = NONE) /\
  LENGTH users + LENGTH (OPTION_TO_LIST oldpc) <= m /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s) (entry::rest) =
    SOME (out,s') ==>
  ?entry'. out = entry'::rest /\ entry'.bb_label = entry.bb_label /\
    DROP (m + LENGTH (OPTION_TO_LIST root)) entry'.bb_instructions =
      DROP m entry.bb_instructions /\
    (!j. j < LENGTH users ==> EL j entry'.bb_instructions = EL j users)
Proof
  strip_tac >> drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  Cases_on `oldpc` >> Cases_on `newpc` >>
  gvs[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
  Cases_on `fn_is_context_entry ctx fn` >>
  simp[DROP_APPEND, EL_APPEND1] >>
  `LENGTH users <= m + LENGTH (OPTION_TO_LIST root)` by decide_tac >>
  `LENGTH (OPTION_TO_LIST root) <= m + LENGTH (OPTION_TO_LIST root) - LENGTH users` by decide_tac >>
  simp[DROP_LENGTH_TOO_LONG] >> AP_TERM_TAC >> decide_tac
QED

Theorem fmp_control_root_layout:
  fn.fn_fmp_signature = NONE /\ FLOOKUP infos fn.fn_name = SOME info /\
  fn.fn_blocks = entry::rest /\
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fmp_make_root_layout ctx fn info runner s = SOME (FmpRootLayout n root newpc s') ==>
  (root = NONE <=> ~info.fi_needs_fmp) /\
  (root = NONE ==> newpc = oldpc) /\
  fmp_stage_root infos ctx fn =
    (if root = NONE then NONE else
       SOME (entry.bb_label, LENGTH users + LENGTH (OPTION_TO_LIST oldpc)))
Proof
  simp[fmp_make_root_layout_def] >> rpt strip_tac >>
  Cases_on `info.fi_needs_fmp` >>
  Cases_on `fn_is_context_entry ctx fn` >>
  Cases_on `oldpc` >>
  gvs[AllCaseEqs(), fmp_stage_root_def, callLayoutDefsTheory.OPTION_TO_LIST_def]
QED

Theorem fmp_control_install_no_root:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) NONE oldpc s) (entry::rest) =
    SOME (out,s') ==>
  out = entry::rest
Proof
  Cases_on `oldpc` >>
  simp[fmp_install_root_def, callLayoutDefsTheory.OPTION_TO_LIST_def] >>
  rpt strip_tac >> gvs[TAKE_APPEND1, DROP_APPEND1, DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
  Cases_on `fn_is_context_entry ctx fn` >> gvs[] >>
  qpat_x_assum `entry.bb_instructions = _` (SUBST1_TAC o GSYM) >>
  simp[basic_block_fupdselfid]
QED

Theorem fmp_control_prefix_plan_absent:
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fn.fn_blocks = entry::rest ==>
  !j. j < LENGTH users + LENGTH (OPTION_TO_LIST oldpc) ==>
    FLOOKUP plan (entry.bb_label,j) = NONE
Proof
  strip_tac >> drule split_fmp_entry_reconstruct >> strip_tac >> gvs[] >>
  drule split_fmp_entry_parameter_prefix >> strip_tac >>
  `lookup_block entry.bb_label fn.fn_blocks = SOME entry` by
    simp[lookup_block_def, FIND_thm] >>
  `!j b. j < LENGTH (users ++ option_CASE oldpc [] (\i. [i])) ==>
    ~MEM ((entry.bb_label,j),b) (fmp_plan_to_alist fn plan)` by
    metis_tac[analyze_fmp_reclaims_parameter_prefix_absent, APPEND_ASSOC] >>
  pop_assum mp_tac >> simp[MEM_fmp_plan_to_alist] >>
  Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
  rpt strip_tac >>
  Cases_on `FLOOKUP plan (entry.bb_label,j)` >> simp[] >>
  gvs[]
QED

Theorem fmp_control_install_other:
  fmp_install_root ctx fn layout (entry::rest) = SOME (out,s') /\
  lbl <> entry.bb_label ==>
  lookup_block lbl out = lookup_block lbl (entry::rest)
Proof
  Cases_on `layout` >> simp[fmp_install_root_def] >> rpt strip_tac >> gvs[] >>
  simp[lookup_block_def, FIND_thm] >> metis_tac[]
QED

Theorem fmp_control_install_users:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail /\
  (newpc = NONE <=> oldpc = NONE) /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s) (entry::rest) =
    SOME (out,s') ==>
  ?entry'. out = entry'::rest /\ entry'.bb_label = entry.bb_label /\
    LENGTH users <= LENGTH entry'.bb_instructions /\
    (!j. j < LENGTH users ==> EL j entry'.bb_instructions = EL j users)
Proof
  strip_tac >> drule_all fmp_install_root_exact_prefix >> strip_tac >> gvs[] >>
  Cases_on `fn_is_context_entry ctx fn` >> simp[EL_APPEND1]
QED
