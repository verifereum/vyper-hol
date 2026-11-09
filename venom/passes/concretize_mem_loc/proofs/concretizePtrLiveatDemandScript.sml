Theory concretizePtrLiveatDemand
Ancestors
  concretizeAnalysisLivenessClosure concretizePtrOrdering concretizePtrUsedDemand
  singleWriterScan concretizeMemLocDefs finite_map list indexedLists

Theorem ptr_liveat_one_pass_scan:
  ml_one_pass bp mems sizes pallocas cfg fn la us = (changed,la',us') /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\
  EVERY (\bb. bb.bb_instructions <> []) fn.fn_blocks /\
  (!lbl. MEM a (ml_lookup la (lbl,0)) <=> T IN X lbl) ==>
  (!lbl. MEM a (ml_lookup la' (lbl,0)) <=>
    T IN sw_scan (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) X lbl)
Proof
  simp[ml_one_pass_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_all ml_liveat_pass_sw_scan >> simp[]
QED

Theorem ptr_liveat_one_pass_ordered[local]:
  ml_one_pass bp mems sizes pallocas cfg fn la us = (changed,la',us') /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la ==>
  ptr_ml_ordered la'
Proof
  simp[ml_one_pass_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_all ptr_liveat_pass_ordered >>
  disch_then (qspecl_then [`sizes`, `cfg.cfg_dfs_post`, `cfg`, `bp`, `fn.fn_blocks`] mp_tac) >>
  simp[]
QED

Theorem ptr_liveat_fuel_rounds:
  !fuel la us n.
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\
  EVERY (\bb. bb.bb_instructions <> []) fn.fn_blocks /\
  (!lbl. MEM a (ml_lookup la (lbl,0)) <=>
    T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n lbl) ==>
  (!lbl. MEM a (ml_lookup
    (FST (ml_iterate_fuel fuel bp mems sizes pallocas cfg fn la us)) (lbl,0)) <=>
    T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) (n+fuel) lbl)
Proof
  Induct >- simp[ml_iterate_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  pure_once_rewrite_tac[ml_iterate_fuel_def] >>
  pure_rewrite_tac[LET_THM] >> pairarg_tac >> simp[] >>
  `!lbl. MEM a (ml_lookup liveat' (lbl,0)) <=>
    T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) (SUC n) lbl` by
    (simp[Once sw_rounds_def] >> drule_all ptr_liveat_one_pass_scan >> simp[]) >>
  `ptr_ml_ordered liveat'` by (drule_all ptr_liveat_one_pass_ordered >> simp[]) >>
  Cases_on `changed`
  >- (simp[] >> `n + SUC fuel = SUC n + fuel` by simp[] >>
      pop_assum SUBST1_TAC >> first_x_assum irule >> simp[]) >>
  gvs[] >> drule ml_one_pass_false_boundary >> strip_tac >>
  `!lbl. T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) (SUC n) lbl <=>
    T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n lbl` by metis_tac[] >>
  drule ptr_rounds_member_stationary >> strip_tac >> metis_tac[]
QED

Theorem ptr_liveat_fuel_endpoints:
  EVERY (\bb. bb.bb_instructions <> []) fn.fn_blocks /\
  (!nm. OL alloc_to (mems nm)) ==>
  (!lbl. MEM a (ml_lookup
    (FST (ml_iterate_fuel fuel bp mems sizes pallocas cfg fn FEMPTY FEMPTY)) (lbl,0)) <=>
    T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) fuel lbl)
Proof
  strip_tac >>
  qspecl_then [`fuel`, `FEMPTY`, `FEMPTY`, `0`] mp_tac ptr_liveat_fuel_rounds >>
  simp[sw_rounds_def, ml_lookup_def]
QED

Theorem ptr_liveat_sweep_other_label[local]:
  !order la. (!b. MEM b (ml_scan_blocks blocks order) ==> b.bb_label <> lbl) ==>
  ml_lookup (SND (ml_one_pass_liveat bp mems sizes cfg blocks order la)) (lbl,i) =
  ml_lookup la (lbl,i)
Proof
  Induct >> simp[ml_one_pass_liveat_def, ml_scan_blocks_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  `ml_lookup la'' (lbl,i) = ml_lookup la' (lbl,i)` by
    (first_x_assum (qspec_then `la'` mp_tac) >> simp[] >> metis_tac[]) >>
  drule ml_liveat_block_other_label >> simp[] >> metis_tac[]
QED

Theorem ptr_liveat_sweep_records[local]:
  !order la X.
  EVERY (\b. b.bb_instructions <> []) blocks /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\
  EVERY (\d. MEM d ds)
    (MAP (ml_liveat_boundary_desc a bp mems sizes cfg) (ml_scan_blocks blocks order)) /\
  sw_consistent ds /\ sw_admissible ds X /\
  (!lbl. MEM a (ml_lookup la (lbl,0)) <=> T IN X lbl) /\
  MEM bb (ml_scan_blocks blocks order) /\ i < LENGTH bb.bb_instructions /\
  ml_liveat_record_bit a bp mems sizes bb.bb_label (bb.bb_label,i)
    (MAPi (\j inst. (j,inst)) bb.bb_instructions)
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\ T IN X lbl) F ==>
  MEM a (ml_lookup (SND (ml_one_pass_liveat bp mems sizes cfg blocks order la))
    (bb.bb_label,i))
Proof
  Induct >- simp[ml_scan_blocks_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `FIND (\b. b.bb_label = h) blocks`
  >- (gvs[ml_one_pass_liveat_def, ml_scan_blocks_def] >>
      first_x_assum (qspecl_then [`la`, `X`] mp_tac) >> simp[]) >>
  rename1 `FIND _ blocks = SOME head` >>
  `MEM head blocks` by metis_tac[venomExecProofsTheory.FIND_MEM] >>
  `head.bb_label = h` by
    (drule venomExecProofsTheory.FIND_P >> simp[]) >>
  `head.bb_instructions <> []` by
    (qpat_x_assum `EVERY (\b. b.bb_instructions <> []) blocks` mp_tac >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  gns[ml_scan_blocks_def] >>
  qpat_x_assum `MEM _ ds /\ _` strip_assume_tac >>
  Cases_on `ml_liveat_block bp mems sizes cfg la head` >>
  rename1 `ml_liveat_block bp mems sizes cfg la head = (ch,mid)` >>
  `ptr_ml_ordered mid` by
    (drule_all ptr_liveat_block_ordered >>
     disch_then (qspecl_then [`sizes`, `cfg`, `bp`, `head`] mp_tac) >> simp[]) >>
  `!lbl. MEM a (ml_lookup mid (lbl,0)) <=>
    T IN sw_update (ml_liveat_boundary_desc a bp mems sizes cfg head) X lbl` by
    (drule_all ml_liveat_block_sw_update >> simp[]) >>
  `sw_admissible ds (sw_update (ml_liveat_boundary_desc a bp mems sizes cfg head) X)` by
    (irule sw_update_admissible >> simp[]) >>
  `sw_le X (sw_update (ml_liveat_boundary_desc a bp mems sizes cfg head) X)` by
    (irule sw_update_grows >> qexists_tac `ds` >> simp[]) >>
  simp[ml_one_pass_liveat_def] >>
  Cases_on `MEM bb (ml_scan_blocks blocks order)`
  >- (first_x_assum (qspecl_then [`mid`,
        `sw_update (ml_liveat_boundary_desc a bp mems sizes cfg head) X`] mp_tac) >>
      impl_tac
      >- (simp[] >>
          `!lbl. T IN X lbl ==> T IN sw_update
            (ml_liveat_boundary_desc a bp mems sizes cfg head) X lbl` by
            metis_tac[sw_le_def, pred_setTheory.SUBSET_DEF] >>
          qpat_x_assum `ml_liveat_record_bit _ _ _ _ _ _ _ _ _` mp_tac >>
          once_rewrite_tac[ml_liveat_record_bit_affine] >> metis_tac[]) >>
      pairarg_tac >> simp[]) >>
  `head = bb` by gvs[] >> gvs[] >>
  `MEM a (ml_lookup mid (bb.bb_label,i))` by
    (drule_all ml_liveat_block_record_exact >> simp[] >> metis_tac[]) >>
  `ml_lookup (SND (ml_one_pass_liveat bp mems sizes cfg blocks order mid)) (bb.bb_label,i) =
    ml_lookup mid (bb.bb_label,i)` by
    (irule ptr_liveat_sweep_other_label >> rpt strip_tac >>
     drule_all ml_scan_blocks_find >> simp[] >> metis_tac[]) >>
  pairarg_tac >> gvs[]
QED

Theorem ptr_liveat_one_pass_records[local]:
  ml_one_pass bp mems sizes pallocas cfg fn la us = (changed,la',us') /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\
  EVERY (\b. b.bb_instructions <> []) fn.fn_blocks /\
  (!lbl. MEM a (ml_lookup la (lbl,0)) <=>
    T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n lbl) /\
  MEM bb (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post) /\ i < LENGTH bb.bb_instructions /\
  ml_liveat_record_bit a bp mems sizes bb.bb_label (bb.bb_label,i)
    (MAPi (\j inst. (j,inst)) bb.bb_instructions)
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\
      T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n lbl) F ==>
  MEM a (ml_lookup la' (bb.bb_label,i))
Proof
  strip_tac >>
  `sw_consistent (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post))` by
    (irule ml_scan_blocks_consistent >> simp[ml_boundary_desc_out]) >>
  `MEM a (ml_lookup
    (SND (ml_one_pass_liveat bp mems sizes cfg fn.fn_blocks cfg.cfg_dfs_post la))
    (bb.bb_label,i))` by
    (irule ptr_liveat_sweep_records >> simp[] >>
     qexists_tac `sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
       (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n` >>
     qexists_tac `MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
       (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)` >>
     simp[sw_rounds_admissible, EVERY_MEM]) >>
  gvs[ml_one_pass_def] >> ntac 2 (pairarg_tac >> gvs[])
QED

Theorem ptr_liveat_fuel_round_records[local]:
  !fuel la us n.
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\
  EVERY (\b. b.bb_instructions <> []) fn.fn_blocks /\
  (!lbl. MEM a (ml_lookup la (lbl,0)) <=>
    T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n lbl) /\
  MEM bb (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post) /\ i < LENGTH bb.bb_instructions /\
  ml_liveat_record_bit a bp mems sizes bb.bb_label (bb.bb_label,i)
    (MAPi (\j inst. (j,inst)) bb.bb_instructions)
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\
      T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) (n+fuel) lbl) F ==>
  MEM a (ml_lookup
    (FST (ml_iterate_fuel (SUC fuel) bp mems sizes pallocas cfg fn la us)) (bb.bb_label,i))
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      pure_once_rewrite_tac[ml_iterate_fuel_def] >>
      pure_rewrite_tac[LET_THM] >> pairarg_tac >> simp[] >>
      Cases_on `changed` >> simp[ml_iterate_fuel_def] >>
      fs[] >> drule_all ptr_liveat_one_pass_records >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  pure_once_rewrite_tac[ml_iterate_fuel_def] >>
  pure_rewrite_tac[LET_THM] >> pairarg_tac >> simp[] >>
  `!lbl. MEM a (ml_lookup liveat' (lbl,0)) <=>
    T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) (SUC n) lbl` by
    (simp[Once sw_rounds_def] >> drule_all ptr_liveat_one_pass_scan >> simp[]) >>
  `ptr_ml_ordered liveat'` by (drule_all ptr_liveat_one_pass_ordered >> simp[]) >>
  Cases_on `changed`
  >- (simp[] >> first_x_assum (qspecl_then [`liveat'`, `used'`, `SUC n`] mp_tac) >>
      fs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM]) >>
  simp[] >> drule ml_one_pass_false_boundary >> strip_tac >>
  `!lbl. T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) (SUC n) lbl <=>
    T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n lbl` by metis_tac[] >>
  drule ptr_rounds_member_stationary >> strip_tac >>
  `ml_liveat_record_bit a bp mems sizes bb.bb_label (bb.bb_label,i)
    (MAPi (\j inst. (j,inst)) bb.bb_instructions)
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\
      T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n lbl) F` by
    (qpat_x_assum `!k v. _` (qspec_then `SUC fuel` assume_tac) >>
     qpat_x_assum `ml_liveat_record_bit _ _ _ _ _ _ _ _ _` mp_tac >> simp[]) >>
  drule_all ptr_liveat_one_pass_records >> simp[]
QED

Theorem ptr_liveat_fuel_records:
  EVERY (\b. b.bb_instructions <> []) fn.fn_blocks /\
  (!nm. OL alloc_to (mems nm)) /\
  MEM bb (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post) /\
  i < LENGTH bb.bb_instructions /\ n + 2 <= fuel /\
  ml_liveat_record_bit a bp mems sizes bb.bb_label (bb.bb_label,i)
    (MAPi (\j inst. (j,inst)) bb.bb_instructions)
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\
      T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n lbl) F ==>
  MEM a (ml_lookup
    (FST (ml_iterate_fuel fuel bp mems sizes pallocas cfg fn FEMPTY FEMPTY)) (bb.bb_label,i))
Proof
  strip_tac >>
  `sw_consistent (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post))` by
    (irule ml_scan_blocks_consistent >> simp[ml_boundary_desc_out]) >>
  `sw_le (sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n)
    (sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) (PRE fuel))` by
    (irule sw_rounds_mono >> simp[] >> decide_tac) >>
  `ml_liveat_record_bit a bp mems sizes bb.bb_label (bb.bb_label,i)
    (MAPi (\j inst. (j,inst)) bb.bb_instructions)
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\
      T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) (PRE fuel) lbl) F` by
    (`!lbl. T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n lbl ==>
      T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) (PRE fuel) lbl` by
        metis_tac[sw_le_def, pred_setTheory.SUBSET_DEF] >>
     qpat_x_assum `ml_liveat_record_bit _ _ _ _ _ _ _ _ _` mp_tac >>
     once_rewrite_tac[ml_liveat_record_bit_affine] >> metis_tac[]) >>
  `fuel = SUC (PRE fuel)` by decide_tac >>
  qpat_x_assum `fuel = _` (fn th => once_rewrite_tac[th]) >>
  qspecl_then [`PRE fuel`, `FEMPTY`, `FEMPTY`, `0`] mp_tac ptr_liveat_fuel_round_records >>
  simp[sw_rounds_def, ml_lookup_def]
QED
