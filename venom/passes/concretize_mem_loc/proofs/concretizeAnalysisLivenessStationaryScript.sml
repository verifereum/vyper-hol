Theory concretizeAnalysisLivenessStationary
Ancestors concretizeAnalysisLivenessClosure concretizeAnalysisLivenessTransfer
  concretizeMemLocDefs singleWriterScan concretizePtrOrdering
  list pred_set finite_map

Theorem ml_iterate_fuel_from_bottom_round:
  ml_iterate_fuel fuel bpr mems sizes pallocas cfg fn FEMPTY FEMPTY = (la,us) ==>
  ?n. ml_full_rounds bpr mems sizes pallocas cfg fn n = (la,us)
Proof
  strip_tac >>
  `ml_iterate_fuel fuel bpr mems sizes pallocas cfg fn
    (FST (ml_full_rounds bpr mems sizes pallocas cfg fn 0))
    (SND (ml_full_rounds bpr mems sizes pallocas cfg fn 0)) = (la,us)` by
    simp[ml_full_rounds_def] >>
  drule ml_iterate_fuel_full_rounds_cases >> simp[] >> strip_tac >>
  metis_tac[]
QED

Theorem ml_iterate_fuel_boundary_witnesses:
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  EVERY (\bb. bb.bb_instructions <> []) fn.fn_blocks /\
  ml_iterate_fuel fuel bpr mems sizes pallocas cfg fn FEMPTY FEMPTY = (la,us) ==>
  ?X Y.
    sw_admissible (MAP (ml_liveat_boundary_desc a bpr mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) X /\
    sw_admissible (MAP (ml_used_boundary_desc a bpr mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) Y /\
    (!lbl. MEM a (ml_lookup la (lbl,0)) <=> T IN X lbl) /\
    (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks us lbl) <=> T IN Y lbl)
Proof
  strip_tac >> drule ml_iterate_fuel_from_bottom_round >> strip_tac >>
  qexistsl [
    `sw_rounds (MAP (ml_liveat_boundary_desc a bpr mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n`,
    `sw_rounds (MAP (ml_used_boundary_desc a bpr mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) n`] >>
  rpt conj_tac
  >- (irule sw_rounds_admissible >> irule ml_scan_blocks_consistent >>
      simp[ml_boundary_desc_out])
  >- (irule sw_rounds_admissible >> irule ml_scan_blocks_consistent >>
      simp[ml_boundary_desc_out])
  >> drule_all ml_full_rounds_boundary_exact >>
  disch_then (qspecl_then [`sizes`, `cfg`, `bpr`, `a`, `n`] mp_tac) >> simp[]
QED

Theorem ml_one_pass_boundary_stationary:
  ml_one_pass bpr mems sizes pallocas cfg fn la us = (changed,la',us') /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\
  EVERY (\bb. bb.bb_instructions <> []) fn.fn_blocks /\
  (!lbl. MEM a (ml_lookup la (lbl,0)) <=> T IN X lbl) /\
  (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks us lbl) <=> T IN Y lbl) /\
  (!addr. MEM a (ml_lookup la' addr) <=> MEM a (ml_lookup la addr)) /\
  (!addr. MEM a (ml_lookup us' addr) <=> MEM a (ml_lookup us addr)) ==>
  (!lbl. T IN sw_scan (MAP (ml_liveat_boundary_desc a bpr mems sizes cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) X lbl <=> T IN X lbl) /\
  (!lbl. T IN sw_scan (MAP (ml_used_boundary_desc a bpr mems pallocas cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) Y lbl <=> T IN Y lbl)
Proof
  strip_tac >>
  `!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks us' lbl) <=>
         MEM a (ml_used_boundary_lookup fn.fn_blocks us lbl)` by
    (qpat_x_assum `!lbl. MEM a (ml_used_boundary_lookup _ _ lbl) <=> _` kall_tac >>
     gen_tac >> simp[ml_used_boundary_lookup_def] >>
     Cases_on `FIND (\bb. bb.bb_label = lbl) fn.fn_blocks` >> simp[]) >>
  drule_all ml_one_pass_sw_scan >> metis_tac[]
QED

Theorem ml_liveat_stationary_block:
  ml_liveat_block bpr mems sizes cfg la bb = (changed,la') /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\
  bb.bb_instructions <> [] /\
  (!lbl. MEM a (ml_lookup la (lbl,0)) <=> T IN X lbl) /\
  sw_consistent ds /\ sw_admissible ds X /\
  (!lbl. T IN sw_scan ds X lbl <=> T IN X lbl) /\
  MEM (ml_liveat_boundary_desc a bpr mems sizes cfg bb) ds ==>
  !lbl. MEM a (ml_lookup la' (lbl,0)) <=> T IN X lbl
Proof
  strip_tac >> drule_all ml_liveat_block_sw_update >> strip_tac >>
  drule_all sw_fixed_writer_member >>
  simp[ml_boundary_desc_out] >> strip_tac >>
  gen_tac >> simp[sw_update_def] >>
  Cases_on `lbl = bb.bb_label` >> gvs[ml_boundary_desc_out]
QED

Theorem ml_used_stationary_block:
  ml_used_block bpr mems pallocas cfg us bb blocks = (changed,us') /\
  FIND (\b. b.bb_label = bb.bb_label) blocks = SOME bb /\
  bb.bb_instructions <> [] /\
  (!lbl. MEM a (ml_used_boundary_lookup blocks us lbl) <=> T IN X lbl) /\
  sw_consistent ds /\ sw_admissible ds X /\
  (!lbl. T IN sw_scan ds X lbl <=> T IN X lbl) /\
  MEM (ml_used_boundary_desc a bpr mems pallocas cfg bb) ds ==>
  !lbl. MEM a (ml_used_boundary_lookup blocks us' lbl) <=> T IN X lbl
Proof
  strip_tac >> drule_all ml_used_block_sw_update >> strip_tac >>
  drule_all sw_fixed_writer_member >>
  simp[ml_boundary_desc_out] >> strip_tac >>
  gen_tac >> simp[sw_update_def] >>
  Cases_on `lbl = bb.bb_label` >> gvs[ml_boundary_desc_out]
QED

Theorem ml_liveat_stationary_record:
  !la c la'.
  ml_one_pass_liveat bpr mems sizes cfg blocks lbls la = (c,la') /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\
  EVERY (\bb. bb.bb_instructions <> []) blocks /\
  (!l. MEM a (ml_lookup la (l,0)) <=> T IN X l) /\
  sw_consistent ds /\ sw_admissible ds X /\
  (!l. T IN sw_scan ds X l <=> T IN X l) /\
  EVERY (\bb. MEM (ml_liveat_boundary_desc a bpr mems sizes cfg bb) ds)
    (ml_scan_blocks blocks lbls) /\
  FIND (\b. b.bb_label = lbl) blocks = SOME target /\
  i < LENGTH target.bb_instructions /\
  (MEM lbl lbls \/
    (MEM a (ml_lookup la (lbl,i)) <=>
      ml_liveat_record_bit a bpr mems sizes lbl (lbl,i)
        (MAPi (\j inst. (j,inst)) target.bb_instructions)
        (?l. MEM l (cfg_succs_of cfg lbl) /\ T IN X l) F)) ==>
  (MEM a (ml_lookup la' (lbl,i)) <=>
    ml_liveat_record_bit a bpr mems sizes lbl (lbl,i)
      (MAPi (\j inst. (j,inst)) target.bb_instructions)
      (?l. MEM l (cfg_succs_of cfg lbl) /\ T IN X l) F)
Proof
  Induct_on `lbls` >- simp[ml_one_pass_liveat_def] >>
  pop_assum (mk_asm "ih") >>
  rpt gen_tac >> pure_once_rewrite_tac[ml_one_pass_liveat_def] >>
  Cases_on `FIND (\bb. bb.bb_label = h) blocks` >> simp[ml_scan_blocks_def]
  >- (strip_tac >> gvs[] >> asm "ih" irule >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rename1 `FIND _ blocks = SOME bb` >>
  ntac 2 (pairarg_tac >> simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >> gnvs[] >>
  rename1 `ml_liveat_block bpr mems sizes cfg la bb = (c1,mid)` >>
  `MEM bb blocks` by metis_tac[venomExecProofsTheory.FIND_MEM] >>
  `bb.bb_label = h` by
    (qpat_x_assum `FIND _ blocks = SOME bb` mp_tac >>
     disch_then (mp_tac o MATCH_MP venomExecProofsTheory.FIND_P) >> simp[]) >>
  `bb.bb_instructions <> []` by fs[EVERY_MEM] >>
  `ptr_ml_ordered mid` by metis_tac[ptr_liveat_block_ordered, pairTheory.SND] >>
  `!l. MEM a (ml_lookup mid (l,0)) <=> T IN X l` by
    (drule_all ml_liveat_stationary_block >> simp[]) >>
  asm "ih" irule >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`c2`, `mid`] >> simp[] >>
  Cases_on `MEM lbl lbls` >> simp[] >>
  Cases_on `lbl = h` >> gvs[]
  >- (drule_all ml_liveat_block_record_exact >>
      disch_then (qspec_then `a` mp_tac) >> simp[]) >>
  drule_all ml_liveat_block_other_label >> simp[]
QED

Theorem ml_used_stationary_record:
  !us c us'.
  ml_one_pass_used bpr mems pallocas cfg blocks lbls us = (c,us') /\
  EVERY (\bb. bb.bb_instructions <> []) blocks /\
  (!l. MEM a (ml_used_boundary_lookup blocks us l) <=> T IN X l) /\
  sw_consistent ds /\ sw_admissible ds X /\
  (!l. T IN sw_scan ds X l <=> T IN X l) /\
  EVERY (\bb. MEM (ml_used_boundary_desc a bpr mems pallocas cfg bb) ds)
    (ml_scan_blocks blocks lbls) /\
  FIND (\b. b.bb_label = lbl) blocks = SOME target /\
  i < LENGTH target.bb_instructions /\
  (MEM lbl lbls \/
    (MEM a (ml_lookup us (lbl,i)) <=>
      ml_used_record_bit a bpr mems lbl (lbl,i)
        (MAPi (\j inst. (j,inst)) target.bb_instructions)
        (MEM a pallocas \/ ?l. MEM l (cfg_preds_of cfg lbl) /\ T IN X l) F)) ==>
  (MEM a (ml_lookup us' (lbl,i)) <=>
    ml_used_record_bit a bpr mems lbl (lbl,i)
      (MAPi (\j inst. (j,inst)) target.bb_instructions)
      (MEM a pallocas \/ ?l. MEM l (cfg_preds_of cfg lbl) /\ T IN X l) F)
Proof
  Induct_on `lbls` >- simp[ml_one_pass_used_def] >>
  pop_assum (mk_asm "ih") >>
  rpt gen_tac >> pure_once_rewrite_tac[ml_one_pass_used_def] >>
  Cases_on `FIND (\bb. bb.bb_label = h) blocks` >> simp[ml_scan_blocks_def]
  >- (strip_tac >> gvs[] >> asm "ih" irule >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rename1 `FIND _ blocks = SOME bb` >>
  ntac 2 (pairarg_tac >> simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >> gnvs[] >>
  rename1 `ml_used_block bpr mems pallocas cfg us bb blocks = (c1,mid)` >>
  `MEM bb blocks` by metis_tac[venomExecProofsTheory.FIND_MEM] >>
  `bb.bb_label = h` by
    (qpat_x_assum `FIND _ blocks = SOME bb` mp_tac >>
     disch_then (mp_tac o MATCH_MP venomExecProofsTheory.FIND_P) >> simp[]) >>
  `bb.bb_instructions <> []` by fs[EVERY_MEM] >>
  `FIND (\b. b.bb_label = bb.bb_label) blocks = SOME bb` by simp[] >>
  `!l. MEM a (ml_used_boundary_lookup blocks mid l) <=> T IN X l` by
    (drule_all ml_used_stationary_block >> simp[]) >>
  asm "ih" irule >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`c2`, `mid`] >> simp[] >>
  Cases_on `MEM lbl lbls` >> simp[] >>
  Cases_on `lbl = h` >> gvs[]
  >- (drule_all ml_used_block_record_exact >>
      disch_then (qspec_then `a` mp_tac) >>
      fs[ml_used_boundary_lookup_def]) >>
  drule_all ml_used_block_other_label >> simp[]
QED

Theorem ml_iterate_fuel_stationary_witnesses:
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  EVERY (\bb. bb.bb_instructions <> []) fn.fn_blocks /\
  ml_iterate_fuel fuel bpr mems sizes pallocas cfg fn FEMPTY FEMPTY = (la,us) /\
  ml_one_pass bpr mems sizes pallocas cfg fn la us = (changed,la',us') /\
  (!addr. MEM a (ml_lookup la' addr) <=> MEM a (ml_lookup la addr)) /\
  (!addr. MEM a (ml_lookup us' addr) <=> MEM a (ml_lookup us addr)) ==>
  ?X Y.
    sw_admissible (MAP (ml_liveat_boundary_desc a bpr mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) X /\
    sw_admissible (MAP (ml_used_boundary_desc a bpr mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) Y /\
    (!lbl. MEM a (ml_lookup la (lbl,0)) <=> T IN X lbl) /\
    (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks us lbl) <=> T IN Y lbl) /\
    (!lbl. T IN sw_scan (MAP (ml_liveat_boundary_desc a bpr mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) X lbl <=> T IN X lbl) /\
    (!lbl. T IN sw_scan (MAP (ml_used_boundary_desc a bpr mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) Y lbl <=> T IN Y lbl)
Proof
  strip_tac >>
  `ptr_ml_ordered la` by
    (drule ml_iterate_fuel_from_bottom_round >> strip_tac >>
     drule_all ml_full_rounds_ordered >>
     disch_then (qspecl_then [`sizes`, `fn`, `cfg`, `bpr`, `n`] mp_tac) >> simp[]) >>
  drule_all ml_iterate_fuel_boundary_witnesses >>
  disch_then (qspec_then `a` strip_assume_tac) >>
  qexistsl [`X`, `Y`] >> simp[] >>
  drule_all ml_one_pass_boundary_stationary >> simp[]
QED

Theorem ml_liveat_stationary_rhs:
  sw_admissible (MAP (ml_liveat_boundary_desc a bpr mems sizes cfg)
    (ml_scan_blocks blocks lbls)) X /\
  (!l. T IN sw_scan (MAP (ml_liveat_boundary_desc a bpr mems sizes cfg)
    (ml_scan_blocks blocks lbls)) X l <=> T IN X l) /\
  MEM bb (ml_scan_blocks blocks lbls) ==>
  (T IN X bb.bb_label <=> ml_liveat_boundary_bit a bpr mems sizes bb
    (?l. MEM l (cfg_succs_of cfg bb.bb_label) /\ T IN X l))
Proof
  strip_tac >>
  `sw_consistent (MAP (ml_liveat_boundary_desc a bpr mems sizes cfg)
    (ml_scan_blocks blocks lbls))` by
    (irule ml_scan_blocks_consistent >> simp[ml_boundary_desc_out]) >>
  `MEM (ml_liveat_boundary_desc a bpr mems sizes cfg bb)
    (MAP (ml_liveat_boundary_desc a bpr mems sizes cfg)
      (ml_scan_blocks blocks lbls))` by (simp[MEM_MAP] >> qexists `bb` >> simp[]) >>
  drule_all sw_fixed_writer_member >>
  simp[ml_boundary_desc_out, ml_liveat_boundary_desc_rhs] >> metis_tac[]
QED

Theorem ml_used_stationary_rhs:
  sw_admissible (MAP (ml_used_boundary_desc a bpr mems pallocas cfg)
    (ml_scan_blocks blocks lbls)) X /\
  (!l. T IN sw_scan (MAP (ml_used_boundary_desc a bpr mems pallocas cfg)
    (ml_scan_blocks blocks lbls)) X l <=> T IN X l) /\
  MEM bb (ml_scan_blocks blocks lbls) ==>
  (T IN X bb.bb_label <=> ml_used_boundary_bit a bpr mems bb
    (MEM a pallocas \/ ?l. MEM l (cfg_preds_of cfg bb.bb_label) /\ T IN X l))
Proof
  strip_tac >>
  `sw_consistent (MAP (ml_used_boundary_desc a bpr mems pallocas cfg)
    (ml_scan_blocks blocks lbls))` by
    (irule ml_scan_blocks_consistent >> simp[ml_boundary_desc_out]) >>
  `MEM (ml_used_boundary_desc a bpr mems pallocas cfg bb)
    (MAP (ml_used_boundary_desc a bpr mems pallocas cfg)
      (ml_scan_blocks blocks lbls))` by (simp[MEM_MAP] >> qexists `bb` >> simp[]) >>
  drule_all sw_fixed_writer_member >>
  simp[ml_boundary_desc_out, ml_used_boundary_desc_rhs] >> metis_tac[]
QED
