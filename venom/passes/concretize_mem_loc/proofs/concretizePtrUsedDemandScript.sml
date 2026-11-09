Theory concretizePtrUsedDemand
Ancestors
  concretizePtrOrdering concretizePtrReadCoverage concretizeMemLocDefs
  concretizeAnalysisLivenessClosure concretizeAnalysisLivenessTransfer singleWriterScan
  finite_map list indexedLists

Theorem ptr_used_inst_membership:
  MEM a (FST (ml_used_inst bp mems label idx inst cur us)) <=>
    MEM a cur \/ ml_used_gen a bp mems inst
Proof
  Cases_on `ml_used_inst bp mems label idx inst cur us` >>
  drule ml_used_exact >> simp[]
QED

Theorem ptr_used_insts_membership:
  !cur us. MEM a (FST (ml_used_insts bp mems label cur us insts)) <=>
    MEM a cur \/ EXISTS (\p. ml_used_gen a bp mems (SND p)) insts
Proof
  Induct_on `insts` >- simp[ml_used_insts_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[ml_used_insts_def] >>
  pairarg_tac >> simp[] >>
  metis_tac[ptr_used_inst_membership, pairTheory.FST]
QED

Theorem ptr_used_insts_other_address[local]:
  !cur us. ~MEM addr (MAP (\p. (label,FST p)) insts) ==>
    ml_lookup (SND (ml_used_insts bp mems label cur us insts)) addr =
    ml_lookup us addr
Proof
  Induct_on `insts` >- simp[ml_used_insts_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[ml_used_insts_def, ml_used_inst_def] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[ml_lookup_def, FLOOKUP_UPDATE]
QED

Theorem ptr_used_inst_record[local]:
  ml_lookup (SND (ml_used_inst bp mems label idx inst cur us)) (label,idx) =
  FST (ml_used_inst bp mems label idx inst cur us)
Proof
  simp[ml_used_inst_def, ml_lookup_def, FLOOKUP_UPDATE]
QED

Theorem ptr_used_insts_input_records:
  !cur us idx inst. ALL_DISTINCT (MAP FST insts) /\
    MEM (idx,inst) insts /\ MEM a cur ==>
    MEM a (ml_lookup (SND (ml_used_insts bp mems label cur us insts)) (label,idx))
Proof
  Induct_on `insts` >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[ml_used_insts_def] >> strip_tac >>
  pairarg_tac >> gvs[]
  >- (`ml_lookup (SND (ml_used_insts bp mems label cur' us' insts)) (label,h0) =
        ml_lookup us' (label,h0)` by
        (irule ptr_used_insts_other_address >>
         gvs[listTheory.MEM_MAP] >> metis_tac[]) >>
      metis_tac[ptr_used_inst_record, ptr_used_inst_membership,
                pairTheory.FST, pairTheory.SND]) >>
  first_x_assum irule >> simp[] >>
  metis_tac[ptr_used_inst_membership, pairTheory.FST]
QED

Theorem ptr_used_insts_head_records[local]:
  ALL_DISTINCT (MAP FST ((idx,inst)::xs)) /\
  MEM (j,i) ((idx,inst)::xs) /\
  (MEM a cur \/ ml_used_gen a bp mems inst) ==>
  MEM a (ml_lookup
    (SND (ml_used_insts bp mems label cur us ((idx,inst)::xs))) (label,j))
Proof
  disch_tac >> simp[ml_used_insts_def] >> pairarg_tac >>
  `MEM a cur'` by metis_tac[ptr_used_inst_membership, pairTheory.FST] >>
  `ALL_DISTINCT (MAP FST ((idx,inst)::xs)) /\ MEM (j,i) ((idx,inst)::xs)`
    by metis_tac[] >>
  qpat_x_assum `_ /\ _ /\ _` kall_tac >> gvs[]
  >- (`ml_lookup (SND (ml_used_insts bp mems label cur' us' xs)) (label,idx) =
        ml_lookup us' (label,idx)` by
        (irule ptr_used_insts_other_address >>
         gvs[listTheory.MEM_MAP] >> metis_tac[]) >>
      metis_tac[ptr_used_inst_record, pairTheory.FST, pairTheory.SND]) >>
  irule ptr_used_insts_input_records >> simp[] >> metis_tac[]
QED

Theorem ptr_used_insts_append[local]:
  !cur us. ml_used_insts bp mems label cur us (xs ++ ys) =
    ml_used_insts bp mems label
      (FST (ml_used_insts bp mems label cur us xs))
      (SND (ml_used_insts bp mems label cur us xs)) ys
Proof
  Induct_on `xs` >- simp[ml_used_insts_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[ml_used_insts_def] >> pairarg_tac >> simp[]
QED

Theorem ptr_used_seed_suffix_records:
  ALL_DISTINCT (MAP FST ((idx,inst)::rest)) /\
  MEM (j,i) ((idx,inst)::rest) /\ ml_used_gen a bp mems inst ==>
  MEM a (ml_lookup
    (SND (ml_used_insts bp mems label cur us (pre ++ (idx,inst)::rest))) (label,j))
Proof
  strip_tac >> simp[ptr_used_insts_append] >>
  irule ptr_used_insts_head_records >> gvs[] >> metis_tac[]
QED

Definition ptr_used_path_def:
  (ptr_used_path cfg b [] c <=> b = c) /\
  (ptr_used_path cfg b (h::t) c <=>
    MEM b (cfg_preds_of cfg h) /\ ptr_used_path cfg h t c)
End

Theorem ptr_used_block_seed_suffix:
  MAPi (\n inst. (n,inst)) bb.bb_instructions = pre ++ (idx,inst)::rest /\
  ALL_DISTINCT (MAP FST ((idx,inst)::rest)) /\
  MEM (j,i) ((idx,inst)::rest) /\ ml_used_gen a bp mems inst ==>
  MEM a (ml_lookup (SND (ml_used_block bp mems pallocas cfg us bb blocks))
    (bb.bb_label,j))
Proof
  strip_tac >> simp[ml_used_block_def] >> pairarg_tac >> simp[] >>
  metis_tac[ptr_used_seed_suffix_records, pairTheory.SND]
QED

Theorem ptr_used_block_unchanged_endpoint:
  ~FST (ml_used_block bp mems pallocas cfg us bb blocks) ==>
  ml_lookup (SND (ml_used_block bp mems pallocas cfg us bb blocks))
    (bb.bb_label,PRE (LENGTH bb.bb_instructions)) =
  ml_lookup us (bb.bb_label,PRE (LENGTH bb.bb_instructions))
Proof
  simp[ml_used_block_def] >> pairarg_tac >> simp[]
QED

Theorem ptr_indexed_distinct[local]:
  ALL_DISTINCT (MAP FST (MAPi (\i inst. (i,inst)) insts))
Proof
  `MAP FST (MAPi (\i inst. (i,inst)) insts) = GENLIST I (LENGTH insts)` by
    (irule listTheory.LIST_EQ >> simp[indexedListsTheory.EL_MAPi]) >>
  simp[listTheory.ALL_DISTINCT_GENLIST]
QED

Theorem ptr_used_block_pred_records:
  MEM pred (cfg_preds_of cfg bb.bb_label) /\
  FIND (\b. b.bb_label = pred) blocks = SOME pbb /\
  MEM a (ml_lookup us (pbb.bb_label,PRE (LENGTH pbb.bb_instructions))) /\
  MEM (j,i) (MAPi (\n inst. (n,inst)) bb.bb_instructions) ==>
  MEM a (ml_lookup (SND (ml_used_block bp mems pallocas cfg us bb blocks))
    (bb.bb_label,j))
Proof
  strip_tac >> simp[ml_used_block_def] >> pairarg_tac >> simp[] >>
  qmatch_asmsub_abbrev_tac `ml_used_insts bp mems bb.bb_label initial us _` >>
  `MEM a initial` by
    (simp[Abbr `initial`, ptr_smerge_union, ml_merge_fold_mem,
          listTheory.EXISTS_MEM, listTheory.MEM_MAP] >>
     disj2_tac >>
     qexists_tac `ml_lookup us (pbb.bb_label,PRE (LENGTH pbb.bb_instructions))` >>
     simp[] >> qexists_tac `pred` >> simp[]) >>
  metis_tac[ptr_used_insts_input_records, ptr_indexed_distinct, pairTheory.SND]
QED

Theorem ptr_used_block_seed_records:
  i <= j /\ j < LENGTH bb.bb_instructions /\
  ml_used_gen a bp mems (EL i bb.bb_instructions) ==>
  MEM a (ml_lookup (SND (ml_used_block bp mems pallocas cfg us bb blocks))
    (bb.bb_label,j))
Proof
  strip_tac >>
  qabbrev_tac `xs = MAPi (\n inst. (n,inst)) bb.bb_instructions` >>
  `i < LENGTH xs /\ j < LENGTH xs` by simp[Abbr `xs`] >>
  `EL i xs = (i,EL i bb.bb_instructions) /\
   EL j xs = (j,EL j bb.bb_instructions)` by
    simp[Abbr `xs`, indexedListsTheory.EL_MAPi] >>
  `xs = TAKE i xs ++ EL i xs :: DROP (SUC i) xs` by
    metis_tac[rich_listTheory.TAKE_DROP_SUC, listTheory.APPEND, listTheory.APPEND_ASSOC] >>
  `ALL_DISTINCT (MAP FST xs)` by simp[Abbr `xs`, ptr_indexed_distinct] >>
  `ALL_DISTINCT (MAP FST (EL i xs :: DROP (SUC i) xs))` by
    metis_tac[listTheory.MAP_APPEND, listTheory.ALL_DISTINCT_APPEND] >>
  `MEM (EL j xs) (EL i xs :: DROP (SUC i) xs)` by
    (Cases_on `j = i` >- simp[] >>
     simp[] >>
     `j = SUC i + (j - SUC i)` by decide_tac >>
     `EL j xs = EL (j - SUC i) (DROP (SUC i) xs)` by
       simp[listTheory.EL_DROP] >>
     `j - SUC i < LENGTH (DROP (SUC i) xs)` by
       (simp[listTheory.LENGTH_DROP] >> decide_tac) >>
     simp[listTheory.MEM_EL] >> qexists_tac `j - SUC i` >> gvs[]) >>
  irule ptr_used_block_seed_suffix >>
  qexistsl_tac [`EL j bb.bb_instructions`, `i`, `EL i bb.bb_instructions`,
               `TAKE i xs`, `DROP (SUC i) xs`] >>
  gvs[Abbr `xs`]
QED

Theorem ptr_used_sweep_other_label:
  !us. (!lbl. MEM lbl order ==> lbl <> FST addr) ==>
  ml_lookup (SND (ml_one_pass_used bp mems pallocas cfg blocks order us)) addr =
  ml_lookup us addr
Proof
  Induct_on `order` >- simp[ml_one_pass_used_def] >>
  rpt gen_tac >> Cases_on `addr` >> strip_tac >> simp[ml_one_pass_used_def] >>
  Cases_on `FIND (\bb. bb.bb_label = h) blocks`
  >- (simp[] >> first_x_assum irule >> metis_tac[listTheory.MEM]) >>
  simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `x.bb_label = h` by (drule venomExecProofsTheory.FIND_P >> simp[]) >>
  metis_tac[ml_used_block_other_label, pairTheory.SND, pairTheory.FST, listTheory.MEM]
QED

Theorem ptr_used_sweep_seed_records:
  !us. MEM bb.bb_label order /\
  FIND (\b. b.bb_label = bb.bb_label) blocks = SOME bb /\
  i <= j /\ j < LENGTH bb.bb_instructions /\
  ml_used_gen a bp mems (EL i bb.bb_instructions) ==>
  MEM a (ml_lookup (SND (ml_one_pass_used bp mems pallocas cfg blocks order us))
    (bb.bb_label,j))
Proof
  Induct_on `order` >- simp[] >>
  rpt gen_tac >> strip_tac >> simp[ml_one_pass_used_def] >>
  Cases_on `MEM bb.bb_label order`
  >- (Cases_on `FIND (\b. b.bb_label = h) blocks` >> simp[] >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> metis_tac[pairTheory.SND]) >>
  `h = bb.bb_label` by gvs[] >> gvs[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `ml_lookup us'' (bb.bb_label,j) = ml_lookup us' (bb.bb_label,j)` by
    (`!lbl. MEM lbl order ==> lbl <> FST (bb.bb_label,j)` by simp[] >>
     drule ptr_used_sweep_other_label >>
     disch_then assume_tac >> metis_tac[pairTheory.SND]) >>
  metis_tac[ptr_used_block_seed_records, pairTheory.SND]
QED

Theorem ptr_used_record_true[local]:
  !old. ml_used_record_bit a bp mems label addr insts T old <=>
    old \/ MEM addr (MAP (\p. (label,FST p)) insts)
Proof
  Induct_on `insts` >- simp[ml_used_record_bit_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[ml_used_record_bit_def] >>
  metis_tac[]
QED

Theorem ptr_used_boundary_transmits:
  bb.bb_instructions <> [] ==>
  ml_used_boundary_bit a bp mems bb T
Proof
  strip_tac >> simp[ml_used_boundary_bit_def, ptr_used_record_true,
    listTheory.MEM_MAP, indexedListsTheory.MEM_MAPi] >>
  qexists_tac `(PRE (LENGTH bb.bb_instructions),
                EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions)` >>
  simp[] >> Cases_on `bb.bb_instructions` >> gvs[]
QED

Theorem ptr_used_descriptor_edge:
  MEM bb (ml_scan_blocks blocks order) /\ bb.bb_instructions <> [] /\
  MEM pred (cfg_preds_of cfg bb.bb_label) ==>
  sw_edge (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
    (ml_scan_blocks blocks order)) pred bb.bb_label
Proof
  strip_tac >> simp[sw_edge_def] >>
  qexistsl_tac [`if ml_used_boundary_bit a bp mems bb (MEM a pallocas)
                 then {T} else {}`, `set (cfg_preds_of cfg bb.bb_label)`] >>
  conj_tac
  >- (simp[listTheory.MEM_MAP] >> qexists_tac `bb` >>
      simp[ml_used_boundary_desc_def, ptr_used_boundary_transmits]) >>
  simp[]
QED

Theorem ptr_used_rounds_path:
  !path b c n.
  ptr_used_path cfg b path c /\
  (!lbl. MEM lbl path ==> ?bb. MEM bb (ml_scan_blocks blocks order) /\
    bb.bb_label = lbl /\ bb.bb_instructions <> []) /\
  T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
    (ml_scan_blocks blocks order)) n b ==>
  T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
    (ml_scan_blocks blocks order)) (n + LENGTH path) c
Proof
  Induct_on `path` >- simp[ptr_used_path_def] >>
  rpt gen_tac >> strip_tac >>
  `sw_consistent (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
    (ml_scan_blocks blocks order))` by
    (irule ml_scan_blocks_consistent >> simp[ml_boundary_desc_out]) >>
  `?bb. MEM bb (ml_scan_blocks blocks order) /\ bb.bb_label = h /\
        bb.bb_instructions <> []` by metis_tac[listTheory.MEM] >>
  `sw_edge (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
    (ml_scan_blocks blocks order)) b h` by
    (gvs[ptr_used_path_def] >> metis_tac[ptr_used_descriptor_edge]) >>
  `T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
    (ml_scan_blocks blocks order)) (SUC n) h` by metis_tac[sw_rounds_edge] >>
  `n + LENGTH (h::path) = SUC n + LENGTH path` by simp[] >>
  pop_assum SUBST1_TAC >> first_x_assum irule >>
  gvs[ptr_used_path_def] >> metis_tac[listTheory.MEM]
QED

Theorem ptr_rounds_member_stationary:
  (!v. a IN sw_rounds ds (SUC n) v <=> a IN sw_rounds ds n v) ==>
  !k v. a IN sw_rounds ds (n+k) v <=> a IN sw_rounds ds n v
Proof
  strip_tac >> Induct >- simp[] >> gen_tac >>
  `n + SUC k = SUC (n+k)` by simp[] >>
  pop_assum SUBST1_TAC >> simp[Once sw_rounds_def] >>
  `a IN sw_scan ds (sw_rounds ds (n+k)) v <=>
   a IN sw_scan ds (sw_rounds ds n) v` by
    (irule sw_scan_member_cong >> simp[]) >>
  qpat_x_assum `!v. a IN sw_rounds ds (SUC n) v <=> _` mp_tac >>
  gvs[sw_rounds_def, arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Theorem ptr_used_one_pass_scan:
  ml_one_pass bp mems sizes pallocas cfg fn la us = (changed,la',us') /\
  EVERY (\bb. bb.bb_instructions <> []) fn.fn_blocks /\
  (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks us lbl) <=> T IN X lbl) ==>
  (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks us' lbl) <=>
    T IN sw_scan (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) X lbl)
Proof
  simp[ml_one_pass_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_all ml_used_pass_sw_scan >> simp[]
QED

Theorem ptr_used_fuel_rounds:
  !fuel la us n.
  EVERY (\bb. bb.bb_instructions <> []) fn.fn_blocks /\
  (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks us lbl) <=>
    T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) n lbl) ==>
  (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks
    (SND (ml_iterate_fuel fuel bp mems sizes pallocas cfg fn la us)) lbl) <=>
    T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) (n+fuel) lbl)
Proof
  Induct >- simp[ml_iterate_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  pure_once_rewrite_tac[ml_iterate_fuel_def] >>
  pure_rewrite_tac[LET_THM] >> pairarg_tac >> simp[] >>
  `!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks used' lbl) <=>
    T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) (SUC n) lbl` by
    (simp[Once sw_rounds_def] >> drule_all ptr_used_one_pass_scan >> simp[]) >>
  Cases_on `changed`
  >- (simp[] >> `n + SUC fuel = SUC n + fuel` by simp[] >>
      pop_assum SUBST1_TAC >> first_x_assum irule >> simp[]) >>
  gvs[] >> drule ml_one_pass_false_boundary >> strip_tac >>
  `!lbl. T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) (SUC n) lbl <=>
    T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) n lbl` by metis_tac[] >>
  drule ptr_rounds_member_stationary >> strip_tac >> metis_tac[]
QED

Theorem ptr_used_boundary_seed:
  i < LENGTH bb.bb_instructions /\ ml_used_gen a bp mems (EL i bb.bb_instructions) ==>
  ml_used_boundary_bit a bp mems bb bit
Proof
  strip_tac >>
  Cases_on `ml_used_block bp mems [] cfg FEMPTY bb []` >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions /\
   i <= PRE (LENGTH bb.bb_instructions)` by decide_tac >>
  `MEM a (ml_lookup r (bb.bb_label,PRE (LENGTH bb.bb_instructions)))` by
    (`MEM a (ml_lookup (SND (ml_used_block bp mems [] cfg FEMPTY bb []))
        (bb.bb_label,PRE (LENGTH bb.bb_instructions)))` suffices_by simp[] >>
     irule ptr_used_block_seed_records >> simp[] >> qexists_tac `i` >> simp[]) >>
  `ml_used_boundary_bit a bp mems bb F` by
    (drule ml_used_block_record_exact >>
     disch_then (qspecl_then [`PRE (LENGTH bb.bb_instructions)`, `a`] mp_tac) >>
     simp[ml_used_boundary_bit_def, ml_lookup_def, listTheory.FIND_thm]) >>
  metis_tac[ml_used_boundary_bit_affine]
QED

Theorem ptr_used_descriptor_seed:
  MEM bb (ml_scan_blocks blocks order) /\ i < LENGTH bb.bb_instructions /\
  ml_used_gen a bp mems (EL i bb.bb_instructions) ==>
  sw_seed (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
    (ml_scan_blocks blocks order)) T bb.bb_label
Proof
  strip_tac >>
  `ml_used_boundary_bit a bp mems bb (MEM a pallocas)` by
    metis_tac[ptr_used_boundary_seed] >>
  simp[sw_seed_def] >>
  qexistsl_tac [`{T}`, `if ml_used_boundary_bit a bp mems bb T then
    set (cfg_preds_of cfg bb.bb_label) else {}`] >>
  simp[listTheory.MEM_MAP] >> qexists_tac `bb` >> simp[ml_used_boundary_desc_def]
QED

Theorem ptr_used_fuel_endpoints:
  EVERY (\bb. bb.bb_instructions <> []) fn.fn_blocks ==>
  (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks
    (SND (ml_iterate_fuel fuel bp mems sizes pallocas cfg fn FEMPTY FEMPTY)) lbl) <=>
    T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) fuel lbl)
Proof
  strip_tac >>
  qspecl_then [`fuel`, `FEMPTY`, `FEMPTY`, `0`] mp_tac ptr_used_fuel_rounds >>
  simp[] >> impl_tac
  >- (gen_tac >> simp[sw_rounds_def, ml_used_boundary_lookup_def] >>
      CASE_TAC >> simp[ml_lookup_def]) >> simp[]
QED

Theorem ptr_used_fuel_endpoint_path_coverage:
  EVERY (\b. b.bb_instructions <> []) fn.fn_blocks /\
  MEM bb (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre) /\
  i < LENGTH bb.bb_instructions /\ ml_used_gen a bp mems (EL i bb.bb_instructions) /\
  ptr_used_path cfg bb.bb_label path dest /\
  (!lbl. MEM lbl path ==> ?b. MEM b (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre) /\
    b.bb_label = lbl /\ b.bb_instructions <> []) /\
  SUC (LENGTH path) <= fuel ==>
  MEM a (ml_used_boundary_lookup fn.fn_blocks
    (SND (ml_iterate_fuel fuel bp mems sizes pallocas cfg fn FEMPTY FEMPTY)) dest)
Proof
  strip_tac >> asm_simp_tac (srw_ss()) [ptr_used_fuel_endpoints] >>
  qmatch_goalsub_abbrev_tac `sw_rounds ds fuel` >>
  `sw_consistent ds` by
    (simp[Abbr `ds`] >> irule ml_scan_blocks_consistent >> simp[ml_boundary_desc_out]) >>
  `sw_seed ds T bb.bb_label` by
    (simp[Abbr `ds`] >> irule ptr_used_descriptor_seed >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `T IN sw_rounds ds 1 bb.bb_label` by metis_tac[sw_rounds_seed] >>
  `T IN sw_rounds ds (1 + LENGTH path) dest` by
    (qunabbrev_tac `ds` >> irule ptr_used_rounds_path >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `sw_le (sw_rounds ds (1 + LENGTH path)) (sw_rounds ds fuel)` by
    (irule sw_rounds_mono >> simp[]) >>
  gvs[sw_le_def, pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem ptr_used_one_pass_seed_records[local]:
  ml_one_pass bp mems sizes pallocas cfg fn la us = (changed,la',us') /\
  MEM bb.bb_label cfg.cfg_dfs_pre /\
  FIND (\b. b.bb_label = bb.bb_label) fn.fn_blocks = SOME bb /\
  i <= j /\ j < LENGTH bb.bb_instructions /\
  ml_used_gen a bp mems (EL i bb.bb_instructions) ==>
  MEM a (ml_lookup us' (bb.bb_label,j))
Proof
  simp[ml_one_pass_def] >> ntac 2 (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[] >>
  `MEM a (ml_lookup
    (SND (ml_one_pass_used bp mems pallocas cfg fn.fn_blocks cfg.cfg_dfs_pre us))
    (bb.bb_label,j))` by
    (irule ptr_used_sweep_seed_records >> simp[] >> metis_tac[]) >> gvs[]
QED

Theorem ptr_used_fuel_seed_records:
  !fuel la us.
  MEM bb.bb_label cfg.cfg_dfs_pre /\
  FIND (\b. b.bb_label = bb.bb_label) fn.fn_blocks = SOME bb /\
  i <= j /\ j < LENGTH bb.bb_instructions /\
  ml_used_gen a bp mems (EL i bb.bb_instructions) ==>
  MEM a (ml_lookup
    (SND (ml_iterate_fuel (SUC fuel) bp mems sizes pallocas cfg fn la us))
    (bb.bb_label,j))
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      pure_once_rewrite_tac[ml_iterate_fuel_def] >>
      pure_rewrite_tac[LET_THM] >> pairarg_tac >> simp[] >>
      Cases_on `changed` >> simp[ml_iterate_fuel_def] >>
      drule_all ptr_used_one_pass_seed_records >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  pure_once_rewrite_tac[ml_iterate_fuel_def] >>
  pure_rewrite_tac[LET_THM] >> pairarg_tac >> simp[] >>
  Cases_on `changed` >> simp[] >>
  drule_all ptr_used_one_pass_seed_records >> simp[]
QED

Theorem ptr_used_sweep_pred_records:
  !order us X.
  EVERY (\b. b.bb_instructions <> []) blocks /\
  EVERY (\d. MEM d ds)
    (MAP (ml_used_boundary_desc a bp mems pallocas cfg) (ml_scan_blocks blocks order)) /\
  sw_consistent ds /\ sw_admissible ds X /\
  (!lbl. MEM a (ml_used_boundary_lookup blocks us lbl) <=> T IN X lbl) /\
  FIND (\b. b.bb_label = bb.bb_label) blocks = SOME bb /\
  MEM bb.bb_label order /\
  FIND (\b. b.bb_label = pred) blocks = SOME pbb /\
  MEM pred (cfg_preds_of cfg bb.bb_label) /\ T IN X pred /\
  j < LENGTH bb.bb_instructions ==>
  MEM a (ml_lookup (SND (ml_one_pass_used bp mems pallocas cfg blocks order us))
    (bb.bb_label,j))
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `FIND (\b. b.bb_label = h) blocks`
  >- (gvs[ml_one_pass_used_def, ml_scan_blocks_def] >> first_x_assum irule >>
      goal_assum (drule_at Any) >> simp[]) >>
  rename1 `FIND _ blocks = SOME head` >>
  `head.bb_label = h /\ MEM head blocks` by
    (qpat_assum `FIND _ blocks = SOME head` (mp_tac o MATCH_MP venomExecProofsTheory.FIND_P) >>
     qpat_assum `FIND _ blocks = SOME head` (mp_tac o MATCH_MP venomExecProofsTheory.FIND_MEM) >>
     simp[]) >>
  `head.bb_instructions <> []` by
    (qpat_x_assum `EVERY (\b. b.bb_instructions <> []) blocks` mp_tac >>
     simp[listTheory.EVERY_MEM] >> disch_then drule >> simp[]) >>
  `FIND (\b. b.bb_label = head.bb_label) blocks = SOME head` by simp[] >>
  gns[ml_scan_blocks_def] >>
  qpat_x_assum `MEM _ ds /\ _` strip_assume_tac >>
  `FIND (\b. b.bb_label = head.bb_label) blocks = SOME head` by simp[] >>
  Cases_on `ml_used_block bp mems pallocas cfg us head blocks` >>
  rename1 `ml_used_block bp mems pallocas cfg us head blocks = (ch,mid)` >>
  `!lbl. MEM a (ml_used_boundary_lookup blocks mid lbl) <=>
    T IN sw_update (ml_used_boundary_desc a bp mems pallocas cfg head) X lbl` by
    (drule_all ml_used_block_sw_update >> simp[]) >>
  `sw_admissible ds (sw_update (ml_used_boundary_desc a bp mems pallocas cfg head) X)` by
    (irule sw_update_admissible >> simp[]) >>
  `T IN sw_update (ml_used_boundary_desc a bp mems pallocas cfg head) X pred` by
    (`sw_le X (sw_update (ml_used_boundary_desc a bp mems pallocas cfg head) X)` by
      (irule sw_update_grows >> qexists_tac `ds` >> simp[]) >>
     gvs[sw_le_def, pred_setTheory.SUBSET_DEF]) >>
  simp[ml_one_pass_used_def] >>
  Cases_on `MEM bb.bb_label order`
  >- (first_x_assum (qspecl_then [`mid`,
        `sw_update (ml_used_boundary_desc a bp mems pallocas cfg head) X`] mp_tac) >>
      simp[] >> pairarg_tac >> simp[]) >>
  `head = bb` by gvs[] >> gvs[] >>
  `MEM a (ml_lookup mid (bb.bb_label,j))` by
    (`MEM a (ml_lookup us (pbb.bb_label,PRE (LENGTH pbb.bb_instructions)))` by
      (qpat_x_assum `!lbl. MEM a (ml_used_boundary_lookup blocks us lbl) <=> _`
         (qspec_then `pred` mp_tac) >> simp[ml_used_boundary_lookup_def]) >>
     `MEM a (ml_lookup (SND (ml_used_block bp mems pallocas cfg us bb blocks))
       (bb.bb_label,j))` suffices_by simp[] >>
     irule ptr_used_block_pred_records >>
     conj_tac
     >- (qexistsl_tac [`pbb`, `pred`] >> simp[]) >>
     qexists_tac `EL j bb.bb_instructions` >>
     simp[indexedListsTheory.MEM_MAPi]) >>
  `ml_lookup (SND (ml_one_pass_used bp mems pallocas cfg blocks order mid)) (bb.bb_label,j) =
    ml_lookup mid (bb.bb_label,j)` by
    (irule ptr_used_sweep_other_label >> simp[] >> metis_tac[]) >>
  pairarg_tac >> gvs[]
QED

Theorem ptr_used_one_pass_pred_records[local]:
  ml_one_pass bp mems sizes pallocas cfg fn la us = (changed,la',us') /\
  EVERY (\b. b.bb_instructions <> []) fn.fn_blocks /\
  (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks us lbl) <=>
    T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) n lbl) /\
  FIND (\b. b.bb_label = bb.bb_label) fn.fn_blocks = SOME bb /\
  MEM bb.bb_label cfg.cfg_dfs_pre /\
  FIND (\b. b.bb_label = pred) fn.fn_blocks = SOME pbb /\
  MEM pred (cfg_preds_of cfg bb.bb_label) /\
  T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) n pred /\
  j < LENGTH bb.bb_instructions ==>
  MEM a (ml_lookup us' (bb.bb_label,j))
Proof
  strip_tac >>
  `sw_consistent (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre))` by
    (irule ml_scan_blocks_consistent >> simp[ml_boundary_desc_out]) >>
  `MEM a (ml_lookup
    (SND (ml_one_pass_used bp mems pallocas cfg fn.fn_blocks cfg.cfg_dfs_pre us))
    (bb.bb_label,j))` by
    (irule ptr_used_sweep_pred_records >>
     simp[] >>
     qexistsl_tac [`sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
         (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) n`,
       `MAP (ml_used_boundary_desc a bp mems pallocas cfg)
       (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)`, `pbb`, `pred`] >>
     simp[sw_rounds_admissible, listTheory.EVERY_MEM] >> metis_tac[]) >>
  gvs[ml_one_pass_def] >> ntac 2 (pairarg_tac >> gvs[])
QED

Theorem ptr_used_fuel_pred_records:
  !fuel la us n.
  EVERY (\b. b.bb_instructions <> []) fn.fn_blocks /\
  (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks us lbl) <=>
    T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) n lbl) /\
  FIND (\b. b.bb_label = bb.bb_label) fn.fn_blocks = SOME bb /\
  MEM bb.bb_label cfg.cfg_dfs_pre /\
  FIND (\b. b.bb_label = pred) fn.fn_blocks = SOME pbb /\
  MEM pred (cfg_preds_of cfg bb.bb_label) /\
  T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) (n+fuel) pred /\
  j < LENGTH bb.bb_instructions ==>
  MEM a (ml_lookup
    (SND (ml_iterate_fuel (SUC fuel) bp mems sizes pallocas cfg fn la us))
    (bb.bb_label,j))
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      pure_once_rewrite_tac[ml_iterate_fuel_def] >>
      pure_rewrite_tac[LET_THM] >> pairarg_tac >> simp[] >>
      Cases_on `changed` >> simp[ml_iterate_fuel_def] >>
      fs[] >> drule_all ptr_used_one_pass_pred_records >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  pure_once_rewrite_tac[ml_iterate_fuel_def] >>
  pure_rewrite_tac[LET_THM] >> pairarg_tac >> simp[] >>
  `!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks used' lbl) <=>
    T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) (SUC n) lbl` by
    (simp[Once sw_rounds_def] >> drule_all ptr_used_one_pass_scan >> simp[]) >>
  Cases_on `changed`
  >- (simp[] >> first_x_assum (qspecl_then [`liveat'`, `used'`, `SUC n`] mp_tac) >>
      fs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM]) >>
  simp[] >> drule ml_one_pass_false_boundary >> strip_tac >>
  `!lbl. T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) (SUC n) lbl <=>
    T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) n lbl` by metis_tac[] >>
  `T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) n pred` by
    (drule ptr_rounds_member_stationary >> metis_tac[]) >>
  drule_all ptr_used_one_pass_pred_records >> simp[]
QED

Theorem ptr_used_fuel_path_records:
  EVERY (\b. b.bb_instructions <> []) fn.fn_blocks /\
  MEM seed (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre) /\
  i < LENGTH seed.bb_instructions /\
  ml_used_gen a bp mems (EL i seed.bb_instructions) /\
  ptr_used_path cfg seed.bb_label path pred /\
  (!lbl. MEM lbl path ==> ?b. MEM b (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre) /\
    b.bb_label = lbl /\ b.bb_instructions <> []) /\
  SUC (LENGTH path) <= fuel /\
  FIND (\b. b.bb_label = bb.bb_label) fn.fn_blocks = SOME bb /\
  MEM bb.bb_label cfg.cfg_dfs_pre /\
  FIND (\b. b.bb_label = pred) fn.fn_blocks = SOME pbb /\
  MEM pred (cfg_preds_of cfg bb.bb_label) /\ j < LENGTH bb.bb_instructions ==>
  MEM a (ml_lookup
    (SND (ml_iterate_fuel (SUC fuel) bp mems sizes pallocas cfg fn FEMPTY FEMPTY))
    (bb.bb_label,j))
Proof
  strip_tac >>
  `MEM a (ml_used_boundary_lookup fn.fn_blocks
    (SND (ml_iterate_fuel fuel bp mems sizes pallocas cfg fn FEMPTY FEMPTY)) pred)` by
    (irule ptr_used_fuel_endpoint_path_coverage >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `T IN sw_rounds (MAP (ml_used_boundary_desc a bp mems pallocas cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) fuel pred` by
    (drule ptr_used_fuel_endpoints >> metis_tac[]) >>
  qspecl_then [`fuel`, `FEMPTY`, `FEMPTY`, `0`] mp_tac ptr_used_fuel_pred_records >>
  simp[] >> disch_then irule >>
  simp[sw_rounds_def]
QED
