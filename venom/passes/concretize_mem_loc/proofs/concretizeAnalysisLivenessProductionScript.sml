Theory concretizeAnalysisLivenessProduction
Ancestors concretizeAnalysisLivenessClosure concretizeAnalysisLivenessStationary
  concretizeAnalysisLivenessTransfer concretizeMemLocDefs cfgAnalysisProps cfgWf
  concretizePtrOrdering singleWriterScan codegenReadyCompute venomWf venomExecProofs
  venomInstProps list pred_set

Theorem ml_cfg_production_coverage:
  wf_function fn /\ all_reachable fn /\ MEM bb fn.fn_blocks ==>
  MEM bb.bb_label (cfg_analyze fn).cfg_dfs_post /\
  MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre
Proof
  strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
    gvs[GSYM fn_reachable_cfg_analyze, all_reachable_def] >>
  drule cfg_analyze_reachable_sets >> simp[EXTENSION] >> metis_tac[]
QED

Theorem ml_production_saturated:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  ml_one_pass bpr mems sizes pallocas (cfg_analyze fn) fn la us =
    (changed,la',us') ==>
  (!addr. MEM a (ml_lookup la' addr) <=> MEM a (ml_lookup la addr)) /\
  (!addr. MEM a (ml_lookup us' addr) <=> MEM a (ml_lookup us addr))
Proof
  strip_tac >> irule ml_iterate_fuel_saturated >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists `concretize_memloc_fuel fn` >> simp[] >>
  conj_tac >- metis_tac[ml_cfg_production_coverage] >>
  simp[concretize_memloc_fuel_def]
QED

Theorem ml_production_ordered:
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) ==>
  ptr_ml_ordered la /\ ptr_ml_ordered us
Proof
  strip_tac >> drule ml_iterate_fuel_from_bottom_round >> strip_tac >>
  drule_all ml_full_rounds_ordered >>
  disch_then (qspecl_then [`sizes`, `fn`, `cfg_analyze fn`, `bpr`, `n`] mp_tac) >> simp[]
QED

Theorem ml_production_stationary_witnesses:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) ==>
  ?X Y.
    sw_admissible (MAP (ml_liveat_boundary_desc a bpr mems sizes (cfg_analyze fn))
      (ml_scan_blocks fn.fn_blocks (cfg_analyze fn).cfg_dfs_post)) X /\
    sw_admissible (MAP (ml_used_boundary_desc a bpr mems pallocas (cfg_analyze fn))
      (ml_scan_blocks fn.fn_blocks (cfg_analyze fn).cfg_dfs_pre)) Y /\
    (!lbl. MEM a (ml_lookup la (lbl,0)) <=> T IN X lbl) /\
    (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks us lbl) <=> T IN Y lbl) /\
    (!lbl. T IN sw_scan (MAP (ml_liveat_boundary_desc a bpr mems sizes (cfg_analyze fn))
      (ml_scan_blocks fn.fn_blocks (cfg_analyze fn).cfg_dfs_post)) X lbl <=> T IN X lbl) /\
    (!lbl. T IN sw_scan (MAP (ml_used_boundary_desc a bpr mems pallocas (cfg_analyze fn))
      (ml_scan_blocks fn.fn_blocks (cfg_analyze fn).cfg_dfs_pre)) Y lbl <=> T IN Y lbl)
Proof
  strip_tac >>
  Cases_on `ml_one_pass bpr mems sizes pallocas (cfg_analyze fn) fn la us` >>
  rename1 `ml_one_pass _ _ _ _ _ _ _ _ = (changed,result)` >>
  Cases_on `result` >>
  drule_all ml_production_saturated >> disch_then (qspec_then `a` strip_assume_tac) >>
  irule ml_iterate_fuel_stationary_witnesses >>
  rpt conj_tac >- simp[]
  >- (qexistsl [`changed`, `q`, `r`] >> simp[])
  >- (qexists `concretize_memloc_fuel fn` >> simp[])
  >- gvs[wf_function_def, EVERY_MEM, bb_well_formed_def]
  >> simp[]
QED

Theorem ml_production_liveat_record:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions ==>
  (MEM a (ml_lookup la (bb.bb_label,i)) <=>
    ml_liveat_record_bit a bpr mems sizes bb.bb_label (bb.bb_label,i)
      (MAPi (\j inst. (j,inst)) bb.bb_instructions)
      (?l. MEM l (cfg_succs_of (cfg_analyze fn) bb.bb_label) /\
        MEM a (ml_lookup la (l,0))) F)
Proof
  strip_tac >>
  drule_all ml_production_stationary_witnesses >>
  disch_then (qspec_then `a` strip_assume_tac) >>
  drule_all ml_production_ordered >> strip_tac >>
  drule_all ml_cfg_production_coverage >> strip_tac >>
  `FIND (\b. b.bb_label = bb.bb_label) fn.fn_blocks = SOME bb` by
    (simp[GSYM venomInstTheory.lookup_block_def] >> irule MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `EVERY (\b. b.bb_instructions <> []) fn.fn_blocks` by
    gvs[wf_function_def, EVERY_MEM, bb_well_formed_def] >>
  Cases_on `ml_one_pass_liveat bpr mems sizes (cfg_analyze fn) fn.fn_blocks
    (cfg_analyze fn).cfg_dfs_post la` >>
  rename1 `ml_one_pass_liveat _ _ _ _ _ _ _ = (c,la')` >>
  `sw_consistent (MAP (ml_liveat_boundary_desc a bpr mems sizes (cfg_analyze fn))
    (ml_scan_blocks fn.fn_blocks (cfg_analyze fn).cfg_dfs_post))` by
    (irule ml_scan_blocks_consistent >> simp[ml_liveat_boundary_desc_def, sw_out_def]) >>
  `EVERY (\b. MEM (ml_liveat_boundary_desc a bpr mems sizes (cfg_analyze fn) b)
    (MAP (ml_liveat_boundary_desc a bpr mems sizes (cfg_analyze fn))
      (ml_scan_blocks fn.fn_blocks (cfg_analyze fn).cfg_dfs_post)))
    (ml_scan_blocks fn.fn_blocks (cfg_analyze fn).cfg_dfs_post)` by
      (simp[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  drule ml_liveat_stationary_record >> simp[] >>
  disch_then (drule_at (Pat `FIND _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`i`,
    `MAP (ml_liveat_boundary_desc a bpr mems sizes (cfg_analyze fn))
      (ml_scan_blocks fn.fn_blocks (cfg_analyze fn).cfg_dfs_post)`, `a`, `X`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `ml_one_pass_used bpr mems pallocas (cfg_analyze fn) fn.fn_blocks
    (cfg_analyze fn).cfg_dfs_pre us` >>
  `ml_one_pass bpr mems sizes pallocas (cfg_analyze fn) fn la us =
    (c \/ q,la',r)` by simp[ml_one_pass_def] >>
  drule_all ml_production_saturated >> disch_then (qspec_then `a` strip_assume_tac) >>
  metis_tac[]
QED

Theorem ml_production_used_record:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions ==>
  (MEM a (ml_lookup us (bb.bb_label,i)) <=>
    ml_used_record_bit a bpr mems bb.bb_label (bb.bb_label,i)
      (MAPi (\j inst. (j,inst)) bb.bb_instructions)
      (MEM a pallocas \/ ?l. MEM l (cfg_preds_of (cfg_analyze fn) bb.bb_label) /\
        MEM a (ml_used_boundary_lookup fn.fn_blocks us l)) F)
Proof
  strip_tac >>
  drule_all ml_production_stationary_witnesses >>
  disch_then (qspec_then `a` strip_assume_tac) >>
  drule_all ml_cfg_production_coverage >> strip_tac >>
  `FIND (\b. b.bb_label = bb.bb_label) fn.fn_blocks = SOME bb` by
    (simp[GSYM venomInstTheory.lookup_block_def] >> irule MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `EVERY (\b. b.bb_instructions <> []) fn.fn_blocks` by
    gvs[wf_function_def, EVERY_MEM, bb_well_formed_def] >>
  Cases_on `ml_one_pass_used bpr mems pallocas (cfg_analyze fn) fn.fn_blocks
    (cfg_analyze fn).cfg_dfs_pre us` >>
  rename1 `ml_one_pass_used _ _ _ _ _ _ _ = (c,us')` >>
  `sw_consistent (MAP (ml_used_boundary_desc a bpr mems pallocas (cfg_analyze fn))
    (ml_scan_blocks fn.fn_blocks (cfg_analyze fn).cfg_dfs_pre))` by
    (irule ml_scan_blocks_consistent >> simp[ml_used_boundary_desc_def, sw_out_def]) >>
  `EVERY (\b. MEM (ml_used_boundary_desc a bpr mems pallocas (cfg_analyze fn) b)
    (MAP (ml_used_boundary_desc a bpr mems pallocas (cfg_analyze fn))
      (ml_scan_blocks fn.fn_blocks (cfg_analyze fn).cfg_dfs_pre)))
    (ml_scan_blocks fn.fn_blocks (cfg_analyze fn).cfg_dfs_pre)` by
      (simp[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  drule ml_used_stationary_record >> simp[] >>
  disch_then (drule_at (Pat `FIND _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`i`,
    `MAP (ml_used_boundary_desc a bpr mems pallocas (cfg_analyze fn))
      (ml_scan_blocks fn.fn_blocks (cfg_analyze fn).cfg_dfs_pre)`, `a`, `Y`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `ml_one_pass_liveat bpr mems sizes (cfg_analyze fn) fn.fn_blocks
    (cfg_analyze fn).cfg_dfs_post la` >>
  `ml_one_pass bpr mems sizes pallocas (cfg_analyze fn) fn la us =
    (q \/ c,r,us')` by simp[ml_one_pass_def] >>
  drule_all ml_production_saturated >> disch_then (qspec_then `a` strip_assume_tac) >>
  metis_tac[]
QED


Theorem ml_production_liveat_generation:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  ml_read_gen a bpr mems (EL i bb.bb_instructions) ==>
  MEM a (ml_lookup la (bb.bb_label,i))
Proof
  strip_tac >> drule_all ml_production_liveat_record >>
  disch_then (qspec_then `a` (fn th => rewrite_tac[th])) >>
  simp[SRULE [] (Q.INST [`n` |-> `0:num`] (SPEC_ALL ml_liveat_record_bit_index))]
QED

Theorem ml_production_liveat_retention:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  MEM bb fn.fn_blocks /\ SUC i < LENGTH bb.bb_instructions /\
  MEM a (ml_lookup la (bb.bb_label,SUC i)) /\
  ~ptr_ml_can_kill a bpr sizes (EL (SUC i) bb.bb_instructions) ==>
  MEM a (ml_lookup la (bb.bb_label,i))
Proof
  strip_tac >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  drule_all ml_production_liveat_record >>
  disch_then (qspec_then `a` (fn th => rewrite_tac[th])) >>
  irule (SRULE [] (Q.INST [`n` |-> `0:num`] (SPEC_ALL ml_liveat_record_bit_adjacent))) >>
  simp[] >>
  qpat_x_assum `i < LENGTH _` kall_tac >>
  drule_all ml_production_liveat_record >>
  disch_then (qspec_then `a` mp_tac) >> simp[]
QED

Theorem ml_production_used_generation:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  ml_used_gen a bpr mems (EL i bb.bb_instructions) ==>
  MEM a (ml_lookup us (bb.bb_label,i))
Proof
  strip_tac >> drule_all ml_production_used_record >>
  disch_then (qspec_then `a` (fn th => rewrite_tac[th])) >>
  simp[SRULE [] (Q.INST [`n` |-> `0:num`] (SPEC_ALL ml_used_record_bit_index))] >>
  disj2_tac >> simp[EXISTS_MEM, MEM_EL] >>
  qexists_tac `EL i bb.bb_instructions` >> simp[] >>
  qexists_tac `i` >> simp[EL_TAKE]
QED

Theorem ml_production_used_retention:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  MEM bb fn.fn_blocks /\ SUC i < LENGTH bb.bb_instructions /\
  MEM a (ml_lookup us (bb.bb_label,i)) ==>
  MEM a (ml_lookup us (bb.bb_label,SUC i))
Proof
  strip_tac >>
  drule_all ml_production_used_record >>
  disch_then (qspec_then `a` (fn th => rewrite_tac[th])) >>
  simp[SRULE [] (Q.INST [`n` |-> `0:num`] (SPEC_ALL ml_used_record_bit_index))] >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  qpat_x_assum `SUC i < LENGTH _` mp_tac >>
  drule_all ml_production_used_record >>
  disch_then (qspec_then `a` mp_tac) >>
  simp[SRULE [] (Q.INST [`n` |-> `0:num`] (SPEC_ALL ml_used_record_bit_index))] >>
  simp[rich_listTheory.TAKE_SUC_BY_TAKE, rich_listTheory.SNOC_APPEND] >> metis_tac[]
QED

Theorem ml_production_liveat_cfg_edge:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  MEM bb fn.fn_blocks /\
  MEM l (cfg_succs_of (cfg_analyze fn) bb.bb_label) /\
  MEM a (ml_lookup la (l,0)) ==>
  MEM a (ml_lookup la (bb.bb_label,PRE (LENGTH bb.bb_instructions)))
Proof
  strip_tac >>
  `bb.bb_instructions <> []` by
    gvs[wf_function_def, EVERY_MEM, bb_well_formed_def] >>
  `0 < LENGTH bb.bb_instructions` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions /\
   SUC (PRE (LENGTH bb.bb_instructions)) = LENGTH bb.bb_instructions` by decide_tac >>
  `DROP (LENGTH bb.bb_instructions)
    (MAPi (\j (inst:instruction). (j,inst)) bb.bb_instructions) = []` by
    metis_tac[listTheory.DROP_LENGTH_NIL, indexedListsTheory.LENGTH_MAPi] >>
  drule_all ml_production_liveat_record >>
  disch_then (qspec_then `a` (fn th => rewrite_tac[th])) >>
  simp[SRULE [] (Q.INST [`n` |-> `0:num`] (SPEC_ALL ml_liveat_record_bit_index)),
    ml_liveat_before_bit_def] >> metis_tac[]
QED

Theorem ml_production_used_pallocas:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\ MEM a pallocas ==>
  MEM a (ml_lookup us (bb.bb_label,i))
Proof
  strip_tac >> drule_all ml_production_used_record >>
  disch_then (qspec_then `a` (fn th => rewrite_tac[th])) >>
  simp[SRULE [] (Q.INST [`n` |-> `0:num`] (SPEC_ALL ml_used_record_bit_index))]
QED

Theorem ml_production_used_cfg_edge:
  wf_function fn /\ all_reachable fn /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  MEM pred fn.fn_blocks /\ MEM bb fn.fn_blocks /\
  MEM pred.bb_label (cfg_preds_of (cfg_analyze fn) bb.bb_label) /\
  MEM a (ml_lookup us (pred.bb_label,PRE (LENGTH pred.bb_instructions))) ==>
  MEM a (ml_lookup us (bb.bb_label,0))
Proof
  strip_tac >>
  `bb.bb_instructions <> []` by
    gvs[wf_function_def, EVERY_MEM, bb_well_formed_def] >>
  `0 < LENGTH bb.bb_instructions` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `FIND (\b. b.bb_label = pred.bb_label) fn.fn_blocks = SOME pred` by
    (simp[GSYM venomInstTheory.lookup_block_def] >> irule MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  drule_all ml_production_used_record >>
  disch_then (qspec_then `a` (fn th => rewrite_tac[th])) >>
  simp[SRULE [] (Q.INST [`n` |-> `0:num`] (SPEC_ALL ml_used_record_bit_index))] >>
  disj1_tac >> disj2_tac >> qexists_tac `pred.bb_label` >>
  simp[ml_used_boundary_lookup_def]
QED
