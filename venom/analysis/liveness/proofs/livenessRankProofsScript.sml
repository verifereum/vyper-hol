Theory livenessRankProofs
Ancestors
  livenessInvariantProofs
Libs
  pred_setTheory finite_mapTheory listTheory pairTheory arithmeticTheory
  cfgDefsTheory dfHelperDefsTheory livenessDefsTheory livenessBlockProofsTheory

Definition lv_labels_def:
  lv_labels cfg = set cfg.cfg_dfs_post UNION
    BIGUNION (IMAGE set (FRANGE cfg.cfg_preds))
End

Theorem lv_labels_finite:
  FINITE (lv_labels cfg)
Proof
  simp[lv_labels_def] >> rpt strip_tac >> gvs[]
QED

Theorem lv_labels_initial:
  EVERY (\l. l IN lv_labels cfg) cfg.cfg_dfs_post
Proof
  simp[EVERY_MEM, lv_labels_def]
QED

Theorem lv_labels_preds:
  EVERY (\p. p IN lv_labels cfg) (cfg_preds_of cfg l)
Proof
  simp[cfg_preds_of_def, fmap_lookup_list_def] >>
  Cases_on `FLOOKUP cfg.cfg_preds l` >> simp[EVERY_MEM, lv_labels_def] >>
  metis_tac[FRANGE_FLOOKUP]
QED

Definition lv_endpoints_def:
  lv_endpoints bbs labels st =
    {(l,t,v) | l IN labels /\ (t:num) < 2 /\
      MEM v (df_at [] st l (if t = 0 then 0 else LENGTH (liveness_instrs bbs l)))}
End

Definition lv_rank_def:
  lv_rank bbs labels st = CARD (lv_endpoints bbs labels st)
End

Theorem lv_endpoints_mem:
  (l,t,v) IN lv_endpoints bbs labels st <=>
  l IN labels /\ (t:num) < 2 /\
  MEM v (df_at [] st l (if t = 0 then 0 else LENGTH (liveness_instrs bbs l)))
Proof
  simp[lv_endpoints_def]
QED

Theorem lv_endpoints_bounded:
  lv_inv bbs cfg st ==>
  lv_endpoints bbs labels st SUBSET
    labels CROSS ({0n;1} CROSS set (fn_all_vars bbs))
Proof
  strip_tac >> simp[SUBSET_DEF, FORALL_PROD, lv_endpoints_mem] >>
  rpt strip_tac >> gvs[lv_inv_def] >>
  metis_tac[lv_bounded_read, DECIDE ``(t:num) < 2 ==> t = 0 \/ t = 1``]
QED

Theorem lv_endpoints_finite:
  FINITE labels /\ lv_inv bbs cfg st ==>
  FINITE (lv_endpoints bbs labels st)
Proof
  rpt strip_tac >> irule SUBSET_FINITE >>
  qexists_tac `labels CROSS ({0n;1} CROSS set (fn_all_vars bbs))` >>
  simp[] >> metis_tac[lv_endpoints_bounded]
QED

Theorem lv_rank_bound:
  FINITE labels /\ lv_inv bbs cfg st ==>
  lv_rank bbs labels st <= 2 * CARD labels * CARD (set (fn_all_vars bbs))
Proof
  rpt strip_tac >>
  `CARD (lv_endpoints bbs labels st) <=
   CARD (labels CROSS ({0n;1} CROSS set (fn_all_vars bbs)))` by
    (irule CARD_SUBSET >> simp[] >> metis_tac[lv_endpoints_bounded]) >>
  gvs[lv_rank_def, CARD_CROSS] >>
  metis_tac[MULT_ASSOC, MULT_COMM]
QED

Theorem lv_endpoints_inflation:
  lv_inv bbs cfg st ==>
  lv_endpoints bbs labels st SUBSET
    lv_endpoints bbs labels (liveness_block bbs cfg lbl st)
Proof
  strip_tac >> simp[SUBSET_DEF, FORALL_PROD, lv_endpoints_mem] >>
  metis_tac[lv_inv_read_inflation, SUBSET_DEF, MEM]
QED

Theorem lv_rank_mono:
  FINITE labels /\ lv_inv bbs cfg st ==>
  lv_rank bbs labels st <= lv_rank bbs labels (liveness_block bbs cfg lbl st)
Proof
  rpt strip_tac >> simp[lv_rank_def] >> irule CARD_SUBSET >>
  metis_tac[lv_endpoints_finite, lv_inv_block, lv_endpoints_inflation]
QED

Theorem lv_endpoints_equal_read:
  lbl IN labels /\
  lv_endpoints bbs labels old = lv_endpoints bbs labels new ==>
  set (df_at [] old lbl 0) = set (df_at [] new lbl 0) /\
  set (df_at [] old lbl (LENGTH (liveness_instrs bbs lbl))) =
  set (df_at [] new lbl (LENGTH (liveness_instrs bbs lbl)))
Proof
  strip_tac >>
  `!t v. (lbl,t,v) IN lv_endpoints bbs labels old <=>
          (lbl,t,v) IN lv_endpoints bbs labels new` by metis_tac[] >>
  pop_assum mp_tac >> simp[lv_endpoints_mem] >>
  disch_tac >> conj_tac
  >- (qpat_x_assum `!t v. _` (qspec_then `0n` mp_tac) >> simp[EXTENSION] >> metis_tac[]) >>
  qpat_x_assum `!t v. _` (qspec_then `1n` mp_tac) >> simp[EXTENSION] >> metis_tac[]
QED

Theorem lv_rank_strict:
  FINITE labels /\ lv_inv bbs cfg st /\ lbl IN labels /\
  liveness_changed bbs lbl st (liveness_block bbs cfg lbl st) ==>
  lv_rank bbs labels st < lv_rank bbs labels (liveness_block bbs cfg lbl st)
Proof
  rpt strip_tac >> simp[lv_rank_def] >> irule CARD_PSUBSET >>
  conj_tac
  >- metis_tac[lv_endpoints_finite, lv_inv_block] >>
  simp[PSUBSET_DEF] >> conj_tac
  >- metis_tac[lv_endpoints_inflation] >>
  strip_tac >> drule_all lv_endpoints_equal_read >> strip_tac >>
  gvs[liveness_changed_def, same_vars_set] >>
  Cases_on `lookup_block lbl bbs` >> gvs[liveness_instrs_def]
QED
