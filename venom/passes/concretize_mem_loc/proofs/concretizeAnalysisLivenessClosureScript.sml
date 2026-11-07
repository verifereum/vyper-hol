Theory concretizeAnalysisLivenessClosure
Ancestors concretizeAnalysisLivenessTransfer singleWriterScan cfgWf
  concretizeMemLocDefs concretizePtrOrdering venomExecProofs enumeral list pred_set finite_map

(* The boundary transfer is Boolean affine: a constant generator or the
   incoming boundary bit passed through a fixed propagation guard. *)
Theorem ml_liveat_before_bit_increasing:
  ml_liveat_before_bit a bpr mems sizes insts F ==>
  ml_liveat_before_bit a bpr mems sizes insts T
Proof
  Induct_on `insts` >- simp[ml_liveat_before_bit_def] >>
  gen_tac >> PairCases_on `h` >> simp[ml_liveat_before_bit_def] >> metis_tac[]
QED

Theorem ml_liveat_before_bit_affine:
  ml_liveat_before_bit a bpr mems sizes insts bit <=>
    ml_liveat_before_bit a bpr mems sizes insts F \/
    (bit /\ ml_liveat_before_bit a bpr mems sizes insts T)
Proof
  Cases_on `bit` >> simp[] >> metis_tac[ml_liveat_before_bit_increasing]
QED

Theorem ml_liveat_record_bit_increasing:
  ml_liveat_record_bit a bpr mems sizes lbl addr insts F F ==>
  ml_liveat_record_bit a bpr mems sizes lbl addr insts T F
Proof
  Induct_on `insts` >- simp[ml_liveat_record_bit_def] >>
  gen_tac >> PairCases_on `h` >> simp[ml_liveat_record_bit_def] >>
  Cases_on `addr = (lbl,h0)` >> simp[] >>
  metis_tac[ml_liveat_before_bit_increasing]
QED

Theorem ml_liveat_record_bit_affine:
  ml_liveat_record_bit a bpr mems sizes lbl addr insts bit F <=>
    ml_liveat_record_bit a bpr mems sizes lbl addr insts F F \/
    (bit /\ ml_liveat_record_bit a bpr mems sizes lbl addr insts T F)
Proof
  Cases_on `bit` >> simp[] >> metis_tac[ml_liveat_record_bit_increasing]
QED

Theorem ml_used_after_bit_increasing:
  !x y. (x ==> y) ==>
  (ml_used_after_bit a bpr mems insts x ==> ml_used_after_bit a bpr mems insts y)
Proof
  Induct_on `insts` >- simp[ml_used_after_bit_def] >>
  gen_tac >> PairCases_on `h` >> simp[ml_used_after_bit_def] >>
  Cases_on `ml_used_gen a bpr mems h1` >> simp[] >> first_x_assum ACCEPT_TAC
QED

Theorem ml_used_after_bit_affine:
  ml_used_after_bit a bpr mems insts bit <=>
    ml_used_after_bit a bpr mems insts F \/
    (bit /\ ml_used_after_bit a bpr mems insts T)
Proof
  Cases_on `bit` >> simp[] >> metis_tac[ml_used_after_bit_increasing]
QED

Theorem ml_used_record_bit_increasing:
  !x y old old2. (x ==> y) /\ (old ==> old2) ==>
  (ml_used_record_bit a bpr mems lbl addr insts x old ==>
   ml_used_record_bit a bpr mems lbl addr insts y old2)
Proof
  Induct_on `insts` >- simp[ml_used_record_bit_def] >>
  gen_tac >> PairCases_on `h` >> simp[ml_used_record_bit_def] >>
  rpt gen_tac >> Cases_on `addr = (lbl,h0)` >> gvs[] >>
  rpt strip_tac >> first_x_assum irule >>
  goal_assum (drule_at (Pat `ml_used_record_bit _ _ _ _ _ _ _ _`)) >> metis_tac[]
QED

Theorem ml_used_record_bit_affine:
  ml_used_record_bit a bpr mems lbl addr insts bit F <=>
    ml_used_record_bit a bpr mems lbl addr insts F F \/
    (bit /\ ml_used_record_bit a bpr mems lbl addr insts T F)
Proof
  Cases_on `bit` >> simp[] >> metis_tac[ml_used_record_bit_increasing]
QED

Theorem ml_liveat_record_bit_old_irrelevant:
  !bit old old2 idx inst.
  MEM (idx,inst) insts ==>
  ml_liveat_record_bit a bpr mems sizes lbl (lbl,idx) insts bit old =
  ml_liveat_record_bit a bpr mems sizes lbl (lbl,idx) insts bit old2
Proof
  Induct_on `insts` >- simp[] >> gen_tac >> PairCases_on `h` >>
  simp[ml_liveat_record_bit_def] >> rpt gen_tac >> strip_tac >> simp[] >>
  Cases_on `idx = h0` >> simp[] >> first_x_assum drule >> simp[]
QED

Theorem ml_used_record_bit_old_irrelevant:
  !bit old old2 idx inst.
  MEM (idx,inst) insts ==>
  ml_used_record_bit a bpr mems lbl (lbl,idx) insts bit old =
  ml_used_record_bit a bpr mems lbl (lbl,idx) insts bit old2
Proof
  Induct_on `insts` >- simp[] >> gen_tac >> PairCases_on `h` >>
  simp[ml_used_record_bit_def] >> rpt gen_tac >> strip_tac >> simp[] >>
  Cases_on `idx = h0` >> simp[] >> first_x_assum drule >> simp[]
QED

Definition ml_liveat_boundary_bit_def:
  ml_liveat_boundary_bit a bpr mems sizes bb bit =
    ml_liveat_record_bit a bpr mems sizes bb.bb_label (bb.bb_label,0)
      (MAPi (\i inst. (i,inst)) bb.bb_instructions) bit F
End

Definition ml_used_boundary_bit_def:
  ml_used_boundary_bit a bpr mems bb bit =
    ml_used_record_bit a bpr mems bb.bb_label
      (bb.bb_label,PRE (LENGTH bb.bb_instructions))
      (MAPi (\i inst. (i,inst)) bb.bb_instructions) bit F
End

Theorem ml_liveat_boundary_bit_affine:
  ml_liveat_boundary_bit a bpr mems sizes bb bit <=>
  ml_liveat_boundary_bit a bpr mems sizes bb F \/
  (bit /\ ml_liveat_boundary_bit a bpr mems sizes bb T)
Proof
  pure_rewrite_tac[ml_liveat_boundary_bit_def] >>
  MATCH_ACCEPT_TAC ml_liveat_record_bit_affine
QED

Theorem ml_used_boundary_bit_affine:
  ml_used_boundary_bit a bpr mems bb bit <=>
  ml_used_boundary_bit a bpr mems bb F \/
  (bit /\ ml_used_boundary_bit a bpr mems bb T)
Proof
  pure_rewrite_tac[ml_used_boundary_bit_def] >>
  MATCH_ACCEPT_TAC ml_used_record_bit_affine
QED

Definition ml_liveat_boundary_desc_def:
  ml_liveat_boundary_desc a bpr mems sizes cfg bb =
    (bb.bb_label,
     if ml_liveat_boundary_bit a bpr mems sizes bb F then {T} else {},
     if ml_liveat_boundary_bit a bpr mems sizes bb T then
       set (cfg_succs_of cfg bb.bb_label) else {})
End

Definition ml_used_boundary_desc_def:
  ml_used_boundary_desc a bpr mems pallocas cfg bb =
    (bb.bb_label,
     if ml_used_boundary_bit a bpr mems bb (MEM a pallocas) then {T} else {},
     if ml_used_boundary_bit a bpr mems bb T then
       set (cfg_preds_of cfg bb.bb_label) else {})
End

Theorem ml_boundary_desc_out:
  sw_out (ml_liveat_boundary_desc a bpr mems sizes cfg bb) = bb.bb_label /\
  sw_out (ml_used_boundary_desc a bpr mems pallocas cfg bb) = bb.bb_label
Proof simp[ml_liveat_boundary_desc_def, ml_used_boundary_desc_def, sw_out_def]
QED

Theorem ml_liveat_boundary_desc_rhs:
  T IN sw_rhs (ml_liveat_boundary_desc a bpr mems sizes cfg bb) X <=>
  ml_liveat_boundary_bit a bpr mems sizes bb
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\ T IN X lbl)
Proof
  simp[ml_liveat_boundary_desc_def, sw_rhs_def] >>
  once_rewrite_tac[ml_liveat_boundary_bit_affine] >>
  rpt IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem ml_used_boundary_desc_rhs:
  T IN sw_rhs (ml_used_boundary_desc a bpr mems pallocas cfg bb) X <=>
  ml_used_boundary_bit a bpr mems bb
    (MEM a pallocas \/ (?lbl. MEM lbl (cfg_preds_of cfg bb.bb_label) /\ T IN X lbl))
Proof
  simp[ml_used_boundary_desc_def, sw_rhs_def] >>
  once_rewrite_tac[ml_used_boundary_bit_affine] >>
  rpt IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem ml_liveat_block_record_exact:
  ml_liveat_block bpr mems sizes cfg la bb = (changed,la') /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\
  i < LENGTH bb.bb_instructions ==>
  (MEM a (ml_lookup la' (bb.bb_label,i)) <=>
   ml_liveat_record_bit a bpr mems sizes bb.bb_label (bb.bb_label,i)
     (MAPi (\j inst. (j,inst)) bb.bb_instructions)
     (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\ MEM a (ml_lookup la (lbl,0))) F)
Proof
  simp[ml_liveat_block_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `OL alloc_to (FOLDL (smerge alloc_to) []
    (MAP (\lbl. ml_lookup la (lbl,0)) (cfg_succs_of cfg bb.bb_label)))` by
    (irule ptr_ordered_merge_fold >>
     fs[OL, EVERY_MAP, EVERY_MEM, ptr_ml_ordered_def]) >>
  drule_all ml_liveat_insts_bits_exact >> disch_then (qspec_then `a` strip_assume_tac) >>
  first_x_assum (qspec_then `(bb.bb_label,i)` mp_tac) >>
  simp[ml_liveat_block_join_mem] >>
  `MEM (i,EL i bb.bb_instructions)
    (MAPi (\j inst. (j,inst)) bb.bb_instructions)` by simp[indexedListsTheory.MEM_MAPi] >>
  strip_tac >> irule ml_liveat_record_bit_old_irrelevant >>
  goal_assum (drule_at Any)
QED

Theorem ml_used_block_record_exact:
  ml_used_block bpr mems pallocas cfg us bb blocks = (changed,us') /\
  i < LENGTH bb.bb_instructions ==>
  (MEM a (ml_lookup us' (bb.bb_label,i)) <=>
   ml_used_record_bit a bpr mems bb.bb_label (bb.bb_label,i)
     (MAPi (\j inst. (j,inst)) bb.bb_instructions)
     (MEM a pallocas \/ ?lbl. MEM lbl (cfg_preds_of cfg bb.bb_label) /\
       MEM a (case FIND (\b. b.bb_label = lbl) blocks of
         NONE => ml_lookup us (lbl,0)
       | SOME b => ml_lookup us (b.bb_label,PRE (LENGTH b.bb_instructions)))) F)
Proof
  simp[ml_used_block_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule ml_used_insts_bits_exact >> disch_then (qspec_then `a` strip_assume_tac) >>
  first_x_assum (qspec_then `(bb.bb_label,i)` mp_tac) >>
  simp[ml_used_block_join_mem] >>
  `MEM (i,EL i bb.bb_instructions)
    (MAPi (\j inst. (j,inst)) bb.bb_instructions)` by simp[indexedListsTheory.MEM_MAPi] >>
  strip_tac >> irule ml_used_record_bit_old_irrelevant >>
  goal_assum (drule_at Any)
QED

Theorem ml_liveat_block_boundary_exact:
  ml_liveat_block bpr mems sizes cfg la bb = (changed,la') /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\
  bb.bb_instructions <> [] ==>
  (MEM a (ml_lookup la' (bb.bb_label,0)) <=>
   T IN sw_rhs (ml_liveat_boundary_desc a bpr mems sizes cfg bb)
     (\lbl. if MEM a (ml_lookup la (lbl,0)) then {T} else {}))
Proof
  strip_tac >> simp[ml_liveat_boundary_desc_rhs, ml_liveat_boundary_bit_def, COND_RAND] >>
  irule ml_liveat_block_record_exact >> simp[] >> Cases_on `bb.bb_instructions` >> gvs[]
QED

Theorem ml_used_block_boundary_exact:
  ml_used_block bpr mems pallocas cfg us bb blocks = (changed,us') /\
  bb.bb_instructions <> [] /\
  (!lbl. MEM lbl (cfg_preds_of cfg bb.bb_label) ==>
    (MEM a (case FIND (\b. b.bb_label = lbl) blocks of
       NONE => ml_lookup us (lbl,0)
     | SOME b => ml_lookup us (b.bb_label,PRE (LENGTH b.bb_instructions))) <=>
     T IN X lbl)) ==>
  (MEM a (ml_lookup us' (bb.bb_label,PRE (LENGTH bb.bb_instructions))) <=>
   T IN sw_rhs (ml_used_boundary_desc a bpr mems pallocas cfg bb) X)
Proof
  strip_tac >> simp[ml_used_boundary_desc_rhs, ml_used_boundary_bit_def] >>
  drule ml_used_block_record_exact >>
  disch_then (qspecl_then [`PRE (LENGTH bb.bb_instructions)`, `a`] mp_tac) >>
  impl_tac >- (Cases_on `bb.bb_instructions` >> gvs[]) >>
  strip_tac >> gvs[] >> AP_THM_TAC >> AP_TERM_TAC >> metis_tac[]
QED

Theorem ml_liveat_block_other_label:
  ml_liveat_block bpr mems sizes cfg la bb = (changed,la') /\
  lbl <> bb.bb_label ==>
  ml_lookup la' (lbl,i) = ml_lookup la (lbl,i)
Proof
  simp[ml_liveat_block_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  irule ml_liveat_insts_other_address >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ml_used_block_other_label:
  ml_used_block bpr mems pallocas cfg us bb blocks = (changed,us') /\
  lbl <> bb.bb_label ==>
  ml_lookup us' (lbl,i) = ml_lookup us (lbl,i)
Proof
  simp[ml_used_block_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  irule ml_used_insts_other_address >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ml_liveat_block_sw_update:
  ml_liveat_block bpr mems sizes cfg la bb = (changed,la') /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\
  bb.bb_instructions <> [] /\
  (!lbl. MEM a (ml_lookup la (lbl,0)) <=> T IN X lbl) ==>
  (!lbl. MEM a (ml_lookup la' (lbl,0)) <=>
    T IN sw_update (ml_liveat_boundary_desc a bpr mems sizes cfg bb) X lbl)
Proof
  strip_tac >> gen_tac >> simp[sw_update_lookup, ml_boundary_desc_out, COND_RAND] >>
  Cases_on `lbl = bb.bb_label` >> gvs[]
  >- (drule_all ml_liveat_block_boundary_exact >>
      simp[ml_liveat_boundary_desc_rhs, COND_RAND]) >>
  drule_all ml_liveat_block_other_label >> simp[]
QED

(* Expand a traversal to its actual sequence of successful block lookups.
   Shared by both directions of the concrete scan. *)
Definition ml_scan_blocks_def:
  (ml_scan_blocks blocks [] = []) /\
  (ml_scan_blocks blocks (lbl::lbls) =
    case FIND (\bb. bb.bb_label = lbl) blocks of
      NONE => ml_scan_blocks blocks lbls
    | SOME bb => bb::ml_scan_blocks blocks lbls)
End

Theorem ml_liveat_pass_sw_scan:
  !la changed la' X.
  ml_one_pass_liveat bpr mems sizes cfg blocks lbls la = (changed,la') /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\
  EVERY (\bb. bb.bb_instructions <> []) blocks /\
  (!lbl. MEM a (ml_lookup la (lbl,0)) <=> T IN X lbl) ==>
  (!lbl. MEM a (ml_lookup la' (lbl,0)) <=>
    T IN sw_scan (MAP (ml_liveat_boundary_desc a bpr mems sizes cfg)
      (ml_scan_blocks blocks lbls)) X lbl)
Proof
  Induct_on `lbls`
  >- simp[ml_one_pass_liveat_def, ml_scan_blocks_def, sw_scan_def] >>
  rpt gen_tac >> simp[ml_one_pass_liveat_def, ml_scan_blocks_def] >>
  Cases_on `FIND (\bb. bb.bb_label = h) blocks` >> simp[]
  >- metis_tac[] >>
  rename1 `FIND _ blocks = SOME bb` >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `MEM bb blocks` by metis_tac[venomExecProofsTheory.FIND_MEM] >>
  `bb.bb_instructions <> []` by
    (qpat_x_assum `EVERY _ blocks` mp_tac >> simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  rename1 `ml_liveat_block bpr mems sizes cfg la bb = (c1,mid)` >>
  `ptr_ml_ordered mid` by
    (drule_all ptr_liveat_block_ordered >>
     disch_then (qspecl_then [`sizes`, `cfg`, `bpr`, `bb`] mp_tac) >> simp[]) >>
  drule_all ml_liveat_block_sw_update >> strip_tac >>
  simp[sw_scan_def] >> first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Definition ml_used_boundary_lookup_def:
  ml_used_boundary_lookup blocks us lbl =
    case FIND (\b. b.bb_label = lbl) blocks of
      NONE => ml_lookup us (lbl,0)
    | SOME b => ml_lookup us (b.bb_label,PRE (LENGTH b.bb_instructions))
End

Theorem ml_used_block_sw_update:
  ml_used_block bpr mems pallocas cfg us bb blocks = (changed,us') /\
  FIND (\b. b.bb_label = bb.bb_label) blocks = SOME bb /\
  bb.bb_instructions <> [] /\
  (!lbl. MEM a (ml_used_boundary_lookup blocks us lbl) <=> T IN X lbl) ==>
  (!lbl. MEM a (ml_used_boundary_lookup blocks us' lbl) <=>
    T IN sw_update (ml_used_boundary_desc a bpr mems pallocas cfg bb) X lbl)
Proof
  strip_tac >> gen_tac >> simp[sw_update_lookup, ml_boundary_desc_out, COND_RAND] >>
  Cases_on `lbl = bb.bb_label` >> gvs[]
  >- (simp[ml_used_boundary_lookup_def] >>
      irule ml_used_block_boundary_exact >> simp[] >>
      goal_assum (drule_at (Pat `ml_used_block _ _ _ _ _ _ _ = _`)) >> simp[] >>
      gvs[ml_used_boundary_lookup_def]) >>
  `ml_used_boundary_lookup blocks us' lbl = ml_used_boundary_lookup blocks us lbl` suffices_by simp[] >>
  simp[ml_used_boundary_lookup_def] >>
  Cases_on `FIND (\b. b.bb_label = lbl) blocks` >> simp[]
  >- (drule_all ml_used_block_other_label >> simp[]) >>
  drule venomExecProofsTheory.FIND_P >> simp[] >> strip_tac >>
  drule_all ml_used_block_other_label >> simp[]
QED

Theorem ml_used_pass_sw_scan:
  !us changed us' X.
  ml_one_pass_used bpr mems pallocas cfg blocks lbls us = (changed,us') /\
  EVERY (\bb. bb.bb_instructions <> []) blocks /\
  (!lbl. MEM a (ml_used_boundary_lookup blocks us lbl) <=> T IN X lbl) ==>
  (!lbl. MEM a (ml_used_boundary_lookup blocks us' lbl) <=>
    T IN sw_scan (MAP (ml_used_boundary_desc a bpr mems pallocas cfg)
      (ml_scan_blocks blocks lbls)) X lbl)
Proof
  Induct_on `lbls`
  >- simp[ml_one_pass_used_def, ml_scan_blocks_def, sw_scan_def] >>
  rpt gen_tac >> simp[ml_one_pass_used_def, ml_scan_blocks_def] >>
  Cases_on `FIND (\bb. bb.bb_label = h) blocks` >> simp[]
  >- metis_tac[] >>
  rename1 `FIND _ blocks = SOME bb` >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `MEM bb blocks` by metis_tac[venomExecProofsTheory.FIND_MEM] >>
  `bb.bb_instructions <> []` by
    (qpat_x_assum `EVERY _ blocks` mp_tac >> simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  `bb.bb_label = h` by
    (drule venomExecProofsTheory.FIND_P >> simp[]) >>
  `FIND (\b. b.bb_label = bb.bb_label) blocks = SOME bb` by simp[] >>
  drule_all ml_used_block_sw_update >> strip_tac >>
  simp[sw_scan_def] >> first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ml_scan_blocks_find:
  !bb. MEM bb (ml_scan_blocks blocks lbls) ==>
  FIND (\b. b.bb_label = bb.bb_label) blocks = SOME bb
Proof
  Induct_on `lbls` >- simp[ml_scan_blocks_def] >>
  gen_tac >> pure_rewrite_tac[ml_scan_blocks_def] >>
  Cases_on `FIND (\bb. bb.bb_label = h) blocks` >> gvs[] >>
  rename1 `FIND _ blocks = SOME found` >>
  `found.bb_label = h` by (drule venomExecProofsTheory.FIND_P >> simp[]) >>
  metis_tac[]
QED

Theorem ml_scan_blocks_consistent:
  (!bb. sw_out (desc bb) = bb.bb_label) ==>
  sw_consistent (MAP desc (ml_scan_blocks blocks lbls))
Proof
  simp[sw_consistent_def, MEM_MAP] >> rpt strip_tac >>
  drule ml_scan_blocks_find >> strip_tac >>
  rev_drule ml_scan_blocks_find >> strip_tac >>
  gvs[] >> metis_tac[optionTheory.SOME_11]
QED

Theorem ml_scan_blocks_mem:
  MEM bb (ml_scan_blocks blocks lbls) ==> MEM bb blocks
Proof
  strip_tac >> drule ml_scan_blocks_find >>
  metis_tac[venomExecProofsTheory.FIND_MEM]
QED

Theorem ml_scan_blocks_outputs:
  (!bb. sw_out (desc bb) = bb.bb_label) ==>
  IMAGE sw_out (set (MAP desc (ml_scan_blocks blocks lbls))) SUBSET
    set (MAP (\bb. bb.bb_label) blocks)
Proof
  simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  drule ml_scan_blocks_mem >> strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ml_scan_blocks_card_bound:
  (!bb. sw_out (desc bb) = bb.bb_label) ==>
  CARD (IMAGE sw_out (set (MAP desc (ml_scan_blocks blocks lbls)))) <= LENGTH blocks
Proof
  strip_tac >>
  `CARD (IMAGE sw_out (set (MAP desc (ml_scan_blocks blocks lbls)))) <=
   CARD (set (MAP (\bb. bb.bb_label) blocks))` by
    (irule CARD_SUBSET >> simp[] >> irule ml_scan_blocks_outputs >> simp[]) >>
  qspec_then `MAP (\bb. bb.bb_label) blocks` mp_tac (GEN_ALL listTheory.CARD_LIST_TO_SET) >> simp[]
QED

Theorem ml_boundary_rounds_stable:
  (!bb. sw_out (desc bb) = bb.bb_label) /\ LENGTH blocks <= n ==>
  sw_scan (MAP desc (ml_scan_blocks blocks lbls))
    (sw_rounds (MAP desc (ml_scan_blocks blocks lbls)) n) =
  sw_rounds (MAP desc (ml_scan_blocks blocks lbls)) n
Proof
  strip_tac >>
  `sw_consistent (MAP desc (ml_scan_blocks blocks lbls))` by
    (irule ml_scan_blocks_consistent >> simp[]) >>
  `CARD (IMAGE sw_out (set (MAP desc (ml_scan_blocks blocks lbls)))) <= n` by
    (drule ml_scan_blocks_card_bound >>
     disch_then (qspecl_then [`lbls`, `blocks`] mp_tac) >> decide_tac) >>
  drule sw_rounds_stable >> disch_then (mp_then Any mp_tac sw_rounds_stationary) >>
  qmatch_goalsub_abbrev_tac `sw_rounds ds` >>
  qmatch_asmsub_abbrev_tac `bound <= n` >>
  strip_tac >>
  first_assum (qspec_then `n - bound` mp_tac) >>
  first_x_assum (qspec_then `SUC n - bound` mp_tac) >>
  `bound + (n - bound) = n /\ bound + (SUC n - bound) = SUC n` by decide_tac >>
  simp[sw_rounds_def]
QED

Theorem ml_liveat_block_false_boundary:
  ml_liveat_block bpr mems sizes cfg la bb = (F,la') ==>
  !lbl. ml_lookup la' (lbl,0) = ml_lookup la (lbl,0)
Proof
  strip_tac >> gen_tac >> Cases_on `lbl = bb.bb_label`
  >- (gvs[] >> qpat_x_assum `ml_liveat_block _ _ _ _ _ _ = _` mp_tac >>
      simp[ml_liveat_block_def] >> pairarg_tac >> simp[] >> metis_tac[]) >>
  drule_all ml_liveat_block_other_label >> simp[]
QED

Theorem ml_used_block_false_boundary:
  ml_used_block bpr mems pallocas cfg us bb blocks = (F,us') /\
  FIND (\b. b.bb_label = bb.bb_label) blocks = SOME bb ==>
  !lbl. ml_used_boundary_lookup blocks us' lbl = ml_used_boundary_lookup blocks us lbl
Proof
  strip_tac >> gen_tac >> Cases_on `lbl = bb.bb_label`
  >- (gvs[ml_used_boundary_lookup_def] >>
      qpat_x_assum `ml_used_block _ _ _ _ _ _ _ = _` mp_tac >>
      simp[ml_used_block_def] >> pairarg_tac >> simp[] >> metis_tac[]) >>
  simp[ml_used_boundary_lookup_def] >>
  Cases_on `FIND (\b. b.bb_label = lbl) blocks` >> simp[]
  >- (drule_all ml_used_block_other_label >> simp[]) >>
  drule venomExecProofsTheory.FIND_P >> simp[] >> strip_tac >>
  drule_all ml_used_block_other_label >> simp[]
QED

Theorem ml_liveat_pass_false_boundary:
  !la la'.
  ml_one_pass_liveat bpr mems sizes cfg blocks lbls la = (F,la') ==>
  !lbl. ml_lookup la' (lbl,0) = ml_lookup la (lbl,0)
Proof
  Induct_on `lbls` >- simp[ml_one_pass_liveat_def] >>
  rpt gen_tac >> simp[ml_one_pass_liveat_def] >>
  Cases_on `FIND (\bb. bb.bb_label = h) blocks` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule ml_liveat_block_false_boundary >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem ml_used_pass_false_boundary:
  !us us'.
  ml_one_pass_used bpr mems pallocas cfg blocks lbls us = (F,us') ==>
  !lbl. ml_used_boundary_lookup blocks us' lbl = ml_used_boundary_lookup blocks us lbl
Proof
  Induct_on `lbls` >- simp[ml_one_pass_used_def] >>
  rpt gen_tac >> simp[ml_one_pass_used_def] >>
  Cases_on `FIND (\bb. bb.bb_label = h) blocks` >> simp[] >>
  rename1 `FIND _ blocks = SOME bb` >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `bb.bb_label = h` by (drule venomExecProofsTheory.FIND_P >> simp[]) >>
  `FIND (\b. b.bb_label = bb.bb_label) blocks = SOME bb` by simp[] >>
  drule_all ml_used_block_false_boundary >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem ml_one_pass_false_boundary:
  ml_one_pass bpr mems sizes pallocas cfg fn la us = (F,la',us') ==>
  (!lbl. ml_lookup la' (lbl,0) = ml_lookup la (lbl,0)) /\
  (!lbl. ml_used_boundary_lookup fn.fn_blocks us' lbl =
         ml_used_boundary_lookup fn.fn_blocks us lbl)
Proof
  simp[ml_one_pass_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  conj_tac
  >- (drule ml_liveat_pass_false_boundary >> simp[]) >>
  drule ml_used_pass_false_boundary >> simp[]
QED

(* Full scans, without early exit, for comparison with the executable fueled
   iterator.  The executable analysis itself is not changed. *)
Definition ml_full_rounds_def:
  (ml_full_rounds bpr mems sizes pallocas cfg fn 0 = (FEMPTY,FEMPTY)) /\
  (ml_full_rounds bpr mems sizes pallocas cfg fn (SUC n) =
    case ml_full_rounds bpr mems sizes pallocas cfg fn n of (la,us) =>
    case ml_one_pass bpr mems sizes pallocas cfg fn la us of (changed,la',us') =>
      (la',us'))
End

Theorem ml_full_rounds_ordered:
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas ==>
  !n. ptr_ml_ordered (FST (ml_full_rounds bpr mems sizes pallocas cfg fn n)) /\
      ptr_ml_ordered (SND (ml_full_rounds bpr mems sizes pallocas cfg fn n))
Proof
  strip_tac >> Induct >> simp[ml_full_rounds_def] >>
  Cases_on `ml_full_rounds bpr mems sizes pallocas cfg fn n` >> gvs[] >>
  rename1 `ml_full_rounds bpr mems sizes pallocas cfg fn n = (la,us)` >>
  Cases_on `ml_one_pass bpr mems sizes pallocas cfg fn la us` >>
  rename1 `ml_one_pass bpr mems sizes pallocas cfg fn la us = (changed,result)` >>
  Cases_on `result` >> gvs[] >>
  drule_all ptr_one_pass_ordered >> simp[]
QED

Theorem ml_one_pass_sw_scan:
  ml_one_pass bpr mems sizes pallocas cfg fn la us = (changed,la',us') /\
  (!nm. OL alloc_to (mems nm)) /\ ptr_ml_ordered la /\
  EVERY (\bb. bb.bb_instructions <> []) fn.fn_blocks /\
  (!lbl. MEM a (ml_lookup la (lbl,0)) <=> T IN X lbl) /\
  (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks us lbl) <=> T IN Y lbl) ==>
  (!lbl. MEM a (ml_lookup la' (lbl,0)) <=>
    T IN sw_scan (MAP (ml_liveat_boundary_desc a bpr mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) X lbl) /\
  (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks us' lbl) <=>
    T IN sw_scan (MAP (ml_used_boundary_desc a bpr mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) Y lbl)
Proof
  simp[ml_one_pass_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >> conj_tac
  >- (drule_all ml_liveat_pass_sw_scan >> simp[]) >>
  drule_all ml_used_pass_sw_scan >> simp[]
QED

Theorem ml_used_boundary_lookup_empty[simp]:
  ml_used_boundary_lookup blocks FEMPTY lbl = []
Proof
  simp[ml_used_boundary_lookup_def, ml_lookup_def] >>
  Cases_on `FIND (\b. b.bb_label = lbl) blocks` >> simp[]
QED

Theorem ml_full_rounds_boundary_exact:
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  EVERY (\bb. bb.bb_instructions <> []) fn.fn_blocks ==>
  !n.
  (!lbl. MEM a (ml_lookup (FST (ml_full_rounds bpr mems sizes pallocas cfg fn n)) (lbl,0)) <=>
    T IN sw_rounds (MAP (ml_liveat_boundary_desc a bpr mems sizes cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n lbl) /\
  (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks
      (SND (ml_full_rounds bpr mems sizes pallocas cfg fn n)) lbl) <=>
    T IN sw_rounds (MAP (ml_used_boundary_desc a bpr mems pallocas cfg)
      (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre)) n lbl)
Proof
  strip_tac >> Induct
  >- simp[ml_full_rounds_def, sw_rounds_def, ml_lookup_def] >>
  `ptr_ml_ordered (FST (ml_full_rounds bpr mems sizes pallocas cfg fn n))` by
    (drule_all ml_full_rounds_ordered >> simp[]) >>
  simp[ml_full_rounds_def, sw_rounds_def] >>
  Cases_on `ml_full_rounds bpr mems sizes pallocas cfg fn n` >> gvs[] >>
  rename1 `ml_full_rounds bpr mems sizes pallocas cfg fn n = (la,us)` >>
  Cases_on `ml_one_pass bpr mems sizes pallocas cfg fn la us` >>
  rename1 `ml_one_pass bpr mems sizes pallocas cfg fn la us = (changed,result)` >>
  Cases_on `result` >> gvs[] >>
  drule_all ml_one_pass_sw_scan >> simp[]
QED

Theorem ml_full_rounds_boundary_stable:
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  EVERY (\bb. bb.bb_instructions <> []) fn.fn_blocks /\
  LENGTH fn.fn_blocks <= n ==>
  (!lbl. MEM a (ml_lookup (FST (ml_full_rounds bpr mems sizes pallocas cfg fn (SUC n))) (lbl,0)) <=>
         MEM a (ml_lookup (FST (ml_full_rounds bpr mems sizes pallocas cfg fn n)) (lbl,0))) /\
  (!lbl. MEM a (ml_used_boundary_lookup fn.fn_blocks
      (SND (ml_full_rounds bpr mems sizes pallocas cfg fn (SUC n))) lbl) <=>
         MEM a (ml_used_boundary_lookup fn.fn_blocks
      (SND (ml_full_rounds bpr mems sizes pallocas cfg fn n)) lbl))
Proof
  strip_tac >> drule_all ml_full_rounds_boundary_exact >>
  strip_tac >> simp[] >> conj_tac >> gen_tac >> simp[sw_rounds_def] >>
  AP_TERM_TAC >> AP_THM_TAC >>
  irule ml_boundary_rounds_stable >> simp[ml_boundary_desc_out]
QED
