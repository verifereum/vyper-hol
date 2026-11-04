Theory concretizePtrReadCoverage
Ancestors
  concretizePtrStoreCoverage concretizeMemLocDefs

(* Arbitrary membership alone cannot justify the sorted intersection. *)
Theorem ptr_unsorted_intersection_probe:
  MEM (Allocation 0) [Allocation 1; Allocation 0] /\
  MEM (Allocation 0) [Allocation 0] /\
  ~MEM (Allocation 0)
    (sinter alloc_to [Allocation 1; Allocation 0] [Allocation 0])
Proof
  EVAL_TAC
QED

Theorem ptr_livesets_insts_preserves[local]:
  !ls addrs. FLOOKUP ls a = SOME addrs /\ MEM p addrs ==>
  ?addrs'. FLOOKUP (ml_livesets_insts label la us ls insts) a = SOME addrs' /\
            MEM p addrs'
Proof
  Induct_on `insts` >> simp[ml_livesets_insts_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[ml_livesets_insts_def, GSYM ptr_store_insert_def, SF ETA_ss] >>
  rpt strip_tac >> first_x_assum irule >>
  irule ptr_store_fold_preserves >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ptr_livesets_insts_covers[local]:
  !ls. MEM (idx,inst) insts /\
  MEM a (sinter alloc_to (ml_lookup la (label,idx)) (ml_lookup us (label,idx))) ==>
  ?addrs. FLOOKUP (ml_livesets_insts label la us ls insts) a = SOME addrs /\
          MEM (label,idx) addrs
Proof
  Induct_on `insts` >> simp[ml_livesets_insts_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[ml_livesets_insts_def, GSYM ptr_store_insert_def, SF ETA_ss] >>
  rpt strip_tac >> gvs[]
  >- (irule ptr_livesets_insts_preserves >>
      irule ptr_store_fold_covers >> simp[])
  >> first_x_assum irule >> simp[]
QED

Theorem ptr_livesets_blocks_preserves[local]:
  !ls addrs. FLOOKUP ls a = SOME addrs /\ MEM p addrs ==>
  ?addrs'. FLOOKUP
    (FOLDL (\m bb. ml_livesets_insts bb.bb_label la us m
      (MAPi (\i inst. (i,inst)) bb.bb_instructions)) ls blocks) a = SOME addrs' /\
    MEM p addrs'
Proof
  Induct_on `blocks` >> simp[] >>
  metis_tac[ptr_livesets_insts_preserves]
QED

Theorem ptr_livesets_blocks_covers[local]:
  !ls. MEM bb blocks /\
  MEM (idx,inst) (MAPi (\i inst. (i,inst)) bb.bb_instructions) /\
  MEM a (sinter alloc_to (ml_lookup la (bb.bb_label,idx))
                         (ml_lookup us (bb.bb_label,idx))) ==>
  ?addrs. FLOOKUP
    (FOLDL (\m bb. ml_livesets_insts bb.bb_label la us m
      (MAPi (\i inst. (i,inst)) bb.bb_instructions)) ls blocks) a = SOME addrs /\
    MEM (bb.bb_label,idx) addrs
Proof
  Induct_on `blocks` >> simp[] >> rpt strip_tac >> gvs[]
  >- metis_tac[ptr_livesets_insts_covers, ptr_livesets_blocks_preserves]
  >> first_x_assum irule >> simp[]
QED

Theorem ptr_compute_livesets_covers:
  MEM bb fn.fn_blocks /\
  MEM (idx,inst) (MAPi (\i inst. (i,inst)) bb.bb_instructions) /\
  MEM a (sinter alloc_to (ml_lookup la (bb.bb_label,idx))
                         (ml_lookup us (bb.bb_label,idx))) ==>
  ?addrs. FLOOKUP (ml_compute_livesets la us fn) a = SOME addrs /\
          MEM (bb.bb_label,idx) addrs
Proof
  rewrite_tac[ml_compute_livesets_def] >> rpt strip_tac >>
  irule ptr_livesets_blocks_covers >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem ptr_compute_livesets_index:
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  MEM a (sinter alloc_to (ml_lookup la (bb.bb_label,i))
                         (ml_lookup us (bb.bb_label,i))) ==>
  MEM (bb.bb_label,i)
    (case FLOOKUP (ml_compute_livesets la us fn) a of NONE => [] | SOME xs => xs)
Proof
  rpt strip_tac >>
  `MEM (i,EL i bb.bb_instructions)
    (MAPi (\i inst. (i,inst)) bb.bb_instructions)` by
    simp[indexedListsTheory.MEM_MAPi] >>
  drule_all ptr_compute_livesets_covers >> strip_tac >> simp[]
QED

Theorem ptr_marked_intersection:
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  MEM a (sinter alloc_to (ml_lookup la (bb.bb_label,i))
                         (ml_lookup us (bb.bb_label,i))) ==>
  ?addrs. FLOOKUP (ml_mark_stores_live bpr fn (ml_compute_livesets la us fn)) a
          = SOME addrs /\ MEM (bb.bb_label,i) addrs
Proof
  strip_tac >> drule_all ptr_compute_livesets_index >>
  Cases_on `FLOOKUP (ml_compute_livesets la us fn) a` >> simp[] >>
  strip_tac >> irule ptr_mark_stores_preserves >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ptr_smerge_union[local]:
  !cmp xs ys. MEM a (smerge cmp xs ys) <=> MEM a xs \/ MEM a ys
Proof
  recInduct enumeralTheory.smerge_ind >>
  simp[enumeralTheory.smerge] >> rpt strip_tac >>
  Cases_on `apto cmp x y` >> fs[] >>
  metis_tac[totoTheory.TotOrd_apto, totoTheory.TotOrd]
QED

Theorem ptr_sdiff_other[local]:
  !xs. MEM a xs /\ a <> b ==> MEM a (sdiff cmp xs [b])
Proof
  `!ys. sdiff cmp ys [] = ys` by
    (Induct >> simp[enumeralTheory.sdiff]) >>
  `!x y. apto cmp x y = EQUAL <=> x = y` by
    (qspec_then `cmp` mp_tac totoTheory.TotOrd_apto >> simp[totoTheory.TotOrd]) >>
  Induct_on `xs` >> simp[enumeralTheory.sdiff] >>
  rpt strip_tac >> Cases_on `apto cmp h b` >>
  gvs[enumeralTheory.sdiff] >>
  metis_tac[]
QED

Theorem ptr_liveat_records:
  MEM a live \/ MEM a (find_base_allocas_opt bpr (inst_read_op inst)) ==>
  MEM a (ml_lookup
    (SND (ml_liveat_inst bpr mems sizes label idx inst live la)) (label,idx))
Proof
  simp[ml_liveat_inst_def, ml_lookup_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >>
  simp[ptr_smerge_union] >>
  Cases_on `inst.inst_operands` >> simp[ptr_smerge_union] >>
  Cases_on `h` >> simp[ptr_smerge_union]
QED

Definition ptr_ml_can_kill_def:
  ptr_ml_can_kill a bpr sizes inst <=>
    ?wsz. inst_write_size inst = SOME wsz /\
      find_base_allocas_opt bpr (inst_write_op inst) = [a] /\
      sizes a = SOME wsz /\
      ~MEM a (find_base_allocas_opt bpr (inst_read_op inst))
End

Theorem ptr_kill_write_preserves[local]:
  MEM a live /\
  ~(a = alloc /\ sizes a = SOME wsz /\ ~MEM a reads) ==>
  MEM a (ml_kill_write sizes reads wsz live alloc)
Proof
  simp[ml_kill_write_def] >>
  Cases_on `sizes alloc` >> simp[] >>
  rpt strip_tac >> rpt IF_CASES_TAC >>
  gvs[ptr_smerge_union] >> metis_tac[ptr_sdiff_other]
QED

Theorem ptr_liveat_preserves:
  MEM a live /\ ~ptr_ml_can_kill a bpr sizes inst ==>
  MEM a (FST (ml_liveat_inst bpr mems sizes label idx inst live la))
Proof
  rpt strip_tac >>
  `MEM a (ml_lookup
    (SND (ml_liveat_inst bpr mems sizes label idx inst live la)) (label,idx))` by
    metis_tac[ptr_liveat_records] >>
  pop_assum mp_tac >>
  simp[ml_liveat_inst_def, ml_lookup_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac `MEM a live2` >>
  Cases_on `inst_write_size inst` >> simp[] >>
  Cases_on `find_base_allocas_opt bpr (inst_write_op inst)` >> simp[] >>
  Cases_on `t` >> simp[] >>
  strip_tac >> irule ptr_kill_write_preserves >>
  gvs[ptr_ml_can_kill_def]
QED

(* Production ordering audit (C1.5.5).
   The canonical invariant required at ml_livesets_insts is
     (!addr. OL alloc_to (ml_lookup la addr)) /\
     (!addr. OL alloc_to (ml_lookup us addr)).
   OL is strict: every head compares LESS with every tail member. Thus it
   already entails duplicate freedom; a separate ALL_DISTINCT premise is
   unnecessary. OL_INTER_IMP supplies the exact intersection membership,
   OL_UNION_IMP/smerge_OL preserve merges, OL_DIFF_IMP preserves kills.

   Missing proof interfaces (not assumptions of the stage statements):
   - OL alloc_to (find_base_allocas bpr op), and its option wrapper.
     The producer uses incr_ssort; it needs no bp-result invariant.
   - OL alloc_to xs /\ EVERY (OL alloc_to) xss ==>
       OL alloc_to (FOLDL (smerge alloc_to) xs xss).
   - The map invariant above for FEMPTY and updates at an arbitrary address.
   - Under (!name. OL alloc_to (mems name)), sorted live and sorted la,
     both the returned live and updated la of ml_liveat_inst are sorted.
     ml_kill_write either retains live, singleton-diffs it, or merges a
     singleton. Its size/read guards do not affect order preservation.
   - The analogous ml_used_inst result for sorted cur_used and us.
   - Lift the pair results through ml_liveat_insts_rev/ml_used_insts;
     then block joins, block-label passes and ml_one_pass. Used block
     joins additionally require OL alloc_to live_pallocas.
   - Lift ml_one_pass preservation through ml_iterate_fuel, generalized
     over initial la/us; and separately through successful ml_iterate
     (OWHILE invariant). Success does not itself establish convergence
     completeness or semantic demand coverage.

   Actual production arguments satisfy the leaf ordering requirements by
   construction: context_mem_livesets sorts MAP FST of callee metadata,
   and supplies [] for live_pallocas. Single-function layout also supplies
   K [] and []. No ordering premise on fn_mems_used itself is justified:
   unique_mems_used preserves discovery order, not comparator order.
   ml_ordered_iter sorts its mems argument for canonical ml_one_pass;
   its separate ola sidecar intentionally preserves insertion order and
   must not be fed to sinter as though it were canonical liveat. The
   sidecar supplies priority only via ml_complete_order.

   Production layout uses the fuel analysis, including fuel=0 (empty maps).
   Unbounded mem_liveness_analyze returns FEMPTY on OWHILE NONE; that is
   vacuously ordered but gives no read coverage. Checked completion fills
   absent allocations by checked_first_fit, while retaining candidate
   placements. Neither fallback nor ordering proves semantic noninterference.
   Also needed downstream: sorted inst_addr lists in canonical livesets,
   since allocate_with_livesets uses sinter inst_addr_to on those lists.
   Their producers insert singletons by smerge starting at FEMPTY; imported
   liveset_info reads this same map. This is a distinct map invariant from
   allocation-list ordering, not a theorem about the unsorted sidecar.
*)
