(*
 * Tail Merge Pass — merge map and lookup_block lemmas
 *
 * Facts about block_sigs, compute_merge_map and lookup_block in the
 * transformed function that depend only on the definitions.
 *)

Theory tailMergeMap
Ancestors
  tailMergeHelpers tailMergeDefs cfgTransform venomInst venomWf cfgTransformProofs

(* ================================================================
   Section 1: lookup_block in transformed function
   ================================================================ *)

Theorem lookup_block_MAP_subst:
  !m bbs lbl bb.
    lookup_block lbl bbs = SOME bb ==>
    lookup_block lbl (MAP (subst_block_labels_block m) bbs) =
      SOME (subst_block_labels_block m bb)
Proof
  Induct_on `bbs` >> rw[lookup_block_def, listTheory.FIND_thm] >>
  gvs[GSYM lookup_block_def]
QED

Theorem lookup_block_FILTER_not_mem:
  !bbs lbl removed bb.
    lookup_block lbl bbs = SOME bb /\ ~MEM lbl removed ==>
    lookup_block lbl (FILTER (\bb. ~MEM bb.bb_label removed) bbs) = SOME bb
Proof
  Induct >> rw[lookup_block_def, listTheory.FIND_thm] >>
  gvs[GSYM lookup_block_def]
QED

Theorem lookup_block_tail_merge:
  !m bbs lbl bb removed.
    lookup_block lbl bbs = SOME bb /\ ~MEM lbl removed ==>
    lookup_block lbl
      (FILTER (\bb'. ~MEM bb'.bb_label removed)
              (MAP (subst_block_labels_block m) bbs)) =
    SOME (subst_block_labels_block m bb)
Proof
  rw[] >> irule lookup_block_FILTER_not_mem >> simp[] >>
  irule lookup_block_MAP_subst >> simp[]
QED

(* ================================================================
   Section 2: Properties of block_sigs and compute_merge_map
   ================================================================ *)

Theorem block_sigs_excludes_entry:
  !func entry bbs lbl sig.
    MEM (lbl, sig) (block_sigs func entry bbs) ==> lbl <> entry
Proof
  Induct_on `bbs` >> simp[block_sigs_def] >> rw[] >> gvs[]
QED

Theorem block_sigs_MEM_blocks:
  !func entry bbs lbl sig.
    MEM (lbl, sig) (block_sigs func entry bbs) ==>
    ?bb. MEM bb bbs /\ bb.bb_label = lbl /\ sig = block_signature bb
Proof
  Induct_on `bbs` >> simp[block_sigs_def] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem block_sigs_FST_subset:
  !func entry bbs lbl.
    MEM lbl (MAP FST (block_sigs func entry bbs)) ==>
    ?bb. MEM bb bbs /\ bb.bb_label = lbl
Proof
  Induct_on `bbs` >> simp[block_sigs_def] >> rw[] >> gvs[] >>
  metis_tac[]
QED

Theorem block_sigs_all_distinct_FST:
  !func entry bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ALL_DISTINCT (MAP FST (block_sigs func entry bbs))
Proof
  Induct_on `bbs` >> simp[block_sigs_def] >> rw[] >> gvs[] >>
  CCONTR_TAC >> gvs[] >>
  drule block_sigs_FST_subset >> strip_tac >>
  gvs[listTheory.MEM_MAP]
QED

Theorem compute_merge_map_source:
  !sigs groups lbl keeper.
    MEM (lbl, keeper) (compute_merge_map sigs groups) ==>
    ?sig. MEM (lbl, SOME sig) sigs
Proof
  Induct >> simp[compute_merge_map_def] >> rw[] >>
  Cases_on `h` >> gvs[compute_merge_map_def] >>
  Cases_on `r` >> gvs[compute_merge_map_def] >-
    metis_tac[] >>
  Cases_on `ALOOKUP groups x` >> gvs[] >> metis_tac[]
QED

Theorem compute_merge_map_keeper_gen:
  !sigs groups lbl keeper.
    MEM (lbl, keeper) (compute_merge_map sigs groups) ==>
    ?sig. MEM (lbl, SOME sig) sigs /\
          (MEM (keeper, SOME sig) sigs \/ ALOOKUP groups sig = SOME keeper)
Proof
  Induct_on `sigs` >- simp[compute_merge_map_def] >>
  rpt gen_tac >> Cases_on `h` >> Cases_on `r` >| [
    simp[compute_merge_map_def] >>
    strip_tac >> first_x_assum drule >> strip_tac >>
    qexists_tac `sig` >> simp[],
    simp[compute_merge_map_def] >>
    Cases_on `ALOOKUP groups x` >> simp[] >| [
      strip_tac >> first_x_assum drule >> strip_tac >>
      fs[alistTheory.ALOOKUP_def] >>
      Cases_on `sig = x` >> fs[] >-
        (qexists_tac `x` >> simp[]) >>
      qexists_tac `sig` >> fs[],
      strip_tac >> fs[] >-
        (qexists_tac `x` >> simp[]) >>
      first_x_assum drule >> strip_tac >>
      qexists_tac `sig` >> fs[]
    ]
  ]
QED

Theorem compute_merge_map_keeper_same_sig:
  !sigs lbl keeper.
    MEM (lbl, keeper) (compute_merge_map sigs []) ==>
    ?sig. MEM (lbl, SOME sig) sigs /\ MEM (keeper, SOME sig) sigs
Proof
  rpt strip_tac >> drule compute_merge_map_keeper_gen >>
  strip_tac >> qexists_tac `sig` >> fs[alistTheory.ALOOKUP_def]
QED

Theorem compute_merge_map_not_entry:
  !func entry bbs lbl keeper.
    MEM (lbl, keeper) (compute_merge_map (block_sigs func entry bbs) []) ==>
    lbl <> entry /\ keeper <> entry
Proof
  rpt strip_tac >>
  drule compute_merge_map_keeper_same_sig >> strip_tac >| [
    drule compute_merge_map_source >> strip_tac >>
    drule_at Any block_sigs_excludes_entry >> simp[],
    imp_res_tac block_sigs_excludes_entry >> gvs[]
  ]
QED

Theorem compute_merge_map_halting:
  !func entry bbs lbl keeper.
    MEM (lbl, keeper) (compute_merge_map (block_sigs func entry bbs) []) ==>
    ?bb_lbl bb_kpr sig.
      MEM bb_lbl bbs /\ bb_lbl.bb_label = lbl /\
      MEM bb_kpr bbs /\ bb_kpr.bb_label = keeper /\
      block_signature bb_lbl = SOME sig /\
      block_signature bb_kpr = SOME sig /\
      bb_is_halting bb_lbl /\ bb_self_contained bb_lbl /\
      bb_is_halting bb_kpr /\ bb_self_contained bb_kpr
Proof
  rpt strip_tac >>
  drule compute_merge_map_keeper_same_sig >> strip_tac >>
  `?bb1. MEM bb1 bbs /\ bb1.bb_label = lbl /\
         SOME sig = block_signature bb1` by metis_tac[block_sigs_MEM_blocks] >>
  `?bb2. MEM bb2 bbs /\ bb2.bb_label = keeper /\
         SOME sig = block_signature bb2` by metis_tac[block_sigs_MEM_blocks] >>
  qexistsl_tac [`bb1`, `bb2`, `sig`] >>
  gvs[block_signature_def]
QED

(* Sources of compute_merge_map come from sigs *)
Theorem compute_merge_map_FST_subset:
  !sigs groups x.
    MEM x (MAP FST (compute_merge_map sigs groups)) ==>
    MEM x (MAP FST sigs)
Proof
  Induct >- simp[compute_merge_map_def] >>
  rpt gen_tac >> Cases_on `h` >> Cases_on `r` >| [
    simp[compute_merge_map_def] >> metis_tac[],
    simp[compute_merge_map_def] >>
    Cases_on `ALOOKUP groups x'` >> simp[] >| [
      strip_tac >> metis_tac[],
      strip_tac >> gvs[] >> metis_tac[]
    ]
  ]
QED

(* Keepers of compute_merge_map come from groups values *)
Theorem compute_merge_map_SND_subset:
  !sigs groups x.
    MEM x (MAP SND (compute_merge_map sigs groups)) ==>
    MEM x (MAP SND groups) \/ MEM x (MAP FST sigs)
Proof
  Induct >- simp[compute_merge_map_def] >>
  rpt gen_tac >> Cases_on `h` >> Cases_on `r` >| [
    (* (lbl, NONE) *)
    simp[compute_merge_map_def] >>
    strip_tac >> res_tac >> simp[],
    (* (lbl, SOME sig) *)
    simp[compute_merge_map_def] >>
    Cases_on `ALOOKUP groups x'` >> simp[] >| [
      (* ALOOKUP = NONE: lbl added to groups *)
      strip_tac >>
      first_x_assum (qspecl_then [`(x', q)::groups`, `x`] mp_tac) >>
      simp[] >> strip_tac >> gvs[] >> metis_tac[],
      (* ALOOKUP = SOME keeper *)
      strip_tac >> gvs[] >| [
        (* x is the keeper from ALOOKUP *)
        rename1 `ALOOKUP groups _ = SOME keeper` >>
        drule alistTheory.ALOOKUP_MEM >> strip_tac >>
        `MEM keeper (MAP SND groups)` by
          metis_tac[listTheory.MEM_MAP, pairTheory.SND] >>
        simp[],
        (* x from recursive call *)
        res_tac >> simp[]
      ]
    ]
  ]
QED

(* Sources (MAP FST) and keepers (MAP SND) of compute_merge_map are disjoint.
   Direct induction: a label is either stored in groups (keeper) or emitted (source),
   never both, because ALL_DISTINCT prevents re-processing. *)
Theorem compute_merge_map_disjoint_gen:
  !sigs groups.
    ALL_DISTINCT (MAP FST sigs) /\
    DISJOINT (set (MAP FST sigs)) (set (MAP SND groups)) ==>
    DISJOINT (set (MAP FST (compute_merge_map sigs groups)))
             (set (MAP SND (compute_merge_map sigs groups)))
Proof
  Induct >- simp[compute_merge_map_def, pred_setTheory.DISJOINT_EMPTY] >>
  rpt gen_tac >> Cases_on `h` >> Cases_on `r` >- (
    (* (lbl, NONE): skip *)
    simp[compute_merge_map_def] >> strip_tac >>
    first_x_assum (qspec_then `groups` mp_tac) >> simp[] >>
    disch_then irule >>
    gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
    metis_tac[]
  ) >>
  (* (lbl, SOME sig) — NONE case solved by simp, only SOME remains *)
  rename1 `(q, SOME sig)` >>
  REWRITE_TAC[compute_merge_map_def] >>
  Cases_on `ALOOKUP groups sig` >> simp[] >>
  (* ALOOKUP = SOME keeper: (q, keeper) emitted *)
  strip_tac >>
  rename1 `ALOOKUP groups sig = SOME keeper` >>
  `MEM keeper (MAP SND groups)` by (
    drule alistTheory.ALOOKUP_MEM >> strip_tac >>
    metis_tac[listTheory.MEM_MAP, pairTheory.SND]) >>
  (* keeper not in FST(rec): keeper is from groups, not sigs *)
  `~MEM keeper (MAP FST (compute_merge_map sigs groups))` by (
    CCONTR_TAC >> gvs[] >>
    drule compute_merge_map_FST_subset >> strip_tac >>
    gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
    metis_tac[]) >>
  (* q <> keeper: q not in groups, keeper is *)
  `q <> keeper` by (
    gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
    metis_tac[]) >>
  (* q not in SND(rec): q not in sigs tail or groups *)
  `~MEM q (MAP SND (compute_merge_map sigs groups))` by (
    CCONTR_TAC >> gvs[] >>
    drule compute_merge_map_SND_subset >> strip_tac >> gvs[]) >>
  simp[]
QED

Theorem compute_merge_map_disjoint:
  !sigs.
    ALL_DISTINCT (MAP FST sigs) ==>
    DISJOINT (set (MAP FST (compute_merge_map sigs [])))
             (set (MAP SND (compute_merge_map sigs [])))
Proof
  rpt strip_tac >> irule compute_merge_map_disjoint_gen >>
  simp[pred_setTheory.DISJOINT_EMPTY]
QED

Theorem compute_merge_map_SND_not_FST:
  !sigs lbl keeper.
    ALL_DISTINCT (MAP FST sigs) /\
    MEM (lbl, keeper) (compute_merge_map sigs []) ==>
    ~MEM keeper (MAP FST (compute_merge_map sigs []))
Proof
  rpt strip_tac >>
  drule compute_merge_map_disjoint >> strip_tac >>
  `MEM keeper (MAP SND (compute_merge_map sigs []))` by
    metis_tac[listTheory.MEM_MAP, pairTheory.SND] >>
  gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
      pred_setTheory.IN_INSERT, listTheory.MEM] >>
  metis_tac[]
QED

(* ALL_DISTINCT of FLAT means distinct sublists are disjoint *)
Theorem all_distinct_flat_disjoint:
  !ls (i:num) j x.
    ALL_DISTINCT (FLAT ls) /\ i < LENGTH ls /\ j < LENGTH ls /\ i <> j /\
    MEM x (EL i ls) /\ MEM x (EL j ls) ==> F
Proof
  rpt strip_tac >>
  wlog_tac `i < j` [`i`, `j`] >- (`j < i` by simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (FLAT (TAKE (SUC i) ls) ++ FLAT (DROP (SUC i) ls))`
    by metis_tac[listTheory.FLAT_APPEND, listTheory.TAKE_DROP] >>
  fs[listTheory.ALL_DISTINCT_APPEND] >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
  `SUC i <= LENGTH ls` by simp[] >>
  conj_tac >- (
    (* MEM x (FLAT (TAKE (SUC i) ls)): EL i ls is in TAKE (SUC i) ls *)
    simp[listTheory.MEM_FLAT] >>
    qexists_tac `EL i ls` >> simp[] >>
    `i < LENGTH (TAKE (SUC i) ls)` by simp[listTheory.LENGTH_TAKE] >>
    `EL i (TAKE (SUC i) ls) = EL i ls` by simp[listTheory.EL_TAKE] >>
    metis_tac[listTheory.EL_MEM]) >>
  (* MEM x (FLAT (DROP (SUC i) ls)): EL j ls is in DROP (SUC i) ls *)
  simp[listTheory.MEM_FLAT] >>
  qexists_tac `EL j ls` >> simp[] >>
  `j - SUC i < LENGTH (DROP (SUC i) ls)` by simp[listTheory.LENGTH_DROP] >>
  `(j - SUC i) + SUC i = j` by simp[] >>
  `EL (j - SUC i) (DROP (SUC i) ls) = EL j ls`
    by metis_tac[listTheory.EL_DROP] >>
  metis_tac[listTheory.EL_MEM]
QED

Theorem compute_merge_map_entry_survives:
  !func entry.
    ~MEM entry (MAP FST
      (compute_merge_map (block_sigs func entry func.fn_blocks) []))
Proof
  simp[listTheory.MEM_MAP] >> rpt strip_tac >>
  PairCases_on `y` >> gvs[] >>
  drule compute_merge_map_not_entry >> simp[]
QED

Theorem compute_merge_map_image_survives:
  !func entry l.
    ALL_DISTINCT (fn_labels func) /\ MEM l (fn_labels func) ==>
    let m = compute_merge_map (block_sigs func entry func.fn_blocks) [] in
    MEM (case ALOOKUP m l of NONE => l | SOME k => k)
      (MAP (\bb. bb.bb_label)
        (FILTER (\bb. ~MEM bb.bb_label (MAP FST m)) func.fn_blocks))
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  Cases_on `ALOOKUP (compute_merge_map
    (block_sigs func entry func.fn_blocks) []) l`
  >- (gvs[alistTheory.ALOOKUP_NONE, fn_labels_def,
           listTheory.MEM_MAP, listTheory.MEM_FILTER] >> metis_tac[]) >>
  drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  `ALL_DISTINCT (MAP FST (block_sigs func entry func.fn_blocks))` by
    (irule block_sigs_all_distinct_FST >> gvs[fn_labels_def]) >>
  drule_all compute_merge_map_SND_not_FST >> strip_tac >>
  drule compute_merge_map_keeper_same_sig >> strip_tac >>
  gvs[listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  metis_tac[block_sigs_MEM_blocks]
QED
