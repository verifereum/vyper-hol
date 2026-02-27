(*
 * CFG Helper Lemmas
 *
 * Characterization lemmas for build_succs, build_preds, build_reachable,
 * and DFS walk functions. Used by cfgCorrectnessProof.
 *)

Theory cfgHelpers
Ancestors
  cfgDefs pred_set finite_map list rich_list relation

(* Register short names for record accessors so that
   cfg_dfs_post / cfg_dfs_pre parse as the accessor constants
   rather than free variables. *)
val _ = Parse.overload_on("cfg_dfs_post",
  prim_mk_const{Name="recordtype.cfg_analysis.seldef.cfg_dfs_post",Thy="cfgDefs"});
val _ = Parse.overload_on("cfg_dfs_pre",
  prim_mk_const{Name="recordtype.cfg_analysis.seldef.cfg_dfs_pre",Thy="cfgDefs"});

(* ==========================================================================
   General FOLDL |+ toolkit (keyed by record field)
   ========================================================================== *)

Theorem foldl_fupdate_keys_fdom[local]:
  !(key : 'a -> 'b) (vf : 'a -> 'c) xs (acc : 'b |-> 'c).
    FDOM (FOLDL (λm x. m |+ (key x, vf x)) acc xs) =
    FDOM acc ∪ set (MAP key xs)
Proof
  ntac 2 gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem foldl_fupdate_keys_flookup_other[local]:
  !(key : 'a -> 'b) (vf : 'a -> 'c) xs (acc : 'b |-> 'c) k.
    ~MEM k (MAP key xs) ==>
    FLOOKUP (FOLDL (λm x. m |+ (key x, vf x)) acc xs) k = FLOOKUP acc k
Proof
  ntac 2 gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`acc |+ (key h, vf h)`, `k`] mp_tac) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem foldl_fupdate_keys_flookup[local]:
  !(key : 'a -> 'b) (vf : 'a -> 'c) xs (acc : 'b |-> 'c) x.
    ALL_DISTINCT (MAP key xs) /\ MEM x xs ==>
    FLOOKUP (FOLDL (λm x. m |+ (key x, vf x)) acc xs) (key x) = SOME (vf x)
Proof
  ntac 2 gen_tac >> Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  simp[foldl_fupdate_keys_flookup_other, FLOOKUP_UPDATE]
QED

(* ==========================================================================
   set_insert and fmap_lookup_list helpers
   ========================================================================== *)

Theorem mem_set_insert:
  !x y xs. MEM x (set_insert y xs) <=> x = y \/ MEM x xs
Proof
  rw[set_insert_def] >> metis_tac[]
QED

Theorem set_set_insert:
  !x xs. set (set_insert x xs) = x INSERT set xs
Proof
  rw[EXTENSION, mem_set_insert] >> metis_tac[]
QED

Theorem fmap_lookup_list_update:
  !m k v k'.
    fmap_lookup_list (m |+ (k, v)) k' =
    if k' = k then v else fmap_lookup_list m k'
Proof
  rw[fmap_lookup_list_def, FLOOKUP_UPDATE]
QED

Theorem fmap_lookup_list_fempty:
  !k. fmap_lookup_list FEMPTY k = []
Proof
  simp[fmap_lookup_list_def, FLOOKUP_DEF]
QED

Theorem fmap_lookup_list_not_in_fdom:
  !m k. k ∉ FDOM m ==> fmap_lookup_list m k = []
Proof
  rw[fmap_lookup_list_def, FLOOKUP_DEF]
QED

(* ==========================================================================
   init_succs / init_preds characterization
   ========================================================================== *)

Theorem bb_label_map[simp]:
  MAP basic_block_bb_label bbs = MAP (λbb. bb.bb_label) bbs
Proof
  simp[MAP_EQ_f, FUN_EQ_THM]
QED

Theorem fdom_init_succs:
  !bbs. FDOM (init_succs bbs) = set (MAP (λbb. bb.bb_label) bbs)
Proof
  simp[init_succs_def, foldl_fupdate_keys_fdom]
QED

Theorem fdom_init_preds:
  !bbs. FDOM (init_preds bbs) = set (MAP (λbb. bb.bb_label) bbs)
Proof
  simp[init_preds_def, foldl_fupdate_keys_fdom]
QED

(* ==========================================================================
   build_succs characterization
   ========================================================================== *)

Theorem fdom_build_succs:
  !bbs. FDOM (build_succs bbs) = set (MAP (λbb. bb.bb_label) bbs)
Proof
  simp[build_succs_def, foldl_fupdate_keys_fdom, fdom_init_succs]
QED

Theorem flookup_build_succs:
  !bbs bb.
    ALL_DISTINCT (MAP (λbb. bb.bb_label) bbs) /\ MEM bb bbs ==>
    FLOOKUP (build_succs bbs) bb.bb_label = SOME (bb_succs bb)
Proof
  rw[build_succs_def] >>
  irule foldl_fupdate_keys_flookup >> simp[]
QED

Theorem cfg_succs_of_build_succs:
  !bbs bb.
    ALL_DISTINCT (MAP (λbb. bb.bb_label) bbs) /\ MEM bb bbs ==>
    fmap_lookup_list (build_succs bbs) bb.bb_label = bb_succs bb
Proof
  rw[fmap_lookup_list_def, flookup_build_succs]
QED

Theorem cfg_succs_of_not_in_labels:
  !bbs lbl.
    ~MEM lbl (MAP (λbb. bb.bb_label) bbs) ==>
    fmap_lookup_list (build_succs bbs) lbl = []
Proof
  rw[fmap_lookup_list_not_in_fdom, fdom_build_succs]
QED

(* ==========================================================================
   build_reachable characterization
   ========================================================================== *)

Theorem foldl_build_reach_flookup_other[local]:
  !(vis : string list) labels (acc : string |-> bool) k.
    ~MEM k labels ==>
    FLOOKUP (FOLDL (λm k. m |+ (k, MEM k vis)) acc labels) k = FLOOKUP acc k
Proof
  gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`acc |+ (h, MEM h vis)`, `k`] mp_tac) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem fdom_build_reachable:
  !(labels : string list) vis. FDOM (build_reachable labels vis) = set labels
Proof
  simp[build_reachable_def] >>
  `!vis labels (acc : string |-> bool).
     FDOM (FOLDL (λm k. m |+ (k, MEM k vis)) acc labels) =
     FDOM acc ∪ set labels` suffices_by simp[] >>
  gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem flookup_build_reachable:
  !(labels : string list) vis k.
    ALL_DISTINCT labels /\ MEM k labels ==>
    FLOOKUP (build_reachable labels vis) k = SOME (MEM k vis)
Proof
  simp[build_reachable_def] >>
  `!vis labels (acc : string |-> bool) k.
     ALL_DISTINCT labels /\ MEM k labels ==>
     FLOOKUP (FOLDL (λm k. m |+ (k, MEM k vis)) acc labels) k =
     SOME (MEM k vis)` suffices_by simp[] >>
  gen_tac >> Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  drule foldl_build_reach_flookup_other >>
  simp[FLOOKUP_UPDATE]
QED

Theorem cfg_reachable_build:
  !(labels : string list) vis k s p dpo dpr.
    ALL_DISTINCT labels ==>
    (cfg_reachable_of
      <| cfg_succs := s; cfg_preds := p;
         cfg_reachable := build_reachable labels vis;
         cfg_dfs_post := dpo; cfg_dfs_pre := dpr |> k <=>
     MEM k labels /\ MEM k vis)
Proof
  rw[cfg_reachable_of_def] >>
  Cases_on `MEM k labels`
  >- simp[flookup_build_reachable]
  >- (`k ∉ FDOM (build_reachable labels vis)` by simp[fdom_build_reachable] >>
      simp[FLOOKUP_DEF])
QED

(* ==========================================================================
   cfg_analyze accessor lemmas
   These avoid the need to manually unfold cfg_analyze_def + pairarg_tac
   in every correctness proof.
   ========================================================================== *)

Theorem cfg_analyze_succs:
  !fn. cfg_succs_of (cfg_analyze fn) = fmap_lookup_list (build_succs fn.fn_blocks)
Proof
  gen_tac >> simp[cfg_succs_of_def, cfg_analyze_def, FUN_EQ_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem cfg_analyze_preds:
  !fn. cfg_preds_of (cfg_analyze fn) =
       fmap_lookup_list (build_preds fn.fn_blocks (build_succs fn.fn_blocks))
Proof
  gen_tac >> simp[cfg_preds_of_def, cfg_analyze_def, FUN_EQ_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem cfg_analyze_dfs_post:
  !fn. (cfg_analyze fn).cfg_dfs_post =
    case entry_block fn of
      NONE => []
    | SOME bb => SND (dfs_post_walk (build_succs fn.fn_blocks) [] bb.bb_label)
Proof
  gen_tac >> simp[cfg_analyze_def] >>
  Cases_on `entry_block fn` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem cfg_analyze_dfs_pre:
  !fn. (cfg_analyze fn).cfg_dfs_pre =
    case entry_block fn of
      NONE => []
    | SOME bb => SND (dfs_pre_walk (build_succs fn.fn_blocks) [] bb.bb_label)
Proof
  gen_tac >> simp[cfg_analyze_def] >>
  Cases_on `entry_block fn` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem cfg_analyze_reachable:
  !fn. (cfg_analyze fn).cfg_reachable =
    case entry_block fn of
      NONE => build_reachable (MAP (λbb. bb.bb_label) fn.fn_blocks) []
    | SOME bb => build_reachable (MAP (λbb. bb.bb_label) fn.fn_blocks)
                   (FST (dfs_post_walk (build_succs fn.fn_blocks) [] bb.bb_label))
Proof
  gen_tac >> simp[cfg_analyze_def] >>
  Cases_on `entry_block fn` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

(* ==========================================================================
   build_preds characterization
   ========================================================================== *)

(* Inner FOLDR: after processing succs_list for one block with label lbl,
   MEM x (lookup result k) iff k is in succs_list and x=lbl, or x was already there *)
Theorem foldr_preds_mem[local]:
  !succs_list (lbl:string) (m:(string,string list) fmap) k x.
    MEM x (fmap_lookup_list
      (FOLDR (λsucc m2. m2 |+ (succ, set_insert lbl (fmap_lookup_list m2 succ))) m succs_list)
      k) <=>
    (MEM k succs_list /\ x = lbl) \/ MEM x (fmap_lookup_list m k)
Proof
  Induct >> simp[fmap_lookup_list_update, mem_set_insert] >>
  rpt gen_tac >> Cases_on `k = h` >> gvs[mem_set_insert] >> metis_tac[]
QED

(* Outer FOLDL with generalized accumulator *)
Theorem foldl_preds_mem[local]:
  !(bbs : basic_block list) (succs : (string, string list) fmap)
   (acc : (string, string list) fmap) lbl pred.
    MEM pred
      (fmap_lookup_list
        (FOLDL (λm bb. FOLDR (λsucc m2. m2 |+ (succ, set_insert bb.bb_label (fmap_lookup_list m2 succ)))
                              m (fmap_lookup_list succs bb.bb_label))
               acc bbs)
        lbl) <=>
     (∃bb. MEM bb bbs /\ bb.bb_label = pred /\
           MEM lbl (fmap_lookup_list succs bb.bb_label)) \/
     MEM pred (fmap_lookup_list acc lbl)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`succs`,
    `FOLDR (λsucc m2. m2 |+ (succ, set_insert h.bb_label (fmap_lookup_list m2 succ)))
           acc (fmap_lookup_list succs h.bb_label)`,
    `lbl`, `pred`] mp_tac) >> simp[] >>
  simp[foldr_preds_mem] >> metis_tac[]
QED

(* init_preds maps every key to [] *)
Theorem init_preds_nil[local]:
  !(bbs : basic_block list) (lbl:string).
    fmap_lookup_list (init_preds bbs) lbl = ([] : string list)
Proof
  simp[init_preds_def] >>
  `!(bbs : basic_block list) (acc:(string,string list) fmap).
     (!k. fmap_lookup_list acc k = ([] : string list)) ==>
     !k. fmap_lookup_list (FOLDL (λm bb. m |+ (bb.bb_label, ([] : string list))) acc bbs) k = []`
    suffices_by
      (disch_then (fn th => rpt gen_tac >> irule th) >> simp[fmap_lookup_list_fempty]) >>
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[fmap_lookup_list_update] >> rw[]
QED

Theorem mem_build_preds:
  !bbs succs lbl pred.
    MEM pred (fmap_lookup_list (build_preds bbs succs) lbl) <=>
    ∃bb. MEM bb bbs /\ bb.bb_label = pred /\
         MEM lbl (fmap_lookup_list succs bb.bb_label)
Proof
  rpt strip_tac >> simp[build_preds_def, foldl_preds_mem, init_preds_nil]
QED

(* FOLDR only grows FDOM *)
Theorem foldr_fdom_mono[local]:
  !succs_list (lbl:string) (m:(string,string list) fmap).
    FDOM m ⊆ FDOM (FOLDR (λsucc m2. m2 |+ (succ, set_insert lbl (fmap_lookup_list m2 succ))) m succs_list)
Proof
  Induct >> simp[SUBSET_DEF, FDOM_FUPDATE] >> rpt strip_tac >>
  disj2_tac >> first_x_assum (qspecl_then [`lbl`, `m`] mp_tac) >>
  simp[SUBSET_DEF]
QED

(* FOLDL for build_preds only grows FDOM *)
Theorem foldl_preds_fdom_mono[local]:
  !(bbs : basic_block list) (succs : (string, string list) fmap)
   (acc : (string, string list) fmap).
    FDOM acc ⊆ FDOM (FOLDL (λm bb. FOLDR (λsucc m2. m2 |+ (succ, set_insert bb.bb_label (fmap_lookup_list m2 succ)))
                                          m (fmap_lookup_list succs bb.bb_label))
                            acc bbs)
Proof
  Induct >> simp[SUBSET_DEF] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`succs`,
    `FOLDR (λsucc m2. m2 |+ (succ, set_insert h.bb_label (fmap_lookup_list m2 succ)))
           acc (fmap_lookup_list succs h.bb_label)`] mp_tac) >>
  simp[SUBSET_DEF] >> disch_then irule >>
  mp_tac (Q.SPECL [`fmap_lookup_list succs h.bb_label`, `h.bb_label`, `acc`] foldr_fdom_mono) >>
  simp[SUBSET_DEF]
QED


(* ==========================================================================
   DFS mutual induction combinator
   
   dfs_prove: Prove a mutual property of walk/walk_list by induction.
   Handles the type variable mismatch between conjuncts by proving at
   a single type and using MP on the simplified induction principle.
   
   Arguments: ind P0 P1 (inl_tac, nil_tac, cons_tac)
   Returns: the proved theorem (at generic types from the ind principle)
   ========================================================================== *)

fun dfs_prove ind P0 P1 (inl_tac, nil_tac, cons_tac) = let
  val simp_ind = ind |> Q.SPECL [P0, P1] |> SIMP_RULE (srw_ss()) []
  val (hyps_tm, _) = dest_imp (concl simp_ind)
  val hyps_thm = prove(hyps_tm,
    rpt conj_tac >| [inl_tac, nil_tac, cons_tac])
in MP simp_ind hyps_thm end;

(* ==========================================================================
   DFS walk helpers — visited set monotonicity
   ========================================================================== *)

(* Shared case tactics for visited_mono *)
val mono_inl_tac = fn walk_def =>
  rpt strip_tac >> simp[Once walk_def] >> rw[] >>
  pairarg_tac >> simp[] >>
  irule SUBSET_TRANS >> qexists_tac `set (set_insert lbl visited)` >>
  simp[set_insert_def, SUBSET_DEF] >> res_tac >> gvs[SUBSET_DEF, set_insert_def];
val mono_cons_tac = fn (walk_def, walk_main) =>
  rpt strip_tac >> simp[Once walk_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  irule SUBSET_TRANS >>
  qexists_tac `set (FST (^walk_main succs visited s))` >> simp[] >>
  irule SUBSET_TRANS >>
  Cases_on `^walk_main succs visited s` >> gvs[] >>
  qexists_tac `set q` >> simp[] >>
  first_x_assum (drule_then assume_tac) >> gvs[];

val dfs_post_walk_visited_mono = save_thm(
  "dfs_post_walk_visited_mono",
  dfs_prove dfs_post_walk_ind
    `\succs visited lbl. set visited ⊆ set (FST (dfs_post_walk succs visited lbl))`
    `\succs visited lst. set visited ⊆ set (FST (dfs_post_walk_list succs visited lst))`
    (mono_inl_tac dfs_post_walk_def,
     simp[Once dfs_post_walk_def],
     mono_cons_tac (dfs_post_walk_def, ``dfs_post_walk``)));

val dfs_pre_walk_visited_mono = save_thm(
  "dfs_pre_walk_visited_mono",
  dfs_prove dfs_pre_walk_ind
    `\succs visited lbl. set visited ⊆ set (FST (dfs_pre_walk succs visited lbl))`
    `\succs visited lst. set visited ⊆ set (FST (dfs_pre_walk_list succs visited lst))`
    (mono_inl_tac dfs_pre_walk_def,
     simp[Once dfs_pre_walk_def],
     mono_cons_tac (dfs_pre_walk_def, ``dfs_pre_walk``)));

(* ==========================================================================
   DFS walk helpers — visited = initial ∪ output
   ========================================================================== *)

val eq_inl_tac = fn walk_def =>
  rpt strip_tac >> simp[Once walk_def] >> rw[]
  >- simp[Once walk_def]
  >- (pairarg_tac >> simp[] >> res_tac >> gvs[] >>
      simp[Once walk_def] >> res_tac >> gvs[set_insert_def, EXTENSION] >>
      metis_tac[]);
val eq_cons_tac = fn (walk_def, walk_main) =>
  rpt strip_tac >> simp[Once walk_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `^walk_main succs visited s` >> gvs[] >>
  simp[Once walk_def, UNION_ASSOC];

val dfs_post_walk_visited_eq = save_thm(
  "dfs_post_walk_visited_eq",
  dfs_prove dfs_post_walk_ind
    `\succs visited lbl. set (FST (dfs_post_walk succs visited lbl)) =
       set visited ∪ set (SND (dfs_post_walk succs visited lbl))`
    `\succs visited lst. set (FST (dfs_post_walk_list succs visited lst)) =
       set visited ∪ set (SND (dfs_post_walk_list succs visited lst))`
    (eq_inl_tac dfs_post_walk_def,
     simp[dfs_post_walk_def],
     eq_cons_tac (dfs_post_walk_def, ``dfs_post_walk``)));

val dfs_pre_walk_visited_eq = save_thm(
  "dfs_pre_walk_visited_eq",
  dfs_prove dfs_pre_walk_ind
    `\succs visited lbl. set (FST (dfs_pre_walk succs visited lbl)) =
       set visited ∪ set (SND (dfs_pre_walk succs visited lbl))`
    `\succs visited lst. set (FST (dfs_pre_walk_list succs visited lst)) =
       set visited ∪ set (SND (dfs_pre_walk_list succs visited lst))`
    (eq_inl_tac dfs_pre_walk_def,
     simp[dfs_pre_walk_def],
     eq_cons_tac (dfs_pre_walk_def, ``dfs_pre_walk``)));

(* ==========================================================================
   DFS walk helpers — ALL_DISTINCT output, DISJOINT from visited
   ========================================================================== *)

val disj_inl_tac = fn (walk_def, walk_list_eq) =>
  rpt strip_tac >> simp[Once walk_def] >> rw[] >>
  pairarg_tac >> simp[ALL_DISTINCT_APPEND] >>
  first_x_assum (fn th => mp_tac th >> impl_tac >- simp[]) >>
  strip_tac >> simp[] >> rpt conj_tac >> rpt strip_tac >>
  gvs[DISJOINT_DEF, EXTENSION, set_insert_def] >>
  TRY (CCONTR_TAC >> gvs[] >>
       mp_tac walk_list_eq >> simp[EXTENSION, set_insert_def] >>
       gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  metis_tac[];
val disj_cons_tac = fn (walk_def, visited_eq) =>
  rpt strip_tac >> simp[Once walk_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[ALL_DISTINCT_APPEND] >>
  first_x_assum (qspecl_then [`v'`, `ords'`] mp_tac) >> simp[] >>
  strip_tac >> gvs[] >> rpt conj_tac >> rpt strip_tac >>
  mp_tac (CONJUNCT1 visited_eq |> Q.SPECL [`succs`, `visited`, `s`]) >>
  gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[];

fun dfs_prove_distinct_disj walk_ind walk_def visited_eq P0 P1 =
  dfs_prove walk_ind P0 P1
    (disj_inl_tac (walk_def, CONJUNCT2 visited_eq),
     simp[walk_def],
     disj_cons_tac (walk_def, visited_eq));

val dfs_post_walk_distinct_disj = save_thm(
  "dfs_post_walk_distinct_disj",
  dfs_prove_distinct_disj dfs_post_walk_ind dfs_post_walk_def
    dfs_post_walk_visited_eq
    `\succs visited lbl.
       ALL_DISTINCT (SND (dfs_post_walk succs visited lbl)) /\
       DISJOINT (set (SND (dfs_post_walk succs visited lbl))) (set visited)`
    `\succs visited lst.
       ALL_DISTINCT (SND (dfs_post_walk_list succs visited lst)) /\
       DISJOINT (set (SND (dfs_post_walk_list succs visited lst))) (set visited)`);

Theorem dfs_post_walk_distinct:
  (!succs visited lbl.
     ALL_DISTINCT (SND (dfs_post_walk succs visited lbl))) /\
  (!succs visited lst.
     ALL_DISTINCT (SND (dfs_post_walk_list succs visited lst)))
Proof
  metis_tac[dfs_post_walk_distinct_disj]
QED

val dfs_pre_walk_distinct_disj = save_thm(
  "dfs_pre_walk_distinct_disj",
  dfs_prove_distinct_disj dfs_pre_walk_ind dfs_pre_walk_def
    dfs_pre_walk_visited_eq
    `\succs visited lbl.
       ALL_DISTINCT (SND (dfs_pre_walk succs visited lbl)) /\
       DISJOINT (set (SND (dfs_pre_walk succs visited lbl))) (set visited)`
    `\succs visited lst.
       ALL_DISTINCT (SND (dfs_pre_walk_list succs visited lst)) /\
       DISJOINT (set (SND (dfs_pre_walk_list succs visited lst))) (set visited)`);

Theorem dfs_pre_walk_distinct:
  (!succs visited lbl.
     ALL_DISTINCT (SND (dfs_pre_walk succs visited lbl))) /\
  (!succs visited lst.
     ALL_DISTINCT (SND (dfs_pre_walk_list succs visited lst)))
Proof
  metis_tac[dfs_pre_walk_distinct_disj]
QED

(* Entry label is LAST of postorder output *)
Theorem dfs_post_walk_entry_last:
  !succs visited lbl.
    ~MEM lbl visited ==>
    SND (dfs_post_walk succs visited lbl) <> [] /\
    LAST (SND (dfs_post_walk succs visited lbl)) = lbl
Proof
  rw[Once dfs_post_walk_def] >>
  Cases_on `dfs_post_walk_list succs (set_insert lbl visited)
              (fmap_lookup_list succs lbl)` >>
  gvs[LAST_APPEND_CONS] >>
  simp[Once dfs_post_walk_def] >> simp[LAST_APPEND_CONS]
QED

(* Entry label is HD of preorder output *)
Theorem dfs_pre_walk_entry_hd:
  !succs visited lbl.
    ~MEM lbl visited ==>
    SND (dfs_pre_walk succs visited lbl) <> [] /\
    HD (SND (dfs_pre_walk succs visited lbl)) = lbl
Proof
  rw[Once dfs_pre_walk_def] >>
  Cases_on `dfs_pre_walk_list succs (set_insert lbl visited)
              (fmap_lookup_list succs lbl)` >>
  gvs[] >>
  simp[Once dfs_pre_walk_def]
QED

(* ==========================================================================
   DFS walk helpers — soundness (output ⊆ RTC-reachable)
   ========================================================================== *)

(* sound_cons_tac: for proving P1 (CONS case) in soundness.
   After pairarg_tac×2, we have ords' from walk on s and ords'' from walk_list on ss.
   For MEM target ords': use P0 IH. For MEM target ords'': use P1 IH. *)
val sound_cons_tac = fn (walk_def, walk_main, walk_list) =>
  rpt strip_tac >>
  qpat_x_assum `MEM _ (SND (_ _ _ (_::_)))` mp_tac >>
  simp[Once walk_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[MEM_APPEND] >>
  strip_tac
  >- (qexists_tac `s` >> simp[] >>
      `MEM target (SND (^walk_main succs visited s))` by
        (Cases_on `^walk_main succs visited s` >> gvs[]) >>
      res_tac)
  >- (first_x_assum (qspecl_then [`v'`, `ords'`] mp_tac) >> simp[] >>
      `MEM target (SND (^walk_list succs v' ss))` by
        (Cases_on `^walk_list succs v' ss` >> gvs[]) >>
      disch_then drule >> strip_tac >>
      qexists_tac `s'` >> simp[]);

val dfs_post_walk_sound = save_thm(
  "dfs_post_walk_sound",
  dfs_prove dfs_post_walk_ind
    `\succs visited lbl.
       !target. MEM target (SND (dfs_post_walk succs visited lbl)) ==>
                RTC (λa b. MEM b (fmap_lookup_list succs a)) lbl target`
    `\succs visited lst.
       !target. MEM target (SND (dfs_post_walk_list succs visited lst)) ==>
                ?s. MEM s lst /\ RTC (λa b. MEM b (fmap_lookup_list succs a)) s target`
    ((* INL: output = walk_list_output ++ [lbl] *)
     rpt strip_tac >>
     qpat_x_assum `MEM _ (SND (dfs_post_walk _ _ _))` mp_tac >>
     simp[Once dfs_post_walk_def] >> rw[] >>
     pairarg_tac >> gvs[MEM_APPEND] >>
     res_tac >> irule (CONJUNCT2 (SPEC_ALL RTC_RULES)) >>
     qexists_tac `s` >> simp[],
     (* NIL *)
     simp[Once dfs_post_walk_def],
     (* CONS *)
     sound_cons_tac (dfs_post_walk_def, ``dfs_post_walk``, ``dfs_post_walk_list``)));

Theorem dfs_post_walk_sound_thm:
  !succs visited lbl target.
    MEM target (SND (dfs_post_walk succs visited lbl)) ==>
    RTC (λa b. MEM b (fmap_lookup_list succs a)) lbl target
Proof
  metis_tac[dfs_post_walk_sound]
QED

val dfs_pre_walk_sound = save_thm(
  "dfs_pre_walk_sound",
  dfs_prove dfs_pre_walk_ind
    `\succs visited lbl.
       !target. MEM target (SND (dfs_pre_walk succs visited lbl)) ==>
                RTC (λa b. MEM b (fmap_lookup_list succs a)) lbl target`
    `\succs visited lst.
       !target. MEM target (SND (dfs_pre_walk_list succs visited lst)) ==>
                ?s. MEM s lst /\ RTC (λa b. MEM b (fmap_lookup_list succs a)) s target`
    ((* INL: output = lbl :: walk_list_output *)
     rpt strip_tac >>
     qpat_x_assum `MEM _ (SND (dfs_pre_walk _ _ _))` mp_tac >>
     simp[Once dfs_pre_walk_def] >> rw[] >>
     pairarg_tac >> gvs[] >>
     res_tac >> irule (CONJUNCT2 (SPEC_ALL RTC_RULES)) >>
     qexists_tac `s` >> simp[],
     (* NIL *)
     simp[Once dfs_pre_walk_def],
     sound_cons_tac (dfs_pre_walk_def, ``dfs_pre_walk``, ``dfs_pre_walk_list``)));

Theorem dfs_pre_walk_sound_thm:
  !succs visited lbl target.
    MEM target (SND (dfs_pre_walk succs visited lbl)) ==>
    RTC (λa b. MEM b (fmap_lookup_list succs a)) lbl target
Proof
  metis_tac[dfs_pre_walk_sound]
QED

(* ==========================================================================
   DFS walk helpers — mem_fst: every input list element ends up in FST
   ========================================================================== *)

(* dfs_post_walk_mem_fst: MEM lbl (FST(walk vis lbl)) ∧ MEM s lst ⇒ MEM s (FST(walk_list vis lst)) *)
val dfs_post_walk_mem_fst = let
  val simp_ind = dfs_post_walk_ind
    |> Q.SPECL [`\succs visited lbl. MEM lbl (FST (dfs_post_walk succs visited lbl))`,
                `\succs visited lst. !s. MEM s lst ==> MEM s (FST (dfs_post_walk_list succs visited lst))`]
    |> SIMP_RULE (srw_ss()) []
  val (hyps_tm, _) = dest_imp (concl simp_ind)
  val hyps_thm = prove(hyps_tm,
    conj_tac >- (
      (* INL: MEM lbl (FST(walk vis lbl)) *)
      rpt strip_tac >> simp[Once dfs_post_walk_def] >> rw[] >>
      pairarg_tac >> simp[] >>
      `set (set_insert lbl visited) ⊆ set (FST (dfs_post_walk_list succs (set_insert lbl visited) (fmap_lookup_list succs lbl)))` by
        simp[dfs_post_walk_visited_mono] >>
      `MEM lbl (set_insert lbl visited)` by simp[mem_set_insert] >>
      fs[SUBSET_DEF] >> res_tac >> gvs[])
    >- (
      (* CONS: MEM s (h::t) ⇒ MEM s (FST(walk_list vis (h::t))) *)
      rpt strip_tac >> simp[Once dfs_post_walk_def] >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> gvs[] >>
      `set v' ⊆ set v''` by
        (mp_tac (CONJUNCT2 dfs_post_walk_visited_mono |> Q.SPECL [`succs`, `v'`, `ss`]) >> gvs[]) >>
      fs[SUBSET_DEF]))
in save_thm("dfs_post_walk_mem_fst", MP simp_ind hyps_thm) end;

val dfs_pre_walk_mem_fst = let
  val simp_ind = dfs_pre_walk_ind
    |> Q.SPECL [`\succs visited lbl. MEM lbl (FST (dfs_pre_walk succs visited lbl))`,
                `\succs visited lst. !s. MEM s lst ==> MEM s (FST (dfs_pre_walk_list succs visited lst))`]
    |> SIMP_RULE (srw_ss()) []
  val (hyps_tm, _) = dest_imp (concl simp_ind)
  val hyps_thm = prove(hyps_tm,
    conj_tac >- (
      rpt strip_tac >> simp[Once dfs_pre_walk_def] >> rw[] >>
      pairarg_tac >> simp[] >>
      `set (set_insert lbl visited) ⊆ set (FST (dfs_pre_walk_list succs (set_insert lbl visited) (fmap_lookup_list succs lbl)))` by
        simp[dfs_pre_walk_visited_mono] >>
      `MEM lbl (set_insert lbl visited)` by simp[mem_set_insert] >>
      fs[SUBSET_DEF] >> res_tac >> gvs[])
    >- (
      rpt strip_tac >> simp[Once dfs_pre_walk_def] >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> gvs[] >>
      `set v' ⊆ set v''` by
        (mp_tac (CONJUNCT2 dfs_pre_walk_visited_mono |> Q.SPECL [`succs`, `v'`, `ss`]) >> gvs[]) >>
      fs[SUBSET_DEF]))
in save_thm("dfs_pre_walk_mem_fst", MP simp_ind hyps_thm) end;

(* ==========================================================================
   DFS walk helpers — closure: successors of output nodes are in visited set
   ========================================================================== *)

(* If x is in the DFS output, all successors of x are in FST (visited set).
   This is the key DFS invariant: when x was processed, its successors were
   passed to walk_list, so they end up in FST. *)

(* Shared CONS case tactic for closure (identical for post/pre)
   After Cases_on + gvs, IHs become: ∀x'. MEM x' r ⇒ ... ⇒ MEM t' q
   and ∀x'. MEM x' r' ⇒ ... ⇒ MEM t' q'. Then res_tac + mono. *)
val closure_cons_tac = fn (walk_def, walk_mono, walk_main, walk_list) =>
  rpt strip_tac >>
  qpat_x_assum `MEM x (SND (_ _ _ (_::_)))` mp_tac >>
  simp[Once walk_def] >>
  Cases_on `^walk_main succs visited s` >>
  Cases_on `^walk_list succs q ss` >>
  gvs[MEM_APPEND] >> strip_tac
  >- ((* x from walk on s: IH gives MEM t q, mono lifts to q' *)
      `MEM t q` by res_tac >>
      `set q ⊆ set q'` by
        (mp_tac (CONJUNCT2 walk_mono |>
           Q.SPECL [`succs`, `q`, `ss`]) >> gvs[]) >>
      `MEM t q'` by fs[SUBSET_DEF] >>
      simp[Once walk_def] >> gvs[])
  >- ((* x from walk_list on ss: IH directly gives MEM t q' *)
      `MEM t q'` by res_tac >>
      simp[Once walk_def] >> gvs[]);

val dfs_post_walk_closure = save_thm(
  "dfs_post_walk_closure",
  dfs_prove dfs_post_walk_ind
    `\succs visited lbl.
       !x. MEM x (SND (dfs_post_walk succs visited lbl)) ==>
           !t. MEM t (fmap_lookup_list succs x) ==>
               MEM t (FST (dfs_post_walk succs visited lbl))`
    `\succs visited lst.
       !x. MEM x (SND (dfs_post_walk_list succs visited lst)) ==>
           !t. MEM t (fmap_lookup_list succs x) ==>
               MEM t (FST (dfs_post_walk_list succs visited lst))`
    ((* INL: output = walk_list_output ++ [lbl] *)
     rpt strip_tac >> simp[Once dfs_post_walk_def] >>
     IF_CASES_TAC >> gvs[]
     >- (qpat_x_assum `MEM x (SND _)` mp_tac >> simp[Once dfs_post_walk_def])
     >- (pairarg_tac >> simp[] >>
         qpat_x_assum `MEM x (SND (dfs_post_walk _ _ _))` mp_tac >>
         simp[Once dfs_post_walk_def] >>
         `dfs_post_walk_list succs (set_insert lbl visited)
            (fmap_lookup_list succs lbl) = (vis2,orders)` by gvs[] >>
         simp[MEM_APPEND] >> strip_tac >> gvs[]
         >- (first_x_assum (fn th => mp_tac (REWRITE_RULE [] (Q.SPEC `x` th))) >> gvs[])
         >- (`MEM t (FST (dfs_post_walk_list succs (set_insert lbl visited)
                (fmap_lookup_list succs lbl)))` suffices_by gvs[] >>
             irule (CONJUNCT2 dfs_post_walk_mem_fst |> SIMP_RULE (srw_ss()) []) >> simp[])),
     (* NIL *)
     simp[Once dfs_post_walk_def],
     (* CONS *)
     closure_cons_tac (dfs_post_walk_def, dfs_post_walk_visited_mono,
                       ``dfs_post_walk``, ``dfs_post_walk_list``)));

val dfs_pre_walk_closure = save_thm(
  "dfs_pre_walk_closure",
  dfs_prove dfs_pre_walk_ind
    `\succs visited lbl.
       !x. MEM x (SND (dfs_pre_walk succs visited lbl)) ==>
           !t. MEM t (fmap_lookup_list succs x) ==>
               MEM t (FST (dfs_pre_walk succs visited lbl))`
    `\succs visited lst.
       !x. MEM x (SND (dfs_pre_walk_list succs visited lst)) ==>
           !t. MEM t (fmap_lookup_list succs x) ==>
               MEM t (FST (dfs_pre_walk_list succs visited lst))`
    ((* INL: output = lbl :: walk_list_output *)
     rpt strip_tac >> simp[Once dfs_pre_walk_def] >>
     IF_CASES_TAC >> gvs[]
     >- (qpat_x_assum `MEM x (SND _)` mp_tac >> simp[Once dfs_pre_walk_def])
     >- (pairarg_tac >> simp[] >>
         qpat_x_assum `MEM x (SND (dfs_pre_walk _ _ _))` mp_tac >>
         simp[Once dfs_pre_walk_def] >>
         `dfs_pre_walk_list succs (set_insert lbl visited)
            (fmap_lookup_list succs lbl) = (vis2,orders)` by gvs[] >>
         simp[] >> strip_tac >> gvs[]
         >- (`MEM t (FST (dfs_pre_walk_list succs (set_insert lbl visited)
                (fmap_lookup_list succs lbl)))` suffices_by gvs[] >>
             irule (CONJUNCT2 dfs_pre_walk_mem_fst |> SIMP_RULE (srw_ss()) []) >> simp[])
         >- (first_x_assum (fn th => mp_tac (REWRITE_RULE [] (Q.SPEC `x` th))) >> gvs[])),
     (* NIL *)
     simp[Once dfs_pre_walk_def],
     (* CONS *)
     closure_cons_tac (dfs_pre_walk_def, dfs_pre_walk_visited_mono,
                       ``dfs_pre_walk``, ``dfs_pre_walk_list``)))

(* ==========================================================================
   DFS completeness: every reachable node is in DFS output (vis=[])
   ========================================================================== *)

(* Key insight: by RTC right-induction (RTC_CASES2):
   - Base: target = lbl → lbl ∈ SND(walk [] lbl) by entry_last/entry_hd
   - Step: RTC lbl mid ∧ step mid target. IH: mid ∈ SND(walk [] lbl).
     By closure: target ∈ FST(walk [] lbl).
     By visited_eq with vis=[]: FST = {} ∪ SND = SND.
     So target ∈ SND(walk [] lbl). *)

val post_entry_s = INST_TYPE [alpha |-> ``:string``] dfs_post_walk_entry_last;
val post_closure_s = CONJUNCT1 (INST_TYPE [alpha |-> ``:string``] dfs_post_walk_closure);
val post_eq_s = CONJUNCT1 (INST_TYPE [alpha |-> ``:string``] dfs_post_walk_visited_eq);

val dfs_post_walk_complete = save_thm("dfs_post_walk_complete", let
  val goal = Term
    `!(succs :string |-> string list) lbl target.
       RTC (\a b. MEM b (fmap_lookup_list succs a)) lbl target ==>
       MEM target (SND (dfs_post_walk succs [] lbl))`
in prove(goal,
  gen_tac >> ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 >> conj_tac
  >- (rw[] >> mp_tac (Q.SPECL [`succs`,`[]`,`lbl`] post_entry_s) >>
      simp[] >> strip_tac >> imp_res_tac MEM_LAST_NOT_NIL >> gvs[])
  >- (rpt strip_tac >> imp_res_tac post_closure_s >>
      mp_tac (Q.SPECL [`succs`,`[]`,`lbl`] post_eq_s) >>
      simp[EXTENSION] >> metis_tac[]))
end);

val pre_entry_s = INST_TYPE [alpha |-> ``:string``] dfs_pre_walk_entry_hd;
val pre_closure_s = CONJUNCT1 (INST_TYPE [alpha |-> ``:string``] dfs_pre_walk_closure);
val pre_eq_s = CONJUNCT1 (INST_TYPE [alpha |-> ``:string``] dfs_pre_walk_visited_eq);

val dfs_pre_walk_complete = save_thm("dfs_pre_walk_complete", let
  val goal = Term
    `!(succs :string |-> string list) lbl target.
       RTC (\a b. MEM b (fmap_lookup_list succs a)) lbl target ==>
       MEM target (SND (dfs_pre_walk succs [] lbl))`
in prove(goal,
  gen_tac >> ho_match_mp_tac RTC_STRONG_INDUCT_RIGHT1 >> conj_tac
  >- (rw[] >> mp_tac (Q.SPECL [`succs`,`[]`,`lbl`] pre_entry_s) >>
      simp[] >> strip_tac >> imp_res_tac HEAD_MEM >> gvs[])
  >- (rpt strip_tac >> imp_res_tac pre_closure_s >>
      mp_tac (Q.SPECL [`succs`,`[]`,`lbl`] pre_eq_s) >>
      simp[EXTENSION] >> metis_tac[]))
end);



(* FST equality: both walks produce the same visited set *)
val dfs_walks_fst_eq = save_thm("dfs_walks_fst_eq",
  dfs_prove dfs_post_walk_ind
    `\succs visited lbl. FST(dfs_post_walk succs visited lbl) = FST(dfs_pre_walk succs visited lbl)`
    `\succs visited lbls. FST(dfs_post_walk_list succs visited lbls) = FST(dfs_pre_walk_list succs visited lbls)`
    ((* inl *) rw[Once dfs_post_walk_def, Once dfs_pre_walk_def] >>
               Cases_on `MEM lbl visited` >> gvs[] >>
               Cases_on `dfs_post_walk_list succs (set_insert lbl visited) (fmap_lookup_list succs lbl)` >>
               Cases_on `dfs_pre_walk_list succs (set_insert lbl visited) (fmap_lookup_list succs lbl)` >>
               gvs[],
     (* nil *) simp[Once dfs_post_walk_def, Once dfs_pre_walk_def],
     (* cons *) rpt strip_tac >>
                simp[Once dfs_post_walk_def, Once dfs_pre_walk_def] >>
                Cases_on `dfs_post_walk succs visited s` >>
                Cases_on `dfs_pre_walk succs visited s` >> gvs[] >>
                Cases_on `dfs_post_walk_list succs q ss` >>
                Cases_on `dfs_pre_walk_list succs q ss` >> gvs[]));

(* Same output sets (not same order) — follows from FST equality + visited_eq + disjointness *)
Theorem dfs_walks_same_output_set:
  !succs visited lbl.
    set (SND (dfs_post_walk succs visited lbl)) =
    set (SND (dfs_pre_walk succs visited lbl))
Proof
  rpt gen_tac >> simp[EXTENSION] >> gen_tac >>
  mp_tac (CONJUNCT1 dfs_walks_fst_eq |> Q.SPECL [`succs`,`visited`,`lbl`]) >>
  mp_tac (CONJUNCT1 dfs_post_walk_visited_eq |> Q.SPECL [`succs`,`visited`,`lbl`]) >>
  mp_tac (CONJUNCT1 dfs_pre_walk_visited_eq |> Q.SPECL [`succs`,`visited`,`lbl`]) >>
  mp_tac (CONJUNCT1 dfs_post_walk_distinct_disj |> Q.SPECL [`succs`,`visited`,`lbl`]) >>
  mp_tac (CONJUNCT1 dfs_pre_walk_distinct_disj |> Q.SPECL [`succs`,`visited`,`lbl`]) >>
  simp[EXTENSION, DISJOINT_DEF, INTER_DEF, EMPTY_DEF] >>
  rpt strip_tac >> EQ_TAC >> strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
  gvs[] >> metis_tac[]
QED

(* ==========================================================================
   INDEX_OF helpers for ordering proofs
   ========================================================================== *)

Triviality index_of_last_max:
  !l (a:'a) b i j.
    ALL_DISTINCT l /\ l <> [] /\ LAST l = a /\
    INDEX_OF a l = SOME j /\ INDEX_OF b l = SOME i /\ b <> a ==>
    i < j
Proof
  rpt strip_tac >>
  `a = EL (PRE (LENGTH l)) l` by metis_tac[LAST_EL] >>
  `PRE (LENGTH l) < LENGTH l` by (Cases_on `l` >> gvs[]) >>
  `j = PRE (LENGTH l)` by
    (`INDEX_OF (EL (PRE (LENGTH l)) l) l = SOME (PRE (LENGTH l))` by
       metis_tac[ALL_DISTINCT_INDEX_OF_EL] >> gvs[]) >>
  gvs[INDEX_OF_eq_SOME] >>
  `i <> PRE (LENGTH l)` by (CCONTR_TAC >> gvs[]) >>
  DECIDE_TAC
QED

Triviality index_of_hd_min:
  !l (a:'a) b i j.
    ALL_DISTINCT l /\ l <> [] /\ HD l = a /\
    INDEX_OF a l = SOME j /\ INDEX_OF b l = SOME i /\ b <> a ==>
    j < i
Proof
  rpt strip_tac >>
  `a = EL 0 l` by (Cases_on `l` >> gvs[]) >>
  `0 < LENGTH l` by (Cases_on `l` >> gvs[]) >>
  `j = 0` by
    (`INDEX_OF (EL 0 l) l = SOME 0` by metis_tac[ALL_DISTINCT_INDEX_OF_EL] >>
     gvs[]) >>
  gvs[INDEX_OF_eq_SOME] >>
  `i <> 0` by (CCONTR_TAC >> gvs[]) >>
  DECIDE_TAC
QED

Triviality index_of_append_left:
  !x (l1:'a list) l2.
    ALL_DISTINCT (l1 ++ l2) /\ MEM x l1 ==>
    INDEX_OF x (l1 ++ l2) = INDEX_OF x l1
Proof
  rpt strip_tac >>
  `ALL_DISTINCT l1` by metis_tac[ALL_DISTINCT_APPEND] >>
  `?n. n < LENGTH l1 /\ EL n l1 = x` by metis_tac[MEM_EL] >>
  `INDEX_OF x l1 = SOME n` by metis_tac[ALL_DISTINCT_INDEX_OF_EL] >>
  `EL n (l1 ++ l2) = x` by simp[EL_APPEND1] >>
  `n < LENGTH (l1 ++ l2)` by simp[] >>
  `INDEX_OF (EL n (l1 ++ l2)) (l1 ++ l2) = SOME n` by
    metis_tac[ALL_DISTINCT_INDEX_OF_EL] >>
  gvs[]
QED

Triviality index_of_append_right:
  !x (l1:'a list) l2 i.
    ALL_DISTINCT (l1 ++ l2) /\ INDEX_OF x l2 = SOME i ==>
    INDEX_OF x (l1 ++ l2) = SOME (i + LENGTH l1)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_APPEND] >>
  gvs[INDEX_OF_eq_SOME] >>
  `EL (i + LENGTH l1) (l1 ++ l2) = EL i l2` by simp[EL_APPEND2] >>
  simp[] >> rpt strip_tac >>
  Cases_on `j < LENGTH l1`
  >- (`EL j (l1 ++ l2) = EL j l1` by metis_tac[EL_APPEND1] >>
      `EL j l1 = EL i l2` by metis_tac[] >>
      `MEM (EL j l1) l1` by (simp[MEM_EL] >> qexists_tac `j` >> simp[]) >>
      `MEM (EL i l2) l2` by (simp[MEM_EL] >> qexists_tac `i` >> simp[]) >>
      gvs[ALL_DISTINCT_APPEND] >> metis_tac[])
  >- (`EL j (l1 ++ l2) = EL (j - LENGTH l1) l2` by (irule EL_APPEND2 >> simp[]) >>
      `EL (j - LENGTH l1) l2 = EL i l2` by metis_tac[] >>
      `j - LENGTH l1 < i` by simp[] >>
      metis_tac[])
QED

(* ==========================================================================
   General DFS ordering (subsumes specialized dfs_post/pre_walk_order)

   For ANY walk starting point, non-back-edge successors appear before
   their predecessors in postorder (and after in preorder).
   ========================================================================== *)

(* String-specialized INDEX_OF helpers — avoid polymorphic metis overhead *)
Triviality index_of_append_left_str:
  !x (l1:string list) l2.
    ALL_DISTINCT (l1 ++ l2) /\ MEM x l1 ==>
    INDEX_OF x (l1 ++ l2) = INDEX_OF x l1
Proof
  metis_tac[index_of_append_left]
QED

Triviality index_of_append_right_str:
  !x (l1:string list) l2 i.
    ALL_DISTINCT (l1 ++ l2) /\ INDEX_OF x l2 = SOME i ==>
    INDEX_OF x (l1 ++ l2) = SOME (i + LENGTH l1)
Proof
  metis_tac[index_of_append_right]
QED

(* ==========================================================================
   General DFS postorder ordering

   For ANY walk, if a→b is a non-back-edge (¬RTC b a) and both
   a,b appear in the walk output, then b appears before a in postorder.
   ========================================================================== *)

Theorem dfs_post_walk_general_order:
  (!succs (visited:string list) lbl a b i j.
    MEM a (SND (dfs_post_walk succs visited lbl)) /\
    MEM b (fmap_lookup_list succs a) /\
    ~RTC (\a b. MEM b (fmap_lookup_list succs a)) b a /\
    INDEX_OF b (SND (dfs_post_walk succs visited lbl)) = SOME i /\
    INDEX_OF a (SND (dfs_post_walk succs visited lbl)) = SOME j ==>
    i < j) /\
  (!succs (visited:string list) lst a b i j.
    MEM a (SND (dfs_post_walk_list succs visited lst)) /\
    MEM b (fmap_lookup_list succs a) /\
    ~RTC (\a b. MEM b (fmap_lookup_list succs a)) b a /\
    INDEX_OF b (SND (dfs_post_walk_list succs visited lst)) = SOME i /\
    INDEX_OF a (SND (dfs_post_walk_list succs visited lst)) = SOME j ==>
    i < j)
Proof
  ho_match_mp_tac dfs_post_walk_ind >> rpt conj_tac
  THENL [
    (* ---- INL case: dfs_post_walk ---- *)
    rpt strip_tac >>
    qpat_x_assum `MEM a (SND (dfs_post_walk _ _ _))` mp_tac >>
    qpat_x_assum `INDEX_OF b (SND (dfs_post_walk _ _ _)) = _` mp_tac >>
    qpat_x_assum `INDEX_OF a (SND (dfs_post_walk _ _ _)) = _` mp_tac >>
    PURE_ONCE_REWRITE_TAC [dfs_post_walk_def] >>
    simp[LET_THM] >> IF_CASES_TAC >> simp[] >>
    Cases_on `dfs_post_walk_list succs (set_insert lbl visited)
                (fmap_lookup_list succs lbl)` >>
    simp[] >> rpt strip_tac >> gvs[MEM_APPEND]
    THENL [
      (* MEM a r *)
      `ALL_DISTINCT r /\ DISJOINT (set r) (set (set_insert lbl visited))` by
        (`SND (dfs_post_walk_list succs (set_insert lbl visited)
              (fmap_lookup_list succs lbl)) = r` by gvs[] >>
         metis_tac[dfs_post_walk_distinct_disj]) >>
      `~MEM lbl r` by
        (gvs[DISJOINT_DEF, EXTENSION, mem_set_insert] >> metis_tac[]) >>
      `ALL_DISTINCT (r ++ [lbl])` by simp[ALL_DISTINCT_APPEND] >>
      Cases_on `MEM b r`
      THENL [
        `INDEX_OF b r = INDEX_OF b (r ++ [lbl])` by
          metis_tac[index_of_append_left_str] >>
        `INDEX_OF a r = INDEX_OF a (r ++ [lbl])` by
          metis_tac[index_of_append_left_str] >>
        gvs[] >>
        first_x_assum (qspecl_then [`a`,`b`,`i`,`j`] mp_tac) >> simp[],
        Cases_on `b = lbl`
        THENL [
          gvs[] >>
          `MEM a (SND (dfs_post_walk_list succs (set_insert b visited)
                (fmap_lookup_list succs b)))` by gvs[] >>
          drule (CONJUNCT2 dfs_post_walk_sound) >> strip_tac >>
          `RTC (\a b. MEM b (fmap_lookup_list succs a)) b a` by
            (irule (CONJUNCT2 (SPEC_ALL RTC_RULES)) >>
             qexists_tac `s` >> simp[]) >>
          metis_tac[],
          `INDEX_OF b (r ++ [lbl]) = NONE` by
            gvs[INDEX_OF_eq_NONE, MEM_APPEND] >>
          gvs[]
        ]
      ],
      (* a = lbl *)
      `b <> a` by (CCONTR_TAC >> fs[]) >>
      match_mp_tac (INST_TYPE [alpha |-> ``:string``] index_of_last_max) >>
      qexistsl_tac [`r ++ [a]`, `a`, `b`] >>
      simp[LAST_APPEND_CONS, LAST_DEF] >>
      `ALL_DISTINCT r /\ DISJOINT (set r) (set (set_insert a visited))` by
        (`SND (dfs_post_walk_list succs (set_insert a visited)
              (fmap_lookup_list succs a)) = r` by gvs[] >>
         metis_tac[dfs_post_walk_distinct_disj]) >>
      `~MEM a r` by
        (gvs[DISJOINT_DEF, EXTENSION, mem_set_insert] >> metis_tac[]) >>
      simp[ALL_DISTINCT_APPEND]
    ],
    (* ---- NIL case ---- *)
    simp[Once dfs_post_walk_def],
    (* ---- CONS case: dfs_post_walk_list (s::ss) ---- *)
    rpt strip_tac >>
    qpat_x_assum `MEM a (SND (dfs_post_walk_list _ _ (_::_)))` mp_tac >>
    qpat_x_assum `INDEX_OF b (SND (dfs_post_walk_list _ _ (_::_))) = _` mp_tac >>
    qpat_x_assum `INDEX_OF a (SND (dfs_post_walk_list _ _ (_::_))) = _` mp_tac >>
    PURE_ONCE_REWRITE_TAC [dfs_post_walk_def] >> simp[LET_THM] >>
    Cases_on `dfs_post_walk succs visited lbl` >>
    Cases_on `dfs_post_walk_list succs q lst` >>
    simp[] >> rpt strip_tac
    THENL [
      (* MEM a r *)
      `ALL_DISTINCT (r ++ r')` by
        (`SND (dfs_post_walk succs visited lbl) = r` by gvs[] >>
         `SND (dfs_post_walk_list succs q lst) = r'` by gvs[] >>
         `ALL_DISTINCT r /\ DISJOINT (set r) (set visited)` by
           metis_tac[dfs_post_walk_distinct_disj] >>
         `ALL_DISTINCT r' /\ DISJOINT (set r') (set q)` by
           metis_tac[dfs_post_walk_distinct_disj] >>
         `set (FST (dfs_post_walk succs visited lbl)) =
          set visited UNION set (SND (dfs_post_walk succs visited lbl))` by
           metis_tac[dfs_post_walk_visited_eq] >>
         gvs[ALL_DISTINCT_APPEND, DISJOINT_DEF, EXTENSION] >>
         metis_tac[]) >>
      Cases_on `MEM b r`
      THENL [
        `INDEX_OF a r = INDEX_OF a (r ++ r')` by
          metis_tac[index_of_append_left_str] >>
        `INDEX_OF b r = INDEX_OF b (r ++ r')` by
          metis_tac[index_of_append_left_str] >>
        gvs[] >>
        first_x_assum (qspecl_then [`a`,`b`,`i`,`j`] mp_tac) >> simp[],
        `MEM a (SND (dfs_post_walk succs visited lbl))` by gvs[] >>
        `MEM b (FST (dfs_post_walk succs visited lbl))` by
          metis_tac[CONJUNCT1 dfs_post_walk_closure] >>
        `MEM b q` by gvs[] >>
        `SND (dfs_post_walk_list succs q lst) = r'` by gvs[] >>
        `DISJOINT (set r') (set q)` by
          metis_tac[dfs_post_walk_distinct_disj] >>
        `~MEM b r'` by (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
        `INDEX_OF b (r ++ r') = NONE` by
          simp[INDEX_OF_eq_NONE, MEM_APPEND] >>
        gvs[]
      ],
      (* MEM a r' *)
      `ALL_DISTINCT (r ++ r')` by
        (`SND (dfs_post_walk succs visited lbl) = r` by gvs[] >>
         `SND (dfs_post_walk_list succs q lst) = r'` by gvs[] >>
         `ALL_DISTINCT r /\ DISJOINT (set r) (set visited)` by
           metis_tac[dfs_post_walk_distinct_disj] >>
         `ALL_DISTINCT r' /\ DISJOINT (set r') (set q)` by
           metis_tac[dfs_post_walk_distinct_disj] >>
         `set (FST (dfs_post_walk succs visited lbl)) =
          set visited UNION set (SND (dfs_post_walk succs visited lbl))` by
           metis_tac[dfs_post_walk_visited_eq] >>
         gvs[ALL_DISTINCT_APPEND, DISJOINT_DEF, EXTENSION] >>
         metis_tac[]) >>
      Cases_on `MEM b r`
      THENL [
        `INDEX_OF b (r ++ r') = INDEX_OF b r` by
          metis_tac[index_of_append_left_str] >>
        `~MEM a r` by metis_tac[ALL_DISTINCT_APPEND] >>
        `?ja. INDEX_OF a r' = SOME ja` by
          (Cases_on `INDEX_OF a r'` >> gvs[INDEX_OF_eq_NONE]) >>
        `INDEX_OF a (r ++ r') = SOME (ja + LENGTH r)` by
          metis_tac[index_of_append_right_str] >>
        `?ib. INDEX_OF b r = SOME ib` by
          (Cases_on `INDEX_OF b r` >> gvs[INDEX_OF_eq_NONE]) >>
        gvs[] >> `i < LENGTH r` by fs[INDEX_OF_eq_SOME] >> simp[],
        `MEM b r'` by
          (`~(INDEX_OF b (r ++ r') = NONE)` by simp[] >>
           `MEM b (r ++ r')` by fs[INDEX_OF_eq_NONE] >>
           gvs[MEM_APPEND]) >>
        `~MEM a r` by metis_tac[ALL_DISTINCT_APPEND] >>
        `?ia. INDEX_OF a r' = SOME ia` by
          (Cases_on `INDEX_OF a r'` >> gvs[INDEX_OF_eq_NONE]) >>
        `INDEX_OF a (r ++ r') = SOME (ia + LENGTH r)` by
          metis_tac[index_of_append_right_str] >>
        `?ib. INDEX_OF b r' = SOME ib` by
          (Cases_on `INDEX_OF b r'` >> gvs[INDEX_OF_eq_NONE]) >>
        `INDEX_OF b (r ++ r') = SOME (ib + LENGTH r)` by
          metis_tac[index_of_append_right_str] >>
        gvs[] >>
        qpat_x_assum `!a' b' i' j'. MEM a' r' /\ _ ==> _`
          (qspecl_then [`a`,`b`,`ib`,`ia`] mp_tac) >>
        simp[]
      ]
    ]
  ]
QED

(* NOTE: dfs_pre_walk_general_order is FALSE — see counterexample:
   Graph: "entry" -> ["s","a"], "s" -> ["b"], "b" -> [], "a" -> ["b"]
   Pre walk output: ["entry","s","b","a"]
   a="a" (index 3), b="b" (index 2), a->b edge, ¬RTC b a.
   Want INDEX_OF "a" < INDEX_OF "b" = 3 < 2? FALSE.
   Cross edges in DFS can violate preorder ordering. *)

(* ==========================================================================
   RTC closure: reachable nodes stay within fn_labels under succs_closed
   ========================================================================== *)

Theorem rtc_build_succs_closed:
  !bbs start target.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    (!bb succ. MEM bb bbs /\ MEM succ (bb_succs bb) ==>
               MEM succ (MAP (\bb. bb.bb_label) bbs)) /\
    MEM start (MAP (\bb. bb.bb_label) bbs) /\
    RTC (\a b. MEM b (fmap_lookup_list (build_succs bbs) a)) start target ==>
    MEM target (MAP (\bb. bb.bb_label) bbs)
Proof
  rpt gen_tac >> strip_tac >>
  `!start target.
     (\a b. MEM b (fmap_lookup_list (build_succs bbs) a))^* start target ==>
     MEM start (MAP (\bb. bb.bb_label) bbs) ==>
     MEM target (MAP (\bb. bb.bb_label) bbs)` suffices_by metis_tac[] >>
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac >> gvs[] >>
  `MEM start'' (MAP (\bb. bb.bb_label) bbs)` suffices_by simp[] >>
  gvs[MEM_MAP] >>
  `fmap_lookup_list (build_succs bbs) bb'.bb_label = bb_succs bb'` by
    metis_tac[cfg_succs_of_build_succs] >>
  gvs[] >> metis_tac[]
QED


