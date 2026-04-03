(*
 * Memory Alias Analysis — Proofs (internal)
 *
 * Cheated proofs for safety properties. The externally-facing API
 * is in memAliasPropsScript.sml (ACCEPT_TAC wrappers).
 *)

Theory memAliasProofs
Ancestors
  memAliasDefs memLocDefs memLocProps basePtrDefs venomMemDefs venomExecSemantics
Libs
  finite_mapTheory alistTheory listTheory pairTheory

(* ===================================================================
   Layer 1: Generic FOLDL helpers
   =================================================================== *)

(* FOLDL with a domain-monotone step preserves domain membership. *)
Theorem foldl_fdom_mono[local]:
  ∀ks f step.
    (∀s k. FDOM s ⊆ FDOM (step s k)) ⇒
    ∀k. k ∈ FDOM f ⇒ k ∈ FDOM (FOLDL step f ks)
Proof
  Induct >> rw[] >>
  first_x_assum irule >> fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

(* FOLDL with step that only modifies the key it's given *)
Theorem foldl_flookup_other[local]:
  ∀ks (f : 'a |-> 'b) step.
    (∀s k k'. k' ≠ k ⇒ FLOOKUP (step s k) k' = FLOOKUP s k') ⇒
    ∀k. ¬MEM k ks ⇒ FLOOKUP (FOLDL step f ks) k = FLOOKUP f k
Proof
  Induct >> rw[] >>
  `FLOOKUP (step f h) k = FLOOKUP f k` by (first_x_assum irule >> fs[]) >>
  `FLOOKUP (FOLDL step (step f h) ks) k = FLOOKUP (step f h) k` by (
    first_x_assum irule >> rw[]
  ) >>
  fs[]
QED

(* FOLDL preserves a property if step preserves it *)
Theorem foldl_preserves_P[local]:
  ∀ks (f : 'a |-> 'b) step P.
    P f ∧ (∀s k. P s ⇒ P (step s k)) ⇒ P (FOLDL step f ks)
Proof
  Induct >> rw[]
QED

(* ===================================================================
   Layer 2: The FOLDL inside ma_add_location
   =================================================================== *)

(* Abbreviation for the FOLDL step function in ma_add_location *)
Definition ma_fold_step_def:
  ma_fold_step loc s k =
    let old = case FLOOKUP s k of NONE => [] | SOME l => l in
    if MEM loc old then s else s |+ (k, loc :: old)
End

(* The FOLDL step preserves domain *)
Theorem ma_fold_step_fdom[local]:
  ∀s k loc. FDOM s ⊆ FDOM (ma_fold_step loc s k)
Proof
  rw[ma_fold_step_def, LET_THM, pred_setTheory.SUBSET_DEF] >>
  Cases_on `MEM loc (case FLOOKUP s k of NONE => [] | SOME l => l)` >>
  fs[FDOM_FUPDATE]
QED

(* Keys not in the fold list are unchanged by FOLDL *)
Theorem ma_fold_step_other[local]:
  ∀s k k' loc. k' ≠ k ⇒ FLOOKUP (ma_fold_step loc s k) k' = FLOOKUP s k'
Proof
  rw[ma_fold_step_def, LET_THM] >>
  Cases_on `MEM loc (case FLOOKUP s k of NONE => [] | SOME l => l)` >>
  fs[FLOOKUP_UPDATE]
QED

(* ma_fold_step puts loc into k's alias list *)
Theorem ma_fold_step_adds[local]:
  ∀s k loc.
    k ∈ FDOM s ⇒
    ∃als. FLOOKUP (ma_fold_step loc s k) k = SOME als ∧ MEM loc als
Proof
  rw[ma_fold_step_def, LET_THM] >>
  Cases_on `FLOOKUP s k` >> fs[FLOOKUP_DEF, FLOOKUP_UPDATE] >>
  Cases_on `MEM loc x` >> fs[FLOOKUP_UPDATE]
QED

(* FOLDL preserves "loc in k's list" for keys not being stepped *)
Theorem ma_foldl_preserves_loc[local]:
  ∀ks s loc k als.
    FLOOKUP s k = SOME als ∧ MEM loc als ∧ ¬MEM k ks ⇒
    ∃als'. FLOOKUP (FOLDL (ma_fold_step loc) s ks) k = SOME als' ∧
           MEM loc als'
Proof
  Induct >> rw[] >>
  first_x_assum irule >> rw[] >>
  `FLOOKUP (ma_fold_step loc s h) k = FLOOKUP s k` by
    (irule ma_fold_step_other >> fs[]) >>
  metis_tac[]
QED

(* After FOLDL, a key in the fold list that was in FDOM has loc in its list *)
Theorem ma_foldl_adds_loc[local]:
  ∀ks s loc k.
    MEM k ks ∧ k ∈ FDOM s ⇒
    ∃als. FLOOKUP (FOLDL (ma_fold_step loc) s ks) k = SOME als ∧
          MEM loc als
Proof
  Induct >> rw[]
  >- ((* k = h: step adds loc, then FOLDL preserves *)
      `∃als. FLOOKUP (ma_fold_step loc s h) h = SOME als ∧ MEM loc als` by
        metis_tac[ma_fold_step_adds] >>
      Cases_on `MEM h ks`
      >- (first_x_assum irule >> rw[] >>
          `FDOM s ⊆ FDOM (ma_fold_step loc s h)` by metis_tac[ma_fold_step_fdom] >>
          fs[pred_setTheory.SUBSET_DEF])
      >- metis_tac[ma_foldl_preserves_loc])
  >- ((* MEM k ks: IH with updated state *)
      first_x_assum irule >> rw[] >>
      `FDOM s ⊆ FDOM (ma_fold_step loc s h)` by metis_tac[ma_fold_step_fdom] >>
      fs[pred_setTheory.SUBSET_DEF])
QED

(* After FOLDL, keys NOT in the fold list are unchanged *)
Theorem ma_foldl_other[local]:
  ∀ks s loc k.
    ¬MEM k ks ⇒
    FLOOKUP (FOLDL (ma_fold_step loc) s ks) k = FLOOKUP s k
Proof
  rw[] >> irule foldl_flookup_other >> rw[] >>
  metis_tac[ma_fold_step_other]
QED

(* FOLDL preserves FDOM exactly when all keys are already in domain *)
Theorem ma_foldl_fdom_exact[local]:
  ∀ks sets loc.
    EVERY (λk. k ∈ FDOM sets) ks ⇒
    FDOM (FOLDL (ma_fold_step loc) sets ks) = FDOM sets
Proof
  Induct >> rw[] >>
  `FDOM (ma_fold_step loc sets h) = FDOM sets` by (
    rw[ma_fold_step_def, LET_THM] >>
    Cases_on `MEM loc (case FLOOKUP sets h of NONE => [] | SOME l => l)` >>
    fs[FDOM_FUPDATE, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `EVERY (λk. k ∈ FDOM (ma_fold_step loc sets h)) ks` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[]
QED

(* Key in FOLDL result ⇒ key in original domain (when all fold keys ∈ FDOM) *)
Theorem ma_foldl_in_fdom[local]:
  ∀ks sets loc k als.
    EVERY (λk. k ∈ FDOM sets) ks ∧
    FLOOKUP (FOLDL (ma_fold_step loc) sets ks) k = SOME als ⇒
    k ∈ FDOM sets
Proof
  rw[] >>
  `FDOM (FOLDL (ma_fold_step loc) sets ks) = FDOM sets` by
    metis_tac[ma_foldl_fdom_exact] >>
  fs[FLOOKUP_DEF]
QED

(* FOLDL correctness: listed aliases actually overlap their key *)
Theorem ma_foldl_correctness[local]:
  ∀ks s loc k als a.
    FLOOKUP (FOLDL (ma_fold_step loc) s ks) k = SOME als ∧
    MEM a als ⇒
    (∃als0. FLOOKUP s k = SOME als0 ∧ MEM a als0) ∨
    (a = loc ∧ MEM k ks)
Proof
  Induct >> rw[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum (qspec_then `a` mp_tac) >> simp[] >>
  strip_tac
  >- ((* From inner FOLDL state *)
      Cases_on `k = h`
      >- (fs[ma_fold_step_def, LET_THM] >>
          Cases_on `MEM loc (case FLOOKUP s h of NONE => [] | SOME l => l)` >>
          fs[FLOOKUP_UPDATE] >>
          `a = loc ∨ MEM a (case FLOOKUP s h of NONE => [] | SOME l => l)` by
            (fs[] >> metis_tac[MEM]) >>
          Cases_on `a = loc` >> fs[] >>
          Cases_on `FLOOKUP s h` >> fs[] >> metis_tac[])
      >- (`FLOOKUP (ma_fold_step loc s h) k = FLOOKUP s k` by
            (irule ma_fold_step_other >> fs[]) >>
          metis_tac[]))
  >- metis_tac[]
QED

(* ===================================================================
   Layer 3: ma_add_location rewrite using ma_fold_step
   =================================================================== *)

(* Rewrite ma_add_location in terms of ma_fold_step for cleaner proofs *)
Theorem ma_add_location_alt[local]:
  ∀sets loc.
    ma_add_location sets loc =
    let current = case FLOOKUP sets loc of NONE => [] | SOME l => l in
    let overlapping = FILTER (λk. may_overlap loc k) (MAP FST (fmap_to_alist sets)) in
    let sets1 = FOLDL (ma_fold_step loc) sets overlapping in
    let self = if may_overlap loc loc then [loc] else [] in
    sets1 |+ (loc, self ++ overlapping ++ current)
Proof
  rw[ma_add_location_def] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  irule FOLDL_CONG >> rw[ma_fold_step_def, LET_THM]
QED

(* Helper: overlapping list membership *)
Theorem mem_overlapping[local]:
  ∀sets loc k.
    MEM k (FILTER (λk. may_overlap loc k) (MAP FST (fmap_to_alist sets))) ⇔
    k ∈ FDOM sets ∧ may_overlap loc k
Proof
  rw[MEM_FILTER, MEM_MAP] >>
  eq_tac >> rw[]
  >- (Cases_on `y` >> fs[MEM_fmap_to_alist_FLOOKUP] >>
      fs[FLOOKUP_DEF])
  >- (qexists_tac `(k, sets ' k)` >>
      fs[MEM_fmap_to_alist, FDOM_DEF])
QED

(* overlapping keys are all in FDOM — precondition for ma_foldl_fdom_exact *)
Theorem overlapping_every_fdom[local]:
  ∀sets loc.
    EVERY (λk. k ∈ FDOM sets)
      (FILTER (λk. may_overlap loc k) (MAP FST (fmap_to_alist sets)))
Proof
  rw[EVERY_MEM, MEM_FILTER, MEM_MAP] >>
  Cases_on `y` >> fs[MEM_fmap_to_alist] >> fs[FLOOKUP_DEF]
QED

(* ===================================================================
   Layer 3: ma_add_location properties
   =================================================================== *)

Theorem ma_add_location_loc_in_domain[local]:
  ∀sets loc. loc ∈ FDOM (ma_add_location sets loc)
Proof
  rw[ma_add_location_def, LET_THM, FDOM_FUPDATE]
QED

Theorem ma_add_location_preserves_domain[local]:
  ∀sets loc k. k ∈ FDOM sets ⇒ k ∈ FDOM (ma_add_location sets loc)
Proof
  rw[ma_add_location_alt, LET_THM, FDOM_FUPDATE] >>
  DISJ2_TAC >>
  irule foldl_fdom_mono >>
  rw[ma_fold_step_fdom]
QED

Theorem ma_add_location_aliases_overlap[local]:
  ∀sets loc aliases.
    FLOOKUP (ma_add_location sets loc) loc = SOME aliases ⇒
    ∀a. MEM a aliases ⇒
      (a = loc ∧ may_overlap loc loc) ∨
      a ∈ FDOM sets ∧ may_overlap loc a ∨
      MEM a (case FLOOKUP sets loc of NONE => [] | SOME l => l)
Proof
  rw[ma_add_location_alt, LET_THM, FLOOKUP_UPDATE] >>
  fs[MEM_APPEND, MEM_FILTER, MEM_MAP] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  Cases_on `y` >> fs[MEM_fmap_to_alist] >> fs[FLOOKUP_DEF]
QED

Theorem ma_add_location_overlap_recorded[local]:
  ∀sets loc k.
    k ∈ FDOM sets ∧ may_overlap loc k ⇒
    ∃aliases. FLOOKUP (ma_add_location sets loc) k = SOME aliases ∧
              MEM loc aliases
Proof
  rw[ma_add_location_alt, LET_THM] >>
  Cases_on `k = loc` >- (
    (* k = loc: loc is in self since may_overlap loc loc (from hyp) *)
    fs[FLOOKUP_UPDATE, MEM_APPEND]
  ) >>
  fs[FLOOKUP_UPDATE] >>
  (* k ≠ loc, so FLOOKUP in FOLDL result *)
  `MEM k (FILTER (λk. may_overlap loc k) (MAP FST (fmap_to_alist sets)))` by
    fs[mem_overlapping] >>
  drule_all ma_foldl_adds_loc >> rw[]
QED

(* ===== wf preservation — the key theorem ===== *)

(* Helper: FOLDL preserves correctness half of wf *)
Theorem ma_foldl_preserves_correctness[local]:
  ∀ks sets loc.
    (∀l als a. FLOOKUP sets l = SOME als ∧ MEM a als ⇒ may_overlap l a) ∧
    (∀k. MEM k ks ⇒ may_overlap loc k) ⇒
    (∀l als a. FLOOKUP (FOLDL (ma_fold_step loc) sets ks) l = SOME als ∧
               MEM a als ⇒ may_overlap l a)
Proof
  rw[] >>
  drule_all ma_foldl_correctness >> strip_tac
  >- metis_tac[]
  >- (fs[] >> metis_tac[may_overlap_comm])
QED

(* Split preserves_wf into correctness and completeness halves *)
Theorem ma_add_location_correct[local]:
  ∀sets loc.
    (∀l als a. FLOOKUP sets l = SOME als ∧ MEM a als ⇒ may_overlap l a) ⇒
    ∀l als a.
      FLOOKUP (ma_add_location sets loc) l = SOME als ∧ MEM a als ⇒
      may_overlap l a
Proof
  rpt strip_tac >>
  fs[ma_add_location_alt, LET_THM, FLOOKUP_UPDATE] >>
  Cases_on `loc = l` >> gvs[]
  (* Goal 1: self list *)
  >- (Cases_on `may_overlap l l` >> gvs[])
  (* Goal 2: overlap filter *)
  >- gvs[MEM_FILTER]
  (* Goal 3: current aliases *)
  >- (Cases_on `FLOOKUP sets l` >> gvs[] >> metis_tac[])
  (* Goal 4: other entry from FOLDL *)
  >- (`∀l' als' a'. FLOOKUP (FOLDL (ma_fold_step loc) sets
         (FILTER (λk. may_overlap loc k) (MAP FST (fmap_to_alist sets))))
         l' = SOME als' ∧ MEM a' als' ⇒ may_overlap l' a'` by (
        match_mp_tac ma_foldl_preserves_correctness >> rw[MEM_FILTER]) >>
      first_x_assum (qspecl_then [`l`, `als`, `a`] mp_tac) >> simp[])
QED

(* Generic: FOLDL preserves list members when step preserves them *)
Theorem foldl_preserves_mem[local]:
  ∀ks step (s : 'a |-> 'b list) k als x.
    (∀s' k' k'' als' y.
       FLOOKUP s' k'' = SOME als' ∧ MEM y als' ⇒
       ∃als''. FLOOKUP (step s' k') k'' = SOME als'' ∧ MEM y als'') ∧
    FLOOKUP s k = SOME als ∧ MEM x als ⇒
    ∃als'. FLOOKUP (FOLDL step s ks) k = SOME als' ∧ MEM x als'
Proof
  Induct >> rw[]
QED

(* ma_fold_step preserves all existing list members *)
Theorem ma_fold_step_preserves_mem[local]:
  ∀s k loc k' als x.
    FLOOKUP s k' = SOME als ∧ MEM x als ⇒
    ∃als'. FLOOKUP (ma_fold_step loc s k) k' = SOME als' ∧ MEM x als'
Proof
  rw[ma_fold_step_def, LET_THM] >>
  Cases_on `MEM loc (case FLOOKUP s k of NONE => [] | SOME l => l)`
  >- metis_tac[]
  >- (Cases_on `k' = k`
      >- (fs[FLOOKUP_UPDATE] >> Cases_on `FLOOKUP s k` >> gvs[] >> metis_tac[MEM])
      >- (fs[FLOOKUP_UPDATE] >> metis_tac[]))
QED

(* FOLDL of ma_fold_step preserves list members (instance of foldl_preserves_mem) *)
Theorem ma_foldl_preserves_mem[local]:
  ∀ks s loc k als x.
    FLOOKUP s k = SOME als ∧ MEM x als ⇒
    ∃als'. FLOOKUP (FOLDL (ma_fold_step loc) s ks) k = SOME als' ∧
           MEM x als'
Proof
  rw[] >> irule foldl_preserves_mem >> metis_tac[ma_fold_step_preserves_mem]
QED

(* FDOM of ma_add_location *)
Theorem ma_add_location_fdom[local]:
  ∀sets loc.
    FDOM (ma_add_location sets loc) = loc INSERT FDOM sets
Proof
  rw[ma_add_location_alt, LET_THM, FDOM_FUPDATE] >>
  `FDOM (FOLDL (ma_fold_step loc) sets
     (FILTER (λk. may_overlap loc k) (MAP FST (fmap_to_alist sets)))) =
   FDOM sets` by
    (irule ma_foldl_fdom_exact >> rw[overlapping_every_fdom]) >>
  rw[pred_setTheory.EXTENSION]
QED

Theorem ma_add_location_complete[local]:
  ∀sets loc.
    (∀loc als a. FLOOKUP sets loc = SOME als ∧ MEM a als ⇒ may_overlap loc a) ∧
    (∀l1 l2 als1.
       FLOOKUP sets l1 = SOME als1 ∧ l2 ∈ FDOM sets ∧ may_overlap l1 l2 ⇒
       MEM l2 als1) ⇒
    ∀l1 l2 als1.
      FLOOKUP (ma_add_location sets loc) l1 = SOME als1 ∧
      l2 ∈ FDOM (ma_add_location sets loc) ∧ may_overlap l1 l2 ⇒
      MEM l2 als1
Proof
  rpt strip_tac >>
  `FDOM (ma_add_location sets loc) = loc INSERT FDOM sets` by
    rw[ma_add_location_fdom] >>
  qabbrev_tac `ovl = FILTER (λk. may_overlap loc k)
                        (MAP FST (fmap_to_alist sets))` >>
  qabbrev_tac `sets1 = FOLDL (ma_fold_step loc) sets ovl` >>
  `l2 ∈ loc INSERT FDOM sets` by metis_tac[] >>
  `l1 ∈ FDOM (ma_add_location sets loc)` by fs[FLOOKUP_DEF] >>
  `l1 ∈ loc INSERT FDOM sets` by metis_tac[] >>
  Cases_on `l1 = loc` >| [
    (* l1 = loc: als1 = self ++ ovl ++ current *)
    gvs[ma_add_location_alt, LET_THM, FLOOKUP_UPDATE] >>
    fs[Abbr `ovl`, mem_overlapping, MEM_APPEND] >> metis_tac[may_overlap_comm],
    (* l1 ≠ loc *)
    `l1 ∈ FDOM sets` by fs[pred_setTheory.IN_INSERT] >>
    `FLOOKUP (ma_add_location sets loc) l1 = FLOOKUP sets1 l1` by
      fs[ma_add_location_alt, LET_THM, FLOOKUP_UPDATE] >>
    Cases_on `l2 = loc` >| [
      (* l2 = loc: FOLDL added loc to l1's list *)
      `MEM l1 ovl` by
        (fs[Abbr `ovl`, mem_overlapping] >> metis_tac[may_overlap_comm]) >>
      `∃als'. FLOOKUP sets1 l1 = SOME als' ∧ MEM loc als'` by
        (rw[Abbr `sets1`] >> irule ma_foldl_adds_loc >> rw[]) >>
      gvs[],
      (* l2 ≠ loc: original completeness + FOLDL preservation *)
      `l2 ∈ FDOM sets` by fs[pred_setTheory.IN_INSERT] >>
      `∃v. FLOOKUP sets l1 = SOME v` by fs[FLOOKUP_DEF] >>
      `MEM l2 v` by (
        first_x_assum (qspecl_then [`l1`, `l2`, `v`] mp_tac) >> rw[]) >>
      `∃als'. FLOOKUP sets1 l1 = SOME als' ∧ MEM l2 als'` by
        (rw[Abbr `sets1`] >> irule ma_foldl_preserves_mem >> metis_tac[]) >>
      gvs[]
    ]
  ]
QED

Theorem ma_add_location_preserves_wf[local]:
  ∀sets loc.
    wf_alias_sets sets ⇒
    wf_alias_sets (ma_add_location sets loc)
Proof
  rw[wf_alias_sets_def] >| [
    irule (SIMP_RULE std_ss [] ma_add_location_correct) >> metis_tac[],
    irule (SIMP_RULE std_ss [] ma_add_location_complete) >>
    qexistsl_tac [`l1`, `loc`, `sets`] >> fs[] >> metis_tac[]
  ]
QED

(* ===================================================================
   Layer 4: Lifting through analyze_inst/block/blocks
   =================================================================== *)

Theorem ma_analyze_inst_preserves_wf[local]:
  ∀bp addr sets inst.
    wf_alias_sets sets ⇒ wf_alias_sets (ma_analyze_inst bp addr sets inst)
Proof
  rw[ma_analyze_inst_def, LET_THM] >>
  metis_tac[ma_add_location_preserves_wf]
QED

Theorem ma_analyze_inst_preserves_domain[local]:
  ∀bp addr sets inst k.
    k ∈ FDOM sets ⇒ k ∈ FDOM (ma_analyze_inst bp addr sets inst)
Proof
  rw[ma_analyze_inst_def, LET_THM] >>
  metis_tac[ma_add_location_preserves_domain]
QED

Theorem ma_analyze_block_domain_mono[local]:
  ∀bp addr sets insts k.
    k ∈ FDOM sets ⇒
    k ∈ FDOM (ma_analyze_block bp addr sets insts)
Proof
  Induct_on `insts` >> rw[ma_analyze_block_def] >>
  first_x_assum irule >>
  irule ma_analyze_inst_preserves_domain >> fs[]
QED

Theorem ma_analyze_block_preserves_wf[local]:
  ∀bp addr sets insts.
    wf_alias_sets sets ⇒ wf_alias_sets (ma_analyze_block bp addr sets insts)
Proof
  Induct_on `insts` >> rw[ma_analyze_block_def] >>
  first_x_assum irule >>
  irule ma_analyze_inst_preserves_wf >> fs[]
QED

Theorem ma_analyze_blocks_domain_mono[local]:
  ∀bp addr sets bbs k.
    k ∈ FDOM sets ⇒
    k ∈ FDOM (ma_analyze_blocks bp addr sets bbs)
Proof
  Induct_on `bbs` >> rw[ma_analyze_blocks_def] >>
  first_x_assum irule >>
  irule ma_analyze_block_domain_mono >> fs[]
QED

Theorem ma_analyze_blocks_preserves_wf[local]:
  ∀bp addr sets bbs.
    wf_alias_sets sets ⇒ wf_alias_sets (ma_analyze_blocks bp addr sets bbs)
Proof
  Induct_on `bbs` >> rw[ma_analyze_blocks_def] >>
  first_x_assum irule >>
  irule ma_analyze_block_preserves_wf >> fs[]
QED

(* ===================================================================
   Layer 5: Main theorems
   =================================================================== *)

Theorem ma_analyze_wf:
  ∀bp_result fn addr_sp.
    wf_alias_sets (ma_analyze bp_result fn addr_sp)
Proof
  rw[ma_analyze_def] >>
  irule ma_analyze_blocks_preserves_wf >>
  rw[wf_alias_sets_def, FLOOKUP_DEF, FDOM_FEMPTY]
QED

Theorem ma_may_alias_iff:
  ∀sets loc1 loc2.
    wf_alias_sets sets ⇒
    (ma_may_alias sets loc1 loc2 ⇔ may_overlap loc1 loc2)
Proof
  rw[ma_may_alias_def, wf_alias_sets_def] >>
  Cases_on `loc1.ml_volatile ∨ loc2.ml_volatile` >> fs[] >>
  Cases_on `FLOOKUP sets loc1` >> Cases_on `FLOOKUP sets loc2` >> fs[] >>
  `loc2 ∈ FDOM sets` by fs[FLOOKUP_DEF] >>
  eq_tac >> rw[] >>
  first_x_assum (qspecl_then [`loc1`, `loc2`, `x`] mp_tac) >> rw[]
QED

Theorem ma_different_alloca_no_alias:
  ∀sets loc1 loc2 a1 a2.
    wf_alias_sets sets ∧
    loc1.ml_alloca = SOME a1 ∧ loc2.ml_alloca = SOME a2 ∧ a1 ≠ a2 ⇒
    ¬ma_may_alias sets loc1 loc2
Proof
  rw[] >> drule ma_may_alias_iff >>
  disch_then (qspecl_then [`loc1`, `loc2`] mp_tac) >>
  rw[] >> metis_tac[different_alloca_no_overlap]
QED

Theorem ma_empty_no_alias:
  ∀sets loc.
    wf_alias_sets sets ⇒
    ¬ma_may_alias sets ml_empty loc
Proof
  rw[] >> drule ma_may_alias_iff >>
  disch_then (qspecl_then [`ml_empty`, `loc`] mp_tac) >>
  rw[empty_no_overlap_l]
QED

(* mk_volatile doesn't change may_overlap *)
Theorem mk_volatile_overlap[local]:
  ∀loc x. may_overlap (mk_volatile loc) x ⇔ may_overlap loc x
Proof
  rw[mk_volatile_def, may_overlap_def]
QED

(* ===== Volatile FOLDL step and helpers ===== *)

(* The volatile FOLDL step: prepend vloc to an existing entry *)
Definition mv_fold_step_def:
  mv_fold_step vloc s a =
    if a = (vloc : mem_loc) then s
    else case FLOOKUP s a of
           SOME alist => s |+ (a, vloc :: alist)
         | NONE => s
End

(* mv_fold_step preserves existing list members *)
Theorem mv_fold_step_preserves_mem[local]:
  ∀s k vloc k' als x.
    FLOOKUP s k' = SOME als ∧ MEM x als ⇒
    ∃als'. FLOOKUP (mv_fold_step vloc s k) k' = SOME als' ∧ MEM x als'
Proof
  rw[mv_fold_step_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[FLOOKUP_UPDATE] >>
  rw[] >> fs[] >> metis_tac[MEM]
QED

(* mv_fold_step preserves FDOM *)
Theorem mv_fold_step_fdom[local]:
  ∀s k vloc. FDOM s ⊆ FDOM (mv_fold_step vloc s k)
Proof
  rw[mv_fold_step_def, pred_setTheory.SUBSET_DEF] >>
  BasicProvers.EVERY_CASE_TAC >> fs[FDOM_FUPDATE]
QED

(* mv_fold_step doesn't change other keys' FLOOKUP *)
Theorem mv_fold_step_other[local]:
  ∀s k vloc k'. k' ≠ k ⇒
    FLOOKUP (mv_fold_step vloc s k) k' = FLOOKUP s k'
Proof
  rw[mv_fold_step_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[FLOOKUP_UPDATE]
QED

(* mv_fold_step adds vloc to a key's list *)
Theorem mv_fold_step_adds[local]:
  ∀s k vloc.
    k ≠ vloc ∧ k ∈ FDOM s ⇒
    ∃als. FLOOKUP (mv_fold_step vloc s k) k = SOME als ∧ MEM vloc als
Proof
  rw[mv_fold_step_def] >>
  `∃v. FLOOKUP s k = SOME v` by fs[FLOOKUP_DEF] >>
  fs[FLOOKUP_UPDATE]
QED

(* FOLDL of mv_fold_step preserves list members *)
Theorem mv_foldl_preserves_mem[local]:
  ∀ks s vloc k als x.
    FLOOKUP s k = SOME als ∧ MEM x als ⇒
    ∃als'. FLOOKUP (FOLDL (mv_fold_step vloc) s ks) k = SOME als' ∧
           MEM x als'
Proof
  rw[] >> irule foldl_preserves_mem >> metis_tac[mv_fold_step_preserves_mem]
QED

(* FOLDL of mv_fold_step: keys not in fold list are unchanged *)
Theorem mv_foldl_other[local]:
  ∀ks s vloc k.
    ¬MEM k ks ⇒
    FLOOKUP (FOLDL (mv_fold_step vloc) s ks) k = FLOOKUP s k
Proof
  rw[] >> irule foldl_flookup_other >> rw[] >> metis_tac[mv_fold_step_other]
QED

(* FOLDL of mv_fold_step preserves FDOM *)
Theorem mv_foldl_fdom[local]:
  ∀ks s vloc k.
    k ∈ FDOM s ⇒ k ∈ FDOM (FOLDL (mv_fold_step vloc) s ks)
Proof
  rw[] >> irule foldl_fdom_mono >> rw[mv_fold_step_fdom]
QED

(* FOLDL of mv_fold_step adds vloc to listed keys *)
Theorem mv_foldl_adds_vloc[local]:
  ∀ks s vloc k.
    MEM k ks ∧ k ≠ vloc ∧ k ∈ FDOM s ⇒
    ∃als. FLOOKUP (FOLDL (mv_fold_step vloc) s ks) k = SOME als ∧
          MEM vloc als
Proof
  Induct >> rw[] >| [
    (* k = h: step adds vloc, then FOLDL preserves *)
    `∃als. FLOOKUP (mv_fold_step vloc s h) h = SOME als ∧ MEM vloc als` by
      metis_tac[mv_fold_step_adds] >>
    Cases_on `MEM h ks` >| [
      first_x_assum irule >> rw[] >>
      `FDOM s ⊆ FDOM (mv_fold_step vloc s h)` by metis_tac[mv_fold_step_fdom] >>
      fs[pred_setTheory.SUBSET_DEF],
      drule_all mv_foldl_preserves_mem >> rw[]
    ],
    (* MEM k ks: IH *)
    first_x_assum irule >> rw[] >>
    `FDOM s ⊆ FDOM (mv_fold_step vloc s h)` by metis_tac[mv_fold_step_fdom] >>
    fs[pred_setTheory.SUBSET_DEF]
  ]
QED

(* Rewrite ma_mark_volatile FOLDL in terms of mv_fold_step *)
Theorem mv_foldl_equiv[local]:
  ∀aliases loc vloc s.
    FOLDL (λs a.
      if a = loc ∨ a = vloc then s
      else case FLOOKUP s a of
             SOME alist => s |+ (a, vloc :: alist)
           | NONE => s) s (FILTER (λa. a ≠ loc ∧ a ≠ vloc) aliases) =
    FOLDL (mv_fold_step vloc) s (FILTER (λa. a ≠ loc ∧ a ≠ vloc) aliases)
Proof
  Induct >> rw[mv_fold_step_def]
QED

(* mv_fold_step preserves FDOM exactly (it only updates existing keys) *)
Theorem mv_fold_step_fdom_exact[local]:
  ∀s k vloc. FDOM (mv_fold_step vloc s k) = FDOM s
Proof
  rw[mv_fold_step_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs[FDOM_FUPDATE, pred_setTheory.EXTENSION, FLOOKUP_DEF] >>
  metis_tac[]
QED

(* FOLDL of mv_fold_step preserves FDOM exactly *)
Theorem mv_foldl_fdom_exact[local]:
  ∀ks s vloc. FDOM (FOLDL (mv_fold_step vloc) s ks) = FDOM s
Proof
  Induct >> rw[mv_fold_step_fdom_exact]
QED

(* mv_fold_step soundness: new list members are vloc or were already present *)
Theorem mv_fold_step_sound[local]:
  ∀s k vloc k' als' x.
    FLOOKUP (mv_fold_step vloc s k) k' = SOME als' ∧ MEM x als' ⇒
    x = vloc ∨ (∃als. FLOOKUP s k' = SOME als ∧ MEM x als)
Proof
  rw[mv_fold_step_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[FLOOKUP_UPDATE] >>
  Cases_on `k = k'` >> gvs[] >> metis_tac[]
QED

(* FOLDL of mv_fold_step soundness: list members are vloc or from original *)
Theorem mv_foldl_sound[local]:
  ∀ks s vloc k als x.
    FLOOKUP (FOLDL (mv_fold_step vloc) s ks) k = SOME als ∧ MEM x als ⇒
    x = vloc ∨ (∃als0. FLOOKUP s k = SOME als0 ∧ MEM x als0)
Proof
  Induct >> rw[] >>
  first_x_assum (qspecl_then [`mv_fold_step vloc s h`, `vloc`, `k`, `als`, `x`]
    mp_tac) >> rw[] >>
  drule_all mv_fold_step_sound >> metis_tac[]
QED

Theorem flookup_in_fdom[local]:
  ∀(f:'a |-> 'b) k v. FLOOKUP f k = SOME v ⇒ k ∈ FDOM f
Proof
  rw[flookup_thm]
QED

(*
 * ma_mark_volatile correctness helper:
 * Every entry in s3's alias lists actually overlaps its key.
 *)
Theorem mk_volatile_overlap_all[local]:
  ∀loc. may_overlap (mk_volatile loc) (mk_volatile loc) = may_overlap loc loc ∧
        may_overlap (mk_volatile loc) loc = may_overlap loc loc ∧
        may_overlap loc (mk_volatile loc) = may_overlap loc loc
Proof
  rw[may_overlap_def, mk_volatile_def]
QED

(* For any x, may_overlap x (mk_volatile loc) = may_overlap x loc *)
Theorem mk_volatile_overlap_rhs[local]:
  ∀loc x. may_overlap x (mk_volatile loc) = may_overlap x loc
Proof
  rw[may_overlap_def, mk_volatile_def]
QED

Theorem mv_correctness[local]:
  ∀sets loc x.
    wf_alias_sets sets ∧ FLOOKUP sets loc = SOME x ⇒
    let vloc = mk_volatile loc in
    let filt = FILTER (λa. a ≠ loc ∧ a ≠ vloc) x in
    let self = if may_overlap vloc vloc then [vloc] else [] in
    let cross = if may_overlap vloc loc then [loc] else [] in
    let loc_als = if may_overlap loc vloc then vloc :: x else x in
    let bse = sets |+ (vloc, self ++ cross ++ filt) |+ (loc, loc_als) in
    let s3 = FOLDL (mv_fold_step vloc) bse filt in
    ∀loc' als a.
      FLOOKUP s3 loc' = SOME als ∧ MEM a als ⇒ may_overlap loc' a
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  qabbrev_tac `vloc = mk_volatile loc` >>
  qabbrev_tac `filt = FILTER (λa. a ≠ loc ∧ a ≠ vloc) x` >>
  qabbrev_tac `bse = sets |+ (vloc,
    (if may_overlap vloc vloc then [vloc] else []) ++
    (if may_overlap vloc loc then [loc] else []) ++ filt)
    |+ (loc, if may_overlap loc vloc then vloc :: x else x)` >>
  (* Key rewrites: mk_volatile doesn't affect may_overlap *)
  `may_overlap vloc = may_overlap loc` by (
    rw[FUN_EQ_THM, Abbr `vloc`, mk_volatile_def, may_overlap_def]) >>
  `∀y. may_overlap y vloc = may_overlap y loc` by (
    rw[Abbr `vloc`] >> rw[mk_volatile_overlap_rhs]) >>
  (* Basic facts *)
  `loc ∈ FDOM sets` by fs[FLOOKUP_DEF] >>
  `∀a'. MEM a' x ⇒ may_overlap loc a'` by (
    fs[wf_alias_sets_def] >> metis_tac[]) >>
  `∀a'. MEM a' filt ⇒ a' ≠ loc ∧ a' ≠ vloc ∧ may_overlap loc a'` by (
    rw[Abbr `filt`, MEM_FILTER]) >>
  `¬MEM vloc filt ∧ ¬MEM loc filt` by (
    rw[Abbr `filt`, MEM_FILTER]) >>
  `FDOM bse = vloc INSERT FDOM sets` by (
    rw[Abbr `bse`, FDOM_FUPDATE, pred_setTheory.EXTENSION] >>
    metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  imp_res_tac flookup_in_fdom >>
  `loc' ∈ vloc INSERT FDOM sets` by metis_tac[mv_foldl_fdom_exact] >>
  fs[pred_setTheory.IN_INSERT] >- (
    (* CASE 1: loc' = vloc — fold doesn't touch vloc's entry *)
    `FLOOKUP (FOLDL (mv_fold_step vloc) bse filt) vloc = FLOOKUP bse vloc` by (
      irule mv_foldl_other >> rw[]) >>
    Cases_on `vloc = loc` >- (
      gvs[Abbr `bse`, FLOOKUP_UPDATE, MEM_APPEND] >>
      Cases_on `may_overlap loc loc` >> gvs[] >> metis_tac[]
    ) >>
    `FLOOKUP bse vloc = SOME (
      (if may_overlap loc vloc then [vloc] else []) ++
      (if may_overlap loc loc then [loc] else []) ++ filt)` by (
      rw[Abbr `bse`, FLOOKUP_UPDATE]) >>
    `may_overlap loc vloc = may_overlap loc loc` by metis_tac[] >>
    gvs[] >> Cases_on `may_overlap loc loc` >> gvs[MEM_FILTER] >> metis_tac[]
  ) >>
  (* CASE 2: loc' ∈ FDOM sets *)
  Cases_on `loc' = loc` >- (
    (* loc' = loc: fold doesn't touch loc's entry *)
    `FLOOKUP (FOLDL (mv_fold_step vloc) bse filt) loc = FLOOKUP bse loc` by (
      irule mv_foldl_other >> rw[]) >>
    gvs[Abbr `bse`, FLOOKUP_UPDATE] >>
    Cases_on `may_overlap loc loc` >> gvs[] >>
    fs[wf_alias_sets_def] >> metis_tac[]
  ) >>
  Cases_on `loc' = vloc` >- (
    (* loc' = vloc ≠ loc: fold doesn't touch vloc's entry *)
    `FLOOKUP (FOLDL (mv_fold_step vloc) bse filt) vloc = FLOOKUP bse vloc` by (
      irule mv_foldl_other >> rw[]) >>
    `FLOOKUP bse vloc = SOME (
      (if may_overlap loc vloc then [vloc] else []) ++
      (if may_overlap loc loc then [loc] else []) ++ filt)` by (
      rw[Abbr `bse`, FLOOKUP_UPDATE]) >>
    gvs[] >> Cases_on `may_overlap loc loc` >> gvs[MEM_FILTER] >> metis_tac[]
  ) >>
  (* loc' ≠ loc, loc' ≠ vloc: bse loc' = sets loc' *)
  `FLOOKUP bse loc' = FLOOKUP sets loc'` by (
    rw[Abbr `bse`, FLOOKUP_UPDATE]) >>
  drule_all mv_foldl_sound >> strip_tac >- (
    (* a = vloc: need may_overlap loc' loc *)
    fs[] >>
    Cases_on `MEM loc' filt` >- metis_tac[may_overlap_sym] >>
    `FLOOKUP (FOLDL (mv_fold_step vloc) bse filt) loc' = FLOOKUP bse loc'` by (
      irule mv_foldl_other >> rw[]) >>
    gvs[] >> fs[wf_alias_sets_def] >> metis_tac[]
  ) >>
  (* a ≠ vloc: a was in sets loc' *)
  gvs[] >> fs[wf_alias_sets_def] >> metis_tac[]
QED

(*
 * ma_mark_volatile completeness helper:
 * Overlapping tracked locations are cross-listed in s3.
 *)
Theorem mv_completeness[local]:
  ∀sets loc x.
    wf_alias_sets sets ∧ FLOOKUP sets loc = SOME x ⇒
    let vloc = mk_volatile loc in
    let filt = FILTER (λa. a ≠ loc ∧ a ≠ vloc) x in
    let self = if may_overlap vloc vloc then [vloc] else [] in
    let cross = if may_overlap vloc loc then [loc] else [] in
    let loc_als = if may_overlap loc vloc then vloc :: x else x in
    let bse = sets |+ (vloc, self ++ cross ++ filt) |+ (loc, loc_als) in
    let s3 = FOLDL (mv_fold_step vloc) bse filt in
    ∀l1 l2 als1.
      FLOOKUP s3 l1 = SOME als1 ∧ l2 ∈ FDOM s3 ∧ may_overlap l1 l2 ⇒
      MEM l2 als1
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  qabbrev_tac `vloc = mk_volatile loc` >>
  qabbrev_tac `filt = FILTER (λa. a ≠ loc ∧ a ≠ vloc) x` >>
  qabbrev_tac `bse = sets |+ (vloc,
    (if may_overlap vloc vloc then [vloc] else []) ++
    (if may_overlap vloc loc then [loc] else []) ++ filt)
    |+ (loc, if may_overlap loc vloc then vloc :: x else x)` >>
  `may_overlap vloc = may_overlap loc` by (
    rw[FUN_EQ_THM, Abbr `vloc`, mk_volatile_def, may_overlap_def]) >>
  `∀y. may_overlap y vloc = may_overlap y loc` by (
    rw[Abbr `vloc`] >> rw[mk_volatile_overlap_rhs]) >>
  `loc ∈ FDOM sets` by fs[FLOOKUP_DEF] >>
  `∀a'. MEM a' x ⇒ may_overlap loc a'` by (
    fs[wf_alias_sets_def] >> metis_tac[]) >>
  `∀a'. MEM a' filt ⇒ a' ≠ loc ∧ a' ≠ vloc ∧ may_overlap loc a'` by (
    rw[Abbr `filt`, MEM_FILTER]) >>
  `FDOM (FOLDL (mv_fold_step vloc) bse filt) = FDOM bse` by
    rw[mv_foldl_fdom_exact] >>
  `FDOM bse = vloc INSERT FDOM sets` by (
    rw[Abbr `bse`, FDOM_FUPDATE, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `¬MEM vloc filt ∧ ¬MEM loc filt` by (
    rw[Abbr `filt`, MEM_FILTER]) >>
  `may_overlap loc vloc = may_overlap loc loc` by metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `l2 ∈ FDOM bse` by metis_tac[] >>
  (* === Case l1 = vloc === *)
  Cases_on `l1 = vloc` >- (
    `FLOOKUP (FOLDL (mv_fold_step vloc) bse filt) vloc = FLOOKUP bse vloc` by (
      irule mv_foldl_other >> rw[]) >>
    Cases_on `vloc = loc` >- (
      `FLOOKUP bse vloc = SOME (if may_overlap loc vloc then vloc :: x else x)` by
        asm_simp_tac std_ss [Abbr `bse`, FLOOKUP_UPDATE] >>
      `als1 = if may_overlap loc vloc then vloc :: x else x` by
        metis_tac[optionTheory.SOME_11] >>
      `l2 ∈ FDOM sets` by metis_tac[pred_setTheory.IN_INSERT] >>
      `may_overlap loc l2` by metis_tac[] >>
      `MEM l2 x` by (fs[wf_alias_sets_def] >> metis_tac[]) >>
      Cases_on `may_overlap loc vloc` >> rw[]
    ) >>
    `FLOOKUP bse vloc = SOME (
      (if may_overlap loc loc then [vloc] else []) ++
      (if may_overlap loc loc then [loc] else []) ++ filt)` by (
      simp_tac std_ss [Abbr `bse`, FLOOKUP_UPDATE] >> metis_tac[]) >>
    `als1 = (if may_overlap loc loc then [vloc] else []) ++
            (if may_overlap loc loc then [loc] else []) ++ filt` by
      metis_tac[optionTheory.SOME_11] >>
    Cases_on `l2 = vloc` >- (
      `may_overlap loc vloc` by metis_tac[] >> fs[]) >>
    Cases_on `l2 = loc` >- (
      `may_overlap loc loc` by metis_tac[] >> fs[MEM_APPEND]) >>
    `l2 ∈ FDOM sets` by metis_tac[pred_setTheory.IN_INSERT] >>
    `may_overlap loc l2` by metis_tac[] >>
    `MEM l2 x` by (fs[wf_alias_sets_def] >> metis_tac[]) >>
    `MEM l2 filt` by (rw[Abbr `filt`, MEM_FILTER]) >>
    fs[MEM_APPEND]
  ) >>
  (* === Case l1 = loc === *)
  Cases_on `l1 = loc` >- (
    `FLOOKUP (FOLDL (mv_fold_step vloc) bse filt) loc = FLOOKUP bse loc` by (
      irule mv_foldl_other >> rw[]) >>
    `FLOOKUP bse loc = SOME (if may_overlap loc vloc then vloc :: x else x)` by
      rw[Abbr `bse`, FLOOKUP_UPDATE] >>
    `als1 = if may_overlap loc vloc then vloc :: x else x` by
      metis_tac[optionTheory.SOME_11] >>
    Cases_on `l2 = vloc` >- (
      rw[] >> Cases_on `may_overlap loc vloc` >> fs[]
    ) >>
    `l2 ∈ FDOM sets` by metis_tac[pred_setTheory.IN_INSERT] >>
    `MEM l2 x` by (fs[wf_alias_sets_def] >> metis_tac[]) >>
    Cases_on `may_overlap loc vloc` >> fs[]
  ) >>
  (* === Case l1 ∈ filt === *)
  Cases_on `MEM l1 filt` >- (
    `l1 ∈ FDOM bse` by (imp_res_tac flookup_in_fdom >> metis_tac[]) >>
    `l1 ∈ FDOM sets` by metis_tac[pred_setTheory.IN_INSERT] >>
    Cases_on `l2 = vloc` >- (
      (* l2=vloc: mv_foldl_adds_vloc shows vloc ∈ als1 *)
      `∃als'. FLOOKUP (FOLDL (mv_fold_step vloc) bse filt) l1 = SOME als' ∧
              MEM vloc als'` by (irule mv_foldl_adds_vloc >> rw[]) >>
      `als1 = als'` by metis_tac[optionTheory.SOME_11] >> gvs[]) >>
    (* l2≠vloc: l2 was already in l1's alias list in sets *)
    `l2 ∈ FDOM sets` by metis_tac[pred_setTheory.IN_INSERT] >>
    `∃old_als. FLOOKUP sets l1 = SOME old_als ∧ MEM l2 old_als` by (
      Cases_on `FLOOKUP sets l1` >- fs[FLOOKUP_DEF] >>
      rw[] >>
      qpat_assum `wf_alias_sets _` (mp_tac o REWRITE_RULE [wf_alias_sets_def]) >>
      disch_then (fn th => mp_tac (Q.SPECL [`l1`, `l2`, `x'`] (CONJUNCT2 th))) >>
      rw[]) >>
    `FLOOKUP bse l1 = SOME old_als` by rw[Abbr `bse`, FLOOKUP_UPDATE] >>
    drule_all mv_foldl_preserves_mem >> strip_tac >>
    first_x_assum (qspecl_then [`filt`, `vloc`] strip_assume_tac) >>
    metis_tac[optionTheory.SOME_11]
  ) >>
  (* === Case l1 ∉ filt, l1 ≠ loc, l1 ≠ vloc === *)
  `FLOOKUP (FOLDL (mv_fold_step vloc) bse filt) l1 = FLOOKUP bse l1` by (
    irule mv_foldl_other >> rw[]) >>
  `FLOOKUP bse l1 = FLOOKUP sets l1` by rw[Abbr `bse`, FLOOKUP_UPDATE] >>
  `FLOOKUP sets l1 = SOME als1` by metis_tac[] >>
  Cases_on `l2 = vloc` >- (
    (* l2=vloc: l1 must be in filt (contradiction) *)
    `l1 ∈ FDOM sets` by fs[FLOOKUP_DEF] >>
    `may_overlap l1 loc` by metis_tac[] >>
    `may_overlap loc l1` by metis_tac[may_overlap_sym] >>
    `MEM l1 x` by (
      qpat_assum `wf_alias_sets _` (mp_tac o REWRITE_RULE [wf_alias_sets_def]) >>
      disch_then (fn th => mp_tac (Q.SPECL [`loc`, `l1`, `x`] (CONJUNCT2 th))) >>
      rw[]) >>
    `MEM l1 filt` by (
      simp_tac std_ss [Abbr `filt`, MEM_FILTER] >> metis_tac[]) >>
    metis_tac[]
  ) >>
  `l2 ∈ FDOM sets` by metis_tac[pred_setTheory.IN_INSERT] >>
  qpat_assum `wf_alias_sets _` (mp_tac o REWRITE_RULE [wf_alias_sets_def]) >>
  disch_then (fn th => mp_tac (Q.SPECL [`l1`, `l2`, `als1`] (CONJUNCT2 th))) >>
  rw[]
QED

(* Main theorem: combine correctness and completeness *)
Theorem ma_mark_volatile_preserves_wf:
  ∀sets loc vloc sets'.
    wf_alias_sets sets ∧
    ma_mark_volatile sets loc = (vloc, sets') ⇒
    wf_alias_sets sets'
Proof
  rw[ma_mark_volatile_def, LET_THM] >>
  Cases_on `FLOOKUP sets loc` >> gvs[] >>
  rw[mv_foldl_equiv] >>
  rw[wf_alias_sets_def] >>
  FIRST [
    irule (SIMP_RULE std_ss [LET_THM] mv_correctness) >>
      qexistsl_tac [`als`, `loc`, `sets`, `x`] >> gvs[],
    irule (SIMP_RULE std_ss [LET_THM] mv_completeness) >>
      qexistsl_tac [`l1`, `loc`, `sets`, `x`] >> gvs[] >>
      metis_tac[may_overlap_sym]
  ]
QED

(* Empty function produces empty alias sets *)
Theorem ma_analyze_empty[local]:
  ∀bp addr_sp fn.
    fn.fn_blocks = [] ⇒
    ma_analyze bp fn addr_sp = FEMPTY
Proof
  rw[ma_analyze_def, ma_analyze_blocks_def]
QED

(* ===== ma_may_alias characterization (local, subsumed by iff) ===== *)

Theorem ma_may_alias_volatile[local]:
  ∀sets loc1 loc2.
    loc1.ml_volatile ∨ loc2.ml_volatile ⇒
    (ma_may_alias sets loc1 loc2 ⇔ may_overlap loc1 loc2)
Proof
  rw[ma_may_alias_def]
QED

Theorem ma_may_alias_unknown[local]:
  ∀sets loc1 loc2.
    ¬loc1.ml_volatile ∧ ¬loc2.ml_volatile ∧
    (FLOOKUP sets loc1 = NONE ∨ FLOOKUP sets loc2 = NONE) ⇒
    (ma_may_alias sets loc1 loc2 ⇔ may_overlap loc1 loc2)
Proof
  rw[ma_may_alias_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* ===== ma_mark_volatile helpers ===== *)

Theorem ma_mark_volatile_is_volatile:
  ∀sets loc vloc sets'.
    ma_mark_volatile sets loc = (vloc, sets') ⇒
    vloc.ml_volatile
Proof
  rw[ma_mark_volatile_def, mk_volatile_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* ===== Soundness ===== *)

Theorem ma_may_alias_sound_proof:
  ∀sets loc1 loc2 s r1 r2.
    wf_alias_sets sets ∧
    ¬ma_may_alias sets loc1 loc2 ∧
    allocas_non_overlapping s ∧
    memloc_runtime_region loc1 s = SOME r1 ∧
    memloc_runtime_region loc2 s = SOME r2 ⇒
    regions_disjoint r1 r2
Proof
  cheat
QED

Theorem ma_may_alias_sound_no_alloca_proof:
  ∀sets loc1 loc2.
    wf_alias_sets sets ∧
    ¬ma_may_alias sets loc1 loc2 ∧
    loc1.ml_alloca = NONE ∧ loc2.ml_alloca = NONE ∧
    IS_SOME loc1.ml_offset ∧ IS_SOME loc1.ml_size ∧
    IS_SOME loc2.ml_offset ∧ IS_SOME loc2.ml_size ⇒
    regions_disjoint
      (THE loc1.ml_offset, THE loc1.ml_size)
      (THE loc2.ml_offset, THE loc2.ml_size)
Proof
  cheat
QED

Theorem bp_segment_from_ops_runtime_region_proof:
  ∀bp ops ml s.
    bp_ptr_sound bp s ∧
    bp_segment_from_ops bp ops = ml ∧
    ml_is_fixed ml ∧
    IS_SOME (eval_operand ops.iao_ofst s) ⇒
    ∃addr.
      eval_operand ops.iao_ofst s = SOME (n2w addr) ∧
      memloc_runtime_region ml s = SOME (addr, THE ml.ml_size)
Proof
  cheat
QED
