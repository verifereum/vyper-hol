(*
 * Generic Dataflow Analysis — Proofs
 *
 * TOP-LEVEL:
 *   df_analyze_fixpoint_proof       — worklist converges to fixpoint
 *   df_at_intra_transfer_proof      — within a block, transfer relates adjacent points
 *   df_at_inter_transfer_proof      — inter-block: fold input = join of neighbors
 *   df_boundary_eq_exit_proof       — boundary = exit value (proof-internal, not exported)
 *   df_analyze_invariant_proof      — lattice invariant preserved through analysis
 *   df_process_inflationary_proof   — lattice monotonicity → process inflationary
 *   df_process_deps_complete_proof  — CFG correctness → worklist deps complete
 *)

Theory dfAnalyzeProofs
Ancestors
  dfAnalyzeDefs worklistProofs cfgDefs cfgHelpers venomWf latticeDefs

(* --- DFS lemmas: dfs_pre and dfs_post visit the same nodes --- *)
(* Proved as SML vals using specialized induction + MP, since ho_match_mp_tac
   can't handle conjunction goals from mutual recursion induction principles. *)

(* Helper: specialize a mutual recursion induction principle and prove antecedent *)
fun dfs_ind_prove (ind : thm) (p0_q : term quotation) (p1_q : term quotation) (tac : tactic) =
  let val ind_s = SIMP_RULE std_ss [] (Q.SPECL [p0_q, p1_q] ind)
  in MP ind_s (prove(ind_s |> concl |> dest_imp |> #1, tac)) end;

(* FST(pre_walk) = FST(post_walk): both walks track the same visited set *)
val dfs_pre_post_fst = dfs_ind_prove dfs_pre_walk_ind
  `\succs visited lbl.
     FST (dfs_pre_walk succs visited lbl) =
     FST (dfs_post_walk succs visited lbl)`
  `\succs visited xs.
     FST (dfs_pre_walk_list succs visited xs) =
     FST (dfs_post_walk_list succs visited xs)`
  (rpt conj_tac
   >- (rpt gen_tac >> strip_tac >>
       simp[Once dfs_pre_walk_def, Once dfs_post_walk_def] >>
       Cases_on `MEM lbl visited` >> simp[] >>
       pairarg_tac >> simp[] >> pairarg_tac >> fs[])
   >- simp[Once dfs_pre_walk_def, Once dfs_post_walk_def]
   >- (rpt gen_tac >> strip_tac >>
       simp[Once dfs_pre_walk_def, Once dfs_post_walk_def] >>
       pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
       pairarg_tac >> simp[] >> pairarg_tac >> fs[] >>
       `v'' = FST (dfs_pre_walk_list succs v' ss)` by fs[] >>
       `v'⁴' = FST (dfs_pre_walk_list succs v'³' ss)` by fs[] >>
       fs[]));

(* visited ⊆ FST(walk): the walk only adds to the visited set *)
val dfs_fst_extends_visited = dfs_ind_prove dfs_pre_walk_ind
  `\succs visited lbl.
     !x. MEM x visited ==> MEM x (FST (dfs_pre_walk succs visited lbl))`
  `\succs visited xs.
     !x. MEM x visited ==> MEM x (FST (dfs_pre_walk_list succs visited xs))`
  (rpt conj_tac
   >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
       simp[Once dfs_pre_walk_def] >>
       Cases_on `MEM lbl visited` >> simp[] >>
       pairarg_tac >> simp[] >> strip_tac >>
       `MEM x (set_insert lbl visited)` by simp[set_insert_def] >>
       qpat_x_assum `dfs_pre_walk_list _ _ _ = _` mp_tac >>
       simp[] >> strip_tac >> fs[])
   >- simp[Once dfs_pre_walk_def]
   >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
       simp[Once dfs_pre_walk_def] >>
       pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
       strip_tac >>
       `MEM x (FST (dfs_pre_walk succs visited s))` by metis_tac[] >>
       `MEM x v'` by fs[] >>
       first_x_assum (qspecl_then [`v'`, `ords'`] mp_tac) >>
       simp[] >> metis_tac[]));

(* SND(pre_walk) ⊆ FST(pre_walk): output labels are all visited *)
val dfs_pre_snd_in_fst = dfs_ind_prove dfs_pre_walk_ind
  `\succs visited lbl.
     !x. MEM x (SND (dfs_pre_walk succs visited lbl)) ==>
         MEM x (FST (dfs_pre_walk succs visited lbl))`
  `\succs visited xs.
     !x. MEM x (SND (dfs_pre_walk_list succs visited xs)) ==>
         MEM x (FST (dfs_pre_walk_list succs visited xs))`
  (rpt conj_tac
   >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
       simp[Once dfs_pre_walk_def] >>
       Cases_on `MEM lbl visited` >> simp[] >>
       pairarg_tac >> simp[] >> strip_tac
       >- (* x = lbl: lbl ∈ set_insert lbl visited ⊆ vis2 *)
          (`FST (dfs_pre_walk succs visited lbl) = vis2` by
             (simp[Once dfs_pre_walk_def] >> pairarg_tac >> fs[]) >>
           rw[] >>
           mp_tac (CONJUNCT2 dfs_fst_extends_visited) >>
           disch_then (qspecl_then [`succs`, `set_insert lbl visited`,
             `fmap_lookup_list succs lbl`, `lbl`] mp_tac) >>
           simp[set_insert_def] >> fs[])
       >- (* MEM x orders: IH gives MEM x vis2 *)
          (`FST (dfs_pre_walk succs visited lbl) = vis2` by
             (simp[Once dfs_pre_walk_def] >> pairarg_tac >> fs[]) >>
           rw[] >>
           `MEM x (SND (dfs_pre_walk_list succs (set_insert lbl visited)
              (fmap_lookup_list succs lbl)))` by fs[] >>
           first_x_assum (drule_then drule) >> simp[]))
   >- simp[Once dfs_pre_walk_def]
   >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
       simp[Once dfs_pre_walk_def] >>
       pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
       `FST (dfs_pre_walk_list succs visited (s::ss)) = v''` by
         (simp[Once dfs_pre_walk_def] >> pairarg_tac >> simp[] >>
          pairarg_tac >> fs[]) >>
       simp[] >> strip_tac
       >- (* MEM x ords': IH1 gives MEM x v', extends to v'' *)
          (`MEM x (SND (dfs_pre_walk succs visited s))` by fs[] >>
           `MEM x (FST (dfs_pre_walk succs visited s))` by metis_tac[] >>
           `FST (dfs_pre_walk succs visited s) = v'` by fs[] >>
           `MEM x v'` by metis_tac[] >>
           mp_tac (CONJUNCT2 dfs_fst_extends_visited) >>
           disch_then (qspecl_then [`succs`, `v'`, `ss`, `x`] mp_tac) >>
           impl_tac >- simp[] >>
           `FST (dfs_pre_walk_list succs v' ss) = v''` by fs[] >>
           metis_tac[])
       >- (* MEM x ords'': IH0 gives MEM x v'' *)
          (first_x_assum (qspecl_then [`v'`, `ords'`] mp_tac) >> simp[] >>
           disch_then (qspec_then `x` mp_tac) >> simp[] >>
           `FST (dfs_pre_walk_list succs v' ss) = v''` by fs[] >>
           metis_tac[])));

(* FST(post_walk) \ visited ⊆ SND(post_walk): all newly visited nodes in output *)
val dfs_post_fst_in_snd = dfs_ind_prove dfs_post_walk_ind
  `\succs visited lbl.
     !x. MEM x (FST (dfs_post_walk succs visited lbl)) /\
         ~MEM x visited ==>
         MEM x (SND (dfs_post_walk succs visited lbl))`
  `\succs visited xs.
     !x. MEM x (FST (dfs_post_walk_list succs visited xs)) /\
         ~MEM x visited ==>
         MEM x (SND (dfs_post_walk_list succs visited xs))`
  (rpt conj_tac
   (* Walk case: SND = orders ++ [lbl], case split x=lbl vs IH *)
   >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
       simp[Once dfs_post_walk_def] >>
       Cases_on `MEM lbl visited` >> simp[] >>
       pairarg_tac >> simp[] >>
       strip_tac >>
       `SND (dfs_post_walk succs visited lbl) = orders ++ [lbl]` by
         (simp[Once dfs_post_walk_def] >> pairarg_tac >> fs[]) >>
       simp[listTheory.MEM_APPEND] >>
       Cases_on `x = lbl` >> simp[] >>
       `¬MEM x (set_insert lbl visited)` by fs[set_insert_def] >>
       `MEM x (FST (dfs_post_walk_list succs (set_insert lbl visited)
          (fmap_lookup_list succs lbl)))` by fs[] >>
       `MEM x (SND (dfs_post_walk_list succs (set_insert lbl visited)
          (fmap_lookup_list succs lbl)))` by metis_tac[] >>
       `SND (dfs_post_walk_list succs (set_insert lbl visited)
          (fmap_lookup_list succs lbl)) = orders` by fs[] >>
       fs[])
   (* Nil case *)
   >- simp[Once dfs_post_walk_def]
   (* Cons case: SND = ords' ++ ords'', case split MEM x v' *)
   >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
       simp[Once dfs_post_walk_def] >>
       pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
       strip_tac >>
       `SND (dfs_post_walk_list succs visited (s::ss)) = ords' ++ ords''` by
         (simp[Once dfs_post_walk_def] >> pairarg_tac >> simp[] >>
          pairarg_tac >> fs[]) >>
       simp[listTheory.MEM_APPEND] >>
       Cases_on `MEM x v'`
       >- (* MEM x v': IH1 gives MEM x ords' *)
          (`FST (dfs_post_walk succs visited s) = v'` by fs[] >>
           `MEM x (SND (dfs_post_walk succs visited s))` by metis_tac[] >>
           `SND (dfs_post_walk succs visited s) = ords'` by fs[] >> fs[])
       >- (* ¬MEM x v': IH0 gives MEM x ords'' *)
          (first_x_assum (qspecl_then [`v'`, `ords'`] mp_tac) >> simp[] >>
           disch_then (qspec_then `x` mp_tac) >>
           `FST (dfs_post_walk_list succs v' ss) = v''` by fs[] >>
           `SND (dfs_post_walk_list succs v' ss) = ords''` by fs[] >>
           simp[])));

(* Combined: MEM in dfs_pre ⇒ MEM in dfs_post, for cfg_analyze *)
Theorem cfg_dfs_pre_mem_post:
  !fn lbl.
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    MEM lbl (cfg_analyze fn).cfg_dfs_post
Proof
  rw[cfgDefsTheory.cfg_analyze_def] >>
  Cases_on `entry_block fn` >> fs[] >>
  pairarg_tac >> fs[] >> pairarg_tac >> fs[] >>
  (* Chain: SND(pre) ⊆ FST(pre) = FST(post) ⊆ SND(post) when visited=[] *)
  `MEM lbl (FST (dfs_pre_walk (build_succs fn.fn_blocks) [] x.bb_label))` by
    metis_tac[CONJUNCT1 dfs_pre_snd_in_fst, pairTheory.SND] >>
  `MEM lbl (FST (dfs_post_walk (build_succs fn.fn_blocks) [] x.bb_label))` by
    metis_tac[CONJUNCT1 dfs_pre_post_fst] >>
  metis_tac[CONJUNCT1 dfs_post_fst_in_snd, listTheory.MEM,
            pairTheory.FST, pairTheory.SND]
QED

(* At convergence, processing any block is a no-op.
   Preconditions are on the derived process function (df_process_block).
   Users derive these from lattice-level properties for their specific analysis. *)

(* KEY LEMMA: The boundary-based changed predicate is equivalent to
   process lbl st ≠ st for the new df_process_block (no inst update,
   conditional boundary update). This equivalence enables using the
   worklist theorems which require changed ⟺ ≠. *)
Theorem df_process_changed_equiv[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st.
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let changed = (λlbl (old:'a df_state) new.
                     df_boundary bottom new lbl <> df_boundary bottom old lbl) in
    changed lbl st (process lbl st) <=> process lbl st <> st
Proof
  rw[df_process_block_def, df_joined_val_def, df_boundary_def] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  simp[df_state_component_equality, finite_mapTheory.fmap_eq_flookup,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  CCONTR_TAC >> fs[] >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> fs[]
QED




(* Helper: FOLDL that only modifies ds_inst preserves ds_boundary *)
Theorem foldl_inst_only_boundary[local]:
  !lbls (f : 'a df_state -> string -> 'a df_state) acc.
    (!st lbl. (f st lbl).ds_boundary = st.ds_boundary) ==>
    (FOLDL f acc lbls).ds_boundary = acc.ds_boundary
Proof
  Induct >> simp[]
QED

(* Helper: df_populate_inst doesn't change ds_boundary *)
Theorem df_populate_inst_boundary[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st.
    (df_populate_inst dir bottom join transfer edge_transfer
       ctx entry_val cfg bbs lbls st).ds_boundary = st.ds_boundary
Proof
  rpt gen_tac >>
  simp[df_populate_inst_def] >>
  irule foldl_inst_only_boundary >>
  simp[LET_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[]
QED

(* Helper: process result depends only on ds_boundary *)
Theorem df_process_block_boundary_only[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st1 st2.
    st1.ds_boundary = st2.ds_boundary ==>
    (df_process_block dir bottom join transfer edge_transfer
       ctx entry_val cfg bbs lbl st1).ds_boundary =
    (df_process_block dir bottom join transfer edge_transfer
       ctx entry_val cfg bbs lbl st2).ds_boundary
Proof
  rpt strip_tac >>
  simp[df_process_block_def, df_joined_val_def, df_boundary_def] >>
  pairarg_tac >> simp[] >>
  rpt IF_CASES_TAC >> gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Helper: is_fixpoint passes through df_populate_inst *)
Theorem is_fixpoint_populate[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls
   all_lbls st.
    is_fixpoint (df_process_block dir bottom join transfer edge_transfer
                   ctx entry_val cfg bbs) all_lbls st ==>
    is_fixpoint (df_process_block dir bottom join transfer edge_transfer
                   ctx entry_val cfg bbs) all_lbls
      (df_populate_inst dir bottom join transfer edge_transfer
         ctx entry_val cfg bbs lbls st)
Proof
  REWRITE_TAC[worklistDefsTheory.is_fixpoint_def] >>
  rpt strip_tac >>
  simp[df_state_component_equality] >>
  (* process on (populate st) has same boundary as process on st *)
  `(df_process_block dir bottom join transfer edge_transfer ctx
      entry_val cfg bbs lbl
      (df_populate_inst dir bottom join transfer edge_transfer ctx
         entry_val cfg bbs lbls st)).ds_boundary =
   (df_process_block dir bottom join transfer edge_transfer ctx
      entry_val cfg bbs lbl st).ds_boundary` by
    (irule df_process_block_boundary_only >>
     simp[df_populate_inst_boundary]) >>
  (* process on (populate st) doesn't change ds_inst *)
  `(df_process_block dir bottom join transfer edge_transfer ctx
      entry_val cfg bbs lbl
      (df_populate_inst dir bottom join transfer edge_transfer ctx
         entry_val cfg bbs lbls st)).ds_inst =
   (df_populate_inst dir bottom join transfer edge_transfer ctx
      entry_val cfg bbs lbls st).ds_inst` by
    (simp[df_process_block_def, df_joined_val_def] >>
     pairarg_tac >> simp[] >> rpt IF_CASES_TAC >> simp[]) >>
  res_tac >> gvs[df_populate_inst_boundary, df_state_component_equality]
QED

Theorem df_analyze_fixpoint_proof:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let changed = (λlbl (old:'a df_state) new.
                     df_boundary bottom new lbl <> df_boundary bottom old lbl) in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let all_lbls = cfg.cfg_dfs_pre in
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete changed process deps
    ==>
      is_fixpoint process all_lbls
        (df_analyze dir bottom join transfer edge_transfer ctx entry_val fn)
Proof
  simp[LET_THM, df_analyze_def] >>
  rpt strip_tac >>
  irule is_fixpoint_populate >>
  irule wl_iterate_fixpoint_proof >>
  rpt conj_tac >> TRY (fs[] >> NO_TAC)
  >- (rpt gen_tac >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv) >>
      disch_then (qspecl_then [`dir`,`bottom`,`join`,`transfer`,
        `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
        `fn.fn_blocks`] mp_tac) >>
      simp[])
  >- (Cases_on `dir` >> simp[cfg_dfs_pre_mem_post])
  >- (MAP_EVERY qexists_tac [`P`,`b`,`leq`,`m`] >>
      Cases_on `entry_val` >> gvs[] >>
      rename1 `SOME ev` >> PairCases_on `ev` >> gvs[])
QED

(* Process-level fixpoint: uses per-step termination condition instead of
   bounded_measure. The key advantage is that the measure m only needs to
   increase when process actually changes the state, avoiding the inst_map
   vs boundary ordering problem that makes bounded_measure hard to prove. *)
Theorem df_analyze_fixpoint_process:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (m : 'a df_state -> num) b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let changed = (λlbl (old:'a df_state) new.
                     df_boundary bottom new lbl <> df_boundary bottom old lbl) in
    let deps = (case dir of Forward => cfg_succs_of cfg
                           | Backward => cfg_preds_of cfg) in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let all_lbls = cfg.cfg_dfs_pre in
      (!lbl st. P st /\ process lbl st <> st ==> m st < m (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. P x ==> m x <= b) /\
      wl_deps_complete changed process deps
    ==>
      is_fixpoint process all_lbls
        (df_analyze dir bottom join transfer edge_transfer ctx entry_val fn)
Proof
  simp[LET_THM, df_analyze_def] >>
  rpt strip_tac >>
  irule is_fixpoint_populate >>
  irule wl_iterate_fixpoint_process_proof >>
  rpt conj_tac >> TRY (fs[] >> NO_TAC)
  >- (rpt gen_tac >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv) >>
      disch_then (qspecl_then [`dir`,`bottom`,`join`,`transfer`,
        `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
        `fn.fn_blocks`] mp_tac) >>
      simp[])
  >- (MAP_EVERY qexists_tac [`P`,`b`,`m`] >>
      Cases_on `entry_val` >> gvs[] >>
      rename1 `SOME ev` >> PairCases_on `ev` >> gvs[])
  >- (rpt strip_tac >> Cases_on `dir` >> gvs[] >>
      MATCH_MP_TAC cfg_dfs_pre_mem_post >> gvs[])
QED


(* Restricted process-level fixpoint: measure/P conditions only required
   for valid_lbl labels. Caller provides valid_lbl and must show:
   - EVERY valid_lbl on the initial worklist (cfg_dfs_pre or cfg_dfs_post)
   - deps closure: valid_lbl lbl ==> EVERY valid_lbl (deps lbl)
   This allows analyses where non-block labels don't satisfy the measure. *)
Theorem df_analyze_fixpoint_process_restricted:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (m : 'a df_state -> num) b (P : 'a df_state -> bool)
   (valid_lbl : string -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let changed = (λlbl (old:'a df_state) new.
                     df_boundary bottom new lbl <> df_boundary bottom old lbl) in
    let deps = (case dir of Forward => cfg_succs_of cfg
                           | Backward => cfg_preds_of cfg) in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let all_lbls = cfg.cfg_dfs_pre in
    let wl0 = (case dir of Forward => cfg.cfg_dfs_pre
                          | Backward => cfg.cfg_dfs_post) in
      (!lbl st. valid_lbl lbl /\ P st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. valid_lbl lbl /\ P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. P x ==> m x <= b) /\
      wl_deps_complete changed process deps /\
      EVERY valid_lbl wl0 /\
      (!lbl. valid_lbl lbl ==> EVERY valid_lbl (deps lbl))
    ==>
      is_fixpoint process all_lbls
        (df_analyze dir bottom join transfer edge_transfer ctx entry_val fn)
Proof
  simp[LET_THM, df_analyze_def] >>
  rpt strip_tac >>
  irule is_fixpoint_populate >>
  irule wl_iterate_fixpoint_process_restricted >>
  rpt conj_tac >> TRY (fs[] >> NO_TAC)
  >- (rpt gen_tac >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv) >>
      disch_then (qspecl_then [`dir`,`bottom`,`join`,`transfer`,
        `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
        `fn.fn_blocks`] mp_tac) >>
      simp[])
  >- (rpt strip_tac >> Cases_on `dir` >> gvs[] >>
      MATCH_MP_TAC cfg_dfs_pre_mem_post >> gvs[])
  >- (MAP_EVERY qexists_tac [`P`,`b`,`m`,`valid_lbl`] >>
      Cases_on `entry_val` >> gvs[] >>
      rename1 `SOME ev` >> PairCases_on `ev` >> gvs[])
QED

(* --- DFS/CFG closure lemmas for restricted fixpoint --- *)

(* cfg_dfs_pre only contains block labels *)
Theorem cfg_dfs_pre_subset_fn_labels:
  !fn lbl. wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    MEM lbl (fn_labels fn)
Proof
  rw[cfgDefsTheory.cfg_analyze_def] >>
  Cases_on `entry_block fn` >> fs[] >>
  pairarg_tac >> fs[] >> pairarg_tac >> fs[] >>
  `(λa b. MEM b (fmap_lookup_list (build_succs fn.fn_blocks) a))^*
     x.bb_label lbl` by
    metis_tac[cfgHelpersTheory.dfs_pre_walk_sound_thm, pairTheory.SND] >>
  `MEM x fn.fn_blocks` by
    (fs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def,
        venomInstTheory.entry_block_def] >>
     Cases_on `fn.fn_blocks` >> fs[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def] >>
  `MEM x.bb_label (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (rw[listTheory.MEM_MAP] >> metis_tac[]) >>
  rw[venomInstTheory.fn_labels_def] >>
  metis_tac[cfgHelpersTheory.rtc_build_succs_closed,
            venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def,
            venomWfTheory.fn_succs_closed_def]
QED

(* fn_labels closed under cfg_succs_of for well-formed functions *)
Theorem fn_labels_succs_closed[local]:
  !fn lbl. wf_function fn /\ MEM lbl (fn_labels fn) ==>
    EVERY (\l. MEM l (fn_labels fn))
      (cfg_succs_of (cfg_analyze fn) lbl)
Proof
  rw[listTheory.EVERY_MEM] >> rpt strip_tac >>
  fs[wf_function_def, fn_succs_closed_def] >>
  `?bb. MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    (fs[venomInstTheory.fn_labels_def] >>
     metis_tac[listTheory.MEM_MAP]) >>
  `fmap_lookup_list (build_succs fn.fn_blocks) lbl = bb_succs bb` by
    (`ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
       fs[venomInstTheory.fn_labels_def] >>
     metis_tac[cfgHelpersTheory.cfg_succs_of_build_succs]) >>
  `MEM l (bb_succs bb)` by
    (fs[cfgDefsTheory.cfg_succs_of_def, cfgDefsTheory.cfg_analyze_def] >>
     Cases_on `entry_block fn` >> fs[] >>
     pairarg_tac >> fs[] >> pairarg_tac >> fs[]) >>
  metis_tac[]
QED

(* Forward analysis fixpoint: convenience theorem for well-formed functions.
   Automatically handles valid_lbl = MEM _ fn_labels, EVERY, and deps closure.
   Only requires measure/P for block labels. *)
Theorem df_analyze_fixpoint_forward:
  !(bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (m : 'a df_state -> num) b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Forward bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
      wf_function fn /\
      (!lbl st. MEM lbl (fn_labels fn) /\ P st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. MEM lbl (fn_labels fn) /\ P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. P x ==> m x <= b) /\
      wl_deps_complete
        (λlbl (old:'a df_state) new.
           df_boundary bottom new lbl <> df_boundary bottom old lbl)
        process (cfg_succs_of cfg)
    ==>
      is_fixpoint process cfg.cfg_dfs_pre
        (df_analyze Forward bottom join transfer edge_transfer ctx
                    entry_val fn)
Proof
  simp[LET_THM]
  \\ rpt strip_tac
  \\ mp_tac (SIMP_RULE std_ss [LET_THM] df_analyze_fixpoint_process_restricted)
  \\ simp[]
  \\ disch_then (qspecl_then [`Forward`,`bottom`,`join`,`transfer`,
       `edge_transfer`,`ctx`,`entry_val`,`fn`,`m`,`b`,`P`,
       `\lbl. MEM lbl (fn_labels fn)`] mp_tac)
  \\ simp[]
  \\ impl_tac
  >- (conj_tac
      >- (simp[listTheory.EVERY_MEM] >>
          metis_tac[cfg_dfs_pre_subset_fn_labels])
      >- (rpt strip_tac >>
          irule fn_labels_succs_closed >> fs[]))
  \\ simp[]
QED

(* Forward analysis state-level invariant: like df_analyze_fixpoint_forward
   but proves Q(result) instead of is_fixpoint. Automatically handles
   valid_lbl = MEM _ fn_labels. *)
Theorem df_analyze_invariant_forward:
  !(bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (m : 'a df_state -> num) b (Q : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Forward bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let changed = (λlbl (old:'a df_state) new.
                     df_boundary bottom new lbl <> df_boundary bottom old lbl) in
    let deps = cfg_succs_of cfg in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let st0' = (case entry_val of NONE => st0
                | SOME (lbl, v) =>
                    st0 with ds_boundary := st0.ds_boundary |+ (lbl, v)) in
    let wl0 = cfg.cfg_dfs_pre in
      wf_function fn /\
      (!lbl st. MEM lbl (fn_labels fn) /\ Q st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. MEM lbl (fn_labels fn) /\ Q st ==> Q (process lbl st)) /\
      Q st0' /\
      (!x. Q x ==> m x <= b)
    ==>
      Q (SND (wl_iterate changed process deps wl0 st0'))
Proof
  simp[LET_THM]
  \\ rpt strip_tac
  \\ ho_match_mp_tac (SIMP_RULE std_ss [LET_THM]
       wl_iterate_invariant_process_restricted)
  \\ qexistsl_tac [`m`, `b`, `\lbl. MEM lbl (fn_labels fn)`]
  \\ rpt conj_tac
  >- (rpt gen_tac >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv) >>
      disch_then (qspecl_then [`Forward`,`bottom`,`join`,`transfer`,
        `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
        `fn.fn_blocks`, `lbl`, `old`] mp_tac) >>
      metis_tac[])
  >- (BETA_TAC >> first_x_assum ACCEPT_TAC)
  >- (BETA_TAC >> first_x_assum ACCEPT_TAC)
  >- first_x_assum ACCEPT_TAC
  >- first_x_assum ACCEPT_TAC
  >- (simp_tac std_ss [listTheory.EVERY_MEM] >>
      metis_tac[cfg_dfs_pre_subset_fn_labels])
  >- (BETA_TAC >> rpt strip_tac >> irule fn_labels_succs_closed >> asm_rewrite_tac[])
QED


(* --- Backward analysis: closure lemmas and convenience wrappers --- *)

(* cfg_dfs_post only contains block labels *)
Theorem cfg_dfs_post_subset_fn_labels:
  !fn lbl. wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_post ==>
    MEM lbl (fn_labels fn)
Proof
  rw[cfgDefsTheory.cfg_analyze_def] >>
  Cases_on `entry_block fn` >> fs[] >>
  pairarg_tac >> fs[] >> pairarg_tac >> fs[] >>
  `(λa b. MEM b (fmap_lookup_list (build_succs fn.fn_blocks) a))^*
     x.bb_label lbl` by
    metis_tac[cfgHelpersTheory.dfs_post_walk_sound_thm, pairTheory.SND] >>
  `MEM x fn.fn_blocks` by
    (fs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def,
        venomInstTheory.entry_block_def] >>
     Cases_on `fn.fn_blocks` >> fs[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def] >>
  `MEM x.bb_label (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (rw[listTheory.MEM_MAP] >> metis_tac[]) >>
  rw[venomInstTheory.fn_labels_def] >>
  metis_tac[cfgHelpersTheory.rtc_build_succs_closed,
            venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def,
            venomWfTheory.fn_succs_closed_def]
QED

(* fn_labels closed under cfg_preds_of for well-formed functions *)
Theorem fn_labels_preds_closed:
  !fn lbl. wf_function fn /\ MEM lbl (fn_labels fn) ==>
    EVERY (\l. MEM l (fn_labels fn))
      (cfg_preds_of (cfg_analyze fn) lbl)
Proof
  rw[listTheory.EVERY_MEM] >> rpt strip_tac >>
  fs[cfgHelpersTheory.cfg_analyze_preds, cfgHelpersTheory.mem_build_preds] >>
  fs[venomInstTheory.fn_labels_def, listTheory.MEM_MAP] >>
  metis_tac[]
QED

(* Preds of any label are fn_labels — no wf_function or MEM needed *)
Theorem preds_subset_fn_labels:
  !fn lbl. EVERY (\l. MEM l (fn_labels fn))
             (cfg_preds_of (cfg_analyze fn) lbl)
Proof
  rw[listTheory.EVERY_MEM] >> rpt strip_tac >>
  fs[cfgHelpersTheory.cfg_analyze_preds, cfgHelpersTheory.mem_build_preds] >>
  fs[venomInstTheory.fn_labels_def, listTheory.MEM_MAP] >>
  metis_tac[]
QED

(* Backward analysis fixpoint: convenience theorem for well-formed functions *)
Theorem df_analyze_fixpoint_backward:
  !(bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (m : 'a df_state -> num) b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Backward bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
      wf_function fn /\
      (!lbl st. MEM lbl (fn_labels fn) /\ P st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. MEM lbl (fn_labels fn) /\ P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. P x ==> m x <= b) /\
      wl_deps_complete
        (λlbl (old:'a df_state) new.
           df_boundary bottom new lbl <> df_boundary bottom old lbl)
        process (cfg_preds_of cfg)
    ==>
      is_fixpoint process cfg.cfg_dfs_pre
        (df_analyze Backward bottom join transfer edge_transfer ctx
                    entry_val fn)
Proof
  simp[LET_THM]
  \\ rpt strip_tac
  \\ mp_tac (SIMP_RULE std_ss [LET_THM] df_analyze_fixpoint_process_restricted)
  \\ simp[]
  \\ disch_then (qspecl_then [`Backward`,`bottom`,`join`,`transfer`,
       `edge_transfer`,`ctx`,`entry_val`,`fn`,`m`,`b`,`P`,
       `\lbl. MEM lbl (fn_labels fn)`] mp_tac)
  \\ simp[] \\ impl_tac
  >- (conj_tac
      >- (simp[listTheory.EVERY_MEM] >>
          metis_tac[cfg_dfs_post_subset_fn_labels])
      >- (rpt strip_tac >>
          irule fn_labels_preds_closed >> fs[]))
  \\ simp[]
QED

(* Backward analysis state-level invariant *)
Theorem df_analyze_invariant_backward:
  !(bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (m : 'a df_state -> num) b (Q : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Backward bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let changed = (\lbl (old:'a df_state) new.
                     df_boundary bottom new lbl <> df_boundary bottom old lbl) in
    let deps = cfg_preds_of cfg in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let st0' = (case entry_val of NONE => st0
                | SOME (lbl, v) =>
                    st0 with ds_boundary := st0.ds_boundary |+ (lbl, v)) in
    let wl0 = cfg.cfg_dfs_post in
      wf_function fn /\
      (!lbl st. MEM lbl (fn_labels fn) /\ Q st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. MEM lbl (fn_labels fn) /\ Q st ==> Q (process lbl st)) /\
      Q st0' /\
      (!x. Q x ==> m x <= b)
    ==>
      Q (SND (wl_iterate changed process deps wl0 st0'))
Proof
  simp[LET_THM]
  \\ rpt strip_tac
  \\ ho_match_mp_tac (SIMP_RULE std_ss [LET_THM]
       wl_iterate_invariant_process_restricted)
  \\ qexistsl_tac [`m`, `b`, `\lbl. MEM lbl (fn_labels fn)`]
  \\ rpt conj_tac
  >- (rpt gen_tac >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv) >>
      disch_then (qspecl_then [`Backward`,`bottom`,`join`,`transfer`,
        `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
        `fn.fn_blocks`, `lbl`, `old`] mp_tac) >>
      metis_tac[])
  >- (BETA_TAC >> first_x_assum ACCEPT_TAC)
  >- (BETA_TAC >> first_x_assum ACCEPT_TAC)
  >- first_x_assum ACCEPT_TAC
  >- first_x_assum ACCEPT_TAC
  >- (simp_tac std_ss [listTheory.EVERY_MEM] >>
      metis_tac[cfg_dfs_post_subset_fn_labels])
  >- (BETA_TAC >> rpt strip_tac >> irule fn_labels_preds_closed >> asm_rewrite_tac[])
QED

(* Backward analysis state-level invariant: no wf_function required.
   Q must be preserved for ALL labels (not just fn_labels). *)
Theorem df_analyze_invariant_backward_nwf:
  !(bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (m : 'a df_state -> num) b (Q : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Backward bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let changed = (\lbl (old:'a df_state) new.
                     df_boundary bottom new lbl <> df_boundary bottom old lbl) in
    let deps = cfg_preds_of cfg in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let st0' = (case entry_val of NONE => st0
                | SOME (lbl, v) =>
                    st0 with ds_boundary := st0.ds_boundary |+ (lbl, v)) in
    let wl0 = cfg.cfg_dfs_post in
      (!lbl st. Q st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      Q st0' /\
      (!x. Q x ==> m x <= b)
    ==>
      Q (SND (wl_iterate changed process deps wl0 st0'))
Proof
  simp[LET_THM]
  \\ rpt strip_tac
  \\ ho_match_mp_tac (SIMP_RULE std_ss [LET_THM]
       wl_iterate_invariant_process_proof)
  \\ qexistsl_tac [`m`, `b`]
  \\ rpt conj_tac
  >- (rpt gen_tac >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv) >>
      disch_then (qspecl_then [`Backward`,`bottom`,`join`,`transfer`,
        `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
        `fn.fn_blocks`, `lbl`, `old`] mp_tac) >>
      metis_tac[])
  >- first_x_assum ACCEPT_TAC
  >- first_x_assum ACCEPT_TAC
  >- first_x_assum ACCEPT_TAC
  >- first_x_assum ACCEPT_TAC
QED

(* Backward analysis state-level invariant with valid_lbl restriction.
   Q only needs to be preserved for valid labels, but valid_lbl must
   cover dfs_post and be deps-closed. *)
Theorem df_analyze_invariant_backward_restricted:
  !(bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (m : 'a df_state -> num) b
   (Q : 'a df_state -> bool) (valid_lbl : string -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Backward bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let changed = (\lbl (old:'a df_state) new.
                     df_boundary bottom new lbl <> df_boundary bottom old lbl) in
    let deps = cfg_preds_of cfg in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let st0' = (case entry_val of NONE => st0
                | SOME (lbl, v) =>
                    st0 with ds_boundary := st0.ds_boundary |+ (lbl, v)) in
    let wl0 = cfg.cfg_dfs_post in
      (!lbl st. valid_lbl lbl /\ Q st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. valid_lbl lbl /\ Q st ==> Q (process lbl st)) /\
      Q st0' /\
      (!x. Q x ==> m x <= b) /\
      EVERY valid_lbl wl0 /\
      (!lbl. valid_lbl lbl ==>
             EVERY valid_lbl (deps lbl))
    ==>
      Q (SND (wl_iterate changed process deps wl0 st0'))
Proof
  simp[LET_THM]
  \\ rpt strip_tac
  \\ ho_match_mp_tac (SIMP_RULE std_ss [LET_THM]
       wl_iterate_invariant_process_restricted)
  \\ qexistsl_tac [`m`, `b`, `valid_lbl`]
  \\ rpt conj_tac
  >- (rpt gen_tac >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv) >>
      disch_then (qspecl_then [`Backward`,`bottom`,`join`,`transfer`,
        `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
        `fn.fn_blocks`, `lbl`, `old`] mp_tac) >>
      metis_tac[])
  >- first_x_assum ACCEPT_TAC
  >- first_x_assum ACCEPT_TAC
  >- first_x_assum ACCEPT_TAC
  >- first_x_assum ACCEPT_TAC
  >- first_x_assum ACCEPT_TAC
  >- first_x_assum ACCEPT_TAC
QED

(* ===== Fold helpers: structural properties of df_fold_forward/backward ===== *)

(* Preservation: forward fold preserves entries not at fold indices *)
Theorem df_fold_forward_preserves:
  !transfer lbl instrs idx acc inst_map fv im.
    df_fold_forward transfer lbl instrs idx acc inst_map = (fv, im) ==>
    !k v. FLOOKUP inst_map k = SOME v /\ (FST k <> lbl \/ SND k < idx) ==>
    FLOOKUP im k = SOME v
Proof
  Induct_on `instrs` >>
  rw[df_fold_forward_def, LET_THM, finite_mapTheory.FLOOKUP_UPDATE] >-
  (`k <> (lbl,idx)` by (Cases_on `k` >> simp[] >> strip_tac >> fs[]) >>
   simp[finite_mapTheory.FLOOKUP_UPDATE]) >>
  first_x_assum drule >> disch_then (qspecl_then [`k`, `v`] mp_tac) >>
  impl_tac >-
  (`k <> (lbl, idx)` by (Cases_on `k` >> simp[] >> strip_tac >> fs[]) >>
   simp[finite_mapTheory.FLOOKUP_UPDATE] >>
   Cases_on `FST k = lbl` >> simp[] >> fs[]) >>
  rw[]
QED

(* Generic invariant: forward fold preserves a pointwise property P *)
Theorem df_fold_forward_invariant:
  !instrs transfer lbl idx acc inst_map fv im P.
    df_fold_forward transfer lbl instrs idx acc inst_map = (fv, im) /\
    P acc /\
    (!k v. FLOOKUP inst_map k = SOME v ==> P v) /\
    (!inst v. MEM inst instrs /\ P v ==> P (transfer inst v)) ==>
    P fv /\ !k v. FLOOKUP im k = SOME v ==> P v
Proof
  Induct >> rpt strip_tac >> fs[df_fold_forward_def, LET_THM]
  (* Base: P fv = P acc *)
  >- rw[]
  (* Base: FLOOKUP (inst_map |+ ((lbl,idx),acc)) k = SOME v *)
  >- (rw[] >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
      Cases_on `(lbl,idx) = k` >> fs[] >> res_tac)
  (* Inductive: both P fv and P v — apply IH to recursive fold call *)
  >> (first_x_assum (qspecl_then [`transfer`, `lbl`, `idx+1`,
        `transfer h acc`, `inst_map |+ ((lbl,idx),acc)`,
        `fv`, `im`, `P`] mp_tac) >>
      impl_tac >- (
        rpt conj_tac
        >- rw[]
        >- (first_x_assum match_mp_tac >> rw[])
        >- (rw[finite_mapTheory.FLOOKUP_UPDATE] >>
            Cases_on `(lbl,idx) = k'` >> fs[] >> res_tac)
        >- (rpt strip_tac >> first_x_assum match_mp_tac >> rw[])
      ) >> metis_tac[])
QED

(* Generic invariant: forward fold from FEMPTY (df_fold_block Forward) *)
Theorem df_fold_block_forward_invariant:
  !transfer lbl instrs init_val fv im P.
    df_fold_block Forward transfer lbl instrs init_val = (fv, im) /\
    P init_val /\
    (!inst v. MEM inst instrs /\ P v ==> P (transfer inst v)) ==>
    P fv /\ !k v. FLOOKUP im k = SOME v ==> P v
Proof
  rw[df_fold_block_def] >>
  drule df_fold_forward_invariant >>
  disch_then (qspec_then `P` mp_tac) >>
  simp[finite_mapTheory.FLOOKUP_EMPTY] >> metis_tac[]
QED

(* Preservation: backward fold preserves entries not at fold indices *)
Theorem df_fold_backward_preserves:
  !transfer lbl instrs idx acc inst_map fv im.
    df_fold_backward transfer lbl instrs idx acc inst_map = (fv, im) ==>
    !k v. FLOOKUP inst_map k = SOME v /\ (FST k <> lbl \/ SND k < idx) ==>
    FLOOKUP im k = SOME v
Proof
  Induct_on `instrs` >>
  rw[df_fold_backward_def, LET_THM, finite_mapTheory.FLOOKUP_UPDATE] >-
  (`k <> (lbl,idx)` by (Cases_on `k` >> simp[] >> strip_tac >> fs[]) >>
   simp[finite_mapTheory.FLOOKUP_UPDATE]) >>
  pairarg_tac >> fs[] >>
  `k <> (lbl,idx)` by (Cases_on `k` >> simp[] >> strip_tac >> fs[]) >>
  `FLOOKUP (inst_map' |+ ((lbl,idx),transfer h acc')) k =
   FLOOKUP inst_map' k` by simp[finite_mapTheory.FLOOKUP_UPDATE] >> fs[] >>
  first_x_assum drule >> disch_then (qspecl_then [`k`, `v`] mp_tac) >>
  impl_tac >- (fs[] >> Cases_on `FST k = lbl` >> fs[]) >>
  rw[]
QED

(* Generalized forward: works with non-empty inst_map *)
Theorem df_fold_forward_at_gen:
  !transfer lbl instrs idx acc inst_map fv im.
    df_fold_forward transfer lbl instrs idx acc inst_map = (fv, im) /\
    (!k. k IN FDOM inst_map ==> FST k = lbl /\ SND k < idx) ==>
    FLOOKUP im (lbl, idx) = SOME acc /\
    (!i. i < LENGTH instrs ==>
      FLOOKUP im (lbl, idx + SUC i) =
        SOME (transfer (EL i instrs) (THE (FLOOKUP im (lbl, idx + i))))) /\
    fv = THE (FLOOKUP im (lbl, idx + LENGTH instrs))
Proof
  Induct_on `instrs`
  (* Base *)
  >- (rpt gen_tac >> strip_tac >>
      fs[df_fold_forward_def] >> rw[finite_mapTheory.FLOOKUP_UPDATE])
  (* Step: unfold, apply IH *)
  >> rpt gen_tac >> strip_tac >>
  fs[df_fold_forward_def, LET_THM] >>
  first_x_assum (qspecl_then [`transfer`, `lbl`, `idx+1`, `transfer h acc`,
    `inst_map |+ ((lbl,idx),acc)`, `fv`, `im`] mp_tac) >>
  impl_tac >- (rw[finite_mapTheory.FDOM_FUPDATE] >> res_tac >> fs[]) >>
  strip_tac >>
  `FLOOKUP im (lbl, idx) = SOME acc` by (
    mp_tac df_fold_forward_preserves >>
    disch_then drule >>
    disch_then (qspecl_then [`(lbl,idx)`, `acc`] mp_tac) >>
    simp[finite_mapTheory.FLOOKUP_UPDATE]) >>
  rpt conj_tac >- rw[]
  >- (rpt strip_tac >> Cases_on `i` >- fs[listTheory.EL]
      >> fs[listTheory.EL, arithmeticTheory.ADD1] >>
      first_x_assum (qspec_then `n` mp_tac) >> fs[])
  >- fs[arithmeticTheory.ADD1]
QED

(* Forward fold: entry value at idx, transfer relation for adjacent indices *)
Theorem df_fold_forward_at:
  !transfer lbl instrs idx acc fv im.
    df_fold_forward transfer lbl instrs idx acc FEMPTY = (fv, im) ==>
    FLOOKUP im (lbl, idx) = SOME acc /\
    (!i. i < LENGTH instrs ==>
      FLOOKUP im (lbl, idx + SUC i) =
        SOME (transfer (EL i instrs)
                       (THE (FLOOKUP im (lbl, idx + i))))) /\
    fv = THE (FLOOKUP im (lbl, idx + LENGTH instrs))
Proof
  rpt strip_tac >>
  mp_tac df_fold_forward_at_gen >>
  disch_then (qspecl_then [`transfer`, `lbl`, `instrs`, `idx`, `acc`,
    `FEMPTY`, `fv`, `im`] mp_tac) >>
  simp[finite_mapTheory.FDOM_FEMPTY]
QED

(* Generalized backward: works with non-empty inst_map *)
Theorem df_fold_backward_at_gen:
  !transfer lbl instrs idx acc inst_map fv im.
    df_fold_backward transfer lbl instrs idx acc inst_map = (fv, im) /\
    (!k. k IN FDOM inst_map ==> FST k = lbl /\ SND k < idx) ==>
    FLOOKUP im (lbl, idx + LENGTH instrs) = SOME acc /\
    (!i. i < LENGTH instrs ==>
      FLOOKUP im (lbl, idx + i) =
        SOME (transfer (EL i instrs)
                       (THE (FLOOKUP im (lbl, idx + SUC i))))) /\
    fv = THE (FLOOKUP im (lbl, idx))
Proof
  Induct_on `instrs`
  (* Base *)
  >- (rpt gen_tac >> strip_tac >>
      fs[df_fold_backward_def] >> rw[finite_mapTheory.FLOOKUP_UPDATE])
  (* Step: unfold, destructure pair, apply IH *)
  >> rpt gen_tac >> strip_tac >>
  fs[df_fold_backward_def, LET_THM] >>
  pairarg_tac >> fs[] >>
  first_x_assum (qspecl_then [`transfer`, `lbl`, `idx+1`, `acc`,
    `inst_map`, `acc'`, `inst_map'`] mp_tac) >>
  impl_tac >- (rw[] >> res_tac >> fs[]) >>
  strip_tac >>
  rpt conj_tac
  (* acc entry preserved through FUPDATE at idx *)
  >- (rw[finite_mapTheory.FLOOKUP_UPDATE] >> fs[arithmeticTheory.ADD1])
  (* Transfer relation *)
  >- (rpt strip_tac >> Cases_on `i`
      >- (simp[listTheory.EL] >> rw[finite_mapTheory.FLOOKUP_UPDATE] >> fs[])
      >> simp[listTheory.EL] >>
      `SUC n + idx <> idx` by simp[] >>
      `idx + SUC (SUC n) <> idx` by simp[] >>
      rw[finite_mapTheory.FLOOKUP_UPDATE] >>
      first_x_assum (qspec_then `n` mp_tac) >>
      simp[arithmeticTheory.ADD1])
  (* fv = THE(FLOOKUP im (lbl, idx)) *)
  >- rw[finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Backward fold: entry value at idx + LENGTH, transfer relation *)
Theorem df_fold_backward_at:
  !transfer lbl instrs idx acc fv im.
    df_fold_backward transfer lbl instrs idx acc FEMPTY = (fv, im) ==>
    FLOOKUP im (lbl, idx + LENGTH instrs) = SOME acc /\
    (!i. i < LENGTH instrs ==>
      FLOOKUP im (lbl, idx + i) =
        SOME (transfer (EL i instrs)
                       (THE (FLOOKUP im (lbl, idx + SUC i))))) /\
    fv = THE (FLOOKUP im (lbl, idx))
Proof
  rpt strip_tac >>
  mp_tac df_fold_backward_at_gen >>
  disch_then (qspecl_then [`transfer`, `lbl`, `instrs`, `idx`, `acc`,
    `FEMPTY`, `fv`, `im`] mp_tac) >>
  simp[finite_mapTheory.FDOM_FEMPTY]
QED

(* Helper: FOLDL with FUNION preserves submaps when domains are disjoint *)
Theorem foldl_funion_preserves_submap[local]:
  !lbls (f : string -> ('a |-> 'b)) acc m.
    m ⊑ acc /\
    (!l. MEM l lbls ==> DISJOINT (FDOM (f l)) (FDOM m)) ==>
    m ⊑ (FOLDL (\st' l. FUNION (f l) st') acc lbls)
Proof
  Induct
  \\ simp[]
  \\ rpt gen_tac \\ strip_tac
  \\ first_x_assum irule \\ rpt conj_tac
  >> metis_tac[finite_mapTheory.SUBMAP_FUNION, pred_setTheory.DISJOINT_SYM]
QED

(* Helper: FUNION in a left-biased FOLDL: if f lbl is added and no later
   f l overlaps its domain, then f lbl ⊑ result *)
Theorem foldl_funion_submap[local]:
  !lbls (f : string -> ('a |-> 'b)) acc lbl.
    MEM lbl lbls /\
    ALL_DISTINCT lbls /\
    (!l1 l2. MEM l1 lbls /\ MEM l2 lbls /\ l1 <> l2 ==>
             DISJOINT (FDOM (f l1)) (FDOM (f l2))) ==>
    f lbl ⊑ (FOLDL (\st' l. FUNION (f l) st') acc lbls)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (* lbl = h: f lbl is at the front *)
     (irule foldl_funion_preserves_submap >>
      simp[finite_mapTheory.SUBMAP_FUNION_ID] >>
      metis_tac[listTheory.MEM])
  
QED

(* At fixpoint, process lbl result = result implies the fold's inst_map
   entries are all present in result.ds_inst with the same values. *)


Theorem df_fold_forward_keys:
  !transfer lbl instrs idx acc inst_map final_val inst_map'.
    df_fold_forward transfer lbl instrs idx acc inst_map = (final_val, inst_map') ==>
    !k. FLOOKUP inst_map' k <> NONE /\ FLOOKUP inst_map k = NONE ==>
        FST k = lbl
Proof
  Induct_on `instrs` >>
  rw[df_fold_forward_def]
  >- (Cases_on `k` >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
      Cases_on `q = lbl /\ r = idx` >> fs[])
  >> first_x_assum drule >> disch_then (qspec_then `k` mp_tac) >>
     rw[] >> Cases_on `k` >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `q = lbl` >> fs[]
QED

Theorem df_fold_backward_keys:
  !transfer lbl instrs idx acc inst_map final_val inst_map'.
    df_fold_backward transfer lbl instrs idx acc inst_map = (final_val, inst_map') ==>
    !k. FLOOKUP inst_map' k <> NONE /\ FLOOKUP inst_map k = NONE ==>
        FST k = lbl
Proof
  Induct_on `instrs` >>
  rw[df_fold_backward_def]
  >- (Cases_on `k` >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
      Cases_on `q = lbl /\ r = idx` >> fs[])
  >> pairarg_tac >> fs[] >>
     Cases_on `k` >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `q = lbl` >> fs[] >>
     `FLOOKUP inst_map'' (q,r) <> NONE` by
       (qpat_x_assum `_ = inst_map'` (SUBST_ALL_TAC o SYM) >>
        fs[finite_mapTheory.FLOOKUP_UPDATE]) >>
     first_x_assum drule >> disch_then (qspec_then `(q,r)` mp_tac) >> fs[]
QED

Theorem df_fold_block_keys:
  !dir transfer lbl instrs init_val final_val inst_map.
    df_fold_block dir transfer lbl instrs init_val = (final_val, inst_map) ==>
    !k. FLOOKUP inst_map k <> NONE ==> FST k = lbl
Proof
  rw[df_fold_block_def] >> Cases_on `dir` >> fs[]
  >- (drule df_fold_forward_keys >> disch_then (qspec_then `k` mp_tac) >>
      rw[finite_mapTheory.FLOOKUP_DEF])
  >- (drule df_fold_backward_keys >> disch_then (qspec_then `k` mp_tac) >>
      rw[finite_mapTheory.FLOOKUP_DEF])
QED

Theorem populate_inst_ds_inst[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st.
    (df_populate_inst dir bottom join transfer edge_transfer
       ctx entry_val cfg bbs lbls st).ds_inst =
    FOLDL (\acc lbl.
      let joined = df_joined_val dir bottom join edge_transfer ctx
                                 entry_val cfg st lbl in
      let instrs = (case lookup_block lbl bbs of
                      NONE => [] | SOME bb => bb.bb_instructions) in
      let (final_val, inst_map) = df_fold_block dir (transfer ctx)
                                    lbl instrs joined in
      FUNION inst_map acc) st.ds_inst lbls
Proof
  Induct_on `lbls`
  \\ simp[df_populate_inst_def, LET_THM]
  \\ rpt gen_tac
  \\ pairarg_tac \\ simp[]
  \\ first_x_assum (qspecl_then [`dir`, `bottom`, `join`, `transfer`,
       `edge_transfer`, `ctx`, `entry_val`, `cfg`, `bbs`,
       `st with ds_inst := inst_map ⊌ st.ds_inst`] mp_tac)
  \\ simp_tac std_ss [df_joined_val_def, df_boundary_def, df_state_accfupds,
       df_populate_inst_def, LET_THM]
QED

Theorem fold_block_keys_disjoint[local]:
  !dir transfer lbl1 lbl2 instrs1 instrs2 init1 init2.
    lbl1 <> lbl2
    ==>
    DISJOINT (FDOM (SND (df_fold_block dir transfer lbl1 instrs1 init1)))
             (FDOM (SND (df_fold_block dir transfer lbl2 instrs2 init2)))
Proof
  rpt strip_tac
  \\ Cases_on `df_fold_block dir transfer lbl1 instrs1 init1`
  \\ Cases_on `df_fold_block dir transfer lbl2 instrs2 init2`
  \\ simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
          pred_setTheory.IN_INTER, pred_setTheory.NOT_IN_EMPTY]
  \\ rpt strip_tac
  \\ CCONTR_TAC \\ gvs[]
  \\ qpat_assum `df_fold_block _ _ lbl1 _ _ = _`
       (strip_assume_tac o MATCH_MP df_fold_block_keys)
  \\ qpat_assum `df_fold_block _ _ lbl2 _ _ = _`
       (strip_assume_tac o MATCH_MP df_fold_block_keys)
  \\ metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]
QED

Theorem populate_inst_submap[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st
   lbl bb.
    MEM lbl lbls /\
    ALL_DISTINCT lbls /\
    lookup_block lbl bbs = SOME bb
    ==>
    let joined = df_joined_val dir bottom join edge_transfer ctx
                               entry_val cfg st lbl in
    let (fv, im) = df_fold_block dir (transfer ctx) lbl
                      bb.bb_instructions joined in
    im ⊑ (df_populate_inst dir bottom join transfer edge_transfer
             ctx entry_val cfg bbs lbls st).ds_inst
Proof
  rpt gen_tac \\ simp[] \\ pairarg_tac \\ simp[] \\ strip_tac
  \\ simp[populate_inst_ds_inst]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ qho_match_abbrev_tac`_ SUBMAP FOLDL (λacc lbl. FUNION (f lbl) acc) _ _`
  \\ `im = f lbl` by simp[Abbr`f`]
  \\ pop_assum SUBST1_TAC
  \\ irule foldl_funion_submap
  \\ rw[Abbr`f`]
  \\ irule fold_block_keys_disjoint
  \\ simp[]
QED

Theorem df_boundary_populate[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st lbl.
    df_boundary bottom
      (df_populate_inst dir bottom join transfer edge_transfer ctx
         entry_val cfg bbs lbls st) lbl =
    df_boundary bottom st lbl
Proof
  rpt gen_tac
  \\ simp[df_boundary_def, df_populate_inst_boundary]
QED

Theorem df_joined_val_populate[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st lbl.
    df_joined_val dir bottom join edge_transfer ctx entry_val cfg
      (df_populate_inst dir bottom join transfer edge_transfer ctx
         entry_val cfg bbs lbls st) lbl =
    df_joined_val dir bottom join edge_transfer ctx entry_val cfg st lbl
Proof
  rpt gen_tac
  \\ simp[df_joined_val_def, df_boundary_def, df_populate_inst_boundary]
QED

Theorem df_analyze_inst_submap[local]:
  !dir bottom join transfer edge_transfer ctx entry_val fn lbl bb.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb
    ==>
    SND (df_fold_block dir (transfer ctx) lbl bb.bb_instructions
           (df_joined_val dir bottom join edge_transfer ctx entry_val
              (cfg_analyze fn)
              (df_analyze dir bottom join transfer edge_transfer ctx entry_val fn)
              lbl)) ⊑
    (df_analyze dir bottom join transfer edge_transfer ctx entry_val fn).ds_inst
Proof
  rpt strip_tac
  \\ simp_tac std_ss [df_analyze_def, LET_THM, direction_case_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ simp_tac std_ss [df_joined_val_populate]
  \\ irule (PairRules.PBETA_RULE (SIMP_RULE std_ss [LET_THM] populate_inst_submap))
  \\ fs[venomInstTheory.fn_labels_def]
  \\ conj_tac
  >- fs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]
  >- (drule_all cfg_dfs_pre_subset_fn_labels >>
      simp[pred_setTheory.SUBSET_DEF, venomInstTheory.fn_labels_def])
QED

Theorem df_fixpoint_fold_submap[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs
   lbl result all_lbls bb.
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
      is_fixpoint process all_lbls result /\
      MEM lbl all_lbls /\
      lookup_block lbl bbs = SOME bb
    ==>
      let joined = df_joined_val dir bottom join edge_transfer ctx
                                 entry_val cfg result lbl in
      let (fv, im) = df_fold_block dir (transfer ctx) lbl
                        bb.bb_instructions joined in
        df_boundary bottom result lbl =
          join (df_boundary bottom result lbl) fv
Proof
  rpt gen_tac \\ simp[] \\ pairarg_tac \\ simp[] \\ strip_tac
  \\ fs[worklistDefsTheory.is_fixpoint_def]
  \\ first_x_assum (qspec_then `lbl` mp_tac) \\ simp[]
  \\ simp_tac std_ss [df_process_block_def, LET_THM]
  \\ strip_tac
  \\ pop_assum mp_tac
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ asm_rewrite_tac[]
  \\ IF_CASES_TAC
  >- (strip_tac \\ gvs[])
  >- (strip_tac \\ gvs[df_state_component_equality] \\
      `FLOOKUP (result.ds_boundary |+ (lbl, join (df_boundary bottom result lbl) fv)) lbl =
       FLOOKUP result.ds_boundary lbl` by asm_rewrite_tac[] \\
      fs[finite_mapTheory.FLOOKUP_UPDATE, df_boundary_def] \\
      Cases_on `FLOOKUP result.ds_boundary lbl` \\ fs[])
QED




(* Helper: SUBMAP + FLOOKUP im (lbl,idx) = SOME v implies df_at = v *)
Theorem df_at_from_submap[local]:
  !im (st : 'a df_state) bottom lbl idx v.
    im ⊑ st.ds_inst /\ FLOOKUP im (lbl, idx) = SOME v ==>
    df_at bottom st lbl idx = v
Proof
  rw[df_at_def] >>
  fs[finite_mapTheory.SUBMAP_DEF, finite_mapTheory.FLOOKUP_DEF] >>
  metis_tac[]
QED

(* Combined helper: at fixpoint, df_at values follow the transfer relation.
   For Forward: df_at(lbl, 0) = joined, df_at(lbl, SUC i) = transfer(EL i instrs, df_at(lbl, i))
   For Backward: df_at(lbl, n) = joined, df_at(lbl, i) = transfer(EL i instrs, df_at(lbl, SUC i))
   Unifies df_fixpoint_fold_submap + df_fold_{forward,backward}_at + df_at_from_submap.
   Statement is LET-free for easier tactic application. *)
Theorem df_fixpoint_at[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs
   lbl result all_lbls bb instrs joined.
    let (fv, im) = df_fold_block dir (transfer ctx) lbl
                      bb.bb_instructions
                      (df_joined_val dir bottom join edge_transfer ctx
                                     entry_val cfg result lbl) in
    is_fixpoint
      (df_process_block dir bottom join transfer edge_transfer
                        ctx entry_val cfg bbs) all_lbls result /\
    MEM lbl all_lbls /\
    lookup_block lbl bbs = SOME bb /\
    instrs = bb.bb_instructions /\
    joined = df_joined_val dir bottom join edge_transfer ctx
                           entry_val cfg result lbl /\
    im ⊑ result.ds_inst
    ==>
      (dir = Forward ==>
        df_at bottom result lbl 0 = joined /\
        !i. i < LENGTH instrs ==>
          df_at bottom result lbl (SUC i) =
            transfer ctx (EL i instrs) (df_at bottom result lbl i)) /\
      (dir = Backward ==>
        df_at bottom result lbl (LENGTH instrs) = joined /\
        !i. i < LENGTH instrs ==>
          df_at bottom result lbl i =
            transfer ctx (EL i instrs) (df_at bottom result lbl (SUC i)))
Proof
  rpt gen_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  (* Get boundary absorption *)
  drule (SIMP_RULE std_ss [LET_THM] df_fixpoint_fold_submap) >>
  disch_then drule >>
  disch_then (qspec_then `bb` mp_tac) >>
  impl_tac >- fs[] >>
  simp[] >> strip_tac >>
  (* im ⊑ result.ds_inst is already an assumption *)
  Cases_on `dir` >> fs[df_fold_block_def] >> strip_tac >> rw[]
  (* Forward: entry *)
  >- (drule df_fold_forward_at >> strip_tac >>
      irule df_at_from_submap >> qexists_tac `im` >> fs[])
  (* Forward: transfer *)
  >- (drule df_fold_forward_at >> strip_tac >>
      `FLOOKUP im (lbl, SUC i) =
       SOME (transfer ctx (EL i bb.bb_instructions)
               (THE (FLOOKUP im (lbl, i))))` by
        (first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
      `df_at bottom result lbl (SUC i) =
       transfer ctx (EL i bb.bb_instructions) (THE (FLOOKUP im (lbl, i)))` by
        (irule df_at_from_submap >> qexists_tac `im` >> fs[]) >>
      `df_at bottom result lbl i = THE (FLOOKUP im (lbl, i))` by
        (irule df_at_from_submap >> qexists_tac `im` >>
         Cases_on `i` >- fs[]
         >- (first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
             strip_tac >> fs[])) >>
      fs[])
  (* Backward: entry *)
  >- (drule df_fold_backward_at >> strip_tac >>
      irule df_at_from_submap >> qexists_tac `im` >> fs[])
  (* Backward: transfer *)
  >- (drule df_fold_backward_at >> strip_tac >>
      `FLOOKUP im (lbl, SUC i) <> NONE` by
        (Cases_on `SUC i < LENGTH bb.bb_instructions`
         >- (first_x_assum (qspec_then `SUC i` mp_tac) >> simp[])
         >- (`SUC i = LENGTH bb.bb_instructions` by simp[] >> fs[])) >>
      `df_at bottom result lbl i =
       transfer ctx (EL i bb.bb_instructions)
         (THE (FLOOKUP im (lbl, SUC i)))` by
        (first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
         irule df_at_from_submap >> qexists_tac `im` >> fs[]) >>
      `df_at bottom result lbl (SUC i) = THE (FLOOKUP im (lbl, SUC i))` by
        (irule df_at_from_submap >> qexists_tac `im` >>
         Cases_on `SUC i < LENGTH bb.bb_instructions`
         >- (first_x_assum (qspec_then `SUC i` mp_tac) >> simp[] >>
             strip_tac >> fs[])
         >- (`SUC i = LENGTH bb.bb_instructions` by simp[] >> fs[])) >>
      fs[])
QED

(* Within a block, the transfer function relates adjacent instruction points.
   Direct corollary of df_fixpoint_at. *)
Theorem df_at_intra_transfer_proof:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn lbl (bb : basic_block) idx.
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let all_lbls = cfg.cfg_dfs_pre in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      wf_function fn /\
      is_fixpoint process all_lbls result /\
      MEM lbl all_lbls /\
      lookup_block lbl bbs = SOME bb /\
      SUC idx ≤ LENGTH bb.bb_instructions
    ==>
      (dir = Forward ==>
        df_at bottom result lbl (SUC idx) =
          transfer ctx (EL idx bb.bb_instructions)
                       (df_at bottom result lbl idx)) /\
      (dir = Backward ==>
        df_at bottom result lbl idx =
          transfer ctx (EL idx bb.bb_instructions)
                       (df_at bottom result lbl (SUC idx)))
Proof
  rpt gen_tac
  \\ simp_tac std_ss [LET_THM]
  \\ strip_tac
  \\ mp_tac (PairRules.PBETA_RULE (SIMP_RULE std_ss [LET_THM] df_fixpoint_at))
  \\ disch_then (qspecl_then [`dir`, `bottom`, `join`, `transfer`, `edge_transfer`,
       `ctx`, `entry_val`, `cfg_analyze fn`, `fn.fn_blocks`, `lbl`,
       `df_analyze dir bottom join transfer edge_transfer ctx entry_val fn`,
       `(cfg_analyze fn).cfg_dfs_pre`, `bb`, `bb.bb_instructions`] mp_tac)
  \\ simp_tac std_ss []
  \\ impl_tac
  >- (asm_rewrite_tac[] >> irule df_analyze_inst_submap >> asm_rewrite_tac[])
  \\ strip_tac \\ fs[]
QED

(* Inter-block transfer: at fixpoint, the fold input to a block equals the
   join of edge-transferred neighbor boundaries.
   Forward: df_at(lbl, 0) = FOLDL join bottom [edge_transfer(pred, lbl, boundary(pred))]
   Backward: df_at(lbl, n) = FOLDL join bottom [edge_transfer(succ, lbl, boundary(succ))]
   When a block has no neighbors, entry_val is used (or bottom if NONE). *)
Theorem df_at_inter_transfer_proof:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn lbl (bb : basic_block).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let all_lbls = cfg.cfg_dfs_pre in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
    let joined = df_joined_val dir bottom join edge_transfer ctx
                               entry_val cfg result lbl in
      wf_function fn /\
      is_fixpoint process all_lbls result /\
      MEM lbl all_lbls /\
      lookup_block lbl bbs = SOME bb
    ==>
      (dir = Forward ==>
        df_at bottom result lbl 0 = joined) /\
      (dir = Backward ==>
        df_at bottom result lbl (LENGTH bb.bb_instructions) = joined)
Proof
  rpt gen_tac
  \\ simp_tac std_ss [LET_THM]
  \\ strip_tac
  \\ mp_tac (PairRules.PBETA_RULE (SIMP_RULE std_ss [LET_THM] df_fixpoint_at))
  \\ disch_then (qspecl_then [`dir`, `bottom`, `join`, `transfer`, `edge_transfer`,
       `ctx`, `entry_val`, `cfg_analyze fn`, `fn.fn_blocks`, `lbl`,
       `df_analyze dir bottom join transfer edge_transfer ctx entry_val fn`,
       `(cfg_analyze fn).cfg_dfs_pre`, `bb`, `bb.bb_instructions`] mp_tac)
  \\ simp_tac std_ss []
  \\ impl_tac
  >- (asm_rewrite_tac[] >> irule df_analyze_inst_submap >> asm_rewrite_tac[])
  \\ strip_tac \\ fs[df_joined_val_def]
QED

(* Boundary fixpoint: at fixpoint, boundary(lbl) = join(boundary(lbl), exit_val).
   The "exit_val" is df_at at the block exit:
   Forward:  df_at(lbl, LENGTH instrs)
   Backward: df_at(lbl, 0)
   This captures: the block's output is already absorbed into the boundary. *)
Theorem df_boundary_fixpoint_proof:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn lbl (bb : basic_block).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let all_lbls = cfg.cfg_dfs_pre in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      wf_function fn /\
      is_fixpoint process all_lbls result /\
      MEM lbl all_lbls /\
      lookup_block lbl bbs = SOME bb
    ==>
      (dir = Forward ==>
        df_boundary bottom result lbl =
          join (df_boundary bottom result lbl)
               (df_at bottom result lbl (LENGTH bb.bb_instructions))) /\
      (dir = Backward ==>
        df_boundary bottom result lbl =
          join (df_boundary bottom result lbl)
               (df_at bottom result lbl 0))
Proof
  rpt gen_tac
  \\ simp_tac std_ss [LET_THM]
  \\ strip_tac
  (* Get boundary absorption + inst submap *)
  \\ mp_tac (PairRules.PBETA_RULE (SIMP_RULE std_ss [LET_THM] df_fixpoint_fold_submap))
  \\ disch_then (qspecl_then [`dir`,`bottom`,`join`,`transfer`,`edge_transfer`,
       `ctx`,`entry_val`,`cfg_analyze fn`,`fn.fn_blocks`,`lbl`,
       `df_analyze dir bottom join transfer edge_transfer ctx entry_val fn`,
       `(cfg_analyze fn).cfg_dfs_pre`,`bb`] mp_tac)
  \\ simp_tac std_ss []
  \\ impl_tac >- asm_rewrite_tac[]
  \\ strip_tac
  \\ mp_tac df_analyze_inst_submap
  \\ disch_then (qspecl_then [`dir`,`bottom`,`join`,`transfer`,`edge_transfer`,
       `ctx`,`entry_val`,`fn`,`lbl`,`bb`] mp_tac)
  \\ impl_tac >- asm_rewrite_tac[]
  \\ strip_tac
  (* Now have:
     - boundary absorption: boundary = join boundary (FST fold)
     - SND fold ⊑ result.ds_inst
     Need: boundary = join boundary (df_at exit_idx)
     Strategy: show FST fold = df_at exit_idx via df_fold_*_at + df_at_from_submap *)
  \\ Cases_on `df_fold_block dir (transfer ctx) lbl bb.bb_instructions
       (df_joined_val dir bottom join edge_transfer ctx entry_val
          (cfg_analyze fn)
          (df_analyze dir bottom join transfer edge_transfer ctx entry_val fn)
          lbl)`
  \\ fs[]
  \\ conj_tac \\ strip_tac \\ gvs[df_fold_block_def]
  (* Forward *)
  >- (drule df_fold_forward_at >> strip_tac >>
      `FLOOKUP r (lbl, LENGTH bb.bb_instructions) = SOME q` by
        (Cases_on `LENGTH bb.bb_instructions`
         >- (fs[] >> Cases_on `FLOOKUP r (lbl, 0)` >> fs[])
         >- (`FLOOKUP r (lbl, 0 + SUC n) <> NONE` by
               (first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
             Cases_on `FLOOKUP r (lbl, 0 + SUC n)` >> fs[])) >>
      `df_at bottom
         (df_analyze Forward bottom join transfer edge_transfer ctx
            entry_val fn) lbl (LENGTH bb.bb_instructions) = q` by
        (irule df_at_from_submap >> qexists_tac `r` >> fs[]) >>
      fs[])
  (* Backward *)
  >- (drule df_fold_backward_at >> strip_tac >>
      `FLOOKUP r (lbl, 0) = SOME q` by
        (Cases_on `LENGTH bb.bb_instructions`
         >- (fs[] >> Cases_on `FLOOKUP r (lbl, 0)` >> fs[])
         >- (`FLOOKUP r (lbl, 0) <> NONE` by
               (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
             Cases_on `FLOOKUP r (lbl, 0)` >> fs[])) >>
      `df_at bottom
         (df_analyze Backward bottom join transfer edge_transfer ctx
            entry_val fn) lbl 0 = q` by
        (irule df_at_from_submap >> qexists_tac `r` >> fs[]) >>
      fs[])
QED

(* Fold P-preservation: forward fold values all satisfy P *)
Theorem df_fold_forward_P:
  !transfer lbl instrs idx acc inst_map fv im.
    df_fold_forward transfer lbl instrs idx acc inst_map = (fv, im) /\
    P acc /\
    (!inst a. P a ==> P (transfer inst a)) /\
    (!k v. FLOOKUP inst_map k = SOME v ==> P v)
    ==>
    P fv /\ (!k v. FLOOKUP im k = SOME v ==> P v)
Proof
  Induct_on `instrs` >>
  rw[dfAnalyzeDefsTheory.df_fold_forward_def, LET_THM]
  (* base: P acc *)
  >- fs[]
  (* base: FLOOKUP (inst_map |+ (..)) k = SOME v ⇒ P v *)
  >- (Cases_on `k = (lbl,idx)` >>
      fs[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[])
  (* step: P fv *)
  >- (first_x_assum (qspecl_then [`transfer`, `lbl`, `idx+1`,
        `transfer h acc`, `inst_map |+ ((lbl,idx),acc)`, `fv`, `im`] mp_tac) >>
      impl_tac
      >- (rw[] >> Cases_on `k = (lbl,idx)` >>
          fs[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[])
      >> rw[])
  (* step: P v *)
  >- (first_x_assum (qspecl_then [`transfer`, `lbl`, `idx+1`,
        `transfer h acc`, `inst_map |+ ((lbl,idx),acc)`, `fv`, `im`] mp_tac) >>
      impl_tac
      >- (rw[] >> Cases_on `k' = (lbl,idx)` >>
          fs[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[])
      >> rw[] >> metis_tac[])
QED

(* Fold P-preservation: backward fold values all satisfy P *)
Theorem df_fold_backward_P:
  !transfer lbl instrs idx acc inst_map fv im.
    df_fold_backward transfer lbl instrs idx acc inst_map = (fv, im) /\
    P acc /\
    (!inst a. P a ==> P (transfer inst a)) /\
    (!k v. FLOOKUP inst_map k = SOME v ==> P v)
    ==>
    P fv /\ (!k v. FLOOKUP im k = SOME v ==> P v)
Proof
  Induct_on `instrs` >> rpt gen_tac >> strip_tac
  (* base case *)
  >- (fs[dfAnalyzeDefsTheory.df_fold_backward_def, LET_THM] >> rw[] >>
      Cases_on `k = (lbl,idx)` >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
      metis_tac[])
  (* step case *)
  >> fs[dfAnalyzeDefsTheory.df_fold_backward_def, LET_THM] >>
     pairarg_tac >> fs[] >> rw[]
     (* P (transfer h acc') *)
     >- (qpat_x_assum `!transfer lbl idx acc inst_map fv im. _`
           (qspecl_then [`transfer`, `lbl`, `idx+1`, `acc`, `inst_map`,
                         `acc'`, `inst_map'`] mp_tac) >>
         rw[] >> res_tac >> fs[])
     (* FLOOKUP (inst_map' |+ ...) k = SOME v ⇒ P v *)
     >> qpat_x_assum `!transfer lbl idx acc inst_map fv im. _`
          (qspecl_then [`transfer`, `lbl`, `idx+1`, `acc`, `inst_map`,
                        `acc'`, `inst_map'`] mp_tac) >>
        rw[] >> Cases_on `k = (lbl,idx)` >>
        fs[finite_mapTheory.FLOOKUP_UPDATE] >> res_tac >> metis_tac[]
QED

(* Fold block P-preservation: unified forward/backward *)
Theorem df_fold_block_P:
  !dir transfer lbl instrs init_val fv im.
    df_fold_block dir transfer lbl instrs init_val = (fv, im) /\
    P init_val /\
    (!inst a. P a ==> P (transfer inst a))
    ==>
    P fv /\ (!k v. FLOOKUP im k = SOME v ==> P v)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dir` >> fs[dfAnalyzeDefsTheory.df_fold_block_def] >>
  (drule df_fold_forward_P ORELSE drule df_fold_backward_P) >>
  disch_then ho_match_mp_tac >> rw[finite_mapTheory.FLOOKUP_DEF]
QED

(* FOLDL preserves P with generalized accumulator *)
Theorem foldl_preserves_P[local]:
  !f xs (a:'a). P a /\ (!x y. P x /\ P y ==> P (f x y)) /\
    EVERY P xs ==> P (FOLDL f a xs)
Proof
  gen_tac >> Induct >> rw[]
QED

(* P for case xs of [] => bottom | _::_ => FOLDL join bottom xs *)
Theorem case_foldl_P[local]:
  !xs. P bottom /\ (!a b. P a /\ P b ==> P (join a b)) /\ EVERY P xs ==>
    P (case xs of [] => bottom | v2::v3 => FOLDL join bottom xs)
Proof
  Cases >> rw[] >> irule foldl_preserves_P >> fs[]
QED

(* df_process_block preserves element-level P for inst and boundary maps *)
(* Helper: df_process_block doesn't change ds_inst *)

(* Helper: df_process_block preserves P for boundary values. *)
Theorem df_process_P[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st.
    P bottom /\
    (case entry_val of NONE => T | SOME (lbl, v) => P v) /\
    (!a b. P a /\ P b ==> P (join a b)) /\
    (!inst a. P a ==> P (transfer ctx inst a)) /\
    (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
    (!k v. FLOOKUP st.ds_inst k = SOME v ==> P v) /\
    (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v)
    ==>
    (!k v. FLOOKUP (df_process_block dir bottom join transfer edge_transfer
                      ctx entry_val cfg bbs lbl st).ds_inst k = SOME v
           ==> P v) /\
    (!k v. FLOOKUP (df_process_block dir bottom join transfer edge_transfer
                      ctx entry_val cfg bbs lbl st).ds_boundary k = SOME v
           ==> P v)
Proof
  rpt gen_tac >> strip_tac >>
  simp[df_process_block_def, df_joined_val_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
  (* THEN: unchanged, trivial *)
  >- (rpt strip_tac >> res_tac)
  (* ELSE: both boundary and inst updated — use old proof structure *)
  \\ `!nbr. P (edge_transfer ctx nbr lbl (df_boundary bottom st nbr))` by
    (rw[df_boundary_def] >>
     Cases_on `FLOOKUP st.ds_boundary nbr` >> fs[] >> res_tac >> fs[])
  \\ `!nbrs. EVERY P (MAP (\nbr. edge_transfer ctx nbr lbl
      (df_boundary bottom st nbr)) nbrs)` by
    (Induct >> rw[])
  \\ `!l nbr. P (edge_transfer ctx nbr l (df_boundary bottom st nbr))` by
    (rpt gen_tac >>
     qpat_x_assum `!src dst a. P a ==> P (edge_transfer _ _ _ _)` irule >>
     rw[df_boundary_def] >>
     Cases_on `FLOOKUP st.ds_boundary nbr` >> fs[] >> res_tac >> fs[])
  \\ `!l. EVERY P (MAP (\nbr. edge_transfer ctx nbr l
       (df_boundary bottom st nbr))
       (case dir of Forward => cfg_preds_of cfg l
                   | Backward => cfg_succs_of cfg l))` by
    (gen_tac >> simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM])
  \\ qmatch_asmsub_abbrev_tac `df_fold_block _ _ _ _ joined_val`
  \\ sg `P joined_val`
  >- (qunabbrev_tac `joined_val` >>
      Cases_on `entry_val` >> simp[]
      >- (irule case_foldl_P >> fs[])
      >> Cases_on `x` >> simp[] >>
      IF_CASES_TAC >> simp[]
      >- (qpat_x_assum `lbl = _` (SUBST_ALL_TAC o SYM) >>
          qpat_x_assum `!a b. P a /\ P b ==> P (join a b)`
            (fn th => irule th >> assume_tac th) >>
          conj_tac
          >- (qpat_x_assum `case _ of NONE => T | _ => _` mp_tac >> simp[])
          >> irule case_foldl_P >> fs[] >>
          simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM])
      >> irule case_foldl_P >> fs[])
  \\ drule_all df_fold_block_P >> strip_tac
  \\ conj_tac
  >- (rw[finite_mapTheory.FLOOKUP_FUNION] >>
      Cases_on `FLOOKUP inst_map k` >> fs[] >> metis_tac[])
  \\ rw[finite_mapTheory.FLOOKUP_UPDATE] >>
     fs[df_boundary_def] >>
     Cases_on `FLOOKUP st.ds_boundary k` >> fs[] >> metis_tac[]
QED

(* Helper: FOLDL join base ls preserves P *)
Theorem foldl_join_P[local]:
  !ls base join.
    P base /\ EVERY P ls /\ (!a b. P a /\ P b ==> P (join a b))
    ==> P (FOLDL join base ls)
Proof
  Induct >> simp[listTheory.EVERY_DEF]
QED

(* Helper: every edge_transfer of a boundary value satisfies P *)
Theorem map_edge_transfer_P[local]:
  !nbrs bottom edge_transfer ctx lbl st.
    P bottom /\
    (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
    (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v)
    ==>
    EVERY P (MAP (\nbr. edge_transfer ctx nbr lbl
                          (df_boundary bottom st nbr)) nbrs)
Proof
  Induct >> simp[listTheory.EVERY_DEF] >> rpt strip_tac
  >- (qpat_x_assum `!src dst a. _` irule >>
      Cases_on `FLOOKUP st.ds_boundary h` >>
      simp[df_boundary_def] >> res_tac)
  >- (qpat_x_assum `!bottom edge_transfer ctx lbl st. _` irule >>
      fs[] >> rpt strip_tac >> res_tac)
QED

(* Helper: P holds for df_joined_val *)
Theorem df_joined_val_P:
  !dir bottom join edge_transfer ctx entry_val cfg st lbl.
    P bottom /\
    (case entry_val of NONE => T | SOME (lbl, v) => P v) /\
    (!a b. P a /\ P b ==> P (join a b)) /\
    (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
    (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v)
    ==>
    P (df_joined_val dir bottom join edge_transfer ctx entry_val cfg st lbl)
Proof
  rpt gen_tac \\ strip_tac
  \\ sg `EVERY P (MAP (\nbr. edge_transfer ctx nbr lbl
                     (df_boundary bottom st nbr))
               (case dir of Forward => cfg_preds_of cfg lbl
                           | Backward => cfg_succs_of cfg lbl))`
  >- (MATCH_MP_TAC map_edge_transfer_P >> rpt strip_tac >> fs[] >> res_tac)
  \\ simp[df_joined_val_def]
  \\ qabbrev_tac `edge_vals = MAP (\nbr. edge_transfer ctx nbr lbl
                     (df_boundary bottom st nbr))
               (case dir of Forward => cfg_preds_of cfg lbl
                           | Backward => cfg_succs_of cfg lbl)`
  \\ sg `EVERY P edge_vals`
  >- fs[Abbr `edge_vals`]
  \\ Cases_on `entry_val` \\ simp[]
  >- (Cases_on `edge_vals` \\ simp[]
      \\ MATCH_MP_TAC foldl_join_P \\ fs[])
  \\ rename1 `SOME ev` \\ PairCases_on `ev` \\ gvs[]
  \\ IF_CASES_TAC \\ gvs[]
  >- (qpat_assum `!a b. P a /\ P b ==> P (join a b)` irule
      \\ conj_tac >- gvs[]
      \\ Cases_on `edge_vals` \\ gvs[]
      \\ MATCH_MP_TAC foldl_join_P \\ fs[])
  >- (Cases_on `edge_vals` \\ gvs[]
      \\ MATCH_MP_TAC foldl_join_P \\ fs[])
QED


Theorem foldl_fupdate_flookup:
  !ls (m : 'a |-> 'b) bot.
    (!k v. FLOOKUP m k = SOME v ==> v = bot) ==>
    !k v. FLOOKUP (FOLDL (\m l. m |+ (l, bot)) m ls) k = SOME v ==> v = bot
Proof
  Induct >> rw[] >>
  first_x_assum (qspecl_then [`m |+ (h, bot)`, `bot`] mp_tac) >>
  impl_tac >- (rw[finite_mapTheory.FLOOKUP_UPDATE] >> res_tac) >>
  disch_then (qspecl_then [`k`, `v`] mp_tac) >> rw[]
QED

Theorem foldl_fempty_val:
  !ls bot k v.
    FLOOKUP (FOLDL (\m l. m |+ (l, bot)) FEMPTY ls) k = SOME v ==> v = bot
Proof
  rw[] >>
  mp_tac (Q.SPECL [`ls`, `FEMPTY`, `bot`] foldl_fupdate_flookup) >>
  impl_tac >- rw[finite_mapTheory.FLOOKUP_DEF] >>
  disch_then drule >> rw[]
QED

(* Generic: FOLDL preserves an inst-map property when each step does *)
Theorem foldl_ds_inst_P[local]:
  !xs f init.
    (!st x. (!k v. FLOOKUP st.ds_inst k = SOME v ==> P v) ==>
            (!k v. FLOOKUP (f st x).ds_inst k = SOME v ==> P v)) /\
    (!k v. FLOOKUP init.ds_inst k = SOME v ==> P v)
    ==>
    (!k v. FLOOKUP (FOLDL f init xs).ds_inst k = SOME v ==> P v)
Proof
  Induct_on `xs` >> rpt strip_tac >> fs[]
  >- res_tac
  \\ first_x_assum (qspecl_then [`f`, `f init h`] mp_tac)
  \\ impl_tac
  >- (fs[] >> rpt strip_tac >> res_tac)
  \\ strip_tac >> res_tac
QED

(* Helper: FOLDL of FUNION-based block processing preserves inst P.
   The fold reads boundaries from a FIXED state `bst`, not the accumulator. *)
Theorem foldl_block_inst_P[local]:
  !lbls acc dir bottom join transfer edge_transfer ctx entry_val cfg bbs bst.
    P bottom /\
    (case entry_val of NONE => T | SOME (lbl, v) => P v) /\
    (!a b. P a /\ P b ==> P (join a b)) /\
    (!inst a. P a ==> P (transfer ctx inst a)) /\
    (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
    (!k v. FLOOKUP bst.ds_boundary k = SOME v ==> P v) /\
    (!k v. FLOOKUP acc.ds_inst k = SOME v ==> P v)
    ==>
    (!k v. FLOOKUP (FOLDL (\st' lbl.
      let joined = df_joined_val dir bottom join edge_transfer ctx
                                 entry_val cfg bst lbl in
      let instrs = case lookup_block lbl bbs of
                     NONE => [] | SOME bb => bb.bb_instructions in
      let (final_val, inst_map) =
        df_fold_block dir (transfer ctx) lbl instrs joined in
      st' with ds_inst := FUNION inst_map st'.ds_inst) acc lbls).ds_inst
       k = SOME v ==> P v)
Proof
  rpt gen_tac \\ strip_tac
  \\ match_mp_tac foldl_ds_inst_P
  \\ reverse conj_tac >- fs[]
  \\ rpt strip_tac
  \\ qpat_x_assum `FLOOKUP _.ds_inst _ = SOME _` mp_tac
  \\ simp[LET_THM]
  \\ pairarg_tac \\ simp[finite_mapTheory.FLOOKUP_FUNION]
  \\ CASE_TAC \\ simp[]
  >- (strip_tac >> res_tac)
  \\ strip_tac
  \\ `P (df_joined_val dir bottom join edge_transfer ctx
                       entry_val cfg bst x)` by
       (match_mp_tac df_joined_val_P \\ rpt conj_tac \\ first_x_assum ACCEPT_TAC)
  \\ drule_all df_fold_block_P
  \\ strip_tac \\ gvs[] \\ res_tac
QED

(* Helper: df_populate_inst preserves P for all inst values. *)
Theorem populate_inst_P:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st.
    P bottom /\
    (case entry_val of NONE => T | SOME (lbl, v) => P v) /\
    (!a b. P a /\ P b ==> P (join a b)) /\
    (!inst a. P a ==> P (transfer ctx inst a)) /\
    (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
    (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v) /\
    (!k v. FLOOKUP st.ds_inst k = SOME v ==> P v)
    ==>
    (!k v. FLOOKUP (df_populate_inst dir bottom join transfer edge_transfer
                      ctx entry_val cfg bbs lbls st).ds_inst k = SOME v
           ==> P v)
Proof
  rpt gen_tac \\ strip_tac
  \\ PURE_ONCE_REWRITE_TAC [df_populate_inst_def]
  \\ match_mp_tac foldl_block_inst_P
  \\ rpt conj_tac \\ first_x_assum ACCEPT_TAC
QED

(* Boundary-only invariant: weaker than df_analyze_invariant — only needs
   P closed under join (not transfer/edge_transfer). Useful when P describes
   a property of boundary values that transfer may violate (e.g. "sublist of
   all_vars" for vardef, where transfer adds new variables).

   Key: boundary(lbl) is only ever updated to join(old_boundary, final_val).
   If P(old_boundary), then P(join(old_boundary, anything)) by the hypothesis
   ∀a b. P a ⇒ P (join a b). So P is preserved for all boundary values. *)

(* Helper: df_process_block doesn't modify ds_inst *)
Theorem df_process_block_inst_unchanged[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st.
    (df_process_block dir bottom join transfer edge_transfer
       ctx entry_val cfg bbs lbl st).ds_inst = st.ds_inst
Proof
  rpt gen_tac >> simp[df_process_block_def] >>
  pairarg_tac >> simp[] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem df_process_boundary_P[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st P.
    P bottom /\
    (case entry_val of NONE => T | SOME (lbl, v) => P v) /\
    (!a b. P a ==> P (join a b)) /\
    (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v)
    ==>
    (!k v. FLOOKUP (df_process_block dir bottom join transfer edge_transfer
                      ctx entry_val cfg bbs lbl st).ds_boundary k = SOME v
           ==> P v)
Proof
  rpt gen_tac \\ strip_tac
  \\ simp_tac std_ss [df_process_block_def, LET_THM]
  \\ pairarg_tac \\ asm_rewrite_tac[]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ IF_CASES_TAC
  >- metis_tac[] >>
  simp[] >>
  reverse $ rw[finite_mapTheory.FLOOKUP_UPDATE]
  >- metis_tac[] >>
  last_x_assum irule >>
  simp_tac std_ss [df_boundary_def] >>
  Cases_on `FLOOKUP st.ds_boundary k` >> simp[] >> metis_tac[]
QED

Theorem df_analyze_boundary_invariant:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (P : 'a -> bool)
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (Q : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a ==> P (join a b)) /\
      (* convergence *)
      (!lbl st. Q st ==> leq st (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure Q leq m b
    ==>
      (!lbl. P (df_boundary bottom result lbl))
Proof
  rpt gen_tac
  \\ simp_tac std_ss [LET_THM]
  \\ strip_tac
  \\ CONV_TAC (REWRITE_CONV [df_analyze_def, LET_THM, direction_case_def])
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ PURE_REWRITE_TAC [df_boundary_populate]
  \\ gen_tac
  \\ qmatch_goalsub_abbrev_tac`wl_iterate changed process deps wl0 st0`
  \\ qho_match_abbrev_tac`P (df_boundary bottom swli lbl)`
  \\ `(λst. Q st ∧ ∀lbl. P (df_boundary bottom st lbl)) swli`
     suffices_by simp[]
  \\ qunabbrev_tac`swli`
  \\ irule wl_iterate_invariant_proof
  \\ simp[]
  (* 1. initial: Q st0 ∧ ∀lbl. P (df_boundary bottom st0 lbl) *)
  \\ conj_tac
  >- (simp[Abbr`st0`] >>
      conj_tac
      >- (BasicProvers.every_case_tac >> first_x_assum ACCEPT_TAC)
      >- (gen_tac >> simp[df_boundary_def] >>
          BasicProvers.every_case_tac >>
          gvs[init_df_state_def, finite_mapTheory.FLOOKUP_UPDATE,
              CaseEq"bool"] >>
          imp_res_tac foldl_fempty_val >> gvs[]))
  (* 2. changed ⟺ ≠ *)
  \\ conj_tac
  >- (simp[Abbr`changed`, Abbr`process`] >>
      rpt gen_tac >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv) >>
      disch_then (qspecl_then [`dir`,`bottom`,`join`,`transfer`,
        `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
        `fn.fn_blocks`, `lbl`, `st`] mp_tac) >>
      simp[])
  (* 3. preservation *)
  \\ conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      `∀k v. FLOOKUP (process lbl st).ds_boundary k = SOME v ⇒ P v` by
        (rpt strip_tac >>
         irule df_process_boundary_P >>
         goal_assum $ drule_then drule >>
         goal_assum $ drule_at Any >>
         gvs[Abbr`process`] >>
         goal_assum $ drule_at Any >>
         qx_gen_tac`lk` >> gen_tac >>
         first_x_assum(qspec_then`lk`mp_tac) >>
         simp[df_boundary_def] >>
         CASE_TAC >> rw[] >> rw[]) >>
      simp_tac std_ss [df_boundary_def] >>
      reverse CASE_TAC >- res_tac >> simp[])
  (* 4. measure *)
  \\ qexistsl_tac [`b`, `leq`, `m`]
  \\ simp[Abbr`process`, bounded_measure_def]
  \\ gvs[bounded_measure_def]
QED

(* Inst invariant: all inst values in the analysis result satisfy P.
   Uses populate_inst_P + combined wl_iterate invariant showing boundary P
   and ds_inst = FEMPTY are maintained throughout the worklist iteration. *)
Theorem df_analyze_inst_invariant[local]:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (P : 'a -> bool)
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (Q : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a ==> P (join a b)) /\
      (!inst a. P a ==> P (transfer ctx inst a)) /\
      (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
      (!lbl st. Q st ==> leq st (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure Q leq m b
    ==>
      (!k v. FLOOKUP result.ds_inst k = SOME v ==> P v)
Proof
  rpt gen_tac \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ `!a b. P a /\ P b ==> P (join a b)` by metis_tac[]
  \\ CONV_TAC (REWRITE_CONV [df_analyze_def, LET_THM, direction_case_def])
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ match_mp_tac populate_inst_P
  \\ qmatch_goalsub_abbrev_tac`wl_iterate changed process deps wl0 init_st`
  (* Suffice: combined invariant implies populate_inst_P's preconditions *)
  \\ `(!lbl. P (df_boundary bottom
        (SND (wl_iterate changed process deps wl0 init_st)) lbl)) /\
      (SND (wl_iterate changed process deps wl0 init_st)).ds_inst = FEMPTY`
     suffices_by (
       strip_tac \\ rpt conj_tac
       \\ TRY (first_x_assum ACCEPT_TAC)
       (* boundary *)
       >- (rpt strip_tac
           \\ first_x_assum (qspec_then `k` mp_tac)
           \\ simp[df_boundary_def]
           \\ CASE_TAC \\ simp[] \\ metis_tac[])
       (* inst *)
       \\ gvs[finite_mapTheory.FLOOKUP_DEF])
  (* Prove combined invariant via wl_iterate_invariant_proof *)
  \\ `(\st. Q st /\ (!lbl. P (df_boundary bottom st lbl)) /\
            st.ds_inst = FEMPTY)
      (SND (wl_iterate changed process deps wl0 init_st))` suffices_by (strip_tac >> gvs[])
  \\ irule wl_iterate_invariant_proof \\ simp[]
  (* 1. initial *)
  \\ conj_tac
  >- (simp[Abbr`init_st`] >> rpt conj_tac
      >- (BasicProvers.every_case_tac >> first_x_assum ACCEPT_TAC)
      >- (gen_tac >> simp[df_boundary_def] >>
          BasicProvers.every_case_tac >>
          gvs[init_df_state_def, finite_mapTheory.FLOOKUP_UPDATE,
              CaseEq"bool"] >>
          imp_res_tac foldl_fempty_val >> gvs[])
      >- (BasicProvers.every_case_tac >> simp[init_df_state_def]))
  (* 2. changed <=> <> *)
  \\ conj_tac
  >- (simp[Abbr`changed`, Abbr`process`] >>
      rpt gen_tac >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv) >>
      disch_then (qspecl_then [`dir`,`bottom`,`join`,`transfer`,
        `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
        `fn.fn_blocks`, `lbl`, `st`] mp_tac) >>
      simp[])
  (* 3. preservation *)
  \\ conj_tac
  >- (rpt gen_tac >> simp[] >> strip_tac >> conj_tac
      (* boundary P preserved *)
      >- (gen_tac >>
          `!k v. FLOOKUP (process lbl st).ds_boundary k = SOME v ==> P v` by
            (rpt strip_tac >>
             irule df_process_boundary_P >>
             goal_assum $ drule_then drule >>
             goal_assum $ drule_at Any >>
             gvs[Abbr`process`] >>
             goal_assum $ drule_at Any >>
             qx_gen_tac`lk` >> gen_tac >>
             first_x_assum(qspec_then`lk`mp_tac) >>
             simp[df_boundary_def] >>
             CASE_TAC >> rw[] >> rw[]) >>
          simp_tac std_ss [df_boundary_def] >>
          reverse CASE_TAC >- res_tac >> simp[])
      (* ds_inst preserved *)
      >- simp[Abbr`process`, df_process_block_inst_unchanged])
  (* 4. bounded_measure *)
  \\ qexistsl_tac [`b`, `leq`, `m`]
  \\ simp[Abbr`process`, bounded_measure_def]
  \\ gvs[bounded_measure_def]
QED

(* Lattice invariant: if P holds for bottom, is closed under join/transfer/
   edge_transfer, then P holds for all values in the analysis result.
   Requires convergence so WHILE result is well-defined. *)
Theorem df_analyze_invariant_proof:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (P : 'a -> bool)
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (Q : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      (* element-level closure *)
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a ==> P (join a b)) /\
      (!inst a. P a ==> P (transfer ctx inst a)) /\
      (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
      (* convergence *)
      (!lbl st. Q st ==> leq st (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure Q leq m b
    ==>
      (!lbl idx. P (df_at bottom result lbl idx)) /\
      (!lbl. P (df_boundary bottom result lbl))
Proof
  rpt gen_tac
  \\ simp_tac std_ss [LET_THM]
  \\ strip_tac
  (* Boundary part: use df_analyze_boundary_invariant *)
  \\ (fn (asl, gl) =>
    let val boundary_gl = snd (dest_conj gl)
        val thm = PART_MATCH (snd o dest_imp)
                    (SIMP_RULE std_ss [LET_THM] df_analyze_boundary_invariant)
                    boundary_gl
        val (ant, _) = dest_imp (concl thm)
        val conj_thm = TAC_PROOF((asl, ant),
                         rpt conj_tac >> first_x_assum ACCEPT_TAC)
    in STRIP_ASSUME_TAC (MP thm conj_thm) (asl, gl) end)
  \\ conj_tac
  (* Inst part: use df_analyze_inst_invariant *)
  >- (rpt gen_tac \\ simp[df_at_def] \\ CASE_TAC >- simp[]
      \\ `!k' v'. FLOOKUP (df_analyze dir bottom join transfer edge_transfer
                     ctx entry_val fn).ds_inst k' = SOME v' ==> P v'`
           suffices_by (disch_then drule >> simp[])
      \\ (fn (asl, gl) =>
        let val thm = PART_MATCH (snd o dest_imp)
                        (SIMP_RULE std_ss [LET_THM] df_analyze_inst_invariant)
                        gl
            val (ant, _) = dest_imp (concl thm)
            val conj_thm = TAC_PROOF((asl, ant),
                             rpt conj_tac >> first_x_assum ACCEPT_TAC)
        in ACCEPT_TAC (MP thm conj_thm) (asl, gl) end))
  (* Boundary part already proved *)
  \\ first_x_assum ACCEPT_TAC
QED

(* Bilateral boundary P: like df_process_boundary_P but uses bilateral join
   (P a ∧ P b ⟹ P (join a b)) instead of unilateral (P a ⟹ P (join a b)).
   Needs transfer and edge_transfer to preserve P so that final_val has P. *)
Theorem df_process_boundary_P_bilateral[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st P.
    P bottom /\
    (case entry_val of NONE => T | SOME (lbl, v) => P v) /\
    (!a b. P a /\ P b ==> P (join a b)) /\
    (!inst a. P a ==> P (transfer ctx inst a)) /\
    (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
    (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v)
    ==>
    (!k v. FLOOKUP (df_process_block dir bottom join transfer edge_transfer
                      ctx entry_val cfg bbs lbl st).ds_boundary k = SOME v
           ==> P v)
Proof
  rpt gen_tac \\ strip_tac
  \\ simp_tac std_ss [df_process_block_def, LET_THM]
  \\ pairarg_tac \\ asm_rewrite_tac[]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ IF_CASES_TAC
  >- metis_tac[]
  \\ simp[]
  \\ rpt gen_tac
  \\ simp_tac std_ss [finite_mapTheory.FLOOKUP_UPDATE]
  \\ IF_CASES_TAC
  >- (* k = lbl: updated boundary *)
     (strip_tac \\ gvs[]
      \\ qpat_assum `!a b. P a /\ P b ==> P (join a b)` irule
      \\ conj_tac
      >- (simp_tac std_ss [df_boundary_def]
          \\ Cases_on `FLOOKUP st.ds_boundary k` \\ simp[]
          \\ metis_tac[])
      \\ (* P final_val *)
      `P (df_joined_val dir bottom join edge_transfer ctx entry_val cfg st k)` by
        (match_mp_tac df_joined_val_P
         \\ rpt conj_tac \\ first_x_assum ACCEPT_TAC)
      \\ drule_all df_fold_block_P \\ simp[])
  >- (* k ≠ lbl: unchanged boundary *)
     metis_tac[]
QED

(* Bilateral boundary invariant: like df_analyze_boundary_invariant but uses
   bilateral join hypothesis (!a b. P a /\ P b ==> P (join a b)) instead of
   unilateral (!a b. P a ==> P (join a b)). Useful for properties like
   cf_keys_ok where join(NONE, b) = b makes unilateral impossible.
   Does NOT prove inst invariant — derive that locally using df_at step
   equations + boundary result + transfer preservation. *)
Theorem df_analyze_boundary_invariant_bilateral:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (P : 'a -> bool)
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (Q : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a /\ P b ==> P (join a b)) /\
      (!inst a. P a ==> P (transfer ctx inst a)) /\
      (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
      (!lbl st. Q st ==> leq st (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure Q leq m b
    ==>
      (!lbl. P (df_boundary bottom result lbl))
Proof
  rpt gen_tac
  \\ simp_tac std_ss [LET_THM]
  \\ strip_tac
  \\ CONV_TAC (REWRITE_CONV [df_analyze_def, LET_THM, direction_case_def])
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ PURE_REWRITE_TAC [df_boundary_populate]
  \\ gen_tac
  \\ qmatch_goalsub_abbrev_tac`wl_iterate changed process deps wl0 st0`
  \\ qho_match_abbrev_tac`P (df_boundary bottom swli lbl)`
  \\ `(λst. Q st ∧ ∀lbl. P (df_boundary bottom st lbl)) swli`
     suffices_by simp[]
  \\ qunabbrev_tac`swli`
  \\ irule wl_iterate_invariant_proof
  \\ simp[]
  (* 1. initial *)
  \\ conj_tac
  >- (simp[Abbr`st0`] >>
      conj_tac
      >- (BasicProvers.every_case_tac >> first_x_assum ACCEPT_TAC)
      >- (gen_tac >> simp[df_boundary_def] >>
          BasicProvers.every_case_tac >>
          gvs[init_df_state_def, finite_mapTheory.FLOOKUP_UPDATE,
              CaseEq"bool"] >>
          imp_res_tac foldl_fempty_val >> gvs[]))
  (* 2. changed ⟺ ≠ *)
  \\ conj_tac
  >- (simp[Abbr`changed`, Abbr`process`] >>
      rpt gen_tac >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv) >>
      disch_then (qspecl_then [`dir`,`bottom`,`join`,`transfer`,
        `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
        `fn.fn_blocks`, `lbl`, `st`] mp_tac) >>
      simp[])
  (* 3. preservation — using bilateral *)
  \\ conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      `∀k v. FLOOKUP (process lbl st).ds_boundary k = SOME v ⇒ P v` by
        (simp[Abbr`process`] >>
         match_mp_tac df_process_boundary_P_bilateral >>
         rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC) >>
         qx_gen_tac`lk` >> gen_tac >>
         first_x_assum(qspec_then`lk`mp_tac) >>
         simp[df_boundary_def] >>
         CASE_TAC >> rw[] >> rw[]) >>
      simp_tac std_ss [df_boundary_def] >>
      reverse CASE_TAC >- res_tac >> simp[])
  (* 4. measure *)
  \\ qexistsl_tac [`b`, `leq`, `m`]
  \\ simp[Abbr`process`, bounded_measure_def]
  \\ gvs[bounded_measure_def]
QED

(* Process-level boundary invariant: like df_analyze_boundary_invariant but
   uses process-level termination instead of bounded_measure. *)
Theorem df_analyze_boundary_invariant_process:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (P : 'a -> bool)
   (m : 'a df_state -> num) b (Q : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a ==> P (join a b)) /\
      (* convergence — process-level *)
      (!lbl st. Q st /\ process lbl st <> st ==> m st < m (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. Q x ==> m x <= b)
    ==>
      (!lbl. P (df_boundary bottom result lbl))
Proof
  rpt gen_tac
  \\ simp_tac std_ss [LET_THM]
  \\ strip_tac
  \\ CONV_TAC (REWRITE_CONV [df_analyze_def, LET_THM, direction_case_def])
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ PURE_REWRITE_TAC [df_boundary_populate]
  \\ gen_tac
  \\ qmatch_goalsub_abbrev_tac`wl_iterate changed process deps wl0 st0`
  \\ qho_match_abbrev_tac`P (df_boundary bottom swli lbl)`
  \\ `(λst. Q st ∧ ∀lbl. P (df_boundary bottom st lbl)) swli`
     suffices_by simp[]
  \\ qunabbrev_tac`swli`
  \\ irule wl_iterate_invariant_process_proof
  \\ simp[]
  (* 1. initial *)
  \\ conj_tac
  >- (simp[Abbr`st0`] >>
      conj_tac
      >- (BasicProvers.every_case_tac >> first_x_assum ACCEPT_TAC)
      >- (gen_tac >> simp[df_boundary_def] >>
          BasicProvers.every_case_tac >>
          gvs[init_df_state_def, finite_mapTheory.FLOOKUP_UPDATE,
              CaseEq"bool"] >>
          imp_res_tac foldl_fempty_val >> gvs[]))
  (* 2. changed *)
  \\ conj_tac
  >- (simp[Abbr`changed`, Abbr`process`] >>
      rpt gen_tac >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv) >>
      disch_then (qspecl_then [`dir`,`bottom`,`join`,`transfer`,
        `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
        `fn.fn_blocks`, `lbl`, `st`] mp_tac) >>
      simp[])
  (* 3. preservation *)
  \\ conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      `∀k v. FLOOKUP (process lbl st).ds_boundary k = SOME v ⇒ P v` by
        (rpt strip_tac >>
         irule df_process_boundary_P >>
         goal_assum $ drule_then drule >>
         goal_assum $ drule_at Any >>
         gvs[Abbr`process`] >>
         goal_assum $ drule_at Any >>
         qx_gen_tac`lk` >> gen_tac >>
         first_x_assum(qspec_then`lk`mp_tac) >>
         simp[df_boundary_def] >>
         CASE_TAC >> rw[] >> rw[]) >>
      simp_tac std_ss [df_boundary_def] >>
      reverse CASE_TAC >- res_tac >> simp[])
  (* 4. measure *)
  \\ qexistsl_tac [`b`, `m`]
  \\ simp[Abbr`process`]
QED

(* Restricted boundary invariant: like df_analyze_boundary_invariant_process
   but Q only needs to be preserved for valid labels. *)
Theorem df_analyze_boundary_invariant_restricted:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (P : 'a -> bool)
   (m : 'a df_state -> num) b (Q : 'a df_state -> bool)
   (valid_lbl : string -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a ==> P (join a b)) /\
      (* convergence — restricted *)
      (!lbl st. valid_lbl lbl /\ Q st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. valid_lbl lbl /\ Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. Q x ==> m x <= b) /\
      EVERY valid_lbl (case dir of
        Forward => cfg.cfg_dfs_pre | Backward => cfg.cfg_dfs_post) /\
      (!lbl. valid_lbl lbl ==>
        EVERY valid_lbl (case dir of
          Forward => cfg_succs_of cfg lbl
        | Backward => cfg_preds_of cfg lbl))
    ==>
      (!lbl. P (df_boundary bottom result lbl))
Proof
  rpt gen_tac
  \\ simp_tac std_ss [LET_THM]
  \\ strip_tac
  \\ CONV_TAC (REWRITE_CONV [df_analyze_def, LET_THM, direction_case_def])
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ PURE_REWRITE_TAC [df_boundary_populate]
  \\ gen_tac
  \\ qmatch_goalsub_abbrev_tac`wl_iterate changed process deps wl0 st0`
  \\ qho_match_abbrev_tac`P (df_boundary bottom swli lbl)`
  \\ `(λst. Q st ∧ ∀lbl. P (df_boundary bottom st lbl)) swli`
     suffices_by simp[]
  \\ qunabbrev_tac`swli`
  \\ irule wl_iterate_invariant_process_restricted
  \\ simp[]
  (* 1. initial *)
  \\ conj_tac
  >- (simp[Abbr`st0`] >>
      conj_tac
      >- (BasicProvers.every_case_tac >> first_x_assum ACCEPT_TAC)
      >- (gen_tac >> simp[df_boundary_def] >>
          BasicProvers.every_case_tac >>
          gvs[init_df_state_def, finite_mapTheory.FLOOKUP_UPDATE,
              CaseEq"bool"] >>
          imp_res_tac foldl_fempty_val >> gvs[]))
  (* 2. changed *)
  \\ conj_tac
  >- (simp[Abbr`changed`, Abbr`process`] >>
      rpt gen_tac >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv) >>
      disch_then (qspecl_then [`dir`,`bottom`,`join`,`transfer`,
        `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
        `fn.fn_blocks`, `lbl`, `st`] mp_tac) >>
      simp[])
  (* 3. existentials *)
  \\ qexistsl_tac [`b`, `m`, `valid_lbl`]
  \\ simp[Abbr`process`, Abbr`deps`, Abbr`wl0`]
  \\ rpt strip_tac
  \\ TRY (first_x_assum irule >> asm_rewrite_tac[] >> NO_TAC)
  (* boundary-P preservation *)
  >- (mp_tac (SIMP_RULE std_ss [] df_process_boundary_P)
      \\ disch_then (qspecl_then [`dir`,`bottom`,`join`,`transfer`,
           `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
           `fn.fn_blocks`,`lbl`,`st`,`P`] mp_tac)
      \\ impl_tac
      >- (asm_rewrite_tac[] >> rpt strip_tac >>
          first_x_assum (qspec_then `k` mp_tac) >>
          simp[df_boundary_def])
      \\ strip_tac
      \\ simp_tac std_ss [df_boundary_def]
      \\ reverse CASE_TAC >- res_tac
      \\ simp[])
  (* deps closure *)
  \\ Cases_on `dir` >> gvs[]
QED

(* Lattice-to-process lifting: join-upper-bound implies df_process_block
   is inflationary w.r.t. the pointwise boundary ordering.
   Processing block lbl sets boundary(lbl) := join old final_val, which
   is ≥ old by the upper-bound property. Other boundaries are unchanged.
   Only boundary values are tracked — inst values are overwritten
   on each processing and are fully determined by boundaries at fixpoint. *)
Theorem df_process_inflationary_proof:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val cfg bbs (elem_leq : 'a -> 'a -> bool).
    reflexive elem_leq /\
    (!a b. elem_leq a (join a b))
  ==>
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let leq = (λst1 st2.
      (!lbl. elem_leq (df_boundary bottom st1 lbl)
                       (df_boundary bottom st2 lbl))) in
    !lbl st. leq st (process lbl st)
Proof
  rw[df_process_block_def, df_joined_val_def, df_boundary_def] >>
  pairarg_tac >> rw[] >>
  Cases_on `lbl = lbl'` >>
  fs[finite_mapTheory.FLOOKUP_UPDATE, relationTheory.reflexive_def]
QED

(* Helper: df_process_block only modifies boundary(lbl) and inst entries for lbl.
   For any other label l ≠ lbl, boundary(l) is unchanged.
   Also, the new boundary is join(old, final_val), so
   re-processing with the same fold input yields join(join(old, fv), fv) = join(old, fv)
   by absorption, making the boundary update a no-op. *)

(* Helper: characterize process output structurally *)
Theorem df_process_block_boundary[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st l.
    l <> lbl ==>
    df_boundary bottom
      (df_process_block dir bottom join transfer edge_transfer
                        ctx entry_val cfg bbs lbl st) l =
    df_boundary bottom st l
Proof
  rw[df_process_block_def, df_joined_val_def, df_boundary_def] >>
  pairarg_tac >> rw[finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Helper: inst_map from df_fold_block only has keys with FST = lbl *)



(* Helper: ds_inst of df_populate_inst is a FOLDL of FUNIONs *)

(* Helper: inst_map domains are disjoint for different labels *)

(* Key lemma: populate produces inst submap for each label *)


(* Helper: if b ≠ lbl and lbl ∉ neighbors(b) and process b st = st,
   then process b (process lbl st) = process lbl st.
   Key structural lemma for deps_complete. *)


(* CFG correctness → worklist deps complete.
   For forward: deps = succs. When processing A changes its boundary,
   successors of A (which read A's boundary) need reprocessing.
   For backward: deps = preds, symmetric argument.
   Requires CFG succs/preds are inverses. *)
(* Core congruence: when two states agree on boundaries at all neighbors
   of lbl, processing lbl produces the same fold output (final_val, inst_map).
   This is the key reusable fact for stable_after, self_idempotent, etc. *)
Theorem df_process_fold_cong[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st1 st2
   final_val1 inst_map1 final_val2 inst_map2.
    let neighbors = (case dir of Forward => cfg_preds_of cfg lbl
                               | Backward => cfg_succs_of cfg lbl) in
    let instrs = (case lookup_block lbl bbs of
                    NONE => [] | SOME bb => bb.bb_instructions) in
    let joined1 = (case MAP (λnbr. edge_transfer ctx nbr lbl
                                     (df_boundary bottom st1 nbr)) neighbors of
                     [] => (case entry_val of NONE => bottom
                            | SOME (ev_lbl,v) => if lbl = ev_lbl then v else bottom)
                   | v4::v5 => FOLDL join bottom
                       (MAP (λnbr. edge_transfer ctx nbr lbl
                               (df_boundary bottom st1 nbr)) neighbors)) in
    let joined2 = (case MAP (λnbr. edge_transfer ctx nbr lbl
                                     (df_boundary bottom st2 nbr)) neighbors of
                     [] => (case entry_val of NONE => bottom
                            | SOME (ev_lbl,v) => if lbl = ev_lbl then v else bottom)
                   | v4::v5 => FOLDL join bottom
                       (MAP (λnbr. edge_transfer ctx nbr lbl
                               (df_boundary bottom st2 nbr)) neighbors)) in
      (!nbr. MEM nbr neighbors ==>
        df_boundary bottom st1 nbr = df_boundary bottom st2 nbr) /\
      df_fold_block dir (transfer ctx) lbl instrs joined1 = (final_val1, inst_map1) /\
      df_fold_block dir (transfer ctx) lbl instrs joined2 = (final_val2, inst_map2)
    ==>
      final_val1 = final_val2 /\ inst_map1 = inst_map2
Proof
  rw[] >>
  `MAP (λnbr. edge_transfer ctx nbr lbl (df_boundary bottom st1 nbr))
       (case dir of Forward => cfg_preds_of cfg lbl
                   | Backward => cfg_succs_of cfg lbl) =
   MAP (λnbr. edge_transfer ctx nbr lbl (df_boundary bottom st2 nbr))
       (case dir of Forward => cfg_preds_of cfg lbl
                   | Backward => cfg_succs_of cfg lbl)` by
    (irule listTheory.MAP_CONG >> rw[] >> Cases_on `dir` >> fs[]) >>
  fs[]
QED

(* Helper: when lbl ∉ neighbors(lbl), processing lbl is idempotent.
   Similar structure to stable_after but b = lbl. *)
(* Test: MAP equality with df_process_block *)
Theorem map_eq_process_test[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st.
    ~MEM lbl (case dir of Forward => cfg_preds_of cfg lbl
                        | Backward => cfg_succs_of cfg lbl) ==>
    MAP (λnbr. edge_transfer ctx nbr lbl
              (df_boundary bottom
                (df_process_block dir bottom join transfer edge_transfer ctx
                  entry_val cfg bbs lbl st) nbr))
        (case dir of Forward => cfg_preds_of cfg lbl
                   | Backward => cfg_succs_of cfg lbl) =
    MAP (λnbr. edge_transfer ctx nbr lbl (df_boundary bottom st nbr))
        (case dir of Forward => cfg_preds_of cfg lbl
                   | Backward => cfg_succs_of cfg lbl)
Proof
  rpt strip_tac
  \\ irule listTheory.MAP_CONG
  \\ simp[]
  \\ rpt strip_tac
  \\ `df_boundary bottom
        (df_process_block dir bottom join transfer edge_transfer ctx
          entry_val cfg bbs lbl st) x = df_boundary bottom st x` by
      (irule df_process_block_boundary \\
       CCONTR_TAC \\ fs[] \\ Cases_on `dir` \\ fs[])
  \\ fs[]
QED

(* Debug helper for ev_lbl case *)
Theorem boundary_cong_ev_case[local]:
  !dir bottom join transfer edge_transfer ctx v cfg bbs lbl st1 st2.
    (!nbr. MEM nbr (case dir of Forward => cfg_preds_of cfg lbl
                               | Backward => cfg_succs_of cfg lbl) ==>
      df_boundary bottom st1 nbr = df_boundary bottom st2 nbr) /\
    df_boundary bottom st1 lbl = df_boundary bottom st2 lbl
  ==>
    df_boundary bottom
      (df_process_block dir bottom join transfer edge_transfer ctx
        (SOME (lbl, v)) cfg bbs lbl st1) lbl =
    df_boundary bottom
      (df_process_block dir bottom join transfer edge_transfer ctx
        (SOME (lbl, v)) cfg bbs lbl st2) lbl
Proof
  rpt gen_tac
  \\ strip_tac
  \\ simp[df_process_block_def, df_joined_val_def]
  \\ pairarg_tac
  \\ simp[]
  \\ pairarg_tac
  \\ simp[]
  \\ sg `MAP (λnbr. edge_transfer ctx nbr lbl (df_boundary bottom st1 nbr))
            (case dir of Forward => cfg_preds_of cfg lbl
                       | Backward => cfg_succs_of cfg lbl) =
         MAP (λnbr. edge_transfer ctx nbr lbl (df_boundary bottom st2 nbr))
            (case dir of Forward => cfg_preds_of cfg lbl
                       | Backward => cfg_succs_of cfg lbl)`
  >- (irule listTheory.MAP_CONG \\ simp[])
  \\ fs[]
  \\ IF_CASES_TAC
  \\ simp[df_boundary_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Helper: if two states agree on all boundaries relevant to lbl
   (neighbors + lbl itself), then processing lbl produces the same
   boundary at lbl. *)
Theorem df_process_boundary_cong[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st1 st2.
    (!nbr. MEM nbr (case dir of Forward => cfg_preds_of cfg lbl
                               | Backward => cfg_succs_of cfg lbl) ==>
      df_boundary bottom st1 nbr = df_boundary bottom st2 nbr) /\
    df_boundary bottom st1 lbl = df_boundary bottom st2 lbl
  ==>
    df_boundary bottom
      (df_process_block dir bottom join transfer edge_transfer ctx
        entry_val cfg bbs lbl st1) lbl =
    df_boundary bottom
      (df_process_block dir bottom join transfer edge_transfer ctx
        entry_val cfg bbs lbl st2) lbl
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `entry_val`
  (* NONE *)
  >- (simp[df_process_block_def, df_joined_val_def]
      \\ pairarg_tac \\ simp[]
      \\ pairarg_tac \\ simp[]
      \\ sg `MAP (λnbr. edge_transfer ctx nbr lbl (df_boundary bottom st1 nbr))
                 (case dir of Forward => cfg_preds_of cfg lbl
                            | Backward => cfg_succs_of cfg lbl) =
             MAP (λnbr. edge_transfer ctx nbr lbl (df_boundary bottom st2 nbr))
                 (case dir of Forward => cfg_preds_of cfg lbl
                            | Backward => cfg_succs_of cfg lbl)`
      >- (irule listTheory.MAP_CONG \\ simp[])
      \\ fs[]
      \\ IF_CASES_TAC
      \\ simp[df_boundary_def, finite_mapTheory.FLOOKUP_UPDATE])
  (* SOME *)
  \\ Cases_on `x`
  \\ Cases_on `lbl = q`
  (* lbl = ev_lbl *)
  >- (gvs[] \\ irule boundary_cong_ev_case \\ fs[])
  (* lbl ≠ ev_lbl *)
  >- (simp[df_process_block_def, df_joined_val_def]
      \\ pairarg_tac \\ simp[]
      \\ pairarg_tac \\ simp[]
      \\ sg `MAP (λnbr. edge_transfer ctx nbr lbl (df_boundary bottom st1 nbr))
                 (case dir of Forward => cfg_preds_of cfg lbl
                            | Backward => cfg_succs_of cfg lbl) =
             MAP (λnbr. edge_transfer ctx nbr lbl (df_boundary bottom st2 nbr))
                 (case dir of Forward => cfg_preds_of cfg lbl
                            | Backward => cfg_succs_of cfg lbl)`
      >- (irule listTheory.MAP_CONG \\ simp[])
      \\ fs[]
      \\ IF_CASES_TAC
      \\ simp[df_boundary_def, finite_mapTheory.FLOOKUP_UPDATE])
QED

Theorem df_process_stable_after[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl b st.
    b <> lbl /\
    ~MEM lbl (case dir of Forward => cfg_preds_of cfg b
                        | Backward => cfg_succs_of cfg b) /\
    df_process_block dir bottom join transfer edge_transfer
                     ctx entry_val cfg bbs b st = st
  ==>
    df_process_block dir bottom join transfer edge_transfer
                     ctx entry_val cfg bbs b
      (df_process_block dir bottom join transfer edge_transfer
                        ctx entry_val cfg bbs lbl st) =
    df_process_block dir bottom join transfer edge_transfer
                     ctx entry_val cfg bbs lbl st
Proof
  rpt gen_tac \\ strip_tac
  (* Use changed_equiv: process b st = st means ¬changed *)
  \\ CONV_TAC (REWR_CONV (GSYM (SIMP_RULE std_ss [LET_THM]
       df_process_changed_equiv)))
  (* Now goal is: ¬changed b (process lbl st) (process b (process lbl st)) *)
  (* Use df_process_boundary_cong: boundary at b after process b is the same
     on st and (process lbl st) since they agree on b's neighborhood *)
  \\ mp_tac (SIMP_RULE std_ss [LET_THM] df_process_boundary_cong)
  \\ disch_then (qspecl_then [`dir`,`bottom`,`join`,`transfer`,
       `edge_transfer`,`ctx`,`entry_val`,`cfg`,`bbs`,`b`,
       `df_process_block dir bottom join transfer edge_transfer ctx
          entry_val cfg bbs lbl st`, `st`] mp_tac)
  \\ impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> irule df_process_block_boundary >>
          CCONTR_TAC >> fs[] >> Cases_on `dir` >> fs[])
      >- (irule df_process_block_boundary >> fs[]))
  \\ strip_tac
  (* Now: boundary at b after process b on (process lbl st) =
          boundary at b after process b on st *)
  (* From process b st = st (via changed_equiv): boundary at b didn't change *)
  \\ `df_boundary bottom
        (df_process_block dir bottom join transfer edge_transfer ctx
           entry_val cfg bbs b st) b =
      df_boundary bottom st b` by asm_rewrite_tac[]
  (* Also boundary at b on (process lbl st) = boundary at b on st *)
  \\ `df_boundary bottom
        (df_process_block dir bottom join transfer edge_transfer ctx
           entry_val cfg bbs lbl st) b =
      df_boundary bottom st b` by
       (irule df_process_block_boundary >> fs[])
  (* Combine: boundary at b after process b on (process lbl st) =
              boundary at b on (process lbl st) *)
  \\ fs[]
QED


(* Helper: boundary at lbl after double process is absorbed *)
Theorem df_process_boundary_absorption[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st.
    ~MEM lbl (case dir of Forward => cfg_preds_of cfg lbl
                        | Backward => cfg_succs_of cfg lbl) /\
    (!a b. join (join a b) b = join a b)
  ==>
    df_boundary bottom
      (df_process_block dir bottom join transfer edge_transfer
         ctx entry_val cfg bbs lbl
         (df_process_block dir bottom join transfer edge_transfer
            ctx entry_val cfg bbs lbl st)) lbl =
    df_boundary bottom
      (df_process_block dir bottom join transfer edge_transfer
         ctx entry_val cfg bbs lbl st) lbl
Proof
  rpt gen_tac \\ strip_tac
  (* Establish MAP equality BEFORE expanding *)
  \\ sg `MAP (λnbr. edge_transfer ctx nbr lbl
              (df_boundary bottom
                (df_process_block dir bottom join transfer edge_transfer ctx
                  entry_val cfg bbs lbl st) nbr))
            (case dir of Forward => cfg_preds_of cfg lbl
                       | Backward => cfg_succs_of cfg lbl) =
         MAP (λnbr. edge_transfer ctx nbr lbl (df_boundary bottom st nbr))
            (case dir of Forward => cfg_preds_of cfg lbl
                       | Backward => cfg_succs_of cfg lbl)`
  >- (irule listTheory.MAP_CONG \\ simp[] \\
      rpt strip_tac \\
      `df_boundary bottom
          (df_process_block dir bottom join transfer edge_transfer ctx
            entry_val cfg bbs lbl st) x = df_boundary bottom st x` by
        (irule df_process_block_boundary \\
         CCONTR_TAC \\ fs[] \\ Cases_on `dir` \\ fs[]) \\
      fs[])
  (* Now expand and use the MAP equality *)
  \\ simp[df_process_block_def, df_joined_val_def]
  \\ pairarg_tac \\ simp[]
  \\ rpt (IF_CASES_TAC \\
     simp[df_boundary_def, finite_mapTheory.FLOOKUP_UPDATE])
QED

Theorem df_process_self_idempotent[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st.
    ~MEM lbl (case dir of Forward => cfg_preds_of cfg lbl
                        | Backward => cfg_succs_of cfg lbl) /\
    (!a b. join (join a b) b = join a b)
  ==>
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    process lbl (process lbl st) = process lbl st
Proof
  rpt gen_tac \\ strip_tac \\ simp[]
  \\ CONV_TAC (REWR_CONV (GSYM (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv)))
  \\ irule df_process_boundary_absorption \\ fs[]
QED

Theorem df_process_deps_complete_proof:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val cfg bbs.
    (* CFG preds/succs are inverses *)
    (!a b. MEM b (cfg_succs_of cfg a) <=> MEM a (cfg_preds_of cfg b)) /\
    (* join absorption for self-stability *)
    (!a b. join (join a b) b = join a b)
  ==>
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let changed = (λlbl (old:'a df_state) new.
                     df_boundary bottom new lbl <> df_boundary bottom old lbl) in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    wl_deps_complete changed process deps
Proof
  rpt gen_tac >> strip_tac >>
  simp[worklistDefsTheory.wl_deps_complete_def] >>
  `!lbl st. (λlbl (old:'a df_state) new.
       df_boundary bottom new lbl <> df_boundary bottom old lbl) lbl st
       (df_process_block dir bottom join transfer edge_transfer
          ctx entry_val cfg bbs lbl st) <=>
     df_process_block dir bottom join transfer edge_transfer
       ctx entry_val cfg bbs lbl st <> st` by
    (rpt gen_tac >>
     mp_tac (SIMP_RULE std_ss [LET_THM] df_process_changed_equiv) >>
     disch_then (qspecl_then [`dir`,`bottom`,`join`,`transfer`,
       `edge_transfer`,`ctx`,`entry_val`,`cfg`,`bbs`] mp_tac) >>
     simp[]) >>
  fs[] >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac
  >- (CCONTR_TAC >> rename1 `MEM b0 _` >>
      `~MEM b0 (case dir of Forward => cfg_preds_of cfg b0
                           | Backward => cfg_succs_of cfg b0)` by
        (Cases_on `dir` >> fs[] >> metis_tac[]) >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_self_idempotent) >>
      disch_then (qspecl_then [`dir`, `bottom`, `join`, `transfer`,
        `edge_transfer`, `ctx`, `entry_val`, `cfg`, `bbs`, `b0`, `old`]
        mp_tac) >>
      impl_tac >- rw[] >>
      fs[])
  >- (CCONTR_TAC >> rename1 `MEM b0 _` >>
      `b0 <> lbl` by (CCONTR_TAC >> fs[]) >>
      `~MEM lbl (case dir of Forward => cfg_preds_of cfg b0
                            | Backward => cfg_succs_of cfg b0)` by
        (Cases_on `dir` >> fs[] >> metis_tac[]) >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_stable_after) >>
      disch_then (qspecl_then [`dir`, `bottom`, `join`, `transfer`,
        `edge_transfer`, `ctx`, `entry_val`, `cfg`, `bbs`, `lbl`, `b0`, `old`]
        mp_tac) >>
      impl_tac >- rw[] >>
      fs[])
QED


(* ========================================================================
   Generic convergence toolkit for list_intersect-based forward analyses.

   Shared infrastructure for proving bounded_measure P leq m b, which
   is needed for df_analyze_fixpoint_forward. Used by:
   - varDefProofs (variable definition analysis)
   - dominatorProofs (dominator analysis)
   - any future forward analysis with list_intersect join

   The pattern: three-component measure
     measure = boundary_complement + inst_complement + CARD(FDOM ds_inst)
   where each component is bounded and the measure strictly increases
   when process changes the state.
   ======================================================================== *)

(* --- FDOM characterization for df_fold_forward/block --- *)

Theorem df_fold_forward_fdom:
  !instrs transfer lbl idx acc inst_map fv im.
    df_fold_forward transfer lbl instrs idx acc inst_map = (fv, im) ==>
    FDOM im = FDOM inst_map UNION
              IMAGE (\j. (lbl, idx + j)) (count (LENGTH instrs + 1))
Proof
  Induct >>
  rw[df_fold_forward_def]
  >- (rw[finite_mapTheory.FDOM_FUPDATE,
         pred_setTheory.EXTENSION, pred_setTheory.IN_INSERT,
         pred_setTheory.IN_UNION, pred_setTheory.IN_IMAGE,
         pred_setTheory.IN_COUNT] >>
      Cases_on `x` >> EQ_TAC >> rw[] >> fs[])
  >> rw[LET_THM] >>
     first_x_assum drule >> strip_tac >>
     rw[finite_mapTheory.FDOM_FUPDATE,
        pred_setTheory.EXTENSION, pred_setTheory.IN_INSERT,
        pred_setTheory.IN_UNION, pred_setTheory.IN_IMAGE,
        pred_setTheory.IN_COUNT] >>
     Cases_on `x` >> EQ_TAC >> rw[] >> fs[] >>
     TRY DECIDE_TAC >>
     Cases_on `j` >> fs[] >> disj2_tac >> qexists_tac `n` >> DECIDE_TAC
QED

Theorem df_fold_forward_append:
  !l1 f lbl l2 idx acc im.
    df_fold_forward f lbl (l1 ++ l2) idx acc im =
      let (mid, im1) = df_fold_forward f lbl l1 idx acc im in
      df_fold_forward f lbl l2 (idx + LENGTH l1) mid im1
Proof
  Induct >> simp[df_fold_forward_def, LET_THM] >>
  rpt gen_tac
  >- (Cases_on `l2` >>
      simp[df_fold_forward_def, LET_THM,
           finite_mapTheory.FUPDATE_EQ])
  >- (Cases_on `df_fold_forward f lbl l1 (idx + 1) (f h acc)
                  (im |+ ((lbl, idx), acc))` >>
      `idx + (LENGTH l1 + 1) = idx + SUC (LENGTH l1)` by DECIDE_TAC >>
      simp[])
QED

(* The full fold's inst_map at position idx+n equals the prefix fold's
   accumulator output. This bridges df_fold_forward_at with intermediate
   fold values, avoiding the need for df_fold_forward_at_gen on non-FEMPTY
   initial maps. *)
(* The full fold's inst_map at split position n equals the prefix fold's
   accumulator output. Both folds are deterministic and process the same
   first n instructions, so their intermediate values at each step match. *)
Theorem df_fold_forward_midpoint:
  !f lbl instrs idx acc fv im n.
    df_fold_forward f lbl instrs idx acc FEMPTY = (fv, im) /\
    n <= LENGTH instrs ==>
    ?mid im_pre.
      df_fold_forward f lbl (TAKE n instrs) idx acc FEMPTY = (mid, im_pre) /\
      FLOOKUP im (lbl, idx + n) = SOME mid
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- (
    (* Base: n=0 — TAKE 0 = [], fold returns (acc, FEMPTY |+ ((lbl,idx),acc)) *)
    simp[listTheory.TAKE_def, df_fold_forward_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
    drule df_fold_forward_at >> simp[])
  >- (
    (* Step: n → SUC n *)
    `n <= LENGTH instrs` by fs[] >>
    first_x_assum (qspecl_then [`f`, `lbl`, `instrs`, `idx`, `acc`,
      `fv`, `im`] mp_tac) >>
    impl_tac >- fs[] >> strip_tac >>
    (* mid is the prefix fold result at position n *)
    (* Now extend by one more instruction *)
    `SUC n <= LENGTH instrs` by fs[] >>
    `n < LENGTH instrs` by fs[] >>
    qpat_assum `df_fold_forward _ _ instrs _ _ _ = _`
      (strip_assume_tac o MATCH_MP df_fold_forward_at) >>
    (* FLOOKUP im (lbl, idx + SUC n) = SOME (f (EL n instrs) (THE (FLOOKUP im (lbl, idx + n)))) *)
    `FLOOKUP im (lbl, idx + SUC n) =
       SOME (f (EL n instrs) (THE (FLOOKUP im (lbl, idx + n))))` by
      (first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
    `THE (FLOOKUP im (lbl, idx + n)) = mid` by fs[] >>
    (* TAKE (SUC n) = TAKE n ++ [EL n instrs] *)
    `TAKE (SUC n) instrs = TAKE n instrs ++ [EL n instrs]` by
      simp[GSYM listTheory.SNOC_APPEND, rich_listTheory.SNOC_EL_TAKE] >>
    pop_assum (fn th => REWRITE_TAC[th]) >>
    REWRITE_TAC[df_fold_forward_append] >>
    simp[LET_THM, df_fold_forward_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    qexistsl_tac [`f (EL n instrs) mid`,
      `im_pre |+ ((lbl, idx + n), mid) |+ ((lbl, idx + SUC n), f (EL n instrs) mid)`] >>
    fs[])
QED

Theorem df_fold_block_fdom:
  !transfer lbl instrs init_val fv im.
    df_fold_block Forward transfer lbl instrs init_val = (fv, im) ==>
    FDOM im = IMAGE (\i. (lbl, i)) (count (LENGTH instrs + 1))
Proof
  rw[df_fold_block_def] >>
  drule df_fold_forward_fdom >>
  simp[finite_mapTheory.FDOM_FEMPTY, pred_setTheory.UNION_EMPTY]
QED

Theorem df_fold_backward_fdom:
  !instrs transfer lbl idx acc inst_map fv im.
    df_fold_backward transfer lbl instrs idx acc inst_map = (fv, im) ==>
    FDOM im = FDOM inst_map UNION
              IMAGE (\j. (lbl, idx + j)) (count (LENGTH instrs + 1))
Proof
  Induct >>
  rw[df_fold_backward_def]
  >- (rw[finite_mapTheory.FDOM_FUPDATE,
         pred_setTheory.EXTENSION, pred_setTheory.IN_INSERT,
         pred_setTheory.IN_UNION, pred_setTheory.IN_IMAGE,
         pred_setTheory.IN_COUNT] >>
      Cases_on `x` >> EQ_TAC >> rw[] >> fs[])
  >> rw[LET_THM] >> pairarg_tac >> fs[] >>
     first_x_assum drule >> strip_tac >>
     rw[finite_mapTheory.FDOM_FUPDATE,
        pred_setTheory.EXTENSION, pred_setTheory.IN_INSERT,
        pred_setTheory.IN_UNION, pred_setTheory.IN_IMAGE,
        pred_setTheory.IN_COUNT] >>
     Cases_on `x` >> EQ_TAC >> rw[] >> fs[] >>
     TRY DECIDE_TAC >>
     Cases_on `j` >> fs[] >> disj2_tac >> qexists_tac `n` >> DECIDE_TAC
QED

Theorem df_fold_block_fdom_backward:
  !transfer lbl instrs init_val fv im.
    df_fold_block Backward transfer lbl instrs init_val = (fv, im) ==>
    FDOM im = IMAGE (\i. (lbl, i)) (count (LENGTH instrs + 1))
Proof
  rw[df_fold_block_def] >>
  drule df_fold_backward_fdom >>
  simp[finite_mapTheory.FDOM_FEMPTY, pred_setTheory.UNION_EMPTY]
QED

(* --- Valid inst keys: generic definitions and properties --- *)

Definition df_valid_inst_keys_def:
  df_valid_inst_keys bbs =
    BIGUNION (set (MAP (\bb.
      IMAGE (\i. (bb.bb_label, i))
        (count (LENGTH bb.bb_instructions + 1))) bbs))
End

Definition df_total_inst_slots_def:
  df_total_inst_slots bbs =
    SUM (MAP (\bb. LENGTH bb.bb_instructions + 1) bbs)
End

Triviality valid_inst_keys_bbs_finite:
  !bbs. FINITE (BIGUNION (set (MAP (\bb.
     IMAGE (\i. (bb.bb_label, i))
       (count (LENGTH bb.bb_instructions + 1))) bbs)))
Proof
  Induct >> rw[listTheory.MAP, listTheory.MEM_MAP] >>
  rw[pred_setTheory.IMAGE_FINITE]
QED

Theorem df_valid_inst_keys_finite:
  !bbs. FINITE (df_valid_inst_keys bbs)
Proof
  rw[df_valid_inst_keys_def, valid_inst_keys_bbs_finite]
QED

Triviality label_index_inj:
  !(lbl:string). INJ (\i:num. (lbl, i)) (count n) UNIV
Proof
  rw[pred_setTheory.INJ_DEF]
QED

Triviality bigunion_image_card_le_sum:
  !bbs. CARD (BIGUNION (set (MAP (\bb.
     IMAGE (\i. (bb.bb_label, i))
       (count (LENGTH bb.bb_instructions + 1))) bbs))) <=
    SUM (MAP (\bb. LENGTH bb.bb_instructions + 1) bbs)
Proof
  Induct >> rw[listTheory.MAP, listTheory.SUM] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `CARD (IMAGE (\i. (h.bb_label, i))
     (count (LENGTH h.bb_instructions + 1))) +
    CARD (BIGUNION (set (MAP (\bb.
     IMAGE (\i. (bb.bb_label, i))
       (count (LENGTH bb.bb_instructions + 1))) bbs)))` >>
  conj_tac
  >- (irule pred_setTheory.CARD_UNION_LE >>
      rw[pred_setTheory.IMAGE_FINITE, valid_inst_keys_bbs_finite])
  >- (rw[pred_setTheory.CARD_INJ_IMAGE, label_index_inj,
         pred_setTheory.CARD_COUNT] >> DECIDE_TAC)
QED

Theorem df_valid_inst_keys_card:
  !bbs. CARD (df_valid_inst_keys bbs) <= df_total_inst_slots bbs
Proof
  rw[df_valid_inst_keys_def, df_total_inst_slots_def,
     bigunion_image_card_le_sum]
QED

(* fold output keys ⊆ valid_inst_keys *)
Theorem df_fold_block_fdom_subset:
  !bbs lbl bb init_val transfer fv im.
    MEM bb bbs /\ bb.bb_label = lbl /\
    df_fold_block Forward transfer lbl
      bb.bb_instructions init_val = (fv, im) ==>
    FDOM im SUBSET df_valid_inst_keys bbs
Proof
  rw[] >> drule df_fold_block_fdom >> rw[] >>
  rw[df_valid_inst_keys_def, pred_setTheory.SUBSET_DEF,
     pred_setTheory.IN_BIGUNION, listTheory.MEM_MAP,
     pred_setTheory.IN_IMAGE, pred_setTheory.IN_COUNT] >>
  qexists_tac `IMAGE (\i. (bb.bb_label, i))
    (count (LENGTH bb.bb_instructions + 1))` >>
  rw[pred_setTheory.IN_IMAGE, pred_setTheory.IN_COUNT] >>
  qexists_tac `bb` >> rw[]
QED

Theorem df_fold_block_fdom_subset_backward:
  !bbs lbl bb init_val transfer fv im.
    MEM bb bbs /\ bb.bb_label = lbl /\
    df_fold_block Backward transfer lbl bb.bb_instructions init_val =
      (fv, im) ==>
    FDOM im SUBSET df_valid_inst_keys bbs
Proof
  rw[] >> drule df_fold_block_fdom_backward >> rw[] >>
  rw[df_valid_inst_keys_def, pred_setTheory.SUBSET_DEF,
     pred_setTheory.IN_BIGUNION, listTheory.MEM_MAP,
     pred_setTheory.IN_IMAGE, pred_setTheory.IN_COUNT] >>
  qexists_tac `IMAGE (\i. (bb.bb_label, i))
    (count (LENGTH bb.bb_instructions + 1))` >>
  rw[pred_setTheory.IN_IMAGE, pred_setTheory.IN_COUNT] >>
  qexists_tac `bb` >> rw[]
QED

(* --- lookup_block --- *)
Theorem lookup_block_exists:
  !lbl bbs.
    MEM lbl (MAP (\bb. bb.bb_label) bbs) ==>
    ?bb. lookup_block lbl bbs = SOME bb /\ MEM bb bbs /\ bb.bb_label = lbl
Proof
  Induct_on `bbs` >> rw[venomInstTheory.lookup_block_def, listTheory.FIND_thm] >>
  Cases_on `h.bb_label = lbl` >> rw[] >>
  fs[venomInstTheory.lookup_block_def] >> metis_tac[]
QED

(* --- Arithmetic helper --- *)
Theorem three_sum_strict:
  !a b c a' b' (c':num).
    a <= a' /\ b <= b' /\ c <= c' /\
    (a < a' \/ b < b' \/ c < c') ==>
    a + b + c < a' + b' + c'
Proof
  rpt strip_tac >> fs[]


QED

(* --- Boundary helpers --- *)

Theorem df_boundary_length_le:
  !universe st lbl.
    ALL_DISTINCT universe /\
    (!l v. FLOOKUP st.ds_boundary l = SOME v ==>
       ALL_DISTINCT v /\ set v SUBSET set universe) ==>
    LENGTH (df_boundary universe st lbl) <= LENGTH universe
Proof
  rw[df_boundary_def] >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> simp[] >>
  res_tac >>
  `FINITE (set universe)` by rw[listTheory.FINITE_LIST_TO_SET] >>
  `CARD (set x) <= CARD (set universe)` by metis_tac[pred_setTheory.CARD_SUBSET] >>
  `CARD (set x) = LENGTH x` by metis_tac[listTheory.ALL_DISTINCT_CARD_LIST_TO_SET] >>
  `CARD (set universe) = LENGTH universe` by
    metis_tac[listTheory.ALL_DISTINCT_CARD_LIST_TO_SET] >>
  DECIDE_TAC
QED

Theorem df_boundary_all_distinct:
  !universe st lbl.
    ALL_DISTINCT universe /\
    (!l v. FLOOKUP st.ds_boundary l = SOME v ==>
       ALL_DISTINCT v /\ set v SUBSET set universe) ==>
    ALL_DISTINCT (df_boundary universe st lbl)
Proof
  rw[df_boundary_def] >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> simp[] >>
  res_tac
QED

(* FOLDL of constant FUPDATE on FEMPTY: any value is that constant *)
Theorem foldl_fupdate_const:
  !ls bot k v.
    FLOOKUP (FOLDL (\m l. m |+ (l, bot)) FEMPTY ls) k = SOME v ==> v = bot
Proof
  metis_tac[foldl_fupdate_flookup, finite_mapTheory.FLOOKUP_EMPTY,
            optionTheory.NOT_SOME_NONE]
QED

(* Init FOLDL: result is either from initial map or the constant *)
Theorem foldl_init_flookup:
  !ls bot m k v.
    FLOOKUP (FOLDL (\m lbl. m |+ (lbl, bot)) m ls) k = SOME v ==>
    FLOOKUP m k = SOME v \/ v = bot
Proof
  Induct >> rw[listTheory.FOLDL] >> res_tac >>
  fs[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `k = h` >> fs[]
QED
