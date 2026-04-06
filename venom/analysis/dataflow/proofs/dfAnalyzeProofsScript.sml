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
  dfAnalyzeDefs worklistProofs cfgDefs cfgHelpers venomWf

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
Theorem df_analyze_fixpoint_proof:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
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
      wl_deps_complete process deps
    ==>
      is_fixpoint process all_lbls
        (df_analyze dir bottom join transfer edge_transfer ctx entry_val fn)
Proof
  rpt gen_tac >> simp[dfAnalyzeDefsTheory.df_analyze_def] >> strip_tac >>
  irule worklistProofsTheory.wl_iterate_fixpoint_proof >>
  rpt conj_tac
  (* all_lbls ⊆ wl0 *)
  >- (rw[] >> Cases_on `dir` >> fs[] >> metis_tac[cfg_dfs_pre_mem_post])
  (* deps_complete — from assumption *)
  >- fs[]
  (* convergence witnesses *)
  >- (qexistsl_tac [`P`, `b`, `leq`, `m`] >> rw[] >>
      Cases_on `entry_val` >> fs[] >>
      Cases_on `x` >> fs[])
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
      wl_deps_complete process deps
    ==>
      is_fixpoint process all_lbls
        (df_analyze dir bottom join transfer edge_transfer ctx entry_val fn)
Proof
  rpt gen_tac >> simp[dfAnalyzeDefsTheory.df_analyze_def] >> strip_tac >>
  irule worklistProofsTheory.wl_iterate_fixpoint_process_proof >>
  rpt conj_tac
  >- (qexistsl_tac [`P`, `b`, `m`] >> rw[] >>
      Cases_on `entry_val` >> fs[] >>
      Cases_on `x` >> fs[])
  >- (rw[] >> Cases_on `dir` >> fs[] >> metis_tac[cfg_dfs_pre_mem_post])
  >- fs[]
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
      wl_deps_complete process deps /\
      EVERY valid_lbl wl0 /\
      (!lbl. valid_lbl lbl ==> EVERY valid_lbl (deps lbl))
    ==>
      is_fixpoint process all_lbls
        (df_analyze dir bottom join transfer edge_transfer ctx entry_val fn)
Proof
  rpt gen_tac >> simp[dfAnalyzeDefsTheory.df_analyze_def] >> strip_tac >>
  irule worklistProofsTheory.wl_iterate_fixpoint_process_restricted >>
  rpt conj_tac
  >- (rw[] >> Cases_on `dir` >> fs[] >> metis_tac[cfg_dfs_pre_mem_post])
  >- (qexistsl_tac [`P`, `b`, `m`, `valid_lbl`] >> rw[] >>
      Cases_on `entry_val` >> fs[] >> Cases_on `x` >> fs[])
  >- fs[]
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
      wl_deps_complete process (cfg_succs_of cfg)
    ==>
      is_fixpoint process cfg.cfg_dfs_pre
        (df_analyze Forward bottom join transfer edge_transfer ctx
                    entry_val fn)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `is_fixpoint
     (df_process_block Forward bottom join transfer edge_transfer ctx
        entry_val (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
     (df_analyze Forward bottom join transfer edge_transfer ctx entry_val fn)`
   suffices_by simp[] >>
  irule (SIMP_RULE std_ss [LET_THM] df_analyze_fixpoint_process_restricted) >>
  conj_tac >- fs[] >>
  qexistsl_tac [`P`, `b`, `m`, `\lbl. MEM lbl (fn_labels fn)`] >>
  simp[] >> rpt conj_tac
  >- metis_tac[fn_labels_succs_closed]
  >- (rw[listTheory.EVERY_MEM] >> metis_tac[cfg_dfs_pre_subset_fn_labels])
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
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
      wf_function fn /\
      (!lbl st. MEM lbl (fn_labels fn) /\ Q st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. MEM lbl (fn_labels fn) /\ Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. Q x ==> m x <= b)
    ==>
      Q result
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  simp[dfAnalyzeDefsTheory.df_analyze_def] >>
  qmatch_goalsub_abbrev_tac `wl_iterate process deps wl0 st0'` >>
  `Q (SND (wl_iterate process deps wl0 st0'))`
    suffices_by simp[] >>
  irule (SIMP_RULE std_ss [LET_THM]
    worklistProofsTheory.wl_iterate_invariant_process_restricted) >>
  conj_tac
  >- (simp[markerTheory.Abbrev_def] >>
      Cases_on `entry_val` >> fs[] >> Cases_on `x` >> fs[]) >>
  qexistsl_tac [`b`, `m`, `\lbl. MEM lbl (fn_labels fn)`] >>
  simp[markerTheory.Abbrev_def] >> rpt conj_tac
  >- metis_tac[fn_labels_succs_closed]
  >- (rw[listTheory.EVERY_MEM] >> metis_tac[cfg_dfs_pre_subset_fn_labels])
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
      wl_deps_complete process (cfg_preds_of cfg)
    ==>
      is_fixpoint process cfg.cfg_dfs_pre
        (df_analyze Backward bottom join transfer edge_transfer ctx
                    entry_val fn)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `is_fixpoint
     (df_process_block Backward bottom join transfer edge_transfer ctx
        entry_val (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
     (df_analyze Backward bottom join transfer edge_transfer ctx entry_val fn)`
   suffices_by simp[] >>
  irule (SIMP_RULE std_ss [LET_THM] df_analyze_fixpoint_process_restricted) >>
  conj_tac >- fs[] >>
  qexistsl_tac [`P`, `b`, `m`, `\lbl. MEM lbl (fn_labels fn)`] >>
  simp[] >> rpt conj_tac
  >- metis_tac[fn_labels_preds_closed]
  >- (rw[listTheory.EVERY_MEM] >> metis_tac[cfg_dfs_post_subset_fn_labels])
QED

(* Backward analysis state-level invariant *)
Theorem df_analyze_invariant_backward:
  !(bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (m : 'a df_state -> num) b (Q : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Backward bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let result = df_analyze Backward bottom join transfer edge_transfer
                            ctx entry_val fn in
      wf_function fn /\
      (!lbl st. MEM lbl (fn_labels fn) /\ Q st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. MEM lbl (fn_labels fn) /\ Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. Q x ==> m x <= b)
    ==>
      Q result
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  simp[dfAnalyzeDefsTheory.df_analyze_def] >>
  qmatch_goalsub_abbrev_tac `wl_iterate process deps wl0 st0'` >>
  `Q (SND (wl_iterate process deps wl0 st0'))`
    suffices_by simp[] >>
  irule (SIMP_RULE std_ss [LET_THM]
    worklistProofsTheory.wl_iterate_invariant_process_restricted) >>
  conj_tac
  >- (simp[markerTheory.Abbrev_def] >>
      Cases_on `entry_val` >> fs[] >> Cases_on `x` >> fs[]) >>
  qexistsl_tac [`b`, `m`, `\lbl. MEM lbl (fn_labels fn)`] >>
  simp[markerTheory.Abbrev_def] >> rpt conj_tac
  >- metis_tac[fn_labels_preds_closed]
  >- (rw[listTheory.EVERY_MEM] >> metis_tac[cfg_dfs_post_subset_fn_labels])
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
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let result = df_analyze Backward bottom join transfer edge_transfer
                            ctx entry_val fn in
      (!lbl st. Q st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. Q x ==> m x <= b)
    ==>
      Q result
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  simp[dfAnalyzeDefsTheory.df_analyze_def] >>
  qmatch_goalsub_abbrev_tac `wl_iterate process deps wl0 st0'` >>
  `Q (SND (wl_iterate process deps wl0 st0'))`
    suffices_by simp[] >>
  irule (SIMP_RULE std_ss [LET_THM]
    worklistProofsTheory.wl_iterate_invariant_process_proof) >>
  conj_tac
  >- (simp[markerTheory.Abbrev_def] >>
      Cases_on `entry_val` >> fs[] >> Cases_on `x` >> fs[])
  >> simp[markerTheory.Abbrev_def] >>
  qexistsl_tac [`b`, `m`] >> simp[]
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
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let result = df_analyze Backward bottom join transfer edge_transfer
                            ctx entry_val fn in
      (!lbl st. valid_lbl lbl /\ Q st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. valid_lbl lbl /\ Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. Q x ==> m x <= b) /\
      EVERY valid_lbl cfg.cfg_dfs_post /\
      (!lbl. valid_lbl lbl ==>
             EVERY valid_lbl (cfg_preds_of cfg lbl))
    ==>
      Q result
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  simp[dfAnalyzeDefsTheory.df_analyze_def] >>
  qmatch_goalsub_abbrev_tac `wl_iterate process deps wl0 st0'` >>
  `Q (SND (wl_iterate process deps wl0 st0'))`
    suffices_by simp[] >>
  irule (SIMP_RULE std_ss [LET_THM]
    worklistProofsTheory.wl_iterate_invariant_process_restricted) >>
  conj_tac
  >- (simp[markerTheory.Abbrev_def] >>
      Cases_on `entry_val` >> fs[] >> Cases_on `x` >> fs[])
  >> qexistsl_tac [`b`, `m`, `valid_lbl`] >>
  simp[markerTheory.Abbrev_def]
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

(* At fixpoint, process lbl result = result implies the fold's inst_map
   entries are all present in result.ds_inst with the same values. *)
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
        im ⊑ result.ds_inst /\
        df_boundary bottom result lbl =
          join (df_boundary bottom result lbl) fv
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  (* Specialize fixpoint at lbl *)
  fs[worklistDefsTheory.is_fixpoint_def] >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >>
  (* Expand process *)
  simp[df_process_block_def, df_joined_val_def] >>
  pairarg_tac >> simp[] >>
  (* lookup_block lbl bbs = SOME bb, so instrs = bb.bb_instructions *)
  strip_tac >>
  (* From process lbl result = result, extract component equalities *)
  `inst_map ⊌ result.ds_inst = result.ds_inst` by
    (qpat_x_assum `<|ds_inst := _; ds_boundary := _|> = result` mp_tac >>
     rw[df_state_component_equality]) >>
  `result.ds_boundary |+ (lbl,
     join (df_boundary bottom result lbl) final_val) =
   result.ds_boundary` by
    (qpat_x_assum `<|ds_inst := _; ds_boundary := _|> = result` mp_tac >>
     rw[df_state_component_equality]) >>
  conj_tac
  (* im ⊑ result.ds_inst: from FUNION absorption *)
  >- metis_tac[finite_mapTheory.SUBMAP_FUNION_ABSORPTION]
  (* join(boundary, fv) = boundary: from boundary update being a no-op *)
  >- (`lbl IN FDOM result.ds_boundary` by
       (`lbl IN FDOM (result.ds_boundary |+
          (lbl, join (df_boundary bottom result lbl) final_val))` by
          simp[finite_mapTheory.FDOM_FUPDATE] >>
        metis_tac[]) >>
      fs[df_boundary_def, finite_mapTheory.FLOOKUP_DEF] >>
      `(result.ds_boundary |+
         (lbl, join (result.ds_boundary ' lbl) final_val)) ' lbl =
       join (result.ds_boundary ' lbl) final_val` by
        simp[finite_mapTheory.FAPPLY_FUPDATE_THM] >>
      metis_tac[])
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
    is_fixpoint
      (df_process_block dir bottom join transfer edge_transfer
                        ctx entry_val cfg bbs) all_lbls result /\
    MEM lbl all_lbls /\
    lookup_block lbl bbs = SOME bb /\
    instrs = bb.bb_instructions /\
    joined = df_joined_val dir bottom join edge_transfer ctx
                           entry_val cfg result lbl
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
  rpt gen_tac >> strip_tac >>
  drule (SIMP_RULE std_ss [LET_THM] df_fixpoint_fold_submap) >>
  disch_then drule >>
  disch_then (qspec_then `bb` mp_tac) >>
  impl_tac >- fs[] >>
  pairarg_tac >> fs[] >> strip_tac >>
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
  rpt gen_tac >> simp[] >> strip_tac >>
  mp_tac df_fixpoint_at >>
  disch_then (qspecl_then [`dir`, `bottom`, `join`, `transfer`, `edge_transfer`,
    `ctx`, `entry_val`, `cfg_analyze fn`, `fn.fn_blocks`, `lbl`,
    `df_analyze dir bottom join transfer edge_transfer ctx entry_val fn`,
    `(cfg_analyze fn).cfg_dfs_pre`, `bb`, `bb.bb_instructions`] mp_tac) >>
  simp[]
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
      is_fixpoint process all_lbls result /\
      MEM lbl all_lbls /\
      lookup_block lbl bbs = SOME bb
    ==>
      (dir = Forward ==>
        df_at bottom result lbl 0 = joined) /\
      (dir = Backward ==>
        df_at bottom result lbl (LENGTH bb.bb_instructions) = joined)
Proof
  rpt gen_tac >> simp[df_joined_val_def] >> strip_tac >>
  mp_tac (SIMP_RULE std_ss [LET_THM] df_fixpoint_at) >>
  disch_then (qspecl_then [`dir`, `bottom`, `join`, `transfer`, `edge_transfer`,
    `ctx`, `entry_val`, `cfg_analyze fn`, `fn.fn_blocks`, `lbl`,
    `df_analyze dir bottom join transfer edge_transfer ctx entry_val fn`,
    `(cfg_analyze fn).cfg_dfs_pre`, `bb`] mp_tac) >>
  simp[df_joined_val_def]
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
  rpt gen_tac >> simp[] >> strip_tac >>
  (* Get fold submap + boundary absorption from local helper *)
  drule (SIMP_RULE std_ss [LET_THM] df_fixpoint_fold_submap) >>
  disch_then drule >>
  disch_then (qspec_then `bb` mp_tac) >>
  impl_tac >- fs[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  (* Now have: im ⊑ result.ds_inst  and
               boundary = join(boundary, fv)
     fv comes from df_fold_block dir ... = (fv, im)
     Need: fv = df_at(lbl, exit_idx) for the right direction *)
  conj_tac >> strip_tac >> gvs[df_fold_block_def]
  (* Forward: fv from df_fold_forward *)
  >- (drule df_fold_forward_at >> strip_tac >>
      (* fv = THE(FLOOKUP im (lbl, LENGTH instrs)) and im(lbl,0) = SOME ... *)
      (* Need FLOOKUP im (lbl, LENGTH instrs) = SOME fv *)
      `FLOOKUP im (lbl, LENGTH bb.bb_instructions) = SOME fv` by
        (Cases_on `LENGTH bb.bb_instructions`
         >- (fs[] >> Cases_on `FLOOKUP im (lbl, 0)` >> fs[])
         >- (`FLOOKUP im (lbl, 0 + SUC n) <> NONE` by
               (first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
             Cases_on `FLOOKUP im (lbl, 0 + SUC n)` >> fs[])) >>
      `df_at bottom
         (df_analyze Forward bottom join transfer edge_transfer ctx
            entry_val fn) lbl (LENGTH bb.bb_instructions) = fv` by
        (irule df_at_from_submap >> qexists_tac `im` >> fs[]) >>
      fs[])
  (* Backward: fv from df_fold_backward *)
  >- (drule df_fold_backward_at >> strip_tac >>
      `FLOOKUP im (lbl, 0) = SOME fv` by
        (Cases_on `LENGTH bb.bb_instructions`
         >- (fs[] >> Cases_on `FLOOKUP im (lbl, 0)` >> fs[])
         >- (`FLOOKUP im (lbl, 0) <> NONE` by
               (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
             Cases_on `FLOOKUP im (lbl, 0)` >> fs[])) >>
      `df_at bottom
         (df_analyze Backward bottom join transfer edge_transfer ctx
            entry_val fn) lbl 0 = fv` by
        (irule df_at_from_submap >> qexists_tac `im` >> fs[]) >>
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
  disch_then irule >> rw[finite_mapTheory.FLOOKUP_DEF]
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
  simp[dfAnalyzeDefsTheory.df_process_block_def, dfAnalyzeDefsTheory.df_joined_val_def, LET_THM] >>
  pairarg_tac >> simp[]
  (* Establish P for all edge_transfer values *)
  \\ sg `!nbr. P (edge_transfer ctx nbr lbl (df_boundary bottom st nbr))`
  >- (rw[dfAnalyzeDefsTheory.df_boundary_def] >>
      Cases_on `FLOOKUP st.ds_boundary nbr` >> fs[] >> res_tac >> fs[])
  \\ sg `!nbrs. EVERY P (MAP (\nbr. edge_transfer ctx nbr lbl
      (df_boundary bottom st nbr)) nbrs)`
  >- (Induct >> rw[])
  \\ qabbrev_tac `evs = MAP (\nbr. edge_transfer ctx nbr lbl
      (df_boundary bottom st nbr)) (case dir of Forward => cfg_preds_of cfg lbl
        | Backward => cfg_succs_of cfg lbl)`
  (* Helper: EVERY P for the evs list *)
  \\ `EVERY P evs` by
    (qpat_x_assum `Abbrev (evs = _)`
       (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     disch_then SUBST1_TAC >>
     simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM])
  (* Also establish P for edge_transfers with arbitrary label *)
  \\ `!l nbr. P (edge_transfer ctx nbr l (df_boundary bottom st nbr))` by
    (rpt gen_tac >>
     qpat_x_assum `!src dst a. P a ==> P (edge_transfer _ _ _ _)` irule >>
     rw[dfAnalyzeDefsTheory.df_boundary_def] >>
     Cases_on `FLOOKUP st.ds_boundary nbr` >> fs[] >> res_tac >> fs[])
  \\ `!l. EVERY P (MAP (\nbr. edge_transfer ctx nbr l
       (df_boundary bottom st nbr))
       (case dir of Forward => cfg_preds_of cfg l
                   | Backward => cfg_succs_of cfg l))` by
    (gen_tac >> simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM])
  (* Establish P(init_val) for df_fold_block_P *)
  \\ qmatch_asmsub_abbrev_tac `df_fold_block _ _ _ _ joined_val`
  \\ sg `P joined_val`
  >- (qunabbrev_tac `joined_val` >>
      Cases_on `entry_val` >> simp[]
      >- (irule case_foldl_P >> fs[])
      >> Cases_on `x` >> simp[] >>
      IF_CASES_TAC >> simp[]
      >- (qpat_x_assum `lbl = _` (SUBST_ALL_TAC o SYM) >>
          qpat_x_assum `∀a b. P a ∧ P b ⇒ P (join a b)`
            (fn th => irule th >> assume_tac th) >>
          conj_tac
          >- (qpat_x_assum `case _ of NONE => T | _ => _` mp_tac >> simp[])
          >> irule case_foldl_P >> fs[] >>
          simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM])
      >> irule case_foldl_P >> fs[])
  (* Apply df_fold_block_P *)
  \\ drule_all df_fold_block_P >> strip_tac
  \\ conj_tac
  >- (rw[finite_mapTheory.FLOOKUP_FUNION] >>
      Cases_on `FLOOKUP inst_map k` >> fs[] >> metis_tac[])
  \\ rw[finite_mapTheory.FLOOKUP_UPDATE] >>
     fs[dfAnalyzeDefsTheory.df_boundary_def] >>
     Cases_on `FLOOKUP st.ds_boundary k` >> fs[] >> metis_tac[]
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
      (!a b. P a /\ P b ==> P (join a b)) /\
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
  rpt gen_tac >> simp[] >> strip_tac >>
  simp[dfAnalyzeDefsTheory.df_analyze_def,
       dfAnalyzeDefsTheory.df_at_def,
       dfAnalyzeDefsTheory.df_boundary_def] >>
  qabbrev_tac `process = df_process_block dir bottom join transfer
    edge_transfer ctx entry_val (cfg_analyze fn) fn.fn_blocks` >>
  qabbrev_tac `st0' = case entry_val of
    NONE => init_df_state bottom (MAP (λbb. bb.bb_label) fn.fn_blocks)
    | SOME (lbl,v) => init_df_state bottom
        (MAP (λbb. bb.bb_label) fn.fn_blocks) with ds_boundary :=
        (init_df_state bottom (MAP (λbb. bb.bb_label) fn.fn_blocks)).
        ds_boundary |+ (lbl,v)` >>
  qabbrev_tac `deps = case dir of Forward => cfg_succs_of (cfg_analyze fn)
                                 | Backward => cfg_preds_of (cfg_analyze fn)` >>
  qabbrev_tac `wl0 = case dir of Forward => (cfg_analyze fn).cfg_dfs_pre
                                | Backward => (cfg_analyze fn).cfg_dfs_post` >>
  qabbrev_tac `result = SND (wl_iterate process deps wl0 st0')` >>
  (* Instantiate wl_iterate_invariant_proof with R = Q ∧ inst_P ∧ boundary_P *)
  mp_tac (
    let val base = INST_TYPE [alpha |-> ``:'a df_state``, beta |-> ``:string``]
                     (SIMP_RULE std_ss [LET_THM] wl_iterate_invariant_proof)
        val sp1 = Q.SPECL [`leq`, `m`, `b`, `process`, `deps`, `wl0`, `st0'`] base
        val R = ``\st:'a df_state.
          Q st /\ (!k v. FLOOKUP st.ds_inst k = SOME v ==> P v) /\
                  (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v)``
    in SIMP_RULE std_ss [] (SPEC R sp1) end) >>
  impl_tac
  >- (conj_tac >| [
    (* 1. leq *)
    rpt gen_tac >> strip_tac >> first_x_assum irule >> fs[],
    (* 2-4: R_preserved ∧ R(st0') ∧ bounded_measure *)
    conj_tac >| [
      (* 2. R preserved *)
      rpt gen_tac >> strip_tac >>
      conj_tac >- (first_x_assum irule >> fs[]) >>
      `process lbl st = df_process_block dir bottom join transfer
        edge_transfer ctx entry_val (cfg_analyze fn) fn.fn_blocks lbl st` by
        fs[markerTheory.Abbrev_def] >>
      pop_assum SUBST1_TAC >>
      irule (SIMP_RULE std_ss [LET_THM] df_process_P) >>
      rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC) >>
      Cases_on `entry_val` >> fs[] >> pairarg_tac >> fs[],
      (* 3-4: R(st0') ∧ bounded_measure *)
      conj_tac >| [
        (* 3. R(st0') *)
        qpat_x_assum `Abbrev (st0' = _)` mp_tac >>
        simp[markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
        simp[dfAnalyzeDefsTheory.init_df_state_def] >>
        Cases_on `entry_val` >> fs[]
        >- (conj_tac >- fs[dfAnalyzeDefsTheory.init_df_state_def] >>
            rw[] >> imp_res_tac foldl_fempty_val >> fs[])
        >> Cases_on `x` >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
           conj_tac >- fs[dfAnalyzeDefsTheory.init_df_state_def] >>
           rw[] >> imp_res_tac foldl_fempty_val >> fs[],
        (* 4. bounded_measure *)
        fs[latticeDefsTheory.bounded_measure_def]
      ]
    ]
  ]) >>
  (* Conclusion: R(result) ⇒ P for all df_at/df_boundary values *)
  strip_tac >>
  qpat_x_assum `Abbrev (result = _)`
    (SUBST_ALL_TAC o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  conj_tac >> rpt gen_tac >| [
    Cases_on `FLOOKUP result.ds_inst (lbl,idx)` >> fs[] >> res_tac,
    Cases_on `FLOOKUP result.ds_boundary lbl` >> fs[] >> res_tac
  ]
QED

(* Boundary-only invariant: weaker than df_analyze_invariant — only needs
   P closed under join (not transfer/edge_transfer). Useful when P describes
   a property of boundary values that transfer may violate (e.g. "sublist of
   all_vars" for vardef, where transfer adds new variables).

   Key: boundary(lbl) is only ever updated to join(old_boundary, final_val).
   If P(old_boundary), then P(join(old_boundary, anything)) by the hypothesis
   ∀a b. P a ⇒ P (join a b). So P is preserved for all boundary values. *)
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
  rpt gen_tac >> simp[] >> strip_tac >>
  simp[dfAnalyzeDefsTheory.df_analyze_def,
       dfAnalyzeDefsTheory.df_boundary_def] >>
  qabbrev_tac `process = df_process_block dir bottom join transfer
    edge_transfer ctx entry_val (cfg_analyze fn) fn.fn_blocks` >>
  qabbrev_tac `st0' = case entry_val of
    NONE => init_df_state bottom (MAP (λbb. bb.bb_label) fn.fn_blocks)
    | SOME (lbl,v) => init_df_state bottom
        (MAP (λbb. bb.bb_label) fn.fn_blocks) with ds_boundary :=
        (init_df_state bottom (MAP (λbb. bb.bb_label) fn.fn_blocks)).
        ds_boundary |+ (lbl,v)` >>
  qabbrev_tac `deps = case dir of Forward => cfg_succs_of (cfg_analyze fn)
                                 | Backward => cfg_preds_of (cfg_analyze fn)` >>
  qabbrev_tac `wl0 = case dir of Forward => (cfg_analyze fn).cfg_dfs_pre
                                | Backward => (cfg_analyze fn).cfg_dfs_post` >>
  qabbrev_tac `result = SND (wl_iterate process deps wl0 st0')` >>
  mp_tac (
    let val base = INST_TYPE [alpha |-> ``:'a df_state``, beta |-> ``:string``]
                     (SIMP_RULE std_ss [LET_THM] wl_iterate_invariant_proof)
        val sp1 = Q.SPECL [`leq`, `m`, `b`, `process`, `deps`, `wl0`, `st0'`] base
        val R = ``\st:'a df_state.
          Q st /\ (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v)``
    in SIMP_RULE std_ss [] (SPEC R sp1) end) >>
  impl_tac >| [
    conj_tac >| [
      (* 1. leq *)
      rpt gen_tac >> strip_tac >> fs[],
      conj_tac >| [
        (* 2. R preserved *)
        rpt gen_tac >> DISCH_TAC >>
        `Q st` by fs[] >>
        `!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v` by fs[] >>
        conj_tac >- fs[] >>
        rpt gen_tac >> strip_tac >>
        `process lbl st = df_process_block dir bottom join transfer
          edge_transfer ctx entry_val (cfg_analyze fn) fn.fn_blocks lbl st` by
          fs[markerTheory.Abbrev_def] >>
        pop_assum SUBST_ALL_TAC >>
        fs[dfAnalyzeDefsTheory.df_process_block_def, dfAnalyzeDefsTheory.df_joined_val_def] >>
        pairarg_tac >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
        Cases_on `lbl = k` >> fs[]
        >- (`P (df_boundary bottom st k)` by
              (rw[dfAnalyzeDefsTheory.df_boundary_def] >>
               Cases_on `FLOOKUP st.ds_boundary k` >> fs[] >> res_tac) >>
            metis_tac[])
        >> res_tac,
        conj_tac >| [
          (* 3. R(st0') *)
          qpat_x_assum `Abbrev (st0' = _)` mp_tac >>
          simp[markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
          simp[dfAnalyzeDefsTheory.init_df_state_def] >>
          Cases_on `entry_val` >> fs[]
          >- (conj_tac >- fs[dfAnalyzeDefsTheory.init_df_state_def] >>
              rw[] >> imp_res_tac foldl_fempty_val >> fs[])
          >> Cases_on `x` >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
             conj_tac >- fs[dfAnalyzeDefsTheory.init_df_state_def] >>
             rw[] >> imp_res_tac foldl_fempty_val >> fs[],
          (* 4. bounded_measure *)
          fs[latticeDefsTheory.bounded_measure_def]
        ]
      ]
    ],
    (* Conclusion *)
    strip_tac >>
    qpat_x_assum `Abbrev (result = _)`
      (SUBST_ALL_TAC o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
    rpt gen_tac >>
    Cases_on `FLOOKUP result.ds_boundary lbl` >> fs[] >> res_tac
  ]
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
  rpt gen_tac >> simp[] >> strip_tac >>
  simp[dfAnalyzeDefsTheory.df_analyze_def,
       dfAnalyzeDefsTheory.df_boundary_def] >>
  qabbrev_tac `process = df_process_block dir bottom join transfer
    edge_transfer ctx entry_val (cfg_analyze fn) fn.fn_blocks` >>
  qabbrev_tac `st0' = case entry_val of
    NONE => init_df_state bottom (MAP (λbb. bb.bb_label) fn.fn_blocks)
    | SOME (lbl,v) => init_df_state bottom
        (MAP (λbb. bb.bb_label) fn.fn_blocks) with ds_boundary :=
        (init_df_state bottom (MAP (λbb. bb.bb_label) fn.fn_blocks)).
        ds_boundary |+ (lbl,v)` >>
  qabbrev_tac `deps = case dir of Forward => cfg_succs_of (cfg_analyze fn)
                                 | Backward => cfg_preds_of (cfg_analyze fn)` >>
  qabbrev_tac `wl0 = case dir of Forward => (cfg_analyze fn).cfg_dfs_pre
                                | Backward => (cfg_analyze fn).cfg_dfs_post` >>
  qabbrev_tac `result = SND (wl_iterate process deps wl0 st0')` >>
  mp_tac (
    let val base = INST_TYPE [alpha |-> ``:'a df_state``, beta |-> ``:string``]
                     (SIMP_RULE std_ss [LET_THM] wl_iterate_invariant_process_proof)
        val sp1 = Q.SPECL [`m`, `b`, `process`, `deps`, `wl0`, `st0'`] base
        val R = ``\st:'a df_state.
          Q st /\ (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v)``
    in SIMP_RULE std_ss [] (SPEC R sp1) end) >>
  impl_tac >| [
    conj_tac >| [
      (* 1. process-level termination *)
      rpt gen_tac >> strip_tac >> fs[],
      conj_tac >| [
        (* 2. R preserved *)
        rpt gen_tac >> DISCH_TAC >>
        `Q st` by fs[] >>
        `!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v` by fs[] >>
        conj_tac >- fs[] >>
        rpt gen_tac >> strip_tac >>
        `process lbl st = df_process_block dir bottom join transfer
          edge_transfer ctx entry_val (cfg_analyze fn) fn.fn_blocks lbl st` by
          fs[markerTheory.Abbrev_def] >>
        pop_assum SUBST_ALL_TAC >>
        fs[dfAnalyzeDefsTheory.df_process_block_def, dfAnalyzeDefsTheory.df_joined_val_def] >>
        pairarg_tac >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
        Cases_on `lbl = k` >> fs[]
        >- (`P (df_boundary bottom st k)` by
              (rw[dfAnalyzeDefsTheory.df_boundary_def] >>
               Cases_on `FLOOKUP st.ds_boundary k` >> fs[] >> res_tac) >>
            metis_tac[])
        >> res_tac,
        conj_tac >| [
          (* 3. R(st0') *)
          qpat_x_assum `Abbrev (st0' = _)` mp_tac >>
          simp[markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
          simp[dfAnalyzeDefsTheory.init_df_state_def] >>
          Cases_on `entry_val` >> fs[]
          >- (conj_tac >- fs[dfAnalyzeDefsTheory.init_df_state_def] >>
              rw[] >> imp_res_tac foldl_fempty_val >> fs[])
          >> Cases_on `x` >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
             conj_tac >- fs[dfAnalyzeDefsTheory.init_df_state_def] >>
             rw[] >> imp_res_tac foldl_fempty_val >> fs[],
          (* 4. bounded measure *)
          rpt gen_tac >> strip_tac >> fs[]
        ]
      ]
    ],
    (* Conclusion *)
    strip_tac >>
    qpat_x_assum `Abbrev (result = _)`
      (SUBST_ALL_TAC o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
    rpt gen_tac >>
    Cases_on `FLOOKUP result.ds_boundary lbl` >> fs[] >> res_tac
  ]
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
  rpt gen_tac >> simp[] >> strip_tac >>
  simp[dfAnalyzeDefsTheory.df_analyze_def,
       dfAnalyzeDefsTheory.df_boundary_def] >>
  qabbrev_tac `process = df_process_block dir bottom join transfer
    edge_transfer ctx entry_val (cfg_analyze fn) fn.fn_blocks` >>
  qabbrev_tac `st0' = case entry_val of
    NONE => init_df_state bottom (MAP (λbb. bb.bb_label) fn.fn_blocks)
    | SOME (lbl,v) => init_df_state bottom
        (MAP (λbb. bb.bb_label) fn.fn_blocks) with ds_boundary :=
        (init_df_state bottom (MAP (λbb. bb.bb_label) fn.fn_blocks)).
        ds_boundary |+ (lbl,v)` >>
  qabbrev_tac `deps = case dir of Forward => cfg_succs_of (cfg_analyze fn)
                                 | Backward => cfg_preds_of (cfg_analyze fn)` >>
  qabbrev_tac `wl0 = case dir of Forward => (cfg_analyze fn).cfg_dfs_pre
                                | Backward => (cfg_analyze fn).cfg_dfs_post` >>
  qabbrev_tac `result = SND (wl_iterate process deps wl0 st0')` >>
  mp_tac (
    let val base = INST_TYPE [alpha |-> ``:'a df_state``, beta |-> ``:string``]
                     (SIMP_RULE std_ss [LET_THM]
                        wl_iterate_invariant_process_restricted)
        val sp1 = Q.SPECL [`m`, `b`, `process`, `deps`, `wl0`, `st0'`] base
        val R = ``\st:'a df_state.
          Q st /\ (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v)``
    in SIMP_RULE std_ss [] (Q.SPECL [`^R`, `valid_lbl`] sp1) end) >>
  impl_tac >| [
    conj_tac >| [
      (* 1. process-level termination *)
      rpt gen_tac >> strip_tac >> fs[],
      conj_tac >| [
        (* 2. R preserved for valid labels *)
        rpt gen_tac >> DISCH_TAC >>
        `valid_lbl lbl` by fs[] >>
        `Q st` by fs[] >>
        `!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v` by fs[] >>
        conj_tac >- fs[] >>
        rpt gen_tac >> strip_tac >>
        `process lbl st = df_process_block dir bottom join transfer
          edge_transfer ctx entry_val (cfg_analyze fn) fn.fn_blocks lbl st` by
          fs[markerTheory.Abbrev_def] >>
        pop_assum SUBST_ALL_TAC >>
        fs[dfAnalyzeDefsTheory.df_process_block_def, dfAnalyzeDefsTheory.df_joined_val_def] >>
        pairarg_tac >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
        Cases_on `lbl = k` >> fs[]
        >- (`P (df_boundary bottom st k)` by
              (rw[dfAnalyzeDefsTheory.df_boundary_def] >>
               Cases_on `FLOOKUP st.ds_boundary k` >> fs[] >> res_tac) >>
            metis_tac[])
        >> res_tac,
        conj_tac >| [
          (* 3. R(st0') *)
          qpat_x_assum `Abbrev (st0' = _)` mp_tac >>
          simp[markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
          simp[dfAnalyzeDefsTheory.init_df_state_def] >>
          Cases_on `entry_val` >> fs[]
          >- (conj_tac >- fs[dfAnalyzeDefsTheory.init_df_state_def] >>
              rw[] >> imp_res_tac foldl_fempty_val >> fs[])
          >> Cases_on `x` >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
             conj_tac >- fs[dfAnalyzeDefsTheory.init_df_state_def] >>
             rw[] >> imp_res_tac foldl_fempty_val >> fs[],
          conj_tac >| [
            (* 4. bounded measure *)
            rpt gen_tac >> strip_tac >> fs[],
            conj_tac >| [
              (* 5. EVERY valid_lbl wl0 *)
              qpat_x_assum `Abbrev (wl0 = _)` mp_tac >>
              simp[markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
              Cases_on `dir` >> fs[],
              (* 6. valid_lbl => EVERY valid_lbl (deps lbl) *)
              rpt gen_tac >> strip_tac >>
              qpat_x_assum `Abbrev (deps = _)` mp_tac >>
              simp[markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
              Cases_on `dir` >> fs[]
            ]
          ]
        ]
      ]
    ],
    (* Conclusion *)
    strip_tac >>
    qpat_x_assum `Abbrev (result = _)`
      (SUBST_ALL_TAC o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
    rpt gen_tac >>
    Cases_on `FLOOKUP result.ds_boundary lbl` >> fs[] >> res_tac
  ]
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

(* Helper: if b ≠ lbl and lbl ∉ neighbors(b) and process b st = st,
   then process b (process lbl st) = process lbl st.
   Key structural lemma for deps_complete. *)
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
  rpt gen_tac >> strip_tac >>
  (* Boundary stability for non-lbl labels *)
  `!l. l <> lbl ==>
    df_boundary bottom
      (df_process_block dir bottom join transfer edge_transfer
        ctx entry_val cfg bbs lbl st) l = df_boundary bottom st l` by
    (rw[] >> irule df_process_block_boundary >> rw[]) >>
  (* Expand process b st = st *)
  qpat_x_assum `_ = st` mp_tac >> simp[df_process_block_def, df_joined_val_def] >>
  pairarg_tac >> strip_tac >>
  qabbrev_tac `nbrs_b = case dir of Forward => cfg_preds_of cfg b
                                   | Backward => cfg_succs_of cfg b` >>
  (* Expand process b (process lbl st) *)
  simp[df_process_block_def, df_joined_val_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  (* Neighbors see same boundaries *)
  `!nbr. MEM nbr nbrs_b ==>
    df_boundary bottom
      (st with <| ds_inst := inst_map'' ⊌ st.ds_inst;
                  ds_boundary := st.ds_boundary |+
                    (lbl, join (df_boundary bottom st lbl) final_val'') |>) nbr =
    df_boundary bottom st nbr` by
    (rw[df_boundary_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `nbr = lbl` >> rw[] >> Cases_on `dir` >>
     fs[markerTheory.Abbrev_def]) >>
  `df_boundary bottom
    (st with <| ds_inst := inst_map'' ⊌ st.ds_inst;
                ds_boundary := st.ds_boundary |+
                  (lbl, join (df_boundary bottom st lbl) final_val'') |>) b =
   df_boundary bottom st b` by
    rw[df_boundary_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `MAP (λnbr. edge_transfer ctx nbr b
        (df_boundary bottom
          (st with <| ds_inst := inst_map'' ⊌ st.ds_inst;
                      ds_boundary := st.ds_boundary |+
                        (lbl, join (df_boundary bottom st lbl) final_val'') |>) nbr))
       nbrs_b =
   MAP (λnbr. edge_transfer ctx nbr b (df_boundary bottom st nbr)) nbrs_b` by
    (irule listTheory.MAP_CONG >> rw[]) >>
  fs[] >>
  `final_val' = final_val /\ inst_map' = inst_map` by (
    (* Both df_fold_block calls for b have same joined expr once we show
       the ev_lbl branch MAP (cfg_preds ev_lbl on modified state) equals
       the one on st. Case-split to handle the nested case/if. *)
    qpat_x_assum `df_fold_block _ _ b _ _ = (final_val', _)` mp_tac >>
    Cases_on `entry_val` >> simp[]
    >- (strip_tac >> fs[])
    >> Cases_on `x` >> simp[] >>
    reverse IF_CASES_TAC >> simp[]
    >- (strip_tac >> fs[])
    (* b = ev_lbl case: cfg_preds ev_lbl = cfg_preds b = nbrs_b by Abbrev *)
    >> pop_assum (SUBST_ALL_TAC o SYM) >>
    `MAP (λnbr. edge_transfer ctx nbr b
          (df_boundary bottom
            (st with <| ds_inst := inst_map'' ⊌ st.ds_inst;
                        ds_boundary := st.ds_boundary |+
                          (lbl, join (df_boundary bottom st lbl) final_val'') |>) nbr))
        (case dir of Forward => cfg_preds_of cfg b
                   | Backward => cfg_succs_of cfg b) =
     MAP (λnbr. edge_transfer ctx nbr b (df_boundary bottom st nbr))
        (case dir of Forward => cfg_preds_of cfg b
                   | Backward => cfg_succs_of cfg b)` by
      (irule listTheory.MAP_CONG >> rw[] >>
       Cases_on `dir` >> fs[markerTheory.Abbrev_def]) >>
    fs[]) >>
  gvs[] >>
  (* From process b st = st: record equality gives component equalities *)
  `inst_map ⊌ st.ds_inst = st.ds_inst` by
    (qpat_x_assum `<|ds_inst := _; ds_boundary := _|> = st` mp_tac >>
     rw[df_state_component_equality]) >>
  `st.ds_boundary |+ (b, join (df_boundary bottom st b) final_val) =
   st.ds_boundary` by
    (qpat_x_assum `<|ds_inst := _; ds_boundary := _|> = st` mp_tac >>
     rw[df_state_component_equality]) >>
  (* From FUNION absorption: inst_map ⊑ st.ds_inst *)
  `inst_map ⊑ st.ds_inst` by
    metis_tac[finite_mapTheory.SUBMAP_FUNION_ABSORPTION] >>
  (* inst_map keys: FST=b, inst_map'' keys: FST=lbl, b≠lbl → DISJOINT *)
  `DISJOINT (FDOM inst_map) (FDOM inst_map'')` by
    (rw[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
     CCONTR_TAC >> fs[] >>
     `FST x = b` by
       (qpat_x_assum `df_fold_block _ _ b _ _ = _`
         (mp_tac o MATCH_MP df_fold_block_keys) >>
        disch_then (qspec_then `x` mp_tac) >>
        fs[finite_mapTheory.FLOOKUP_DEF]) >>
     `FST x = lbl` by
       (qpat_x_assum `df_fold_block _ _ lbl _ _ = _`
         (mp_tac o MATCH_MP df_fold_block_keys) >>
        disch_then (qspec_then `x` mp_tac) >>
        fs[finite_mapTheory.FLOOKUP_DEF]) >>
     fs[]) >>
  `inst_map ⊑ inst_map'' ⊌ st.ds_inst` by
    (irule finite_mapTheory.SUBMAP_FUNION >> DISJ2_TAC >> rw[]) >>
  simp[df_state_component_equality] >> conj_tac
  (* Goal 1: ds_inst — inst_map ⊌ (inst_map'' ⊌ st.ds_inst) = inst_map'' ⊌ st.ds_inst *)
  >- metis_tac[finite_mapTheory.SUBMAP_FUNION_ABSORPTION]
  (* Goal 2: ds_boundary *)
  >- (qpat_x_assum `st.ds_boundary |+ (b, _) = st.ds_boundary` mp_tac >>
      simp[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_UPDATE] >>
      strip_tac >>
      simp[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_UPDATE] >>
      rw[] >> metis_tac[])
QED


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
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `nbrs = case dir of Forward => cfg_preds_of cfg lbl
                                 | Backward => cfg_succs_of cfg lbl` >>
  (* Expand both: process lbl (process lbl st) and RHS process lbl st *)
  simp[df_process_block_def, df_joined_val_def] >>
  (* First pairarg_tac handles the outer fold (for process lbl applied to
     the result of the inner process). Need to handle naming carefully. *)
  pairarg_tac >> simp[] >>
  (* Second pairarg_tac handles the inner fold *)
  pairarg_tac >> simp[] >>
  (* At this point, the second fold's input state contains the unevaluated
     pair from the inner process. Use PairCases or reverse: first establish
     the MAP equality, then derive fold equality. *)
  (* Key: for any vals fv/im, neighbors see same boundaries *)
  `!fv im nbr. MEM nbr nbrs ==>
    df_boundary bottom
      (st with <| ds_inst := im ⊌ st.ds_inst;
                  ds_boundary := st.ds_boundary |+
                    (lbl, join (df_boundary bottom st lbl) fv) |>) nbr =
    df_boundary bottom st nbr` by
    (rw[df_boundary_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `nbr = lbl` >> fs[] >> Cases_on `dir` >>
     fs[markerTheory.Abbrev_def]) >>
  (* Apply to both inner fold (inst_map'/final_val') and outer fold *)
  `MAP (λnbr. edge_transfer ctx nbr lbl
        (df_boundary bottom
          (st with <| ds_inst := inst_map' ⊌ st.ds_inst;
                      ds_boundary := st.ds_boundary |+
                        (lbl, join (df_boundary bottom st lbl) final_val') |>) nbr))
       nbrs =
   MAP (λnbr. edge_transfer ctx nbr lbl (df_boundary bottom st nbr)) nbrs` by
    (irule listTheory.MAP_CONG >> rw[]) >>
  (* Now this MAP equality lets fs rewrite the outer fold's input *)
  fs[] >>
  (* Both folds have same input, so same output.
     Case-split on entry_val to handle ev_lbl branch MAP. *)
  `final_val = final_val' /\ inst_map = inst_map'` by (
    qpat_x_assum `df_fold_block _ _ lbl _ _ = (final_val, _)` mp_tac >>
    Cases_on `entry_val` >> simp[]
    >- (strip_tac >> fs[])
    >> Cases_on `x` >> simp[] >>
    reverse IF_CASES_TAC >> simp[]
    >- (strip_tac >> fs[])
    >> pop_assum (SUBST_ALL_TAC o SYM) >>
    `MAP (λnbr. edge_transfer ctx nbr lbl
          (df_boundary bottom
            (st with <| ds_inst := inst_map' ⊌ st.ds_inst;
                        ds_boundary := st.ds_boundary |+
                          (lbl, join (df_boundary bottom st lbl) final_val') |>) nbr))
        nbrs =
     MAP (λnbr. edge_transfer ctx nbr lbl (df_boundary bottom st nbr))
        nbrs` by
      (irule listTheory.MAP_CONG >> rw[]) >>
    fs[]) >>
  gvs[] >>
  simp[df_state_component_equality] >> conj_tac
  >- metis_tac[finite_mapTheory.FUNION_ASSOC, finite_mapTheory.FUNION_IDEMPOT]
  >- rw[df_boundary_def, finite_mapTheory.FLOOKUP_UPDATE]
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
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    wl_deps_complete process deps
Proof
  rpt gen_tac >> strip_tac >>
  simp[worklistDefsTheory.wl_deps_complete_def] >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac
  (* Case 1: b = lbl *)
  >- (CCONTR_TAC >>
      `~MEM b (case dir of Forward => cfg_preds_of cfg b
                          | Backward => cfg_succs_of cfg b)` by
        (Cases_on `dir` >> fs[] >> metis_tac[]) >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_self_idempotent) >>
      disch_then (qspecl_then [`dir`, `bottom`, `join`, `transfer`,
        `edge_transfer`, `ctx`, `entry_val`, `cfg`, `bbs`, `b`, `st`]
        mp_tac) >>
      impl_tac >- rw[] >>
      fs[])
  (* Case 2: process b st = st *)
  >- (CCONTR_TAC >>
      `b <> lbl` by (CCONTR_TAC >> fs[]) >>
      `~MEM lbl (case dir of Forward => cfg_preds_of cfg b
                            | Backward => cfg_succs_of cfg b)` by
        (Cases_on `dir` >> fs[] >> metis_tac[]) >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_process_stable_after) >>
      disch_then (qspecl_then [`dir`, `bottom`, `join`, `transfer`,
        `edge_transfer`, `ctx`, `entry_val`, `cfg`, `bbs`, `lbl`, `b`, `st`]
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
  rpt strip_tac >> fs[] >> DECIDE_TAC
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
