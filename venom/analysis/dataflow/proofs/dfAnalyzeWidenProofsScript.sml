(*
 * Generic Dataflow Analysis with Widening — Proofs
 *
 * Convergence and correctness theorems for widening-based iteration.
 * Mirror of dfAnalyzeProofs for the df_analyze_widen variant.
 *
 * TOP-LEVEL:
 *   df_analyze_widen_fixpoint_proof       — worklist converges to fixpoint
 *   df_widen_at_intra_transfer_proof      — within-block transfer
 *   df_widen_at_inter_transfer_proof      — inter-block: fold input = widened join
 *   df_analyze_widen_invariant_proof      — lattice invariant propagation
 *   df_process_widen_inflationary_proof   — monotone ops → inflationary
 *   df_process_widen_deps_complete_proof  — CFG inverse → deps complete
 *)

Theory dfAnalyzeWidenProofs
Ancestors
  dfAnalyzeWidenDefs dfAnalyzeProofs worklistProofs cfgDefs

(* Convergence: widening ensures the worklist empties.
   The widening operator must guarantee that the sequence of entry values
   for each block stabilizes after finitely many steps.
   widen_bounded: widening produces a value that is an upper bound AND
   the ascending chain from repeated widening has bounded length. *)
Theorem df_analyze_widen_fixpoint_proof:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (leq : 'a df_widen_state -> 'a df_widen_state -> bool)
   m b (P : 'a df_widen_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_widen_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let all_lbls = cfg.cfg_dfs_pre in
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with dws_boundary := st0.dws_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps
    ==>
      is_fixpoint process all_lbls
        (df_analyze_widen dir bottom join widen threshold
           transfer edge_transfer ctx entry_val fn)
Proof
  rpt gen_tac >> simp[dfAnalyzeWidenDefsTheory.df_analyze_widen_def] >>
  strip_tac >>
  irule worklistProofsTheory.wl_iterate_fixpoint_proof >>
  rpt conj_tac
  >- (rw[] >> Cases_on `dir` >> fs[] >>
      metis_tac[dfAnalyzeProofsTheory.cfg_dfs_pre_mem_post])
  >- fs[]
  >- (qexistsl_tac [`P`, `b`, `leq`, `m`] >> rw[] >>
      Cases_on `entry_val` >> fs[] >>
      Cases_on `x` >> fs[])
QED

(* ===== Local helpers for fixpoint analysis ===== *)

(* At fixpoint, process lbl result = result. Expanding the definition,
   the if-guard forces the "unchanged" branch, giving component equalities.
   This is the key lemma: it extracts FUNION/boundary/entry absorption. *)
Theorem df_widen_fixpoint_newst_eq[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl result all_lbls bb final_val inst_map entry.
    is_fixpoint
      (df_process_block_widen dir bottom join widen threshold
        transfer edge_transfer ctx entry_val cfg bbs) all_lbls result /\
    MEM lbl all_lbls /\
    lookup_block lbl bbs = SOME bb /\
    df_fold_block dir (transfer ctx) lbl bb.bb_instructions entry =
      (final_val, inst_map) /\
    entry = (let neighbors = (case dir of Forward => cfg_preds_of cfg lbl
                                        | Backward => cfg_succs_of cfg lbl) in
             let edge_vals = MAP (λnbr. edge_transfer ctx nbr lbl
                                  (df_widen_boundary bottom result nbr)) neighbors in
             let joined = (case edge_vals of
                             [] => (case entry_val of NONE => bottom
                                    | SOME (ev_lbl, v) =>
                                        if lbl = ev_lbl then v else bottom)
                           | _ => FOLDL join bottom edge_vals) in
               if df_widen_visits result lbl >= threshold then
                 widen (df_widen_entry bottom result lbl) joined
               else joined)
    ==>
      FUNION inst_map result.dws_inst = result.dws_inst /\
      result.dws_boundary |+ (lbl,
        join (df_widen_boundary bottom result lbl) final_val) =
        result.dws_boundary /\
      result.dws_entry |+ (lbl, entry) = result.dws_entry
Proof
  rpt gen_tac >> strip_tac >>
  fs[worklistDefsTheory.is_fixpoint_def] >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >>
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def, LET_THM] >>
  strip_tac >>
  (* The hypothesis is (if ... then result else ...) = result, already stripped.
     Actually, strip_tac introduced the if=result equation as an assumption.
     Use Cases_on the if-condition. *)
  pop_assum mp_tac >>
  IF_CASES_TAC
  >- (* new_st = result: hypothesis gives result = result, trivially true.
        Conclusion follows from new_st = result via component equality *)
     (strip_tac >>
      pop_assum (K ALL_TAC) >>
      fs[dfAnalyzeWidenDefsTheory.df_widen_state_component_equality])
  >- (* new_st ≠ result: hypothesis gives new_st with visits = result.
        Component equality gives inst/boundary/entry equalities. *)
     (strip_tac >>
      fs[dfAnalyzeWidenDefsTheory.df_widen_state_component_equality])
QED

(* At fixpoint, fold's inst_map entries are all in result.dws_inst,
   boundary is absorbed, and entry is cached.
   Combined proof: expands process directly, uses IF_CASES_TAC for guard,
   then derives SUBMAP + boundary/entry absorption from component equality. *)
Theorem df_widen_fixpoint_fold_submap[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl result all_lbls bb final_val inst_map entry.
    is_fixpoint
      (df_process_block_widen dir bottom join widen threshold
        transfer edge_transfer ctx entry_val cfg bbs) all_lbls result /\
    MEM lbl all_lbls /\
    lookup_block lbl bbs = SOME bb /\
    df_fold_block dir (transfer ctx) lbl bb.bb_instructions entry =
      (final_val, inst_map) /\
    entry = (let neighbors = (case dir of Forward => cfg_preds_of cfg lbl
                                        | Backward => cfg_succs_of cfg lbl) in
             let edge_vals = MAP (λnbr. edge_transfer ctx nbr lbl
                                  (df_widen_boundary bottom result nbr)) neighbors in
             let joined = (case edge_vals of
                             [] => (case entry_val of NONE => bottom
                                    | SOME (ev_lbl, v) =>
                                        if lbl = ev_lbl then v else bottom)
                           | _ => FOLDL join bottom edge_vals) in
               if df_widen_visits result lbl >= threshold then
                 widen (df_widen_entry bottom result lbl) joined
               else joined)
    ==>
      inst_map ⊑ result.dws_inst /\
      df_widen_boundary bottom result lbl =
        join (df_widen_boundary bottom result lbl) final_val /\
      df_widen_entry bottom result lbl = entry
Proof
  rpt gen_tac >> strip_tac >>
  (* Get component equalities from newst_eq *)
  drule df_widen_fixpoint_newst_eq >> rpt (disch_then drule) >>
  strip_tac >>
  rpt conj_tac
  (* inst_map ⊑ result.dws_inst *)
  >- metis_tac[finite_mapTheory.SUBMAP_FUNION_ABSORPTION]
  (* boundary absorption *)
  >- (`lbl IN FDOM result.dws_boundary` by
       (`lbl IN FDOM (result.dws_boundary |+
          (lbl, join (df_widen_boundary bottom result lbl) final_val))` by
          simp[finite_mapTheory.FDOM_FUPDATE] >>
        metis_tac[]) >>
      fs[dfAnalyzeWidenDefsTheory.df_widen_boundary_def,
         finite_mapTheory.FLOOKUP_DEF] >>
      `(result.dws_boundary |+
         (lbl, join (result.dws_boundary ' lbl) final_val)) ' lbl =
       join (result.dws_boundary ' lbl) final_val` by
        simp[finite_mapTheory.FAPPLY_FUPDATE_THM] >>
      metis_tac[])
  (* entry absorption *)
  >- (`lbl IN FDOM result.dws_entry` by
       (`lbl IN FDOM (result.dws_entry |+ (lbl, entry))` by
          simp[finite_mapTheory.FDOM_FUPDATE] >>
        metis_tac[]) >>
      fs[dfAnalyzeWidenDefsTheory.df_widen_entry_def,
         finite_mapTheory.FLOOKUP_DEF] >>
      `(result.dws_entry |+ (lbl, entry)) ' lbl = entry` by
        simp[finite_mapTheory.FAPPLY_FUPDATE_THM] >>
      metis_tac[])
QED

(* SUBMAP + FLOOKUP → df_widen_at *)
Theorem df_widen_at_from_submap[local]:
  !im (st : 'a df_widen_state) bottom lbl idx v.
    im ⊑ st.dws_inst /\ FLOOKUP im (lbl, idx) = SOME v ==>
    df_widen_at bottom st lbl idx = v
Proof
  rw[dfAnalyzeWidenDefsTheory.df_widen_at_def] >>
  fs[finite_mapTheory.SUBMAP_DEF, finite_mapTheory.FLOOKUP_DEF] >>
  metis_tac[]
QED

(* Combined: at fixpoint, df_widen_at values follow transfer relation *)
Theorem df_widen_fixpoint_at[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl result all_lbls bb instrs entry.
    is_fixpoint
      (df_process_block_widen dir bottom join widen threshold
        transfer edge_transfer ctx entry_val cfg bbs) all_lbls result /\
    MEM lbl all_lbls /\
    lookup_block lbl bbs = SOME bb /\
    instrs = bb.bb_instructions /\
    entry = (let neighbors = (case dir of Forward => cfg_preds_of cfg lbl
                                        | Backward => cfg_succs_of cfg lbl) in
             let edge_vals = MAP (λnbr. edge_transfer ctx nbr lbl
                                  (df_widen_boundary bottom result nbr)) neighbors in
             let joined = (case edge_vals of
                             [] => (case entry_val of NONE => bottom
                                    | SOME (ev_lbl, v) =>
                                        if lbl = ev_lbl then v else bottom)
                           | _ => FOLDL join bottom edge_vals) in
             let visits = df_widen_visits result lbl in
               if visits >= threshold then
                 widen (df_widen_entry bottom result lbl) joined
               else joined)
    ==>
      (dir = Forward ==>
        df_widen_at bottom result lbl 0 = entry /\
        !i. i < LENGTH instrs ==>
          df_widen_at bottom result lbl (SUC i) =
            transfer ctx (EL i instrs) (df_widen_at bottom result lbl i)) /\
      (dir = Backward ==>
        df_widen_at bottom result lbl (LENGTH instrs) = entry /\
        !i. i < LENGTH instrs ==>
          df_widen_at bottom result lbl i =
            transfer ctx (EL i instrs) (df_widen_at bottom result lbl (SUC i)))
Proof
  rpt gen_tac >> strip_tac >>
  (* Compute the fold *)
  `?fv im. df_fold_block dir (transfer ctx) lbl bb.bb_instructions entry =
     (fv, im)` by metis_tac[pairTheory.PAIR] >>
  (* Use mp_tac + qspecl_then instead of drule_all (LET in hyps blocks drule) *)
  mp_tac df_widen_fixpoint_fold_submap >>
  disch_then (qspecl_then [`dir`, `bottom`, `join`, `widen`, `threshold`,
    `transfer`, `edge_transfer`, `ctx`, `entry_val`, `cfg`, `bbs`, `lbl`,
    `result`, `all_lbls`, `bb`, `fv`, `im`, `entry`] mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  Cases_on `dir` >> fs[dfAnalyzeDefsTheory.df_fold_block_def] >> strip_tac >> rw[]
  (* Forward: entry *)
  >- (drule dfAnalyzeProofsTheory.df_fold_forward_at >> strip_tac >>
      irule df_widen_at_from_submap >> qexists_tac `im` >> fs[])
  (* Forward: transfer *)
  >- (drule dfAnalyzeProofsTheory.df_fold_forward_at >> strip_tac >>
      `FLOOKUP im (lbl, SUC i) =
       SOME (transfer ctx (EL i bb.bb_instructions)
               (THE (FLOOKUP im (lbl, i))))` by
        (first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
      `df_widen_at bottom result lbl (SUC i) =
       transfer ctx (EL i bb.bb_instructions) (THE (FLOOKUP im (lbl, i)))` by
        (irule df_widen_at_from_submap >> qexists_tac `im` >> fs[]) >>
      `df_widen_at bottom result lbl i = THE (FLOOKUP im (lbl, i))` by
        (irule df_widen_at_from_submap >> qexists_tac `im` >>
         Cases_on `i` >- fs[]
         >- (first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
             strip_tac >> fs[])) >>
      fs[])
  (* Backward: entry *)
  >- (drule dfAnalyzeProofsTheory.df_fold_backward_at >> strip_tac >>
      irule df_widen_at_from_submap >> qexists_tac `im` >> fs[])
  (* Backward: transfer *)
  >- (drule dfAnalyzeProofsTheory.df_fold_backward_at >> strip_tac >>
      `FLOOKUP im (lbl, SUC i) <> NONE` by
        (Cases_on `SUC i < LENGTH bb.bb_instructions`
         >- (first_x_assum (qspec_then `SUC i` mp_tac) >> simp[])
         >- (`SUC i = LENGTH bb.bb_instructions` by simp[] >> fs[])) >>
      `df_widen_at bottom result lbl i =
       transfer ctx (EL i bb.bb_instructions)
         (THE (FLOOKUP im (lbl, SUC i)))` by
        (first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
         irule df_widen_at_from_submap >> qexists_tac `im` >> fs[]) >>
      `df_widen_at bottom result lbl (SUC i) = THE (FLOOKUP im (lbl, SUC i))` by
        (irule df_widen_at_from_submap >> qexists_tac `im` >>
         Cases_on `SUC i < LENGTH bb.bb_instructions`
         >- (first_x_assum (qspec_then `SUC i` mp_tac) >> simp[] >>
             strip_tac >> fs[])
         >- (`SUC i = LENGTH bb.bb_instructions` by simp[] >> fs[])) >>
      fs[])
QED

(* Within a block, transfer relates adjacent instruction points.
   Same structure as df_at_intra_transfer but for df_widen_state. *)
Theorem df_widen_at_intra_transfer_proof:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn lbl (bb : basic_block) idx.
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let all_lbls = cfg.cfg_dfs_pre in
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      is_fixpoint process all_lbls result /\
      MEM lbl all_lbls /\
      lookup_block lbl bbs = SOME bb /\
      SUC idx ≤ LENGTH bb.bb_instructions
    ==>
      (dir = Forward ==>
        df_widen_at bottom result lbl (SUC idx) =
          transfer ctx (EL idx bb.bb_instructions)
                       (df_widen_at bottom result lbl idx)) /\
      (dir = Backward ==>
        df_widen_at bottom result lbl idx =
          transfer ctx (EL idx bb.bb_instructions)
                       (df_widen_at bottom result lbl (SUC idx)))
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  mp_tac df_widen_fixpoint_at >>
  disch_then (qspecl_then [`dir`, `bottom`, `join`, `widen`, `threshold`,
    `transfer`, `edge_transfer`, `ctx`, `entry_val`,
    `cfg_analyze fn`, `fn.fn_blocks`, `lbl`,
    `df_analyze_widen dir bottom join widen threshold
       transfer edge_transfer ctx entry_val fn`,
    `(cfg_analyze fn).cfg_dfs_pre`, `bb`, `bb.bb_instructions`] mp_tac) >>
  simp[]
QED

(* Inter-block transfer for widening variant.
   The fold input equals the (possibly widened) join of neighbor boundaries.
   Unlike the base case, widening may have been applied if visits >= threshold. *)
Theorem df_widen_at_inter_transfer_proof:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn lbl (bb : basic_block).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let all_lbls = cfg.cfg_dfs_pre in
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      is_fixpoint process all_lbls result /\
      MEM lbl all_lbls /\
      lookup_block lbl bbs = SOME bb
    ==>
      (dir = Forward ==>
        df_widen_at bottom result lbl 0 =
          df_widen_entry bottom result lbl) /\
      (dir = Backward ==>
        df_widen_at bottom result lbl (LENGTH bb.bb_instructions) =
          df_widen_entry bottom result lbl)
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  (* Get fixpoint_at: gives df_widen_at(0) = entry for Forward, etc. *)
  `?fv im. df_fold_block dir (transfer ctx) lbl bb.bb_instructions
     (let neighbors = (case dir of Forward => cfg_preds_of (cfg_analyze fn) lbl
                                  | Backward => cfg_succs_of (cfg_analyze fn) lbl) in
      let edge_vals = MAP (λnbr. edge_transfer ctx nbr lbl
                            (df_widen_boundary bottom
                              (df_analyze_widen dir bottom join widen threshold
                                transfer edge_transfer ctx entry_val fn) nbr)) neighbors in
      let joined = (case edge_vals of
                      [] => (case entry_val of NONE => bottom
                             | SOME (ev_lbl, v) => if lbl = ev_lbl then v else bottom)
                    | _ => FOLDL join bottom edge_vals) in
        if df_widen_visits (df_analyze_widen dir bottom join widen threshold
             transfer edge_transfer ctx entry_val fn) lbl >= threshold then
          widen (df_widen_entry bottom (df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn) lbl) joined
        else joined) = (fv, im)` by metis_tac[pairTheory.PAIR] >>
  (* Get fold_submap for entry = df_widen_entry *)
  mp_tac df_widen_fixpoint_fold_submap >>
  disch_then (qspecl_then [`dir`, `bottom`, `join`, `widen`, `threshold`,
    `transfer`, `edge_transfer`, `ctx`, `entry_val`,
    `cfg_analyze fn`, `fn.fn_blocks`, `lbl`,
    `df_analyze_widen dir bottom join widen threshold
       transfer edge_transfer ctx entry_val fn`,
    `(cfg_analyze fn).cfg_dfs_pre`, `bb`, `fv`, `im`] mp_tac) >>
  simp[] >> strip_tac >>
  (* Get fixpoint_at *)
  mp_tac df_widen_fixpoint_at >>
  disch_then (qspecl_then [`dir`, `bottom`, `join`, `widen`, `threshold`,
    `transfer`, `edge_transfer`, `ctx`, `entry_val`,
    `cfg_analyze fn`, `fn.fn_blocks`, `lbl`,
    `df_analyze_widen dir bottom join widen threshold
       transfer edge_transfer ctx entry_val fn`,
    `(cfg_analyze fn).cfg_dfs_pre`, `bb`, `bb.bb_instructions`] mp_tac) >>
  simp[] >> strip_tac >>
  (* Now we have: df_widen_at(0) = entry AND df_widen_entry = entry *)
  Cases_on `dir` >> fs[]
QED

(* Component extraction: the result of df_process_block_widen is either
   st unchanged, or has predictable inst/boundary/entry components.
   This avoids UNCURRY issues when reasoning about the result. *)
Theorem df_widen_process_components:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl (st:'a df_widen_state).
    let neighbors = (case dir of Forward => cfg_preds_of cfg lbl
                                | Backward => cfg_succs_of cfg lbl) in
    let edge_vals = MAP (\nbr. edge_transfer ctx nbr lbl
                          (df_widen_boundary bottom st nbr)) neighbors in
    let joined = (case edge_vals of
                    [] => (case entry_val of NONE => bottom
                           | SOME (ev_lbl,v) => if lbl = ev_lbl then v
                                                else bottom)
                  | v4::v5 => FOLDL join bottom edge_vals) in
    let entry = (if df_widen_visits st lbl >= threshold
                 then widen (df_widen_entry bottom st lbl) joined
                 else joined) in
    let instrs = (case lookup_block lbl bbs of
                    NONE => [] | SOME bb => bb.bb_instructions) in
    let (final_val, inst_map) =
          df_fold_block dir (transfer ctx) lbl instrs entry in
    let result = df_process_block_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val cfg bbs lbl st in
      (result = st \/
       (result.dws_inst = inst_map ⊌ st.dws_inst /\
        result.dws_boundary = st.dws_boundary |+
          (lbl, join (df_widen_boundary bottom st lbl) final_val) /\
        result.dws_entry = st.dws_entry |+ (lbl, entry) /\
        result.dws_visits = st.dws_visits |+
          (lbl, df_widen_visits st lbl + 1)))
Proof
  rpt gen_tac >>
  simp_tac std_ss [LET_THM,
    dfAnalyzeWidenDefsTheory.df_process_block_widen_def] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  rpt IF_CASES_TAC >> simp[]
QED

(* SML helper: LET-free version of process_components for mp_tac *)
val process_components =
  SIMP_RULE std_ss [LET_THM] df_widen_process_components;

(* FOLDL join P helper *)
val foldl_join_P = prove(
  ``!xs (a:'a). P a /\ (!x y. P x /\ P y ==> P (join x y)) /\
    EVERY P xs ==> P (FOLDL join a xs)``,
  Induct >> rw[] >> first_x_assum irule >> fs[] >> metis_tac[]);

(* Helper: joined value preserves P *)
Triviality joined_P:
  P bottom /\
  (case entry_val of NONE => T | SOME (lbl, v) => P v) /\
  (!a b. P a /\ P b ==> P (join a b)) /\
  EVERY P edge_vals ==>
  P (case edge_vals of
       [] => (case entry_val of NONE => bottom
              | SOME (ev_lbl,v) => if lbl = ev_lbl then v else bottom)
     | _ => FOLDL join bottom edge_vals)
Proof
  Cases_on `edge_vals` >> rw[]
  >- (Cases_on `entry_val` >> fs[] >>
      Cases_on `x` >> fs[] >> rw[] >> fs[])
  >> irule foldl_join_P >> fs[listTheory.EVERY_DEF] >> metis_tac[]
QED

(* Shared tactics for proving P preservation *)
val P_edge_vals_tac =
  simp[listTheory.EVERY_MEM, listTheory.MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >>
  qpat_assum `!src dst a. P a ==> P (edge_transfer _ _ _ _)`
    (fn eth => irule eth) >> simp[];

val P_joined_tac =
  irule joined_P >> simp[] >> P_edge_vals_tac;

val P_init_val_tac =
  IF_CASES_TAC
  >- (qpat_assum `!a b. P a /\ P b ==> P (widen a b)`
        (fn wth => irule wth) >> simp[] >> P_joined_tac)
  >> P_joined_tac;

(* df_process_block_widen preserves element-level P for inst, boundary, entry *)
Theorem df_widen_process_P[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl (st : 'a df_widen_state).
    P bottom /\
    (case entry_val of NONE => T | SOME (lbl, v) => P v) /\
    (!a b. P a /\ P b ==> P (join a b)) /\
    (!a b. P a /\ P b ==> P (widen a b)) /\
    (!inst a. P a ==> P (transfer ctx inst a)) /\
    (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
    (!k v. FLOOKUP st.dws_inst k = SOME v ==> P v) /\
    (!k v. FLOOKUP st.dws_boundary k = SOME v ==> P v) /\
    (!k v. FLOOKUP st.dws_entry k = SOME v ==> P v)
    ==>
    let result = df_process_block_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val cfg bbs lbl st in
    (!k v. FLOOKUP result.dws_inst k = SOME v ==> P v) /\
    (!k v. FLOOKUP result.dws_boundary k = SOME v ==> P v) /\
    (!k v. FLOOKUP result.dws_entry k = SOME v ==> P v)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  mp_tac (Q.SPECL [`dir`,`bottom`,`join`,`widen`,`threshold`,`transfer`,
    `edge_transfer`,`ctx`,`entry_val`,`cfg`,`bbs`,`lbl`,`st`]
    process_components) >>
  pairarg_tac >> simp[] >> strip_tac
  (* Case 1: result = st *)
  >- (rw[] >> metis_tac[])
  (* Case 2: component equalities — establish P facts then close *)
  >>
  (* Fact A: P for boundary lookups *)
  `!l. P (df_widen_boundary bottom st l)` by (
    rw[dfAnalyzeWidenDefsTheory.df_widen_boundary_def] >>
    Cases_on `FLOOKUP st.dws_boundary l` >> simp[] >> metis_tac[]) >>
  (* Fact B: P for entry lookups *)
  `!l. P (df_widen_entry bottom st l)` by (
    rw[dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
    Cases_on `FLOOKUP st.dws_entry l` >> simp[] >> metis_tac[]) >>
  (* Fact C: P(final_val) and FLOOKUP inst_map P — via df_fold_block_P *)
  `P final_val /\ !k v. FLOOKUP inst_map k = SOME v ==> P v` by (
    qpat_assum `df_fold_block _ _ _ _ _ = _`
      (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
        dfAnalyzeProofsTheory.df_fold_block_P)) >>
    impl_tac >- P_init_val_tac >>
    impl_tac >- metis_tac[] >>
    simp[]) >>
  (* Close three FLOOKUP obligations *)
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `_.dws_inst = _` (fn th => pop_assum
        (mp_tac o REWRITE_RULE [th, finite_mapTheory.FLOOKUP_FUNION])) >>
      Cases_on `FLOOKUP inst_map k` >> simp[] >> metis_tac[])
  >- (qpat_x_assum `_.dws_boundary = _` (fn th => pop_assum
        (mp_tac o REWRITE_RULE [th, finite_mapTheory.FLOOKUP_UPDATE])) >>
      IF_CASES_TAC >> simp[]
      >- (strip_tac >> gvs[] >>
          qpat_assum `!a b. P a /\ P b ==> P (join a b)`
            (fn jth => irule jth) >> simp[])
      >> strip_tac >> metis_tac[])
  >> qpat_x_assum `_.dws_entry = _` (fn th => pop_assum
       (mp_tac o REWRITE_RULE [th, finite_mapTheory.FLOOKUP_UPDATE])) >>
     IF_CASES_TAC >> simp[]
     >- (strip_tac >> gvs[] >> P_init_val_tac)
     >> strip_tac >> metis_tac[]
QED

(* Lattice invariant for widening: if P is closed under all operations
   including widen, then P holds everywhere in the result.
   Requires convergence so WHILE result is well-defined. *)
Theorem df_analyze_widen_invariant_proof:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn (P : 'a -> bool)
   (leq : 'a df_widen_state -> 'a df_widen_state -> bool)
   m b (Q : 'a df_widen_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let st0 = init_df_widen_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      (* element-level closure *)
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a /\ P b ==> P (join a b)) /\
      (!a b. P a /\ P b ==> P (widen a b)) /\
      (!inst a. P a ==> P (transfer ctx inst a)) /\
      (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
      (* convergence *)
      (!lbl st. Q st ==> leq st (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with dws_boundary := st0.dws_boundary |+ (lbl, v))) /\
      bounded_measure Q leq m b
    ==>
      (!lbl idx. P (df_widen_at bottom result lbl idx)) /\
      (!lbl. P (df_widen_boundary bottom result lbl)) /\
      (!lbl. P (df_widen_entry bottom result lbl))
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_analyze_widen_def,
       dfAnalyzeWidenDefsTheory.df_widen_at_def,
       dfAnalyzeWidenDefsTheory.df_widen_boundary_def,
       dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
  qabbrev_tac `process = df_process_block_widen dir bottom join widen threshold
    transfer edge_transfer ctx entry_val (cfg_analyze fn) fn.fn_blocks` >>
  qabbrev_tac `st0' = case entry_val of
    NONE => init_df_widen_state bottom (MAP (λbb. bb.bb_label) fn.fn_blocks)
    | SOME (lbl,v) => init_df_widen_state bottom
        (MAP (λbb. bb.bb_label) fn.fn_blocks) with dws_boundary :=
        (init_df_widen_state bottom (MAP (λbb. bb.bb_label) fn.fn_blocks)).
        dws_boundary |+ (lbl,v)` >>
  qabbrev_tac `deps = case dir of Forward => cfg_succs_of (cfg_analyze fn)
                                 | Backward => cfg_preds_of (cfg_analyze fn)` >>
  qabbrev_tac `wl0 = case dir of Forward => (cfg_analyze fn).cfg_dfs_pre
                                | Backward => (cfg_analyze fn).cfg_dfs_post` >>
  qabbrev_tac `result = SND (wl_iterate process deps wl0 st0')` >>
  (* Instantiate wl_iterate_invariant_proof with R *)
  mp_tac (
    let val base = INST_TYPE [alpha |-> ``:'a df_widen_state``, beta |-> ``:string``]
                     (SIMP_RULE std_ss [LET_THM] wl_iterate_invariant_proof)
        val sp1 = Q.SPECL [`leq`, `m`, `b`, `process`, `deps`, `wl0`, `st0'`] base
        val R = ``\st:'a df_widen_state.
          Q st /\ (!k v. FLOOKUP st.dws_inst k = SOME v ==> P v) /\
                  (!k v. FLOOKUP st.dws_boundary k = SOME v ==> P v) /\
                  (!k v. FLOOKUP st.dws_entry k = SOME v ==> P v)``
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
      `process lbl st = df_process_block_widen dir bottom join widen threshold
        transfer edge_transfer ctx entry_val (cfg_analyze fn)
        fn.fn_blocks lbl st` by
        fs[markerTheory.Abbrev_def] >>
      pop_assum SUBST1_TAC >>
      irule (SIMP_RULE std_ss [LET_THM] df_widen_process_P) >>
      rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC) >>
      Cases_on `entry_val` >> fs[] >> pairarg_tac >> fs[],
      (* 3-4: R(st0') ∧ bounded_measure *)
      conj_tac >| [
        (* 3. R(st0') *)
        qpat_x_assum `Abbrev (st0' = _)` mp_tac >>
        simp[markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
        simp[dfAnalyzeWidenDefsTheory.init_df_widen_state_def] >>
        Cases_on `entry_val` >> fs[]
        >- (conj_tac
            >- fs[dfAnalyzeWidenDefsTheory.init_df_widen_state_def] >>
            rw[] >> imp_res_tac dfAnalyzeProofsTheory.foldl_fempty_val >> fs[])
        >> Cases_on `x` >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
           conj_tac
           >- fs[dfAnalyzeWidenDefsTheory.init_df_widen_state_def] >>
           rw[] >> imp_res_tac dfAnalyzeProofsTheory.foldl_fempty_val >> fs[],
        (* 4. bounded_measure *)
        fs[latticeDefsTheory.bounded_measure_def]
      ]
    ]
  ]) >>
  (* Conclusion: R(result) ⇒ P for all values *)
  strip_tac >>
  qpat_x_assum `Abbrev (result = _)`
    (SUBST_ALL_TAC o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rpt conj_tac >> rpt gen_tac >| [
    Cases_on `FLOOKUP result.dws_inst (lbl,idx)` >> fs[] >> res_tac,
    Cases_on `FLOOKUP result.dws_boundary lbl` >> fs[] >> res_tac,
    Cases_on `FLOOKUP result.dws_entry lbl` >> fs[] >> res_tac
  ]
QED

(* FOLDL join acc xs is sound for any xs when sound is first-arg closed.
   Note: join:'a->'b->'a (not 'a->'a->'a) because FOLDL generalizes. *)
val foldl_join_sound = prove(
  ``!xs (join:'a -> 'b -> 'a) acc (sound:'a -> 'c -> bool).
    (!a b s. sound a s ==> sound (join a b) s) /\
    (!s. sound acc s) ==>
    !s. sound (FOLDL join acc xs) s``,
  Induct >> rw[listTheory.FOLDL] >>
  first_x_assum irule >> metis_tac[]);

(* The joined value is sound (first-arg closure suffices, edge_vals irrelevant) *)
val joined_sound = prove(
  ``(!a b s. sound a s ==> sound (join a b) s) /\
    (!s. sound bottom s) /\
    (case entry_val of NONE => T | SOME (lbl,v) => !s. sound v s)
    ==>
    !s. sound (case edge_vals of
           [] => (case entry_val of NONE => bottom
                  | SOME (ev_lbl,v) => if lbl = ev_lbl then v else bottom)
         | v4::v5 => FOLDL join bottom edge_vals) s``,
  strip_tac >> gen_tac >> Cases_on `edge_vals` >> rw[]
  >- (Cases_on `entry_val` >> fs[] >>
      Cases_on `x` >> fs[] >> rw[] >> fs[])
  >> `!s. sound (FOLDL join bottom (h::t)) s` suffices_by simp[] >>
     irule foldl_join_sound >> fs[]);

(* process preserves entry-only soundness (no transfer/edge_transfer needed) *)
Triviality df_widen_process_entry_sound:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl (st : 'a df_widen_state) (sound : 'a -> 'b -> bool).
    (!a b s. sound a s ==> sound (join a b) s) /\
    (!a b s. sound a s ==> sound (widen a b) s) /\
    (!s. sound bottom s) /\
    (case entry_val of NONE => T | SOME (lbl, v) => !s. sound v s) /\
    (!k v. FLOOKUP st.dws_entry k = SOME v ==> !s. sound v s)
    ==>
    let result = df_process_block_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val cfg bbs lbl st in
    (!k v. FLOOKUP result.dws_entry k = SOME v ==> !s. sound v s)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  simp_tac std_ss [dfAnalyzeWidenDefsTheory.df_process_block_widen_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  IF_CASES_TAC >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `lbl = k` >> fs[finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> TRY (metis_tac[]) >> TRY (res_tac >> fs[]) >>
  (* Remaining goals: k=lbl, new_st<>st, entry is widen(...) or joined *)
  TRY (qpat_x_assum `!a b s. sound a s ==> sound (widen a b) s`
    (fn th => irule th) >>
    rw[dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
    Cases_on `FLOOKUP st.dws_entry k` >> fs[]) >>
  TRY (
    Cases_on `MAP (\nbr. edge_transfer ctx nbr k (df_widen_boundary bottom st nbr))
      (case dir of Forward => cfg_preds_of cfg k | Backward => cfg_succs_of cfg k)` >>
    fs[]
    >- (Cases_on `entry_val` >> fs[] >> Cases_on `x` >> fs[] >> rw[])
    >> (`!xs (acc:'a). (!s:'b. sound acc s) ==> !s. sound (FOLDL join acc xs) s` by
          (Induct >> rw[listTheory.FOLDL] >> first_x_assum irule >> rw[] >> metis_tac[]) >>
        first_x_assum irule >> rw[])) >>
  TRY (res_tac >> fs[])
QED

(* Entry-only soundness: weaker hypotheses than the full invariant.
   Only needs first-arg closure for join/widen, plus bottom/entry_val.
   Does NOT need transfer or edge_transfer closure.
   This is because FOLDL join bottom edge_vals is sound regardless
   of what edge_vals are (join only needs first arg sound, FOLDL
   starts from bottom which is sound). And widen preserves first-arg
   soundness, so the widening step also preserves entry soundness.
   Requires convergence witnesses (Q, leq, m, b) so wl_iterate result
   is well-defined. *)
Theorem df_widen_entry_sound_proof:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (sound : 'a -> 'b -> bool)
   (leq : 'a df_widen_state -> 'a df_widen_state -> bool)
   m b (Q : 'a df_widen_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let st0 = init_df_widen_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      (!a b s. sound a s ==> sound (join a b) s) /\
      (!a b s. sound a s ==> sound (widen a b) s) /\
      (!s. sound bottom s) /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => !s. sound v s) /\
      (* convergence *)
      (!lbl st. Q st ==> leq st (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with dws_boundary := st0.dws_boundary |+ (lbl, v))) /\
      bounded_measure Q leq m b
    ==>
      (!lbl s. sound (df_widen_entry bottom result lbl) s)
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_analyze_widen_def,
       dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
  qabbrev_tac `process = df_process_block_widen dir bottom join widen threshold
    transfer edge_transfer ctx entry_val (cfg_analyze fn) fn.fn_blocks` >>
  qabbrev_tac `st0' = case entry_val of
    NONE => init_df_widen_state bottom (MAP (\bb. bb.bb_label) fn.fn_blocks)
    | SOME (lbl,v) => init_df_widen_state bottom
        (MAP (\bb. bb.bb_label) fn.fn_blocks) with dws_boundary :=
        (init_df_widen_state bottom (MAP (\bb. bb.bb_label) fn.fn_blocks)).
        dws_boundary |+ (lbl,v)` >>
  qabbrev_tac `deps = case dir of Forward => cfg_succs_of (cfg_analyze fn)
                                 | Backward => cfg_preds_of (cfg_analyze fn)` >>
  qabbrev_tac `wl0 = case dir of Forward => (cfg_analyze fn).cfg_dfs_pre
                                | Backward => (cfg_analyze fn).cfg_dfs_post` >>
  qabbrev_tac `result = SND (wl_iterate process deps wl0 st0')` >>
  (* Use wl_iterate_invariant_proof with R tracking Q + entry soundness *)
  mp_tac (
    let val base = INST_TYPE [alpha |-> ``:'a df_widen_state``, beta |-> ``:string``]
                     (SIMP_RULE std_ss [LET_THM] wl_iterate_invariant_proof)
        val sp1 = Q.SPECL [`leq`, `m`, `b`, `process`, `deps`, `wl0`, `st0'`] base
        val R = ``\st:'a df_widen_state.
          Q st /\ (!k v. FLOOKUP st.dws_entry k = SOME v ==> !s:'b. sound v s)``
    in SIMP_RULE std_ss [] (SPEC R sp1) end) >>
  impl_tac
  >- (conj_tac >| [
    (* 1. leq *)
    rpt gen_tac >> strip_tac >> first_x_assum irule >> fs[],
    (* 2-4: R_preserved, R(st0'), bounded_measure *)
    conj_tac >| [
      (* 2. R preserved by process *)
      rpt gen_tac >> strip_tac >>
      conj_tac >- (first_x_assum irule >> fs[]) >>
      `process lbl st = df_process_block_widen dir bottom join widen threshold
        transfer edge_transfer ctx entry_val (cfg_analyze fn)
        fn.fn_blocks lbl st` by
        fs[markerTheory.Abbrev_def] >>
      pop_assum (fn eq => REWRITE_TAC [eq]) >>
      mp_tac (Q.SPECL [`dir`,`bottom`,`join`,`widen`,`threshold`,`transfer`,
          `edge_transfer`,`ctx`,`entry_val`,`cfg_analyze fn`,
          `fn.fn_blocks`,`lbl`,`st`,`sound`]
          (SIMP_RULE std_ss [LET_THM] df_widen_process_entry_sound)) >>
      impl_tac >- (
        rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC) >>
        Cases_on `entry_val` >> fs[] >> pairarg_tac >> fs[]) >>
      simp[],
      (* 3-4: R(st0'), bounded_measure *)
      conj_tac >| [
        (* 3. R(st0') — entry map is FEMPTY initially *)
        qpat_x_assum `Abbrev (st0' = _)` mp_tac >>
        simp[markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
        Cases_on `entry_val` >> fs[]
        >- fs[dfAnalyzeWidenDefsTheory.init_df_widen_state_def]
        >> Cases_on `x` >> fs[dfAnalyzeWidenDefsTheory.init_df_widen_state_def],
        (* 4. bounded_measure *)
        fs[latticeDefsTheory.bounded_measure_def]
      ]
    ]
  ]) >>
  (* Conclusion: R(result) => entry values are sound *)
  strip_tac >>
  qpat_x_assum `Abbrev (result = _)`
    (SUBST_ALL_TAC o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rpt gen_tac >>
  Cases_on `FLOOKUP result.dws_entry lbl` >> fs[] >> res_tac >> fs[]
QED

(* Join-upper-bound → df_process_block_widen is inflationary w.r.t.
   the pointwise boundary ordering. Same argument as base variant:
   boundary(lbl) := join old final_val ≥ old. Widening affects entry
   (fold input), not boundary (fold output joined with old). *)
Theorem df_process_widen_inflationary_proof:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val cfg bbs
   (elem_leq : 'a -> 'a -> bool).
    reflexive elem_leq /\
    (!a b. elem_leq a (join a b))
  ==>
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let leq = (λst1 st2.
      (!lbl. elem_leq (df_widen_boundary bottom st1 lbl)
                       (df_widen_boundary bottom st2 lbl))) in
    !lbl st. leq st (process lbl st)
Proof
  rw[dfAnalyzeWidenDefsTheory.df_process_block_widen_def,
     dfAnalyzeWidenDefsTheory.df_widen_boundary_def] >>
  pairarg_tac >> rw[] >>
  Cases_on `lbl = lbl'` >>
  fs[finite_mapTheory.FLOOKUP_UPDATE, relationTheory.reflexive_def]
QED

(* ===== Deps complete helpers ===== *)

(* Non-lbl boundary stability: process only updates lbl's boundary *)
Theorem df_widen_process_boundary[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl st l.
    l <> lbl ==>
    df_widen_boundary bottom
      (df_process_block_widen dir bottom join widen threshold
        transfer edge_transfer ctx entry_val cfg bbs lbl st) l =
    df_widen_boundary bottom st l
Proof
  rw[dfAnalyzeWidenDefsTheory.df_process_block_widen_def,
     dfAnalyzeWidenDefsTheory.df_widen_boundary_def] >>
  pairarg_tac >> rw[finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Non-lbl visits stability: process only updates lbl's visits *)
Theorem df_widen_process_visits[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl st l.
    l <> lbl ==>
    df_widen_visits
      (df_process_block_widen dir bottom join widen threshold
        transfer edge_transfer ctx entry_val cfg bbs lbl st) l =
    df_widen_visits st l
Proof
  rw[dfAnalyzeWidenDefsTheory.df_process_block_widen_def,
     dfAnalyzeWidenDefsTheory.df_widen_visits_def] >>
  pairarg_tac >> rw[finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Non-lbl entry stability: process only updates lbl's entry *)
Theorem df_widen_process_entry[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl st l.
    l <> lbl ==>
    df_widen_entry bottom
      (df_process_block_widen dir bottom join widen threshold
        transfer edge_transfer ctx entry_val cfg bbs lbl st) l =
    df_widen_entry bottom st l
Proof
  rw[dfAnalyzeWidenDefsTheory.df_process_block_widen_def,
     dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
  pairarg_tac >> rw[finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Fixpoint characterization: process b st = st iff the three-field record
   update is identity. Uses visits contradiction to rule out else-branch. *)
Theorem df_widen_process_fixpoint[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl (st:'a df_widen_state).
    df_process_block_widen dir bottom join widen threshold
      transfer edge_transfer ctx entry_val cfg bbs lbl st = st
    <=>
    (let (final_val, inst_map) =
       df_fold_block dir (transfer ctx) lbl
         (case lookup_block lbl bbs of NONE => [] | SOME bb => bb.bb_instructions)
         (let edge_vals = MAP (\nbr. edge_transfer ctx nbr lbl
               (df_widen_boundary bottom st nbr))
               (case dir of Forward => cfg_preds_of cfg lbl
                          | Backward => cfg_succs_of cfg lbl) in
          let joined = case edge_vals of
               [] => (case entry_val of NONE => bottom
                      | SOME (ev_lbl,v) => if lbl = ev_lbl then v else bottom)
             | v4::v5 => FOLDL join bottom edge_vals in
            if df_widen_visits st lbl >= threshold
            then widen (df_widen_entry bottom st lbl) joined
            else joined) in
     st with <|dws_boundary := st.dws_boundary |+
                 (lbl, join (df_widen_boundary bottom st lbl) final_val);
               dws_entry := st.dws_entry |+ (lbl,
                 (let edge_vals = MAP (\nbr. edge_transfer ctx nbr lbl
                       (df_widen_boundary bottom st nbr))
                       (case dir of Forward => cfg_preds_of cfg lbl
                                  | Backward => cfg_succs_of cfg lbl) in
                  let joined = case edge_vals of
                       [] => (case entry_val of NONE => bottom
                              | SOME (ev_lbl,v) => if lbl = ev_lbl then v else bottom)
                    | v4::v5 => FOLDL join bottom edge_vals in
                    if df_widen_visits st lbl >= threshold
                    then widen (df_widen_entry bottom st lbl) joined
                    else joined));
               dws_inst := FUNION inst_map st.dws_inst|> = st)
Proof
  rpt gen_tac >>
  simp_tac std_ss [LET_THM,
    dfAnalyzeWidenDefsTheory.df_process_block_widen_def] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qmatch_goalsub_abbrev_tac `if new_st = st then _ else _` >>
  eq_tac
  >- ((* Forward: process = st ==> new_st = st *)
      Cases_on `new_st = st` >> simp[] >>
      strip_tac >>
      (* else branch: visits contradiction *)
      qpat_x_assum `_ = st`
        (mp_tac o AP_TERM ``\(s:'a df_widen_state). s.dws_visits``) >>
      simp[] >>
      simp[dfAnalyzeWidenDefsTheory.df_widen_visits_def] >>
      Cases_on `FLOOKUP st.dws_visits lbl` >>
      simp[finite_mapTheory.fmap_eq_flookup] >>
      qexists_tac `lbl` >> simp[finite_mapTheory.FLOOKUP_UPDATE])
  >- ((* Backward: new_st = st ==> process = st *)
      simp[markerTheory.Abbrev_def])
QED

(* SML val: LET-free fixpoint characterization *)
val process_fixpoint =
  SIMP_RULE std_ss [LET_THM] df_widen_process_fixpoint;

(* Fold congruence: if two states agree on neighbor boundaries,
   they produce the same fold output *)
Theorem df_widen_process_fold_cong[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl st1 st2.
    let neighbors = (case dir of Forward => cfg_preds_of cfg lbl
                               | Backward => cfg_succs_of cfg lbl) in
    (!nbr. MEM nbr neighbors ==>
      df_widen_boundary bottom st1 nbr = df_widen_boundary bottom st2 nbr) /\
    df_widen_visits st1 lbl = df_widen_visits st2 lbl /\
    df_widen_entry bottom st1 lbl = df_widen_entry bottom st2 lbl
    ==>
    let instrs = (case lookup_block lbl bbs of
                    NONE => [] | SOME bb => bb.bb_instructions) in
    let edge_vals1 = MAP (λnbr. edge_transfer ctx nbr lbl
                           (df_widen_boundary bottom st1 nbr)) neighbors in
    let joined1 = (case edge_vals1 of
                     [] => (case entry_val of NONE => bottom
                            | SOME (ev_lbl,v) => if lbl = ev_lbl then v else bottom)
                   | _ => FOLDL join bottom edge_vals1) in
    let entry1 = if df_widen_visits st1 lbl >= threshold then
                   widen (df_widen_entry bottom st1 lbl) joined1
                 else joined1 in
    let (fv1, im1) = df_fold_block dir (transfer ctx) lbl instrs entry1 in
    let edge_vals2 = MAP (λnbr. edge_transfer ctx nbr lbl
                           (df_widen_boundary bottom st2 nbr)) neighbors in
    let joined2 = (case edge_vals2 of
                     [] => (case entry_val of NONE => bottom
                            | SOME (ev_lbl,v) => if lbl = ev_lbl then v else bottom)
                   | _ => FOLDL join bottom edge_vals2) in
    let entry2 = if df_widen_visits st2 lbl >= threshold then
                   widen (df_widen_entry bottom st2 lbl) joined2
                 else joined2 in
    let (fv2, im2) = df_fold_block dir (transfer ctx) lbl instrs entry2 in
      fv1 = fv2 /\ im1 = im2
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  `MAP (\nbr. edge_transfer ctx nbr lbl (df_widen_boundary bottom st1 nbr))
       (case dir of Forward => cfg_preds_of cfg lbl
                   | Backward => cfg_succs_of cfg lbl) =
   MAP (\nbr. edge_transfer ctx nbr lbl (df_widen_boundary bottom st2 nbr))
       (case dir of Forward => cfg_preds_of cfg lbl
                   | Backward => cfg_succs_of cfg lbl)` by
    (irule listTheory.MAP_CONG >> rw[] >> Cases_on `dir` >> fs[]) >>
  qpat_x_assum `MAP _ _ = MAP _ _` SUBST_ALL_TAC >>
  pairarg_tac >> simp[]
QED

(* Visits at lbl: monotonically non-decreasing *)
Triviality process_visits_ge:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl st.
    df_widen_visits
      (df_process_block_widen dir bottom join widen threshold
        transfer edge_transfer ctx entry_val cfg bbs lbl st) lbl >=
    df_widen_visits st lbl
Proof
  rpt gen_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  rw[dfAnalyzeWidenDefsTheory.df_widen_visits_def,
     finite_mapTheory.FLOOKUP_UPDATE]
QED

(* ===== Process at-lbl characterization ===== *)

(* When process lbl st ≠ st, characterize all fields of the result.
   This encapsulates the definition expansion so downstream proofs
   (self_idempotent, stable_after) don't need to expand it. *)
Triviality process_at_lbl:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl st.
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs;
        st1 = process lbl st;
        neighbors = case dir of Forward => cfg_preds_of cfg lbl
                              | Backward => cfg_succs_of cfg lbl;
        edge_vals = MAP (\nbr. edge_transfer ctx nbr lbl
                     (df_widen_boundary bottom st nbr)) neighbors;
        joined = case edge_vals of
                   [] => (case entry_val of NONE => bottom
                         | SOME (ev_lbl, v) => if lbl = ev_lbl then v
                                               else bottom)
                 | v4::v5 => FOLDL join bottom edge_vals;
        entry = if df_widen_visits st lbl >= threshold
                then widen (df_widen_entry bottom st lbl) joined
                else joined;
        instrs = case lookup_block lbl bbs of NONE => []
                 | SOME bb => bb.bb_instructions
    in
      st1 = st \/
      (df_widen_boundary bottom st1 lbl =
         join (df_widen_boundary bottom st lbl)
           (FST (df_fold_block dir (transfer ctx) lbl instrs entry)) /\
       df_widen_entry bottom st1 lbl = entry /\
       df_widen_visits st1 lbl = df_widen_visits st lbl + 1)
Proof
  rpt gen_tac >>
  simp_tac std_ss [LET_THM] >>
  simp_tac std_ss [dfAnalyzeWidenDefsTheory.df_process_block_widen_def,
                   LET_THM] >>
  pairarg_tac >> simp_tac std_ss [] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  rw[] >>
  simp[dfAnalyzeWidenDefsTheory.df_widen_boundary_def,
       dfAnalyzeWidenDefsTheory.df_widen_entry_def,
       dfAnalyzeWidenDefsTheory.df_widen_visits_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

val pal_clean = SIMP_RULE std_ss [LET_THM] process_at_lbl;

(* Unify two pairarg_tac pair equations on the same fold expression.
   After two pairarg_tac calls produce fold=(a,b) and fold=(c,d),
   this tactic derives a=c and b=d, substitutes, and rewrites FST/SND. *)
fun unify_pairs_tac (pat1 : term quotation) (pat2 : term quotation) : tactic =
  qpat_x_assum pat2 (fn h2 =>
    qpat_x_assum pat1 (fn h1 =>
      let val eq = TRANS (SYM h2) h1
          val peq = REWRITE_RULE [pairTheory.PAIR_EQ] eq
      in SUBST_ALL_TAC (CONJUNCT1 peq) >>
         SUBST_ALL_TAC (CONJUNCT2 peq) >>
         RULE_ASSUM_TAC (REWRITE_RULE [h1, pairTheory.FST, pairTheory.SND]) >>
         REWRITE_TAC [h1, pairTheory.FST, pairTheory.SND]
      end));

(* ===== Process absorbs: sufficient conditions for process to be a no-op ===== *)

(* If the FLOOKUP entries exist and the computed values match what's stored,
   then process is an identity. Used by self_idempotent and stable_after. *)
Theorem process_absorbs:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl (st':'a df_widen_state).
    let neighbors = case dir of Forward => cfg_preds_of cfg lbl
                              | Backward => cfg_succs_of cfg lbl in
    let edge_vals = MAP (\nbr. edge_transfer ctx nbr lbl
                     (df_widen_boundary bottom st' nbr)) neighbors in
    let joined = case edge_vals of
                   [] => (case entry_val of NONE => bottom
                         | SOME (ev_lbl, v) => if lbl = ev_lbl then v else bottom)
                 | v4::v5 => FOLDL join bottom edge_vals in
    let entry = if df_widen_visits st' lbl >= threshold
                then widen (df_widen_entry bottom st' lbl) joined
                else joined in
    let instrs = case lookup_block lbl bbs of NONE => []
                 | SOME bb => bb.bb_instructions in
    let (fv, im) = df_fold_block dir (transfer ctx) lbl instrs entry in
      FLOOKUP st'.dws_boundary lbl = SOME (df_widen_boundary bottom st' lbl) /\
      FLOOKUP st'.dws_entry lbl = SOME (df_widen_entry bottom st' lbl) /\
      entry = df_widen_entry bottom st' lbl /\
      join (df_widen_boundary bottom st' lbl) fv =
        df_widen_boundary bottom st' lbl /\
      im SUBMAP st'.dws_inst
    ==>
      df_process_block_widen dir bottom join widen threshold
        transfer edge_transfer ctx entry_val cfg bbs lbl st' = st'
Proof
  rpt gen_tac >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp_tac std_ss [] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  strip_tac >>
  simp_tac std_ss [Once process_fixpoint, LET_THM] >>
  pairarg_tac >> simp_tac std_ss [] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  unify_pairs_tac `_ = (fv, im)` `_ = (final_val, inst_map)` >>
  simp[dfAnalyzeWidenDefsTheory.df_widen_state_component_equality] >>
  rpt conj_tac
  >- metis_tac[finite_mapTheory.SUBMAP_FUNION_ABSORPTION]
  >- (irule finite_mapTheory.FUPDATE_ELIM >> rpt conj_tac >>
      fs[finite_mapTheory.FLOOKUP_DEF])
  >- (irule finite_mapTheory.FUPDATE_ELIM >> rpt conj_tac >>
      fs[finite_mapTheory.FLOOKUP_DEF])
QED

val pa_clean = CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
                 (SIMP_RULE std_ss [LET_THM] process_absorbs);

(* From f |+ (k,v) = f, derive FLOOKUP f k = SOME v *)
Triviality flookup_from_fupdate_id:
  !(f:'a |-> 'b) k v. f |+ (k, v) = f ==> FLOOKUP f k = SOME v
Proof
  rw[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_UPDATE] >>
  pop_assum (qspec_then `k` mp_tac) >> simp[]
QED

Triviality boundary_from_fupdate:
  !(st:'a df_widen_state) lbl v bottom.
    st.dws_boundary |+ (lbl, v) = st.dws_boundary ==>
    df_widen_boundary bottom st lbl = v
Proof
  rw[dfAnalyzeWidenDefsTheory.df_widen_boundary_def] >>
  imp_res_tac flookup_from_fupdate_id >> fs[]
QED

Triviality entry_from_fupdate:
  !(st:'a df_widen_state) lbl v bottom.
    st.dws_entry |+ (lbl, v) = st.dws_entry ==>
    df_widen_entry bottom st lbl = v
Proof
  rw[dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
  imp_res_tac flookup_from_fupdate_id >> fs[]
QED

Triviality flookup_from_bnd_fupdate:
  !(st:'a df_widen_state) lbl v.
    st.dws_boundary |+ (lbl, v) = st.dws_boundary ==>
    FLOOKUP st.dws_boundary lbl = SOME v
Proof
  rw[] >> irule flookup_from_fupdate_id >> metis_tac[]
QED

Triviality flookup_from_ent_fupdate:
  !(st:'a df_widen_state) lbl v.
    st.dws_entry |+ (lbl, v) = st.dws_entry ==>
    FLOOKUP st.dws_entry lbl = SOME v
Proof
  rw[] >> irule flookup_from_fupdate_id >> metis_tac[]
QED

(* process b st = st implies the pa_clean conditions hold for b on st.
   This extracts FLOOKUP-level facts from the fixpoint identity without
   exposing the giant record-update term. *)
Theorem process_fixpoint_absorbs:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl (st:'a df_widen_state).
    df_process_block_widen dir bottom join widen threshold
      transfer edge_transfer ctx entry_val cfg bbs lbl st = st
  ==>
    let neighbors = case dir of Forward => cfg_preds_of cfg lbl
                              | Backward => cfg_succs_of cfg lbl in
    let edge_vals = MAP (\nbr. edge_transfer ctx nbr lbl
                     (df_widen_boundary bottom st nbr)) neighbors in
    let joined = case edge_vals of
                   [] => (case entry_val of NONE => bottom
                         | SOME (ev_lbl, v) => if lbl = ev_lbl then v else bottom)
                 | v4::v5 => FOLDL join bottom edge_vals in
    let entry = if df_widen_visits st lbl >= threshold
                then widen (df_widen_entry bottom st lbl) joined
                else joined in
    let instrs = case lookup_block lbl bbs of NONE => []
                 | SOME bb => bb.bb_instructions in
    let (fv, im) = df_fold_block dir (transfer ctx) lbl instrs entry in
      FLOOKUP st.dws_boundary lbl = SOME (df_widen_boundary bottom st lbl) /\
      FLOOKUP st.dws_entry lbl = SOME (df_widen_entry bottom st lbl) /\
      entry = df_widen_entry bottom st lbl /\
      join (df_widen_boundary bottom st lbl) fv =
        df_widen_boundary bottom st lbl /\
      im SUBMAP st.dws_inst
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp_tac std_ss [] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qpat_x_assum `_ = st` (fn th =>
    assume_tac (REWRITE_RULE [process_fixpoint, LET_THM] th)) >>
  pairarg_tac >> fs[] >>
  (* Extract field-level equalities via record accessor projection *)
  FIRST_X_ASSUM (fn th =>
    if is_eq (concl th) andalso
       (let val ty = type_of (rhs (concl th))
        in fst (dest_type ty) = "df_widen_state" handle _ => false end)
       andalso not (is_comb (lhs (concl th)) andalso
                    (fst (dest_const (rator (lhs (concl th)))) = "df_process_block_widen"
                     handle _ => false))
    then
      let val extract = fn acc =>
            SIMP_RULE std_ss [dfAnalyzeWidenDefsTheory.df_widen_state_accessors,
               dfAnalyzeWidenDefsTheory.df_widen_state_accfupds]
             (CONV_RULE (DEPTH_CONV BETA_CONV) (AP_TERM acc th))
      in assume_tac (extract ``\(s:'a df_widen_state). s.dws_boundary``) >>
         assume_tac (extract ``\(s:'a df_widen_state). s.dws_entry``) >>
         assume_tac (extract ``\(s:'a df_widen_state). s.dws_inst``)
      end
    else FAIL_TAC "not record eq") >>
  imp_res_tac boundary_from_fupdate >>
  imp_res_tac entry_from_fupdate >>
  imp_res_tac flookup_from_bnd_fupdate >>
  imp_res_tac flookup_from_ent_fupdate >>
  rpt conj_tac >| [
    (* FLOOKUP boundary *)
    qpat_x_assum `FLOOKUP st.dws_boundary lbl = _` (fn flk =>
      FIRST_X_ASSUM (fn bnd =>
        if is_forall (concl bnd) andalso
           can (find_term (fn t => fst (dest_const t) = "df_widen_boundary"
                           handle _ => false)) (concl bnd) andalso
           not (can (find_term (fn t => fst (dest_const t) = "df_widen_entry"
                                handle _ => false)) (concl bnd))
        then ACCEPT_TAC (REWRITE_RULE [GSYM (SPEC ``bottom:'a`` bnd)] flk)
        else FAIL_TAC "")),
    (* FLOOKUP entry *)
    qpat_x_assum `FLOOKUP st.dws_entry lbl = _` (fn flk =>
      FIRST_X_ASSUM (fn ent =>
        if is_forall (concl ent) andalso
           can (find_term (fn t => fst (dest_const t) = "df_widen_entry"
                           handle _ => false)) (concl ent)
        then ACCEPT_TAC (REWRITE_RULE [GSYM (SPEC ``bottom:'a`` ent)] flk)
        else FAIL_TAC "")),
    (* entry = accessor *)
    metis_tac[],
    (* boundary absorption *)
    metis_tac[],
    (* inst submap *)
    metis_tac[finite_mapTheory.SUBMAP_FUNION_ABSORPTION]
  ]
QED

val pfa_clean = CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
                  (SIMP_RULE std_ss [LET_THM] process_fixpoint_absorbs);

(* ===== Self-idempotent ===== *)

(* Self-idempotent: process lbl (process lbl st) = process lbl st
   when lbl ∉ neighbors(lbl) and join/widen are absorptive.

   Strategy: case split on st1=st (trivial). For st1≠st, use
   process_components for raw field info, then process_absorbs. *)
Theorem df_widen_process_self_idempotent[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl st.
    ~MEM lbl (case dir of Forward => cfg_preds_of cfg lbl
                        | Backward => cfg_succs_of cfg lbl) /\
    (!a b. join (join a b) b = join a b) /\
    (!a b. widen (widen a b) b = widen a b) /\
    (!a. widen a a = a)
  ==>
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    process lbl (process lbl st) = process lbl st
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [LET_THM] >>
  qabbrev_tac `st1 = df_process_block_widen dir bottom join widen threshold
    transfer edge_transfer ctx entry_val cfg bbs lbl st` >>
  Cases_on `st1 = st` >- fs[markerTheory.Abbrev_def] >>
  irule pa_clean >>
  (* Step 1: Rewrite neighbor boundaries st1 → st *)
  `!nbr. MEM nbr (case dir of Forward => cfg_preds_of cfg lbl
                             | Backward => cfg_succs_of cfg lbl) ==>
    df_widen_boundary bottom st1 nbr = df_widen_boundary bottom st nbr` by
    (rpt strip_tac >> `nbr <> lbl` by (CCONTR_TAC >> fs[]) >>
     qunabbrev_tac `st1` >> irule df_widen_process_boundary >> simp[]) >>
  `MAP (\nbr. edge_transfer ctx nbr lbl (df_widen_boundary bottom st1 nbr))
       (case dir of Forward => cfg_preds_of cfg lbl
                   | Backward => cfg_succs_of cfg lbl) =
   MAP (\nbr. edge_transfer ctx nbr lbl (df_widen_boundary bottom st nbr))
       (case dir of Forward => cfg_preds_of cfg lbl
                   | Backward => cfg_succs_of cfg lbl)` by
    (irule listTheory.MAP_CONG >> rw[] >> res_tac >> Cases_on `dir` >> fs[]) >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  (* Step 2: Get accessor facts (pal_clean) and raw fields (process_components) *)
  mp_tac (Q.SPECL [`dir`,`bottom`,`join`,`widen`,`threshold`,`transfer`,
    `edge_transfer`,`ctx`,`entry_val`,`cfg`,`bbs`,`lbl`,`st`] pal_clean) >>
  qpat_x_assum `Abbrev (st1 = _)` (fn th =>
    let val eq = REWRITE_RULE [markerTheory.Abbrev_def] th
    in REWRITE_TAC [GSYM eq] >> assume_tac th end) >>
  strip_tac >>
  mp_tac (Q.SPECL [`dir`,`bottom`,`join`,`widen`,`threshold`,`transfer`,
    `edge_transfer`,`ctx`,`entry_val`,`cfg`,`bbs`,`lbl`,`st`]
    (SIMP_RULE std_ss [LET_THM] df_widen_process_components)) >>
  simp_tac std_ss [] >>
  pairarg_tac >> simp_tac std_ss [] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qpat_x_assum `Abbrev (st1 = _)` (fn th =>
    let val eq = REWRITE_RULE [markerTheory.Abbrev_def] th
    in REWRITE_TAC [GSYM eq] >> assume_tac th end) >>
  strip_tac >>
  (* Step 3: Rewrite st1 accessors, case split, unify folds *)
  qpat_x_assum `df_widen_entry bottom st1 lbl = _` (fn th =>
    REWRITE_TAC [th] >> assume_tac th) >>
  qpat_x_assum `df_widen_visits st1 lbl = _` (fn th =>
    REWRITE_TAC [th] >> assume_tac th) >>
  qpat_x_assum `df_widen_boundary bottom st1 lbl = _` (fn th =>
    REWRITE_TAC [th] >> assume_tac th) >>
  Cases_on `df_widen_visits st lbl >= threshold` >> fs[] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[finite_mapTheory.SUBMAP_FUNION_ID]
QED

(* If f SUBMAP h and FDOM f, FDOM g are disjoint, then f SUBMAP (g FUNION h) *)
Triviality submap_funion_disjoint:
  !(f:'a |-> 'b) g h.
    f SUBMAP h /\ DISJOINT (FDOM f) (FDOM g) ==> f SUBMAP (FUNION g h)
Proof
  rw[finite_mapTheory.SUBMAP_DEF, finite_mapTheory.FUNION_DEF,
     pred_setTheory.IN_UNION, pred_setTheory.DISJOINT_DEF,
     pred_setTheory.EXTENSION, pred_setTheory.IN_INTER,
     pred_setTheory.NOT_IN_EMPTY] >>
  metis_tac[]
QED

(* Fold output keys for different labels are disjoint *)
Theorem fold_inst_disjoint:
  !dir transfer b instrs_b entry_b fv_b im_b
   lbl instrs_lbl entry_lbl fv_lbl im_lbl.
    b <> lbl /\
    df_fold_block dir transfer b instrs_b entry_b = (fv_b, im_b) /\
    df_fold_block dir transfer lbl instrs_lbl entry_lbl = (fv_lbl, im_lbl)
  ==>
    DISJOINT (FDOM im_b) (FDOM im_lbl)
Proof
  rw[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
     pred_setTheory.IN_INTER, pred_setTheory.NOT_IN_EMPTY] >>
  CCONTR_TAC >> fs[] >>
  imp_res_tac dfAnalyzeProofsTheory.df_fold_block_keys >>
  `FST x = b` by (first_x_assum irule >> fs[finite_mapTheory.FLOOKUP_DEF]) >>
  `FST x = lbl` by (first_x_assum irule >> fs[finite_mapTheory.FLOOKUP_DEF]) >>
  fs[]
QED

(* Congruence: boundary/entry depend only on FLOOKUP of the respective field *)
Triviality boundary_flookup_cong:
  !bottom (st1:'a df_widen_state) st2 lbl.
    FLOOKUP st1.dws_boundary lbl = FLOOKUP st2.dws_boundary lbl ==>
    df_widen_boundary bottom st1 lbl = df_widen_boundary bottom st2 lbl
Proof
  rw[dfAnalyzeWidenDefsTheory.df_widen_boundary_def]
QED

Triviality entry_flookup_cong:
  !bottom (st1:'a df_widen_state) st2 lbl.
    FLOOKUP st1.dws_entry lbl = FLOOKUP st2.dws_entry lbl ==>
    df_widen_entry bottom st1 lbl = df_widen_entry bottom st2 lbl
Proof
  rw[dfAnalyzeWidenDefsTheory.df_widen_entry_def]
QED

(* Fold inst for block b stays SUBMAP after processing a different block lbl *)
Theorem process_inst_grows:
  !dir (bottom:'a) join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs (b:string) lbl instrs_b entry_b fv_b im_b (st:'a df_widen_state).
    b <> lbl /\
    df_fold_block dir (transfer ctx) b instrs_b entry_b = (fv_b, im_b) /\
    im_b SUBMAP st.dws_inst
  ==>
    im_b SUBMAP (df_process_block_widen dir bottom join widen threshold
      transfer edge_transfer ctx entry_val cfg bbs lbl st).dws_inst
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [dfAnalyzeWidenDefsTheory.df_process_block_widen_def,
                   LET_THM] >>
  pairarg_tac >> simp_tac std_ss [] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  rw[] >>
  `DISJOINT (FDOM im_b) (FDOM inst_map)` by
    (imp_res_tac fold_inst_disjoint >> first_assum ACCEPT_TAC) >>
  irule submap_funion_disjoint >> simp[]
QED

(* Stable after: process b after process lbl gives same result as just
   process lbl, when b's neighbors don't include lbl and process b st = st *)
Theorem df_widen_process_stable_after[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl b st.
    b <> lbl /\
    ~MEM lbl (case dir of Forward => cfg_preds_of cfg b
                        | Backward => cfg_succs_of cfg b) /\
    df_process_block_widen dir bottom join widen threshold
      transfer edge_transfer ctx entry_val cfg bbs b st = st
  ==>
    df_process_block_widen dir bottom join widen threshold
      transfer edge_transfer ctx entry_val cfg bbs b
      (df_process_block_widen dir bottom join widen threshold
        transfer edge_transfer ctx entry_val cfg bbs lbl st) =
    df_process_block_widen dir bottom join widen threshold
      transfer edge_transfer ctx entry_val cfg bbs lbl st
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `st' = df_process_block_widen dir bottom join widen
    threshold transfer edge_transfer ctx entry_val cfg bbs lbl st` >>
  irule pa_clean >>
  (* Step 1: Rewrite neighbor boundaries st' → st (lbl ∉ neighbors(b)) *)
  `!nbr. MEM nbr (case dir of Forward => cfg_preds_of cfg b
                             | Backward => cfg_succs_of cfg b) ==>
     df_widen_boundary bottom st' nbr = df_widen_boundary bottom st nbr` by
    (rpt strip_tac >> qunabbrev_tac `st'` >>
     irule df_widen_process_boundary >>
     Cases_on `dir` >> fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `MAP (\nbr. edge_transfer ctx nbr b (df_widen_boundary bottom st' nbr))
       (case dir of Forward => cfg_preds_of cfg b
                   | Backward => cfg_succs_of cfg b) =
   MAP (\nbr. edge_transfer ctx nbr b (df_widen_boundary bottom st nbr))
       (case dir of Forward => cfg_preds_of cfg b
                   | Backward => cfg_succs_of cfg b)` by
    (irule listTheory.MAP_CONG >> rw[] >> Cases_on `dir` >> fs[]) >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  (* Step 2: Rewrite visits and entry at b: st' → st *)
  `df_widen_visits st' b = df_widen_visits st b` by
    (qunabbrev_tac `st'` >> irule df_widen_process_visits >> simp[]) >>
  `df_widen_entry bottom st' b = df_widen_entry bottom st b` by
    (qunabbrev_tac `st'` >> irule df_widen_process_entry >> simp[]) >>
  qpat_x_assum `df_widen_visits st' b = _` (fn th =>
    REWRITE_TAC [th] >> assume_tac th) >>
  qpat_x_assum `df_widen_entry bottom st' b = _` (fn th =>
    REWRITE_TAC [th] >> assume_tac th) >>
  (* Now the fold for b on st' uses identical inputs to fold for b on st *)
  (* Step 3: Use pfa_clean to extract fixpoint facts from process b st = st *)
  mp_tac (Q.SPECL [`dir`,`bottom`,`join`,`widen`,`threshold`,`transfer`,
    `edge_transfer`,`ctx`,`entry_val`,`cfg`,`bbs`,`b`,`st`] pfa_clean) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  (* simp_tac simplifies goal's if-then-else entry to df_widen_entry *)
  simp_tac std_ss [] >> strip_tac >>
  (* pfa_clean gives 5 facts about st. The entry/join/SUBMAP facts use the
     expanded if-then-else form while the goal uses df_widen_entry. *)
  (* Step 4: Transfer FLOOKUP facts from st to st' (b ≠ lbl) *)
  qpat_x_assum `Abbrev (st' = _)` (fn th =>
    assume_tac th >> assume_tac th >>
    assume_tac (REWRITE_RULE [markerTheory.Abbrev_def] th)) >>
  `FLOOKUP st'.dws_boundary b = FLOOKUP st.dws_boundary b` by
    (qunabbrev_tac `st'` >>
     simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def] >>
     pairarg_tac >> rw[finite_mapTheory.FLOOKUP_UPDATE]) >>
  `FLOOKUP st'.dws_entry b = FLOOKUP st.dws_entry b` by
    (qunabbrev_tac `st'` >>
     simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def] >>
     pairarg_tac >> rw[finite_mapTheory.FLOOKUP_UPDATE]) >>
  `df_widen_boundary bottom st' b = df_widen_boundary bottom st b` by
    (ONCE_REWRITE_TAC [dfAnalyzeWidenDefsTheory.df_widen_boundary_def] >>
     qpat_x_assum `FLOOKUP st'.dws_boundary b = _` (fn th =>
       REWRITE_TAC [th])) >>
  (* Step 5: Establish the 5 pa_clean conditions *)
  rpt conj_tac
  >- ((* join (bnd st' b, FST fold) = bnd st' b *)
      qpat_x_assum `df_widen_boundary bottom st' b = _` (fn th =>
        REWRITE_TAC [th]) >>
      qpat_x_assum `(if _ then widen _ _ else _) = _` (fn entry_eq =>
        qpat_x_assum `join _ (FST _) = _` (fn join_eq =>
          ACCEPT_TAC (REWRITE_RULE [entry_eq] join_eq))))
  >- ((* FLOOKUP st'.bnd b = SOME (bnd st' b) *)
      qpat_x_assum `df_widen_boundary bottom st' b = _` (fn th =>
        REWRITE_TAC [th]) >>
      qpat_x_assum `FLOOKUP st'.dws_boundary b = _` (fn th =>
        REWRITE_TAC [th]) >>
      first_assum ACCEPT_TAC)
  >- ((* FLOOKUP st'.entry b = SOME (entry st b) *)
      qpat_x_assum `FLOOKUP st'.dws_entry b = _` (fn th =>
        REWRITE_TAC [th]) >>
      first_assum ACCEPT_TAC)
  >- ((* im ⊑ st'.inst *)
      (* Bridge entry forms so fold in assumption matches fold in goal *)
      qpat_x_assum `(if _ then widen _ _ else _) = _` (fn entry_eq =>
        qpat_x_assum `SND _ SUBMAP _` (fn sub =>
          assume_tac (REWRITE_RULE [entry_eq] sub))) >>
      qpat_x_assum `st' = _` (fn def => REWRITE_TAC [def]) >>
      match_mp_tac process_inst_grows >>
      MAP_EVERY qexists_tac [
        `b`,
        `case lookup_block b bbs of NONE => [] | SOME bb => bb.bb_instructions`,
        `df_widen_entry bottom st b`,
        `FST (df_fold_block dir (transfer ctx) b
          (case lookup_block b bbs of NONE => [] | SOME bb => bb.bb_instructions)
          (df_widen_entry bottom st b))`] >>
      simp[pairTheory.PAIR])
QED

(* CFG preds/succs inverse → deps complete for widening process.
   Join absorption needed for self-stability. *)
(* Fixed: df_process_block_widen now guards dws_visits increment on
   actual state change (new_st ≠ st). When process is a no-op,
   visits are not incremented, so process lbl st = st holds at fixpoint. *)
Theorem df_process_widen_deps_complete_proof:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val cfg bbs.
    (!a b. MEM b (cfg_succs_of cfg a) <=> MEM a (cfg_preds_of cfg b)) /\
    (!a b. join (join a b) b = join a b) /\
    (!a b. widen (widen a b) b = widen a b) /\
    (!a. widen a a = a)
  ==>
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
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
      mp_tac (SIMP_RULE std_ss [LET_THM] df_widen_process_self_idempotent) >>
      disch_then (qspecl_then [`dir`, `bottom`, `join`, `widen`, `threshold`,
        `transfer`, `edge_transfer`, `ctx`, `entry_val`, `cfg`, `bbs`, `b`,
        `st`] mp_tac) >>
      impl_tac >- rw[] >>
      fs[])
  (* Case 2: process b st = st *)
  >- (CCONTR_TAC >>
      `b <> lbl` by (CCONTR_TAC >> fs[]) >>
      `~MEM lbl (case dir of Forward => cfg_preds_of cfg b
                            | Backward => cfg_succs_of cfg b)` by
        (Cases_on `dir` >> fs[] >> metis_tac[]) >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_widen_process_stable_after) >>
      disch_then (qspecl_then [`dir`, `bottom`, `join`, `widen`, `threshold`,
        `transfer`, `edge_transfer`, `ctx`, `entry_val`, `cfg`, `bbs`,
        `lbl`, `b`, `st`] mp_tac) >>
      impl_tac >- rw[] >>
      fs[])
QED

(* ===== Visit-counting convergence ===== *)

(* Structural: process either preserves state or increments visits by 1 *)
Theorem df_widen_process_visits_inc:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl st.
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let st' = process lbl st in
    st' = st \/
    (df_widen_visits st' lbl = df_widen_visits st lbl + 1 /\
     !l. l <> lbl ==> df_widen_visits st' l = df_widen_visits st l)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >>
  simp_tac std_ss [df_process_block_widen_def, LET_THM] >>
  pairarg_tac >> simp_tac std_ss [] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  rw[] >>
  simp[df_widen_visits_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* SUM helpers for visit-counting proofs *)
Triviality sum_map_le[local]:
  !(f:'b->num) g ls. (!l. MEM l ls ==> f l <= g l) ==>
    SUM (MAP f ls) <= SUM (MAP g ls)
Proof
  Induct_on `ls` >> simp[] >> rpt strip_tac >>
  `f h <= g h` by simp[] >>
  `SUM (MAP f ls) <= SUM (MAP g ls)` by
    (first_x_assum irule >> metis_tac[]) >>
  fs[]
QED

Theorem sum_map_inc:
  !(f:'b->num) g ls x.
    MEM x ls /\ f x < g x /\ (!l. l <> x ==> f l = g l) ==>
    SUM (MAP f ls) < SUM (MAP g ls)
Proof
  Induct_on `ls` >> simp[] >> rpt gen_tac >> strip_tac
  >- (* x = h: substitute, need f h < g h + SUM(f ls) <= SUM(g ls) *)
     (gvs[] >>
      `SUM (MAP f ls) <= SUM (MAP g ls)` suffices_by fs[] >>
      irule sum_map_le >> rpt strip_tac >>
      Cases_on `l = h` >> fs[])
  >- (* MEM x ls: use IH for SUM < SUM, need f h <= g h *)
     (`f h <= g h` by (Cases_on `h = x` >> fs[]) >>
      `SUM (MAP f ls) < SUM (MAP g ls)` by
        (first_x_assum irule >> qexists_tac `x` >> fs[]) >>
      fs[])
QED

Theorem sum_bound:
  !(f:'b->num) k ls.
    (!l. MEM l ls ==> f l <= k) ==>
    SUM (MAP f ls) <= k * LENGTH ls
Proof
  Induct_on `ls` >> simp[arithmeticTheory.MULT_CLAUSES] >>
  rpt strip_tac >>
  `f h <= k` by simp[] >>
  `SUM (MAP f ls) <= k * LENGTH ls` by
    metis_tac[listTheory.MEM] >>
  fs[]
QED

Triviality cfg_dfs_post_mem_pre:
  !fn lbl.
    MEM lbl (cfg_analyze fn).cfg_dfs_post ==>
    MEM lbl (cfg_analyze fn).cfg_dfs_pre
Proof
  rw[cfgHelpersTheory.cfg_analyze_dfs_post,
     cfgHelpersTheory.cfg_analyze_dfs_pre] >>
  Cases_on `entry_block fn` >> fs[] >>
  metis_tac[cfgHelpersTheory.dfs_post_walk_sound_thm,
            cfgHelpersTheory.dfs_pre_walk_complete]
QED

(* Generic convergence: if visits per label are bounded by K under P,
   and P implies stabilization at K visits, then iteration converges. *)
Theorem df_analyze_widen_fixpoint_by_visits:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (K : num) (P : 'a df_widen_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let all_lbls = cfg.cfg_dfs_pre in
      (* Lattice absorption/idem for deps_complete *)
      (!a b. MEM b (cfg_succs_of cfg a) <=> MEM a (cfg_preds_of cfg b)) /\
      (!a b. join (join a b) b = join a b) /\
      (!a b. widen (widen a b) b = widen a b) /\
      (!a. widen a a = a) /\
      (* Invariant P *)
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of
         NONE => P (init_df_widen_state bottom (MAP (\bb. bb.bb_label) bbs))
       | SOME (lbl, v) =>
           P ((init_df_widen_state bottom (MAP (\bb. bb.bb_label) bbs)) with
              dws_boundary := (init_df_widen_state bottom
                (MAP (\bb. bb.bb_label) bbs)).dws_boundary |+ (lbl, v))) /\
      (* Stabilization: at K visits under P, process is identity *)
      (!lbl st. P st /\ df_widen_visits st lbl >= K ==>
                process lbl st = st) /\
      (* Deps closure: succs of dfs_pre stay in dfs_pre *)
      (!lbl. MEM lbl all_lbls ==>
             EVERY (\s. MEM s all_lbls) (deps lbl))
    ==>
      is_fixpoint process all_lbls
        (df_analyze_widen dir bottom join widen threshold
           transfer edge_transfer ctx entry_val fn)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >>
  strip_tac >>
  simp_tac std_ss [df_analyze_widen_def, LET_THM] >>
  irule wl_iterate_fixpoint_process_restricted >>
  qabbrev_tac `process = df_process_block_widen dir bottom join widen
    threshold transfer edge_transfer ctx entry_val (cfg_analyze fn)
    fn.fn_blocks` >>
  qabbrev_tac `all_lbls = (cfg_analyze fn).cfg_dfs_pre` >>
  conj_tac
  >- (Cases_on `dir` >> fs[markerTheory.Abbrev_def] >>
      metis_tac[cfg_dfs_pre_mem_post]) >>
  conj_tac
  >- (qexistsl_tac [
        `\st. P st /\ !l. df_widen_visits st l <= K'`,
        `K' * LENGTH all_lbls`,
        `\st. SUM (MAP (\l. df_widen_visits st l) all_lbls)`,
        `\l. MEM l all_lbls`] >>
      simp[] >>
      conj_tac
      >- (Cases_on `entry_val` >> fs[]
          >- simp[init_df_widen_state_def, df_widen_visits_def,
                  finite_mapTheory.FLOOKUP_EMPTY]
          >- (Cases_on `x` >> fs[] >>
              simp[init_df_widen_state_def, df_widen_visits_def,
                   finite_mapTheory.FLOOKUP_EMPTY])) >>
      conj_tac
      >- (rpt strip_tac >> irule sum_bound >> simp[]) >>
      conj_tac
      >- (rpt strip_tac >>
          mp_tac (SIMP_RULE std_ss [LET_THM] df_widen_process_visits_inc) >>
          disch_then (qspecl_then [`dir`,`bottom`,`join`,`widen`,`threshold`,
            `transfer`,`edge_transfer`,`ctx`,`entry_val`,
            `cfg_analyze fn`, `fn.fn_blocks`,`lbl`,`st`] mp_tac) >>
          simp[markerTheory.Abbrev_def] >> strip_tac
          >- simp[]
          >- (Cases_on `l = lbl` >> fs[] >>
              CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS_EQUAL] >>
              `df_widen_visits st lbl >= K'` by DECIDE_TAC >>
              res_tac >> fs[])) >>
      conj_tac
      >- (rpt strip_tac >>
          mp_tac (SIMP_RULE std_ss [LET_THM] df_widen_process_visits_inc) >>
          disch_then (qspecl_then [`dir`,`bottom`,`join`,`widen`,`threshold`,
            `transfer`,`edge_transfer`,`ctx`,`entry_val`,
            `cfg_analyze fn`, `fn.fn_blocks`,`lbl`,`st`] mp_tac) >>
          simp[markerTheory.Abbrev_def] >> strip_tac >> gvs[] >>
          irule sum_map_inc >> qexists_tac `lbl` >> simp[]) >>
      Cases_on `dir` >> fs[listTheory.EVERY_MEM, markerTheory.Abbrev_def] >>
      metis_tac[cfg_dfs_post_mem_pre])
  >- (qunabbrev_tac `process` >>
      irule (SIMP_RULE std_ss [LET_THM] df_process_widen_deps_complete_proof) >>
      metis_tac[])
QED

(* Variant: takes wl_deps_complete directly instead of deriving it from
   absorption+idem. Useful when widen is not idempotent (e.g. normalized). *)
Theorem df_analyze_widen_fixpoint_by_visits_no_idem:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (K : num) (P : 'a df_widen_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let all_lbls = cfg.cfg_dfs_pre in
      (* Invariant P *)
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of
         NONE => P (init_df_widen_state bottom (MAP (\bb. bb.bb_label) bbs))
       | SOME (lbl, v) =>
           P ((init_df_widen_state bottom (MAP (\bb. bb.bb_label) bbs)) with
              dws_boundary := (init_df_widen_state bottom
                (MAP (\bb. bb.bb_label) bbs)).dws_boundary |+ (lbl, v))) /\
      (* Stabilization: at K visits under P, process is identity *)
      (!lbl st. P st /\ df_widen_visits st lbl >= K ==>
                process lbl st = st) /\
      (* Deps closure: succs of dfs_pre stay in dfs_pre *)
      (!lbl. MEM lbl all_lbls ==>
             EVERY (\s. MEM s all_lbls) (deps lbl)) /\
      (* deps_complete provided directly *)
      wl_deps_complete process deps
    ==>
      is_fixpoint process all_lbls
        (df_analyze_widen dir bottom join widen threshold
           transfer edge_transfer ctx entry_val fn)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >>
  strip_tac >>
  simp_tac std_ss [df_analyze_widen_def, LET_THM] >>
  irule wl_iterate_fixpoint_process_restricted >>
  qabbrev_tac `process = df_process_block_widen dir bottom join widen
    threshold transfer edge_transfer ctx entry_val (cfg_analyze fn)
    fn.fn_blocks` >>
  qabbrev_tac `all_lbls = (cfg_analyze fn).cfg_dfs_pre` >>
  conj_tac
  >- (Cases_on `dir` >> fs[markerTheory.Abbrev_def] >>
      metis_tac[cfg_dfs_pre_mem_post]) >>
  conj_tac
  >- (qexistsl_tac [
        `\st. P st /\ !l. df_widen_visits st l <= K'`,
        `K' * LENGTH all_lbls`,
        `\st. SUM (MAP (\l. df_widen_visits st l) all_lbls)`,
        `\l. MEM l all_lbls`] >>
      simp[] >>
      conj_tac
      >- (Cases_on `entry_val` >> fs[]
          >- simp[init_df_widen_state_def, df_widen_visits_def,
                  finite_mapTheory.FLOOKUP_EMPTY]
          >- (Cases_on `x` >> fs[] >>
              simp[init_df_widen_state_def, df_widen_visits_def,
                   finite_mapTheory.FLOOKUP_EMPTY])) >>
      conj_tac
      >- (rpt strip_tac >> irule sum_bound >> simp[]) >>
      conj_tac
      >- (rpt strip_tac >>
          mp_tac (SIMP_RULE std_ss [LET_THM] df_widen_process_visits_inc) >>
          disch_then (qspecl_then [`dir`,`bottom`,`join`,`widen`,`threshold`,
            `transfer`,`edge_transfer`,`ctx`,`entry_val`,
            `cfg_analyze fn`, `fn.fn_blocks`,`lbl`,`st`] mp_tac) >>
          simp[markerTheory.Abbrev_def] >> strip_tac
          >- simp[]
          >- (Cases_on `l = lbl` >> fs[] >>
              CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS_EQUAL] >>
              `df_widen_visits st lbl >= K'` by DECIDE_TAC >>
              res_tac >> fs[])) >>
      conj_tac
      >- (rpt strip_tac >>
          mp_tac (SIMP_RULE std_ss [LET_THM] df_widen_process_visits_inc) >>
          disch_then (qspecl_then [`dir`,`bottom`,`join`,`widen`,`threshold`,
            `transfer`,`edge_transfer`,`ctx`,`entry_val`,
            `cfg_analyze fn`, `fn.fn_blocks`,`lbl`,`st`] mp_tac) >>
          simp[markerTheory.Abbrev_def] >> strip_tac >> gvs[] >>
          irule sum_map_inc >> qexists_tac `lbl` >> simp[]) >>
      Cases_on `dir` >> fs[listTheory.EVERY_MEM, markerTheory.Abbrev_def] >>
      metis_tac[cfg_dfs_post_mem_pre])
  >- first_assum ACCEPT_TAC
QED

Theorem df_widen_process_boundary_other:
  ∀dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl st l.
    l ≠ lbl ⇒
    df_widen_boundary bottom (df_process_block_widen dir bottom join widen
      threshold transfer edge_transfer ctx entry_val cfg bbs lbl st) l =
    df_widen_boundary bottom st l
Proof
  rpt strip_tac >>
  simp_tac std_ss [df_process_block_widen_def, LET_THM] >>
  pairarg_tac >> simp_tac std_ss [] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  COND_CASES_TAC >- simp[] >>
  simp[df_widen_boundary_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

val _ = export_theory();
