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
Libs
  dep_rewrite

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
     join (df_widen_boundary bottom st lbl) final_val =
       df_widen_boundary bottom st lbl /\
     (let edge_vals = MAP (\nbr. edge_transfer ctx nbr lbl
           (df_widen_boundary bottom st nbr))
           (case dir of Forward => cfg_preds_of cfg lbl
                      | Backward => cfg_succs_of cfg lbl) in
      let joined = case edge_vals of
           [] => (case entry_val of NONE => bottom
                  | SOME (ev_lbl,v) => if lbl = ev_lbl then v else bottom)
        | v4::v5 => FOLDL join bottom edge_vals in
        (if df_widen_visits st lbl >= threshold
         then widen (df_widen_entry bottom st lbl) joined
         else joined) = df_widen_entry bottom st lbl))
Proof
  rpt gen_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  strip_tac >>
  qpat_x_assum `_ = st` (fn th =>
    let val th' = AP_TERM ``\(s:'a df_widen_state). s.dws_visits`` th
    in assume_tac (BETA_RULE th') end) >>
  fs[] >>
  pop_assum (mp_tac o Q.AP_TERM `\f. FLOOKUP f lbl`) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE,
       dfAnalyzeWidenDefsTheory.df_widen_visits_def] >>
  Cases_on `FLOOKUP st.dws_visits lbl` >> simp[]
QED

(* Any FOLDL that only updates dws_inst preserves boundary/entry/visits *)
Triviality foldl_inst_only_preserves[local]:
  !lbls (f : 'a df_widen_state -> string -> 'a df_widen_state) acc.
    (!st lbl. (f st lbl).dws_boundary = st.dws_boundary) /\
    (!st lbl. (f st lbl).dws_entry = st.dws_entry) /\
    (!st lbl. (f st lbl).dws_visits = st.dws_visits) ==>
    (FOLDL f acc lbls).dws_boundary = acc.dws_boundary /\
    (FOLDL f acc lbls).dws_entry = acc.dws_entry /\
    (FOLDL f acc lbls).dws_visits = acc.dws_visits
Proof
  Induct >> rw[]
QED

(* populate only changes dws_inst, so boundary/entry/visits are preserved *)
Triviality populate_widen_inst_preserves_fields:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbls (st:'a df_widen_state).
    (df_populate_widen_inst dir bottom join widen threshold transfer
       edge_transfer ctx entry_val cfg bbs lbls st).dws_boundary =
      st.dws_boundary /\
    (df_populate_widen_inst dir bottom join widen threshold transfer
       edge_transfer ctx entry_val cfg bbs lbls st).dws_entry =
      st.dws_entry /\
    (df_populate_widen_inst dir bottom join widen threshold transfer
       edge_transfer ctx entry_val cfg bbs lbls st).dws_visits =
      st.dws_visits
Proof
  rpt gen_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_populate_widen_inst_def] >>
  irule foldl_inst_only_preserves >>
  rw[] >> pairarg_tac >> rw[]
QED

(* After populate, FLOOKUP dws_inst (lbl, idx) equals the fold output for lbl.
   Requires: fold outputs for different labels have disjoint keys. *)
Triviality foldl_funion_unchanged[local]:
  !lbls (f : string -> (string # num, 'a) fmap) acc k.
    (!l. MEM l lbls ==> k NOTIN FDOM (f l)) ==>
    FLOOKUP (FOLDL (\m l. FUNION (f l) m) acc lbls) k = FLOOKUP acc k
Proof
  Induct >> rw[] >>
  simp[finite_mapTheory.FLOOKUP_FUNION] >>
  `k NOTIN FDOM (f h)` by metis_tac[] >>
      fs[finite_mapTheory.FLOOKUP_DEF]
QED

Triviality foldl_funion_lookup[local]:
  !lbls (f : string -> (string # num, 'a) fmap) acc lbl k.
    MEM lbl lbls /\
    (!l. MEM l lbls /\ l <> lbl ==> k NOTIN FDOM (f l)) /\
    k IN FDOM (f lbl) ==>
    FLOOKUP (FOLDL (\m l. FUNION (f l) m) acc lbls) k = FLOOKUP (f lbl) k
Proof
  Induct >> rw[] >> fs[] >>
  simp[finite_mapTheory.FLOOKUP_FUNION] >>
  Cases_on`MEM h lbls` >- ( first_x_assum irule >> rw[] ) >>
  DEP_REWRITE_TAC[foldl_funion_unchanged] >>
  simp[finite_mapTheory.FLOOKUP_FUNION] >>
  gvs[finite_mapTheory.TO_FLOOKUP] >>
  CASE_TAC >> gvs[] >> rw[] >>
  first_x_assum irule >> rw[] >>
  strip_tac >> gvs[]
QED

(* f(lbl) ⊑ FOLDL (\acc l. f(l) ⊌ acc) init lbls when MEM lbl lbls
   and fold keys for different labels are disjoint *)
(* f \sqsubseteq acc and all additions are disjoint from f
   ==> f \sqsubseteq FOLDL (\m l. g l \cup m) acc lbls *)
Triviality submap_foldl_funion_disjoint[local]:
  !lbls (g : string -> (string # num, 'a) fmap) acc0
   (f0 : (string # num, 'a) fmap).
    f0 SUBMAP acc0 /\
    (!l. MEM l lbls ==> DISJOINT (FDOM f0) (FDOM (g l)))
  ==>
    f0 SUBMAP FOLDL (\m l. FUNION (g l) m) acc0 lbls
Proof
  Induct >> simp[] >> rw[] >>
  first_x_assum irule >> rw[] >>
  irule finite_mapTheory.SUBMAP_FUNION >> DISJ2_TAC >> fs[pred_setTheory.DISJOINT_SYM]
QED

Triviality foldl_funion_submap[local]:
  !lbls (f : string -> (string # num, 'a) fmap) acc lbl.
    MEM lbl lbls /\
    (!l1 l2. MEM l1 lbls /\ MEM l2 lbls /\ l1 <> l2 ==>
             DISJOINT (FDOM (f l1)) (FDOM (f l2)))
  ==>
    f lbl SUBMAP FOLDL (\m l. FUNION (f l) m) acc lbls
Proof
  Induct >> rw[] >> fs[] >>
  metis_tac[submap_foldl_funion_disjoint,
            finite_mapTheory.SUBMAP_FUNION_ID]
QED

(* Extract dws_inst from FOLDL that only updates dws_inst *)
Triviality foldl_extract_dws_inst[local]:
  !lbls (f : string -> (string # num, 'a) fmap) (st:'a df_widen_state).
    (FOLDL (\st' l. st' with dws_inst := FUNION (f l) st'.dws_inst)
           st lbls).dws_inst =
    FOLDL (\acc l. FUNION (f l) acc) st.dws_inst lbls
Proof
  Induct >> simp[]
QED

(* Extraction: dws_inst of populate = FOLDL of FUNION over fold outputs *)
Triviality populate_widen_inst_ds_inst[local]:
  !lbls dir (bottom:'a) join widen threshold transfer edge_transfer ctx
   entry_val cfg bbs (st:'a df_widen_state).
    (df_populate_widen_inst dir bottom join widen threshold transfer
       edge_transfer ctx entry_val cfg bbs lbls st).dws_inst =
    FOLDL (\acc lbl.
      let neighbors = case dir of Forward => cfg_preds_of cfg lbl
                                | Backward => cfg_succs_of cfg lbl in
      let edge_vals = MAP (\nbr. edge_transfer ctx nbr lbl
                       (df_widen_boundary bottom st nbr)) neighbors in
      let joined = case edge_vals of
                     [] => (case entry_val of NONE => bottom
                           | SOME (ev_lbl, v) => if lbl = ev_lbl then v
                                                  else bottom)
                   | v4::v5 => FOLDL join bottom edge_vals in
      let entry = if df_widen_visits st lbl >= threshold
                  then widen (df_widen_entry bottom st lbl) joined
                  else joined in
      let instrs = case lookup_block lbl bbs of NONE => []
                   | SOME bb => bb.bb_instructions in
      let (fv, im) = df_fold_block dir (transfer ctx) lbl instrs entry in
        FUNION im acc) st.dws_inst lbls
Proof
  Induct
  >> simp[dfAnalyzeWidenDefsTheory.df_populate_widen_inst_def, LET_THM]
  >> rpt gen_tac >> pairarg_tac >> simp[]
  >> first_x_assum (qspecl_then [`dir`, `bottom`, `join`, `widen`,
       `threshold`, `transfer`, `edge_transfer`, `ctx`, `entry_val`,
       `cfg`, `bbs`,
       `st with dws_inst := FUNION inst_map st.dws_inst`] mp_tac)
  >> simp_tac std_ss [
       dfAnalyzeWidenDefsTheory.df_widen_boundary_def,
       dfAnalyzeWidenDefsTheory.df_widen_entry_def,
       dfAnalyzeWidenDefsTheory.df_widen_visits_def,
       dfAnalyzeWidenDefsTheory.df_populate_widen_inst_def,
       dfAnalyzeWidenDefsTheory.df_widen_state_accfupds,
       LET_THM]
QED

Triviality fold_inst_disjoint_snd[local]:
  !dir transfer l1 i1 e1 l2 i2 e2.
    l1 <> l2 ==>
    DISJOINT (FDOM (SND (df_fold_block dir transfer l1 i1 e1)))
             (FDOM (SND (df_fold_block dir transfer l2 i2 e2)))
Proof
  rpt strip_tac >>
  Cases_on `df_fold_block dir transfer l1 i1 e1` >>
  Cases_on `df_fold_block dir transfer l2 i2 e2` >>
  fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
     pred_setTheory.IN_INTER, pred_setTheory.NOT_IN_EMPTY] >>
  rpt strip_tac >> CCONTR_TAC >> fs[] >>
  imp_res_tac dfAnalyzeProofsTheory.df_fold_block_keys >>
  `FST x = l1` by (first_x_assum irule >> fs[finite_mapTheory.FLOOKUP_DEF]) >>
  `FST x = l2` by (first_x_assum irule >> fs[finite_mapTheory.FLOOKUP_DEF]) >>
  fs[]
QED

(* For a label in lbls, the fold inst_map is a submap of populate result *)
Triviality populate_widen_inst_submap[local]:
  !dir (bottom:'a) join widen threshold transfer edge_transfer ctx
   entry_val cfg bbs lbls (st:'a df_widen_state) lbl bb.
    MEM lbl lbls /\
    ALL_DISTINCT lbls /\
    lookup_block lbl bbs = SOME bb
  ==>
    let neighbors = case dir of Forward => cfg_preds_of cfg lbl
                              | Backward => cfg_succs_of cfg lbl in
    let edge_vals = MAP (\nbr. edge_transfer ctx nbr lbl
                     (df_widen_boundary bottom st nbr)) neighbors in
    let joined = case edge_vals of
                   [] => (case entry_val of NONE => bottom
                         | SOME (ev_lbl, v) => if lbl = ev_lbl then v
                                                else bottom)
                 | v4::v5 => FOLDL join bottom edge_vals in
    let entry = if df_widen_visits st lbl >= threshold
                then widen (df_widen_entry bottom st lbl) joined
                else joined in
    let (fv, im) = df_fold_block dir (transfer ctx) lbl
                     bb.bb_instructions entry in
    im SUBMAP (df_populate_widen_inst dir bottom join widen threshold
                 transfer edge_transfer ctx entry_val cfg bbs lbls st).dws_inst
Proof
  rpt gen_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  simp[populate_widen_inst_ds_inst] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qho_match_abbrev_tac`im SUBMAP
    FOLDL (\acc l. FUNION (g l) acc) _ _` >>
  `im = g lbl` by (
    simp[Abbr`g`] >>
    Cases_on `lookup_block lbl bbs` >> fs[] >> gvs[] >>
    pairarg_tac >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  irule foldl_funion_submap >> simp[] >> rw[Abbr`g`] >>
  metis_tac[fold_inst_disjoint_snd]
QED

(* is_fixpoint transfers through populate when process only depends on
   boundary/entry/visits *)
Triviality is_fixpoint_populate_widen:
  !process dir bottom join widen threshold transfer edge_transfer ctx
   entry_val cfg bbs lbls all_lbls (st:'a df_widen_state).
    (!lbl st1 st2.
       st1.dws_boundary = st2.dws_boundary /\
       st1.dws_entry = st2.dws_entry /\
       st1.dws_visits = st2.dws_visits /\
       process lbl st1 = st1 ==>
       process lbl st2 = st2) /\
    is_fixpoint process all_lbls st ==>
    is_fixpoint process all_lbls
      (df_populate_widen_inst dir bottom join widen threshold transfer
         edge_transfer ctx entry_val cfg bbs lbls st)
Proof
  rw[worklistDefsTheory.is_fixpoint_def] >>
  first_x_assum irule >>
  first_x_assum drule >> rw[] >>
  goal_assum drule >>
  rw[populate_widen_inst_preserves_fields]
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

Theorem process_at_lbl_simple:
    (process = df_process_block_widen dir bottom join widen threshold
                transfer edge_transfer ctx entry_val cfg bbs /\
    st1 = process lbl st /\
    neighbors = (case dir of Forward => cfg_preds_of cfg lbl
                          | Backward => cfg_succs_of cfg lbl) /\
    edge_vals = MAP (\nbr. edge_transfer ctx nbr lbl
                 (df_widen_boundary bottom st nbr)) neighbors /\
    joined = (case edge_vals of
               [] => (case entry_val of NONE => bottom
                     | SOME (ev_lbl, v) => if lbl = ev_lbl then v
                                           else bottom)
             | v4::v5 => FOLDL join bottom edge_vals) /\
    entry = (if df_widen_visits st lbl >= threshold
            then widen (df_widen_entry bottom st lbl) joined
            else joined) /\
    instrs = (case lookup_block lbl bbs of NONE => []
             | SOME bb => bb.bb_instructions))
    ==>
      (st1 = st \/
      (df_widen_boundary bottom st1 lbl =
         join (df_widen_boundary bottom st lbl)
           (FST (df_fold_block dir (transfer ctx) lbl instrs entry)) /\
       df_widen_entry bottom st1 lbl = entry /\
       df_widen_visits st1 lbl = df_widen_visits st lbl + 1))
Proof
  strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  strip_assume_tac process_at_lbl >>
  gvs[]
QED

Triviality process_fixpoint_simple[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl st entry fv.
    entry = (let edge_vals = MAP (\nbr. edge_transfer ctx nbr lbl
                  (df_widen_boundary bottom st nbr))
                  (case dir of Forward => cfg_preds_of cfg lbl
                             | Backward => cfg_succs_of cfg lbl) in
             let joined = case edge_vals of
                  [] => (case entry_val of NONE => bottom
                        | SOME (ev_lbl,v) => if lbl = ev_lbl then v else bottom)
               | v4::v5 => FOLDL join bottom edge_vals in
               if df_widen_visits st lbl >= threshold
               then widen (df_widen_entry bottom st lbl) joined
               else joined) /\
    fv = FST (df_fold_block dir (transfer ctx) lbl
           (case lookup_block lbl bbs of NONE => [] | SOME bb => bb.bb_instructions)
           entry)
    ==>
    (df_process_block_widen dir bottom join widen threshold
       transfer edge_transfer ctx entry_val cfg bbs lbl st = st <=>
     join (df_widen_boundary bottom st lbl) fv = df_widen_boundary bottom st lbl /\
     entry = df_widen_entry bottom st lbl)
Proof
  rpt gen_tac >>
  strip_tac >>
  rewrite_tac[df_widen_process_fixpoint] >>
  gvs[] >>
  pairarg_tac >> gvs[]
QED

(* Same as process_fixpoint_simple but with process as a variable *)
Triviality process_fixpoint_simple2[local]:
  !process lbl st entry fv.
    process = df_process_block_widen dir bottom join widen threshold
                transfer edge_transfer ctx entry_val cfg bbs /\
    entry = (let edge_vals = MAP (\nbr. edge_transfer ctx nbr lbl
                  (df_widen_boundary bottom st nbr))
                  (case dir of Forward => cfg_preds_of cfg lbl
                             | Backward => cfg_succs_of cfg lbl) in
             let joined = case edge_vals of
                  [] => (case entry_val of NONE => bottom
                        | SOME (ev_lbl,v) => if lbl = ev_lbl then v else bottom)
               | v4::v5 => FOLDL join bottom edge_vals in
               if df_widen_visits st lbl >= threshold
               then widen (df_widen_entry bottom st lbl) joined
               else joined) /\
    fv = FST (df_fold_block dir (transfer ctx) lbl
           (case lookup_block lbl bbs of NONE => [] | SOME bb => bb.bb_instructions)
           entry)
    ==>
    (process lbl st = st <=>
     join (df_widen_boundary bottom st lbl) fv = df_widen_boundary bottom st lbl /\
     entry = df_widen_entry bottom st lbl)
Proof
  rw[] >> irule process_fixpoint_simple >> simp[]
QED

(* process result only depends on boundary/entry/visits fields *)
Triviality process_fields_independent[local]:
  !process lbl st1 st2.
    process = df_process_block_widen dir bottom join widen threshold
      transfer edge_transfer ctx entry_val cfg bbs /\
    st1.dws_boundary = st2.dws_boundary /\
    st1.dws_entry = st2.dws_entry /\
    st1.dws_visits = st2.dws_visits /\
    process lbl st1 = st1 ==>
    process lbl st2 = st2
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `!lbl. df_widen_boundary bottom st1 lbl = df_widen_boundary bottom st2 lbl` by
    fs[dfAnalyzeWidenDefsTheory.df_widen_boundary_def] >>
  `!lbl. df_widen_entry bottom st1 lbl = df_widen_entry bottom st2 lbl` by
    fs[dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
  `!lbl. df_widen_visits st1 lbl = df_widen_visits st2 lbl` by
    fs[dfAnalyzeWidenDefsTheory.df_widen_visits_def] >>
  fs[SIMP_RULE std_ss [LET_THM] df_widen_process_fixpoint]
QED

(* CFG preds/succs inverse → deps complete for widening process.
   Join absorption needed for self-stability. *)
(* Fixed: df_process_block_widen now guards dws_visits increment on
   actual state change (new_st ≠ st). When process is a no-op,
   visits are not incremented, so process lbl st = st holds at fixpoint. *)
(* changed iff process ≠ st *)
Theorem df_widen_process_changed_equiv[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl (st:'a df_widen_state).
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let changed = (\lbl (old:'a df_widen_state) new.
                     df_widen_boundary bottom new lbl <>
                       df_widen_boundary bottom old lbl \/
                     df_widen_entry bottom new lbl <>
                       df_widen_entry bottom old lbl) in
    changed lbl st (process lbl st) <=> process lbl st <> st
Proof
  rpt gen_tac
  \\ BasicProvers.LET_ELIM_TAC >>
  Cases_on`process lbl st = st`
  >- gvs[Abbr`changed`] >>
  mp_tac process_at_lbl >>
  qpat_assum`Abbrev(process = _)`(fn th =>
    disch_then(mp_tac o (SPECL(#2(strip_comb(rand(rand(concl th)))))))) >>
  disch_then(qspecl_then[`lbl`,`st`]mp_tac) >>
  BasicProvers.LET_ELIM_TAC >> gvs[] >>
  gvs[Abbr`changed`] >>
  strip_tac >>
  qpat_assum`_ = df_widen_entry _ _ _`(SUBST1_TAC o SYM) >>
  qmatch_asmsub_abbrev_tac`join bnd fv = bnd` >>
  qmatch_asmsub_abbrev_tac`entry_expr = df_widen_entry _ _ _` >>
  gs[] >>
  strip_tac >>
  qspecl_then[`entry_expr`,`fv`]mp_tac(
  CONV_RULE(RESORT_FORALL_CONV(sort_vars["entry","fv"]))
    process_fixpoint_simple) >>
  disch_then(qspecl_then[`dir`,`bottom`,`join`,`widen`,`threshold`,
                         `transfer`,`edge_transfer`,`ctx`, `entry_val`,
                         `cfg`,`bbs`,`lbl`,`st`]mp_tac) >>
  impl_tac >- (rw[] >> gvs[]) >> rw[]
QED

Theorem df_widen_process_changed_equiv_simple[local]:
    process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs ∧
    changed = (\lbl (old:'a df_widen_state) new.
                     df_widen_boundary bottom new lbl <>
                       df_widen_boundary bottom old lbl \/
                     df_widen_entry bottom new lbl <>
                       df_widen_entry bottom old lbl)
                       ==>
    (changed lbl st (process lbl st) <=> process lbl st <> st)
Proof
  mp_tac df_widen_process_changed_equiv \\ rw[]
QED


(* ===== Self-idempotent ===== *)

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
  rpt gen_tac >> strip_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  rw[dfAnalyzeWidenDefsTheory.df_widen_boundary_def,
     finite_mapTheory.FLOOKUP_UPDATE]
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
  rpt gen_tac >> strip_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  rw[dfAnalyzeWidenDefsTheory.df_widen_visits_def,
     finite_mapTheory.FLOOKUP_UPDATE]
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
  rpt gen_tac >> strip_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  rw[dfAnalyzeWidenDefsTheory.df_widen_entry_def,
     finite_mapTheory.FLOOKUP_UPDATE]
QED

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
  rpt gen_tac >> BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum`Abbrev(process = _)`(assume_tac o
    REWRITE_RULE[markerTheory.Abbrev_def]) >>
  drule process_at_lbl_simple >>
  pop_assum(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]) >>
  disch_then(qspecl_then[`process lbl st`,`st`]mp_tac) >>
  disch_then(mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
  disch_then(qspec_then`lbl`mp_tac) >>
  rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac`_ = neighbours` >>
  disch_then(qspec_then`neighbours`mp_tac) >>
  rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac`_ = edge_vals` >>
  disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["edge_vals'"]))) >>
  disch_then(qspec_then`edge_vals`mp_tac) >>
  rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac`_ = joined` >>
  disch_then(qspec_then`joined`mp_tac) >>
  rewrite_tac[] >>
  disch_then(mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
  qmatch_goalsub_abbrev_tac`_ = entry` >>
  disch_then(qspec_then`entry`mp_tac) >>
  rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac`_ = instrs` >>
  disch_then(qspec_then`instrs`mp_tac) >>
  rewrite_tac[] >>
  Cases_on `process lbl st = st` >- simp[] >>
  simp[] >> strip_tac >>
  qpat_assum`_ = entry`(fn th => SUBST_ALL_TAC th >> assume_tac th) >>
  sg`MAP (λnbr. edge_transfer ctx nbr lbl (df_widen_boundary bottom (process lbl st) nbr)) neighbours =
   edge_vals`
  >- (
    simp[Abbr`edge_vals`, listTheory.MAP_EQ_f] >> rw[] >>
    AP_TERM_TAC >>
    qunabbrev_tac`process` >>
    irule df_widen_process_boundary >>
    strip_tac >> gvs[] ) >>
  qspecl_then[`process`,`lbl`,`process lbl st`]
    mp_tac process_fixpoint_simple2 >>
  qmatch_goalsub_abbrev_tac`_ /\ _ = entry1 /\ _` >>
  disch_then(qspec_then`entry1`mp_tac) >>
  qmatch_goalsub_abbrev_tac`_ /\ _ = fv1` >>
  disch_then(qspec_then`fv1`mp_tac) >>
  impl_tac >- rw[] >>
  disch_then SUBST1_TAC >>
  gvs[Abbr`entry`] >>
  reverse conj_asm2_tac >- (
    gvs[Abbr`entry1`] >>
    Cases_on`df_widen_visits st lbl + 1 ≥ threshold` >> simp[] >>
    Cases_on`df_widen_visits st lbl ≥ threshold` >> gvs[] ) >>
  gvs[Abbr`fv1`,Abbr`entry1`]
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
  rpt strip_tac >>
  qabbrev_tac `process = df_process_block_widen dir bottom join widen threshold
    transfer edge_transfer ctx entry_val cfg bbs` >>
  `process b st = st` by fs[Abbr`process`] >>
  (* Neighbor boundaries for b unchanged *)
  sg`MAP (λnbr. edge_transfer ctx nbr b (df_widen_boundary bottom (process lbl st) nbr))
       (case dir of Forward => cfg_preds_of cfg b | Backward => cfg_succs_of cfg b) =
     MAP (λnbr. edge_transfer ctx nbr b (df_widen_boundary bottom st nbr))
       (case dir of Forward => cfg_preds_of cfg b | Backward => cfg_succs_of cfg b)`
  >- (irule listTheory.MAP_CONG >> rw[] >> AP_TERM_TAC >>
      qunabbrev_tac`process` >> irule df_widen_process_boundary >>
      strip_tac >> gvs[] >> Cases_on `dir` >> fs[]) >>
  `df_widen_entry bottom (process lbl st) b = df_widen_entry bottom st b` by
    (qunabbrev_tac`process` >> irule df_widen_process_entry >> fs[]) >>
  `df_widen_visits (process lbl st) b = df_widen_visits st b` by
    (qunabbrev_tac`process` >> irule df_widen_process_visits >> fs[]) >>
  (* Apply fixpoint iff for b on (process lbl st) *)
  qspecl_then[`process`,`b`,`process lbl st`]
    mp_tac process_fixpoint_simple2 >>
  qmatch_goalsub_abbrev_tac`_ /\ _ = entry_b1 /\ _` >>
  disch_then(qspec_then`entry_b1`mp_tac) >>
  qmatch_goalsub_abbrev_tac`_ /\ _ = fv_b1` >>
  disch_then(qspec_then`fv_b1`mp_tac) >>
  impl_tac >- rw[] >>
  disch_then SUBST1_TAC >>
  (* Apply fixpoint iff for b on st (process b st = st) *)
  qspecl_then[`process`,`b`,`st`]
    mp_tac process_fixpoint_simple2 >>
  qmatch_goalsub_abbrev_tac`_ /\ _ = entry_b0 /\ _` >>
  disch_then(qspec_then`entry_b0`mp_tac) >>
  qmatch_goalsub_abbrev_tac`_ /\ _ = fv_b0` >>
  disch_then(qspec_then`fv_b0`mp_tac) >>
  impl_tac >- rw[] >>
  disch_then(fn th => fs[th]) >>
  (* entry_b1 = entry_b0 and fv_b1 = fv_b0 since all inputs match *)
  `entry_b1 = entry_b0` by fs[Abbr`entry_b1`, Abbr`entry_b0`] >>
  `df_widen_boundary bottom (process lbl st) b = df_widen_boundary bottom st b` by
    (qunabbrev_tac`process` >> irule df_widen_process_boundary >> fs[]) >>
  fs[Abbr`fv_b1`, Abbr`fv_b0`]
QED

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
    let changed = (\lbl (old:'a df_widen_state) new.
                     df_widen_boundary bottom new lbl <>
                       df_widen_boundary bottom old lbl \/
                     df_widen_entry bottom new lbl <>
                       df_widen_entry bottom old lbl) in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    wl_deps_complete changed process deps
Proof
  rpt gen_tac >> strip_tac >>
  BasicProvers.LET_ELIM_TAC >>
  simp[worklistDefsTheory.wl_deps_complete_def] >>
  rpt gen_tac >> strip_tac >>
  gen_tac >>
  disch_then assume_tac >>
  CCONTR_TAC >>
  sg`changed lbl st (process lbl st) <=> process lbl st <> st`
  >- (
    irule df_widen_process_changed_equiv_simple
    \\ metis_tac[] ) >>
  sg`process b (process lbl st) ≠ process lbl st`
  >- (
    irule (iffLR df_widen_process_changed_equiv_simple)
    \\ metis_tac[] ) >>
  Cases_on`b = lbl` >> gvs[]
  >- (
    gvs[Abbr`deps`] >>
    qspec_then`dir`mp_tac df_widen_process_self_idempotent >>
    Cases_on`dir` \\ gvs[] >>
    metis_tac[] ) >>
  sg`process b st = st` >- (
    CCONTR_TAC >>
    drule_at Any (iffRL df_widen_process_changed_equiv_simple) >>
    metis_tac[] ) >>
  drule df_widen_process_stable_after >>
  simp[] >> gvs[Abbr`deps`] >> qexists_tac`dir` >>
  qexistsl_tac[`bottom`,`join`,`widen`,`threshold`,`transfer`,
               `edge_transfer`,`ctx`,`entry_val`,`cfg`,`bbs`] >>
  gvs[] >>
  goal_assum $ drule_at Any >> gvs[] >>
  CASE_TAC >> gvs[]
QED

Theorem df_process_widen_deps_complete_simple:
    (!a b. MEM b (cfg_succs_of cfg a) <=> MEM a (cfg_preds_of cfg b)) /\
    (!a b. join (join a b) b = join a b) /\
    (!a b. widen (widen a b) b = widen a b) /\
    (!a. widen a a = a) /\
    process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs /\
    changed = (\lbl (old:'a df_widen_state) new.
                     df_widen_boundary bottom new lbl <>
                       df_widen_boundary bottom old lbl \/
                     df_widen_entry bottom new lbl <>
                       df_widen_entry bottom old lbl) /\
    deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) ==>
    wl_deps_complete changed process deps
Proof
  mp_tac df_process_widen_deps_complete_proof \\ rw[]
QED

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
    let changed = (\lbl (old:'a df_widen_state) new.
                     df_widen_boundary bottom new lbl <>
                       df_widen_boundary bottom old lbl \/
                     df_widen_entry bottom new lbl <>
                       df_widen_entry bottom old lbl) in
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
      wl_deps_complete changed process deps
    ==>
      is_fixpoint process all_lbls
        (df_analyze_widen dir bottom join widen threshold
           transfer edge_transfer ctx entry_val fn)
Proof
  rw[df_analyze_widen_def] >>
  qmatch_goalsub_abbrev_tac `wl_iterate ch process deps wl0 st0` >>
  irule is_fixpoint_populate_widen >>
  conj_tac
  >- (rw[] >>
      irule process_fields_independent >>
      metis_tac[]) >>
  irule wl_iterate_fixpoint_proof >>
  conj_tac >- (
    rw[] >> irule df_widen_process_changed_equiv_simple >>
    metis_tac[]) >>
  conj_tac >- (
    rw[Abbr`wl0`] >> Cases_on `dir` >> simp[] >>
    metis_tac[dfAnalyzeProofsTheory.cfg_dfs_pre_mem_post]) >>
  conj_tac >- fs[] >>
  qexistsl_tac [`P`, `b`, `leq`, `m`] >>
  rw[Abbr`st0`] >>
  Cases_on `entry_val` >> fs[] >>
  Cases_on `x` >> fs[]
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
       (result.dws_boundary = st.dws_boundary |+
          (lbl, join (df_widen_boundary bottom st lbl) final_val) /\
        result.dws_entry = st.dws_entry |+ (lbl, entry) /\
        result.dws_visits = st.dws_visits |+
          (lbl, df_widen_visits st lbl + 1)))
Proof
  rpt gen_tac >>
  simp_tac std_ss [LET_THM] >>
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def, LET_THM] >>
  pairarg_tac >> fs[] >>
  IF_CASES_TAC >> fs[]
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
  Cases_on `edge_vals` >> simp[]
  >- (rw[] >> Cases_on `entry_val` >> fs[] >>
      Cases_on `x` >> fs[] >> rw[] >> fs[])
  >> strip_tac >>
     irule foldl_join_P >> fs[listTheory.EVERY_DEF]
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
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >- (rpt strip_tac >> res_tac) >>
  (* changed case *)
  `!nbr. P (df_widen_boundary bottom st nbr)` by
    (rw[dfAnalyzeWidenDefsTheory.df_widen_boundary_def] >>
     Cases_on `FLOOKUP st.dws_boundary nbr` >> fs[] >> res_tac) >>
  qmatch_asmsub_abbrev_tac
    `df_fold_block dir _ lbl _ entry_v = (final_val, inst_map)` >>
  sg `P entry_v`
  >- (qunabbrev_tac `entry_v` >> IF_CASES_TAC >> simp[]
      >- (qpat_x_assum `!a b. P a /\ P b ==> P (widen a b)`
            (fn wth => irule wth) >> conj_tac
          >- (simp[dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
              Cases_on `FLOOKUP st.dws_entry lbl` >> fs[] >> res_tac)
          >> irule joined_P >> simp[] >> P_edge_vals_tac)
      >> irule joined_P >> simp[] >> P_edge_vals_tac) >>
  drule_all (REWRITE_RULE [GSYM AND_IMP_INTRO]
    dfAnalyzeProofsTheory.df_fold_block_P) >> strip_tac >>
  rpt conj_tac
  >- (rpt strip_tac >> res_tac)
  >- (rpt strip_tac >>
      fs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >> gvs[] >>
      TRY res_tac >>
      first_x_assum irule >> conj_tac >> gvs[] >>
      simp[dfAnalyzeWidenDefsTheory.df_widen_boundary_def] >>
      Cases_on `FLOOKUP st.dws_boundary lbl` >> gvs[] >> res_tac)
  >> rpt strip_tac >>
     fs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >> gvs[] >> res_tac
QED

(* Generic: FOLDL preserves dws_inst property when each step does *)
Triviality foldl_dws_inst_P[local]:
  !xs (f : 'a df_widen_state -> string -> 'a df_widen_state) init.
    (!st x. (!k v. FLOOKUP st.dws_inst k = SOME v ==> P v) ==>
            (!k v. FLOOKUP (f st x).dws_inst k = SOME v ==> P v)) /\
    (!k v. FLOOKUP init.dws_inst k = SOME v ==> P v)
    ==>
    (!k v. FLOOKUP (FOLDL f init xs).dws_inst k = SOME v ==> P v)
Proof
  Induct_on `xs` >> rpt strip_tac >> fs[]
  >- res_tac
  \\ first_x_assum (qspecl_then [`f`, `f init h`] mp_tac)
  \\ impl_tac
  >- (fs[] >> rpt strip_tac >> res_tac)
  \\ strip_tac >> res_tac
QED

(* Generic: FOLDL of FUNION preserves P when each step's fmap has P *)
Triviality foldl_funion_P[local]:
  !lbls (g : string -> (string # num, 'a) fmap) acc.
    (!lbl k v. FLOOKUP (g lbl) k = SOME v ==> P v) /\
    (!k v. FLOOKUP acc k = SOME v ==> P v)
    ==>
    !k v. FLOOKUP (FOLDL (\m l. FUNION (g l) m) acc lbls) k = SOME v ==> P v
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`g`, `FUNION (g h) acc`] mp_tac) >>
  impl_tac
  >- (fs[] >> rpt strip_tac >>
      fs[finite_mapTheory.FLOOKUP_FUNION, AllCaseEqs()] >> res_tac)
  >> simp[]
QED

(* Helper: populate preserves element-level P for inst values *)
Triviality populate_widen_inst_P[local]:
  !dir (bottom:'a) join widen threshold transfer edge_transfer ctx
   entry_val cfg bbs lbls (st:'a df_widen_state).
    P bottom /\
    (case entry_val of NONE => T | SOME (lbl, v) => P v) /\
    (!a b. P a /\ P b ==> P (join a b)) /\
    (!a b. P a /\ P b ==> P (widen a b)) /\
    (!inst a. P a ==> P (transfer ctx inst a)) /\
    (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
    (!k v. FLOOKUP st.dws_boundary k = SOME v ==> P v) /\
    (!k v. FLOOKUP st.dws_entry k = SOME v ==> P v) /\
    (!k v. FLOOKUP st.dws_inst k = SOME v ==> P v)
    ==>
    (!k v. FLOOKUP (df_populate_widen_inst dir bottom join widen threshold
             transfer edge_transfer ctx entry_val cfg bbs lbls st).dws_inst
             k = SOME v ==> P v)
Proof
  rpt gen_tac >> strip_tac >>
  PURE_ONCE_REWRITE_TAC
    [dfAnalyzeWidenDefsTheory.df_populate_widen_inst_def] >>
  match_mp_tac foldl_dws_inst_P >>
  reverse conj_tac >- fs[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  BETA_TAC >> BasicProvers.LET_ELIM_TAC >>
  gvs[finite_mapTheory.FLOOKUP_FUNION, AllCaseEqs()] >>
  `!nbr. P (df_widen_boundary bottom st nbr)` by
    (rw[dfAnalyzeWidenDefsTheory.df_widen_boundary_def] >>
     Cases_on `FLOOKUP st.dws_boundary nbr` >> fs[] >> res_tac) >>
  `!lbl'. P (df_widen_entry bottom st lbl')` by
    (rw[dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
     Cases_on `FLOOKUP st.dws_entry lbl'` >> fs[] >> res_tac) >>
  `P entry` by
    (MAP_EVERY qunabbrev_tac
       [`entry`, `joined`, `edge_vals`, `neighbors`] >>
     P_init_val_tac) >>
  drule_all (REWRITE_RULE [GSYM AND_IMP_INTRO]
    dfAnalyzeProofsTheory.df_fold_block_P) >>
  strip_tac >> res_tac
QED

(* Helper: FOLDL of constant fupdate preserves P when P holds for
   bottom and for all initial values *)
Triviality foldl_fupdate_P[local]:
  !lbls bottom acc k v.
    P bottom ==>
    (!k v. FLOOKUP acc k = SOME v ==> P v) ==>
    FLOOKUP (FOLDL (\m lbl. m |+ (lbl, bottom)) acc lbls) k = SOME v ==>
    P v
Proof
  Induct >> simp[] >> rpt strip_tac
  >- res_tac
  \\ first_x_assum (qspecl_then [`bottom`, `acc |+ (h, bottom)`, `k`, `v`]
    mp_tac) >> simp[] >> disch_then irule >>
  rpt gen_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `h = k'` >> gvs[] >> res_tac
QED

(* Helper: FOLDL of constant fupdate preserves acc-values = c *)
Triviality foldl_fupdate_all_const_gen[local]:
  !lbls c acc k v.
    (!k' v'. FLOOKUP acc k' = SOME v' ==> v' = c) ==>
    FLOOKUP (FOLDL (\m lbl. m |+ (lbl, c)) acc lbls) k = SOME v ==> v = c
Proof
  Induct >> simp[] >> rpt strip_tac
  >- res_tac
  \\ first_x_assum (qspecl_then [`c`, `acc |+ (h,c)`, `k`, `v`] mp_tac) >>
     disch_then irule >>
     conj_tac
     >- (rpt gen_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
         rpt strip_tac >> Cases_on `h = k'` >> gvs[] >> res_tac)
     >> first_x_assum ACCEPT_TAC
QED

(* Corollary for FEMPTY accumulator *)
Triviality foldl_fupdate_all_const[local]:
  !lbls c k v.
    FLOOKUP (FOLDL (\m lbl. m |+ (lbl, c)) FEMPTY lbls) k = SOME v ==> v = c
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`lbls`, `c`, `FEMPTY`, `k`, `v`] foldl_fupdate_all_const_gen) >>
  simp[finite_mapTheory.FLOOKUP_EMPTY]
QED

(* Helper: df_process_block_widen preserves dws_inst field *)
Triviality process_widen_preserves_inst[local]:
  !(dir : direction) (bottom : 'a) join widen threshold transfer
   edge_transfer ctx entry_val cfg bbs lbl st.
    (df_process_block_widen dir bottom join widen threshold transfer
       edge_transfer ctx entry_val cfg bbs lbl st).dws_inst = st.dws_inst
Proof
  rpt gen_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
QED


(* Helper: process preserves bnd-P, ent-P, inst-P together.
   Wraps df_widen_process_P + process_widen_preserves_inst. *)
Triviality process_preserves_all_P[local]:
  !(dir : direction) (bottom : 'a) join widen threshold transfer
   edge_transfer ctx entry_val cfg bbs lbl st.
    P bottom /\
    (case entry_val of NONE => T | SOME (lbl, v) => P v) /\
    (!a b. P a /\ P b ==> P (join a b)) /\
    (!a b. P a /\ P b ==> P (widen a b)) /\
    (!inst a. P a ==> P (transfer ctx inst a)) /\
    (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
    (!k v. FLOOKUP st.dws_boundary k = SOME v ==> P v) /\
    (!k v. FLOOKUP st.dws_entry k = SOME v ==> P v) /\
    (!k v. FLOOKUP st.dws_inst k = SOME v ==> P v)
    ==>
    (!k v. FLOOKUP (df_process_block_widen dir bottom join widen threshold
             transfer edge_transfer ctx entry_val cfg bbs lbl st).dws_boundary
             k = SOME v ==> P v) /\
    (!k v. FLOOKUP (df_process_block_widen dir bottom join widen threshold
             transfer edge_transfer ctx entry_val cfg bbs lbl st).dws_entry
             k = SOME v ==> P v) /\
    (!k v. FLOOKUP (df_process_block_widen dir bottom join widen threshold
             transfer edge_transfer ctx entry_val cfg bbs lbl st).dws_inst
             k = SOME v ==> P v)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (SIMP_RULE std_ss [LET_THM] df_widen_process_P) >>
  disch_then (qspecl_then [`dir`,`bottom`,`join`,`widen`,`threshold`,
    `transfer`,`edge_transfer`,`ctx`,`entry_val`,`cfg`,`bbs`,
    `lbl`,`st`] mp_tac) >>
  simp[] >> impl_tac >- metis_tac[] >>
  strip_tac >> simp[process_widen_preserves_inst] >>
  rpt conj_tac >> first_x_assum ACCEPT_TAC
QED

(* Helper: wl_iterate preserves boundary/entry/inst P.
   Standalone for debuggability with hol_state_at. *)
Triviality wl_iterate_bnd_ent_inst_P[local]:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn (P : 'a -> bool)
   (leq : 'a df_widen_state -> 'a df_widen_state -> bool)
   m b (Q : 'a df_widen_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let st0 = init_df_widen_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let chg = (\lbl old new.
        df_widen_boundary bottom new lbl =
        df_widen_boundary bottom old lbl ==>
        df_widen_entry bottom new lbl <>
        df_widen_entry bottom old lbl) in
    let depf = (case dir of Forward => cfg_succs_of cfg
                           | Backward => cfg_preds_of cfg) in
    let wl0 = (case dir of Forward => cfg.cfg_dfs_pre
                          | Backward => cfg.cfg_dfs_post) in
    let st0' = (case entry_val of NONE => st0
                | SOME (lbl, v) =>
                    st0 with dws_boundary := st0.dws_boundary |+ (lbl, v)) in
      P bottom /\
      (case entry_val of NONE => T | SOME (lbl, v) => P v) /\
      (!a b. P a /\ P b ==> P (join a b)) /\
      (!a b. P a /\ P b ==> P (widen a b)) /\
      (!inst a. P a ==> P (transfer ctx inst a)) /\
      (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
      (!lbl st. Q st ==> leq st (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with dws_boundary := st0.dws_boundary |+ (lbl, v))) /\
      bounded_measure Q leq m b
    ==>
      (!k v. FLOOKUP (SND (wl_iterate chg process depf wl0 st0')).dws_boundary
             k = SOME v ==> P v) /\
      (!k v. FLOOKUP (SND (wl_iterate chg process depf wl0 st0')).dws_entry
             k = SOME v ==> P v) /\
      (!k v. FLOOKUP (SND (wl_iterate chg process depf wl0 st0')).dws_inst
             k = SOME v ==> P v)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `FLOOKUP wli.dws_boundary` >>
  `(\st. Q st /\
     (!k v. FLOOKUP st.dws_boundary k = SOME v ==> P v) /\
     (!k v. FLOOKUP st.dws_entry k = SOME v ==> P v) /\
     (!k v. FLOOKUP st.dws_inst k = SOME v ==> P v)) wli`
     suffices_by metis_tac[]
  \\ qunabbrev_tac `wli`
  \\ irule wl_iterate_invariant_proof >> simp[]
  \\ conj_tac
  >- (conj_tac
      >- (BasicProvers.every_case_tac >> first_x_assum ACCEPT_TAC)
      >> BasicProvers.every_case_tac >>
         simp[dfAnalyzeWidenDefsTheory.init_df_widen_state_def,
              finite_mapTheory.FLOOKUP_UPDATE] >>
         rpt strip_tac >>
         BasicProvers.every_case_tac >> gvs[] >>
         drule foldl_fupdate_all_const >> gvs[])
  (* 2. Changed <=> <> *)
  \\ conj_tac
  >- (rpt gen_tac >>
      PURE_ONCE_REWRITE_TAC
        [GSYM dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
      PURE_ONCE_REWRITE_TAC
        [GSYM dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
      simp[SIMP_RULE std_ss [LET_THM] df_widen_process_changed_equiv])
  \\ conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule process_preserves_all_P >>
      rpt conj_tac >> first_x_assum ACCEPT_TAC)
  (* 4. Bounded measure *)
  \\ qexistsl_tac [`b`, `leq`, `m`]
  \\ gvs[latticeDefsTheory.bounded_measure_def]
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
  rpt gen_tac
  \\ simp_tac std_ss [LET_THM]
  \\ strip_tac
  \\ simp[dfAnalyzeWidenDefsTheory.df_analyze_widen_def, LET_THM]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ qmatch_goalsub_abbrev_tac `SND (wl_iterate chg proc depf wl0 st0')`
  (* Step 1: boundary/entry/inst P via wl_iterate_invariant_proof *)
  \\ `(\st. Q st /\
       (!k v. FLOOKUP st.dws_boundary k = SOME v ==> P v) /\
       (!k v. FLOOKUP st.dws_entry k = SOME v ==> P v) /\
       (!k v. FLOOKUP st.dws_inst k = SOME v ==> P v))
     (SND (wl_iterate chg proc depf wl0 st0'))` by (
    MAP_EVERY qunabbrev_tac [`chg`, `proc`, `depf`, `wl0`, `st0'`] >>
    irule wl_iterate_invariant_proof >> simp[] >>
    (* 1. Initial *)
    conj_tac >- (conj_tac
        >- (BasicProvers.every_case_tac >> first_x_assum ACCEPT_TAC)
        >> BasicProvers.every_case_tac >>
           simp[dfAnalyzeWidenDefsTheory.init_df_widen_state_def,
                finite_mapTheory.FLOOKUP_UPDATE] >>
           rpt strip_tac >>
           BasicProvers.every_case_tac >> gvs[] >>
           drule foldl_fupdate_all_const >> gvs[]) >>
    (* 2. Changed *)
    conj_tac >- (rpt gen_tac >>
        PURE_ONCE_REWRITE_TAC
          [GSYM dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
        PURE_ONCE_REWRITE_TAC
          [GSYM dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
        simp[SIMP_RULE std_ss [LET_THM] df_widen_process_changed_equiv]) >>
    (* 3. Preservation *)
    conj_tac >- (rpt gen_tac >> strip_tac >>
        irule process_preserves_all_P >>
        rpt conj_tac >> first_x_assum ACCEPT_TAC) >>
    (* 4. Bounded measure *)
    qexistsl_tac [`b`, `leq`, `m`] >>
    gvs[latticeDefsTheory.bounded_measure_def])
  \\ pop_assum mp_tac >> BETA_TAC >> strip_tac
  (* Step 2: convert to boundary/entry/at *)
  \\ qmatch_goalsub_abbrev_tac
       `df_populate_widen_inst _ _ _ _ _ _ _ _ _ _ _ _ swli`
  \\ simp[dfAnalyzeWidenDefsTheory.df_widen_boundary_def,
          dfAnalyzeWidenDefsTheory.df_widen_entry_def,
          dfAnalyzeWidenDefsTheory.df_widen_at_def,
          populate_widen_inst_preserves_fields]
  \\ rpt conj_tac
  (* at: use populate_widen_inst_P *)
  >- (rpt gen_tac >>
      Cases_on `FLOOKUP (df_populate_widen_inst dir bottom join widen
        threshold transfer edge_transfer ctx entry_val (cfg_analyze fn)
        fn.fn_blocks (MAP (\bb. bb.bb_label) fn.fn_blocks) swli).dws_inst
        (lbl,idx)` >> simp[] >>
      (* SOME case: establish inst-P of populate result *)
      `!k v. FLOOKUP (df_populate_widen_inst dir bottom join widen
        threshold transfer edge_transfer ctx entry_val (cfg_analyze fn)
        fn.fn_blocks (MAP (\bb. bb.bb_label) fn.fn_blocks) swli).dws_inst
        k = SOME v ==> P v` by (
        mp_tac (Q.SPECL [`dir`, `bottom`, `join`, `widen`, `threshold`,
          `transfer`, `edge_transfer`, `ctx`, `entry_val`,
          `cfg_analyze fn`, `fn.fn_blocks`,
          `MAP (\bb. bb.bb_label) fn.fn_blocks`,
          `swli`] (SIMP_RULE std_ss [LET_THM]
          populate_widen_inst_P)) >>
        impl_tac >- (rpt conj_tac >> first_x_assum ACCEPT_TAC) >>
        simp[]) >>
      res_tac)
  (* boundary *)
  >- (gen_tac >>
      Cases_on `FLOOKUP swli.dws_boundary lbl` >> simp[] >> res_tac)
  (* entry *)
  >> gen_tac >>
     Cases_on `FLOOKUP swli.dws_entry lbl` >> simp[] >> res_tac
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
  rpt gen_tac
  \\ simp_tac std_ss [LET_THM]
  \\ strip_tac
  \\ rpt gen_tac
  \\ simp[dfAnalyzeWidenDefsTheory.df_analyze_widen_def, LET_THM,
          dfAnalyzeWidenDefsTheory.df_widen_entry_def,
          populate_widen_inst_preserves_fields]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  (* Goal: sound (case FLOOKUP (SND (wl_iterate ...)).dws_entry lbl of
                   NONE => bottom | SOME v => v) s *)
  \\ qmatch_goalsub_abbrev_tac`SND (wl_iterate chg proc depf wl0 st0')`
  (* Prove all entries of wl_iterate result are sound *)
  (* Prove invariant for the wl_iterate result via helper lemma *)
  \\ `(\st. Q st /\ !k v. FLOOKUP st.dws_entry k = SOME v ==> !s. sound v s)
       (SND (wl_iterate chg proc depf wl0 st0'))` by (
    irule wl_iterate_invariant_proof >> simp[] >>
    (* After simp[]: 4 conjuncts: initial, changed, entry-pres, measure *)
    conj_tac
    (* 1. Initial: Q st0' /\ entry-sound st0' *)
    (* 1. Initial: Q st0' /\ entry-sound st0' *)
    >- (simp[Abbr`st0'`] >> conj_tac
        >- (BasicProvers.every_case_tac >> first_x_assum ACCEPT_TAC)
        >> BasicProvers.every_case_tac >>
           simp[dfAnalyzeWidenDefsTheory.init_df_widen_state_def,
                finite_mapTheory.FLOOKUP_UPDATE,
                dfAnalyzeWidenDefsTheory.df_widen_state_component_equality] >>
           rpt strip_tac >>
           gvs[finite_mapTheory.FLOOKUP_DEF]) >>
    conj_tac
    (* 2. Changed <=> <> *)
    >- (rpt gen_tac >> simp[Abbr`chg`, Abbr`proc`] >>
        PURE_ONCE_REWRITE_TAC [GSYM dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
        PURE_ONCE_REWRITE_TAC [GSYM dfAnalyzeWidenDefsTheory.df_widen_entry_def] >>
        simp[SIMP_RULE std_ss [LET_THM] df_widen_process_changed_equiv]) >>
    conj_tac
    (* 3. Entry-sound preservation *)
    >- (rpt strip_tac >>
        irule (SIMP_RULE std_ss [LET_THM] df_widen_process_entry_sound) >>
        gvs[Abbr`proc`] >> metis_tac[]) >>
    (* 4. Bounded_measure *)
    qexistsl_tac [`b`, `leq`, `m`] >>
    gvs[latticeDefsTheory.bounded_measure_def, Abbr`proc`])
  \\ pop_assum mp_tac >> BETA_TAC >> strip_tac
  \\ Cases_on `FLOOKUP (SND (wl_iterate chg proc depf wl0 st0')).dws_entry lbl`
  >> fs[] >> res_tac >> fs[]
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
  rpt strip_tac >>
  simp_tac std_ss [LET_THM] >>
  rpt gen_tac >>
  Cases_on `lbl' = lbl`
  >- (rw[] >>
      simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def, LET_THM] >>
      pairarg_tac >> simp[] >>
      IF_CASES_TAC >> fs[relationTheory.reflexive_def] >>
      simp[dfAnalyzeWidenDefsTheory.df_widen_boundary_def,
           finite_mapTheory.FLOOKUP_UPDATE])
  >> simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def, LET_THM] >>
     pairarg_tac >> simp[] >>
     rw[dfAnalyzeWidenDefsTheory.df_widen_boundary_def,
        finite_mapTheory.FLOOKUP_UPDATE] >>
     fs[relationTheory.reflexive_def]
QED

(* ===== Deps complete helpers ===== *)

(* Non-lbl boundary stability: process only updates lbl's boundary *)
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
  rpt gen_tac >>
  simp_tac std_ss [LET_THM] >>
  strip_tac >>
  `MAP (\nbr. edge_transfer ctx nbr lbl (df_widen_boundary bottom st1 nbr))
       (case dir of Forward => cfg_preds_of cfg lbl
                  | Backward => cfg_succs_of cfg lbl) =
   MAP (\nbr. edge_transfer ctx nbr lbl (df_widen_boundary bottom st2 nbr))
       (case dir of Forward => cfg_preds_of cfg lbl
                  | Backward => cfg_succs_of cfg lbl)` by
    (irule listTheory.MAP_CONG >> rw[] >> res_tac >> simp[]) >>
  fs[] >> pairarg_tac >> fs[]
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
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  strip_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def, LET_THM] >>
  pairarg_tac >> fs[] >> rw[] >>
  gvs[finite_mapTheory.fmap_eq_flookup,
      finite_mapTheory.FLOOKUP_UPDATE,
      dfAnalyzeWidenDefsTheory.df_widen_boundary_def,
      dfAnalyzeWidenDefsTheory.df_widen_entry_def,
      dfAnalyzeWidenDefsTheory.df_widen_visits_def]
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
      entry = df_widen_entry bottom st lbl /\
      join (df_widen_boundary bottom st lbl) fv =
        df_widen_boundary bottom st lbl
Proof
  rpt gen_tac >>
  simp_tac std_ss [LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> fs[] >>
  strip_tac >>
  qpat_x_assum `_ = st` (fn th =>
    let val th' = AP_TERM ``\(s:'a df_widen_state). s.dws_visits`` th
    in assume_tac (BETA_RULE th') end) >>
  fs[] >>
  pop_assum (mp_tac o Q.AP_TERM `\f. FLOOKUP f lbl`) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE,
       dfAnalyzeWidenDefsTheory.df_widen_visits_def] >>
  Cases_on `FLOOKUP st.dws_visits lbl` >> simp[]
QED

val pfa_clean = CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
                  (SIMP_RULE std_ss [LET_THM] process_fixpoint_absorbs);

(* ===== Widen inst SUBMAP and fixpoint characterization ===== *)

(* Boundary/entry/visits of populate result equal those of pre-populate state *)
Triviality df_widen_boundary_populate[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbls (st:'a df_widen_state) lbl.
    df_widen_boundary bottom
      (df_populate_widen_inst dir bottom join widen threshold transfer
         edge_transfer ctx entry_val cfg bbs lbls st) lbl =
    df_widen_boundary bottom st lbl
Proof
  rpt gen_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_widen_boundary_def,
       populate_widen_inst_preserves_fields]
QED

Triviality df_widen_entry_populate[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbls (st:'a df_widen_state) lbl.
    df_widen_entry bottom
      (df_populate_widen_inst dir bottom join widen threshold transfer
         edge_transfer ctx entry_val cfg bbs lbls st) lbl =
    df_widen_entry bottom st lbl
Proof
  rpt gen_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_widen_entry_def,
       populate_widen_inst_preserves_fields]
QED

Triviality df_widen_visits_populate[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbls (st:'a df_widen_state) lbl.
    df_widen_visits
      (df_populate_widen_inst dir bottom join widen threshold transfer
         edge_transfer ctx entry_val cfg bbs lbls st) lbl =
    df_widen_visits st lbl
Proof
  rpt gen_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_widen_visits_def,
       populate_widen_inst_preserves_fields]
QED

val find_some_mem = prove(
  ``!P ls x. FIND P ls = SOME x ==> MEM x ls /\ P x``,
  gen_tac >> Induct >> simp[listTheory.FIND_thm] >>
  rpt strip_tac >> gvs[AllCaseEqs()]);

(* The inst_map for a label is a submap of the analyze result *)
Triviality df_widen_analyze_inst_submap[local]:
  !dir (bottom:'a) join widen threshold transfer edge_transfer ctx
   entry_val fn lbl bb.
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
    wf_function fn /\
    is_fixpoint (df_process_block_widen dir bottom join widen threshold
                  transfer edge_transfer ctx entry_val
                  (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb
  ==>
    SND (df_fold_block dir (transfer ctx) lbl bb.bb_instructions
           (df_widen_entry bottom result lbl))
      SUBMAP result.dws_inst
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  (* Get entry = computed_entry from fixpoint *)
  qpat_x_assum `is_fixpoint _ _ _` (fn fp =>
    assume_tac fp >>
    mp_tac (REWRITE_RULE [worklistDefsTheory.is_fixpoint_def] fp)) >>
  disch_then (qspec_then `lbl` mp_tac) >> simp[] >>
  disch_then (mp_tac o MATCH_MP pfa_clean) >>
  simp_tac std_ss [LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  strip_tac >>
  (* entry equality: first conjunct, rewrite goal *)
  pop_assum (K ALL_TAC) >>  (* drop boundary eq *)
  pop_assum (fn th => SUBST_ALL_TAC (SYM th)) >>
  (* Now entry in goal is the computed form *)
  simp_tac std_ss [dfAnalyzeWidenDefsTheory.df_analyze_widen_def, LET_THM,
                   dfAnalyzeDefsTheory.direction_case_def] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp_tac std_ss [df_widen_entry_populate, df_widen_boundary_populate,
                   df_widen_visits_populate] >>
  ho_match_mp_tac (PairRules.PBETA_RULE
           (SIMP_RULE std_ss [LET_THM] populate_widen_inst_submap)) >>
  fs[venomInstTheory.fn_labels_def,
     venomWfTheory.wf_function_def,
     venomInstTheory.lookup_block_def] >>
  imp_res_tac find_some_mem >>
  fs[listTheory.MEM_MAP] >> metis_tac[]
QED

(* df_widen_at from SUBMAP *)
Triviality df_widen_at_from_submap[local]:
  !(im : (string # num, 'a) fmap) (st : 'a df_widen_state) bottom lbl idx v.
    im SUBMAP st.dws_inst /\ FLOOKUP im (lbl, idx) = SOME v ==>
    df_widen_at bottom st lbl idx = v
Proof
  rw[dfAnalyzeWidenDefsTheory.df_widen_at_def] >>
  fs[finite_mapTheory.SUBMAP_DEF, finite_mapTheory.FLOOKUP_DEF] >>
  metis_tac[]
QED

(* Combined: at fixpoint, df_widen_at values follow the transfer relation *)
Triviality df_widen_fixpoint_at[local]:
  !dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl result all_lbls bb instrs entry.
    let (fv, im) = df_fold_block dir (transfer ctx) lbl
                     bb.bb_instructions
                     (df_widen_entry bottom result lbl) in
    is_fixpoint
      (df_process_block_widen dir bottom join widen threshold
        transfer edge_transfer ctx entry_val cfg bbs) all_lbls result /\
    MEM lbl all_lbls /\
    lookup_block lbl bbs = SOME bb /\
    instrs = bb.bb_instructions /\
    entry = df_widen_entry bottom result lbl /\
    im SUBMAP result.dws_inst
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
  rpt gen_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  Cases_on `dir` >> fs[dfAnalyzeDefsTheory.df_fold_block_def] >> strip_tac >> rw[]
  >- (drule dfAnalyzeProofsTheory.df_fold_forward_at >> strip_tac >>
      irule df_widen_at_from_submap >> qexists_tac `im` >> fs[])
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
  >- (drule dfAnalyzeProofsTheory.df_fold_backward_at >> strip_tac >>
      irule df_widen_at_from_submap >> qexists_tac `im` >> fs[])
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

(* ===== Transfer proofs ===== *)

val widen_fixpoint_at_clean =
  PairRules.PBETA_RULE (SIMP_RULE std_ss [LET_THM] df_widen_fixpoint_at);

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
      wf_function fn /\
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
  rpt gen_tac
  \\ simp_tac std_ss [LET_THM]
  \\ strip_tac
  \\ `SND (df_fold_block dir (transfer ctx) lbl bb.bb_instructions
         (df_widen_entry bottom
            (df_analyze_widen dir bottom join widen threshold
               transfer edge_transfer ctx entry_val fn) lbl))
       SUBMAP
       (df_analyze_widen dir bottom join widen threshold
          transfer edge_transfer ctx entry_val fn).dws_inst` by
    (irule (SIMP_RULE std_ss [LET_THM] df_widen_analyze_inst_submap) \\
     asm_rewrite_tac[])
  \\ mp_tac widen_fixpoint_at_clean
  \\ disch_then (qspecl_then [`dir`, `bottom`, `join`, `widen`, `threshold`,
       `transfer`, `edge_transfer`, `ctx`, `entry_val`,
       `cfg_analyze fn`, `fn.fn_blocks`, `lbl`,
       `df_analyze_widen dir bottom join widen threshold
          transfer edge_transfer ctx entry_val fn`,
       `(cfg_analyze fn).cfg_dfs_pre`, `bb`,
       `bb.bb_instructions`,
       `df_widen_entry bottom
          (df_analyze_widen dir bottom join widen threshold
             transfer edge_transfer ctx entry_val fn) lbl`] mp_tac)
  \\ simp[]
QED

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
      wf_function fn /\
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
  rpt gen_tac
  \\ simp_tac std_ss [LET_THM]
  \\ strip_tac
  \\ `SND (df_fold_block dir (transfer ctx) lbl bb.bb_instructions
         (df_widen_entry bottom
            (df_analyze_widen dir bottom join widen threshold
               transfer edge_transfer ctx entry_val fn) lbl))
       SUBMAP
       (df_analyze_widen dir bottom join widen threshold
          transfer edge_transfer ctx entry_val fn).dws_inst` by
    (irule (SIMP_RULE std_ss [LET_THM] df_widen_analyze_inst_submap) \\
     asm_rewrite_tac[])
  \\ mp_tac widen_fixpoint_at_clean
  \\ disch_then (qspecl_then [`dir`, `bottom`, `join`, `widen`, `threshold`,
       `transfer`, `edge_transfer`, `ctx`, `entry_val`,
       `cfg_analyze fn`, `fn.fn_blocks`, `lbl`,
       `df_analyze_widen dir bottom join widen threshold
          transfer edge_transfer ctx entry_val fn`,
       `(cfg_analyze fn).cfg_dfs_pre`, `bb`,
       `bb.bb_instructions`,
       `df_widen_entry bottom
          (df_analyze_widen dir bottom join widen threshold
             transfer edge_transfer ctx entry_val fn) lbl`] mp_tac)
  \\ simp[]
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
  rw[dfAnalyzeDefsTheory.df_fold_block_def] >>
  Cases_on `dir` >> fs[] >>
  imp_res_tac dfAnalyzeProofsTheory.df_fold_forward_fdom >>
  imp_res_tac dfAnalyzeProofsTheory.df_fold_backward_fdom >>
  fs[finite_mapTheory.FDOM_FEMPTY, pred_setTheory.UNION_EMPTY] >>
  rw[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
     pred_setTheory.IN_INTER, pred_setTheory.IN_IMAGE,
     pred_setTheory.NOT_IN_EMPTY, pred_setTheory.IN_COUNT] >>
  metis_tac[pairTheory.FST]
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
  rw[] >>
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
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
  rpt gen_tac >>
  simp_tac std_ss [LET_THM] >>
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def, LET_THM] >>
  pairarg_tac >> fs[] >>
  IF_CASES_TAC >> fs[] >>
  rw[dfAnalyzeWidenDefsTheory.df_widen_visits_def,
     finite_mapTheory.FLOOKUP_UPDATE]
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
  Induct_on `ls` >> rw[]
  (* x = h *)
  >- (`SUM (MAP f ls) <= SUM (MAP g ls)` by
        (irule sum_map_le >> rw[] >>
         Cases_on `l = h` >> fs[]) >> simp[])
  (* x in ls *)
  >> Cases_on `x = h` >> fs[]
  (* x = h again: both h in ls and head *)
  >- (`SUM (MAP f ls) <= SUM (MAP g ls)` by
        (irule sum_map_le >> rw[] >>
         Cases_on `l = h` >> fs[]) >> simp[])
  (* x ≠ h: h unchanged, recurse *)
  >> `f h = g h` by (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
     simp[] >>
     first_x_assum irule >> metis_tac[]
QED

Theorem sum_bound:
  !(f:'b->num) k ls.
    (!l. MEM l ls ==> f l <= k) ==>
    SUM (MAP f ls) <= k * LENGTH ls
Proof
  Induct_on `ls` >> rw[] >> fs[] >>
  `f h <= k` by simp[] >>
  `SUM (MAP f ls) <= k * LENGTH ls` by (first_x_assum irule >> simp[]) >>
  simp[arithmeticTheory.MULT_SUC]
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
  rpt gen_tac >> BasicProvers.LET_ELIM_TAC >>
  rw[df_analyze_widen_def] >>
  irule is_fixpoint_populate_widen >>
  conj_tac >- (rw[] >> irule process_fields_independent >> metis_tac[]) >>
  irule worklistProofsTheory.wl_iterate_fixpoint_process_restricted >>
  conj_tac >- (
    irule df_widen_process_changed_equiv_simple >> metis_tac[]) >>
  conj_tac >- (
    rw[Abbr`all_lbls`] >> Cases_on `dir` >> simp[] >>
    metis_tac[dfAnalyzeProofsTheory.cfg_dfs_pre_mem_post]) >>
  conj_tac >- (
    qexistsl_tac [
      `\st. P st /\ !lbl. df_widen_visits st lbl <= K'`,
      `K' * LENGTH all_lbls`,
      `\st. SUM (MAP (df_widen_visits st) all_lbls)`,
      `\lbl. MEM lbl all_lbls`] >>
    simp[GSYM CONJ_ASSOC] >>
    (* P' st0 *)
    conj_asm1_tac >- (CASE_TAC >> gvs[] >> CASE_TAC >> gvs[]) >>
    qmatch_goalsub_abbrev_tac `df_widen_visits cst` >>
    conj_asm1_tac >- (
      simp[Abbr`cst`, dfAnalyzeWidenDefsTheory.df_widen_visits_def,
           dfAnalyzeWidenDefsTheory.init_df_widen_state_def] >>
      CASE_TAC >> gvs[] >> CASE_TAC >> gvs[]) >>
    (* m x ≤ b *)
    conj_tac >- (rw[] >> irule sum_bound >> rw[]) >>
    (* P' preserved by process for valid labels *)
    conj_tac >- (
      rw[] >> fs[] >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_widen_process_visits_inc) >>
      disch_then (qspecl_then [`dir`,`bottom`,`join`,`widen`,`threshold`,
        `transfer`,`edge_transfer`,`ctx`,`entry_val`,`cfg`,`bbs`,`lbl`,`st`]
        strip_assume_tac) >>
      gvs[] >>
      `df_widen_visits st lbl < K'` by (
        CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS] >> res_tac >> fs[]) >>
      gvs[] >>
      Cases_on`lbl = lbl'` \\ gvs[]) >>
    (* measure increases for valid labels *)
    conj_tac >- (
      rw[] >>
      irule sum_map_inc >>
      qexists_tac `lbl` >> rw[] >>
      mp_tac (SIMP_RULE std_ss [LET_THM] df_widen_process_visits_inc) >>
      disch_then (qspecl_then [`dir`,`bottom`,`join`,`widen`,`threshold`,
        `transfer`,`edge_transfer`,`ctx`,`entry_val`,`cfg`,`bbs`,`lbl`,`st`]
        strip_assume_tac) >>
      gvs[] >>
      `df_widen_visits st lbl < K'` by (
        CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS] >> res_tac >> fs[]) >>
      fs[]) >>
    (* valid_lbl closed under deps *)
    (* EVERY valid_lbl wl0 *)
    Cases_on `dir` >> simp[listTheory.EVERY_MEM] >> rw[Abbr`all_lbls`] >>
    metis_tac[cfg_dfs_post_mem_pre]) >>
  irule df_process_widen_deps_complete_simple >>
  simp[Abbr`process`,Abbr`deps`, FUN_EQ_THM] >>
  goal_assum(drule_at(Pos(el 3))) >>
  goal_assum(drule_at(Pos(el 3))) >>
  goal_assum(drule_at(Pos(el 2))) >>
  metis_tac[]
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
    let chg = (\lbl old new.
                 df_widen_boundary bottom new lbl <>
                 df_widen_boundary bottom old lbl \/
                 df_widen_entry bottom new lbl <>
                 df_widen_entry bottom old lbl) in
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
      wl_deps_complete chg process deps
    ==>
      is_fixpoint process all_lbls
        (df_analyze_widen dir bottom join widen threshold
           transfer edge_transfer ctx entry_val fn)
Proof
  rpt gen_tac >> BasicProvers.LET_ELIM_TAC >>
  rw[df_analyze_widen_def] >>
  irule is_fixpoint_populate_widen >>
  conj_tac >- (rw[] >> irule process_fields_independent >> metis_tac[]) >>
  irule worklistProofsTheory.wl_iterate_fixpoint_process_restricted >>
  simp[] >>
  conj_tac >- (
    irule df_widen_process_changed_equiv_simple >> metis_tac[]) >>
  conj_tac >- (
    rw[Abbr`all_lbls`] >> Cases_on `dir` >> simp[] >>
    metis_tac[dfAnalyzeProofsTheory.cfg_dfs_pre_mem_post]) >>
  qexistsl_tac [
    `\st. P st /\ !lbl. df_widen_visits st lbl <= K'`,
    `K' * LENGTH all_lbls`,
    `\st. SUM (MAP (df_widen_visits st) all_lbls)`,
    `\lbl. MEM lbl all_lbls`] >>
  simp[GSYM CONJ_ASSOC] >>
  conj_asm1_tac >- (CASE_TAC >> gvs[] >> CASE_TAC >> gvs[]) >>
  qmatch_goalsub_abbrev_tac `df_widen_visits cst` >>
  conj_asm1_tac >- (
    simp[Abbr`cst`, dfAnalyzeWidenDefsTheory.df_widen_visits_def,
         dfAnalyzeWidenDefsTheory.init_df_widen_state_def] >>
    CASE_TAC >> gvs[] >> CASE_TAC >> gvs[]) >>
  conj_tac >- (rw[] >> irule sum_bound >> rw[]) >>
  conj_tac >- (
    rw[] >> fs[] >>
    mp_tac (SIMP_RULE std_ss [LET_THM] df_widen_process_visits_inc) >>
    disch_then (qspecl_then [`dir`,`bottom`,`join`,`widen`,`threshold`,
      `transfer`,`edge_transfer`,`ctx`,`entry_val`,`cfg`,`bbs`,`lbl`,`st`]
      strip_assume_tac) >>
    gvs[] >>
    `df_widen_visits st lbl < K'` by (
      CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS] >> res_tac >> fs[]) >>
    gvs[] >>
    Cases_on`lbl = lbl'` \\ gvs[]) >>
  conj_tac >- (
    rw[] >>
    irule sum_map_inc >>
    qexists_tac `lbl` >> rw[] >>
    mp_tac (SIMP_RULE std_ss [LET_THM] df_widen_process_visits_inc) >>
    disch_then (qspecl_then [`dir`,`bottom`,`join`,`widen`,`threshold`,
      `transfer`,`edge_transfer`,`ctx`,`entry_val`,`cfg`,`bbs`,`lbl`,`st`]
      strip_assume_tac) >>
    gvs[] >>
    `df_widen_visits st lbl < K'` by (
      CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS] >> res_tac >> fs[]) >>
    fs[]) >>
  Cases_on `dir` >> simp[listTheory.EVERY_MEM] >> rw[Abbr`all_lbls`] >>
  metis_tac[cfg_dfs_post_mem_pre]
QED

Theorem df_widen_process_boundary_other:
  ∀dir bottom join widen threshold transfer edge_transfer ctx entry_val
   cfg bbs lbl st l.
    l ≠ lbl ⇒
    df_widen_boundary bottom (df_process_block_widen dir bottom join widen
      threshold transfer edge_transfer ctx entry_val cfg bbs lbl st) l =
    df_widen_boundary bottom st l
Proof
  rpt gen_tac >> strip_tac >>
  simp[dfAnalyzeWidenDefsTheory.df_process_block_widen_def] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  rw[dfAnalyzeWidenDefsTheory.df_widen_boundary_def,
     finite_mapTheory.FLOOKUP_UPDATE]
QED

val _ = export_theory();
