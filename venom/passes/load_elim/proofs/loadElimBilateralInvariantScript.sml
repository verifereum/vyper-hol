Theory loadElimBilateralInvariant
Ancestors
  dfAnalyzeDefs dfAnalyzeProofs worklistDefs worklistProofs latticeDefs
  cfgDefs finite_map list
Libs
  pairLib

(* These implementation facts are local in dfAnalyzeProofs. *)
Theorem le_df_process_changed[local]:
  (df_boundary bottom
      (df_process_block dir bottom join transfer edge ctx entry cfg bbs lbl st) lbl <>
    df_boundary bottom st lbl) <=>
  df_process_block dir bottom join transfer edge ctx entry cfg bbs lbl st <> st
Proof
  rw[df_process_block_def, df_joined_val_def, df_boundary_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[] >>
  simp[df_state_component_equality, fmap_eq_flookup, FLOOKUP_UPDATE] >>
  CCONTR_TAC >> fs[] >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> fs[]
QED

Theorem le_df_process_inst[local]:
  (df_process_block dir bottom join transfer edge ctx entry cfg bbs lbl st).
    ds_inst = st.ds_inst
Proof
  simp[df_process_block_def] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem le_df_process_boundary_bilateral[local]:
  P bottom /\
  (case entry of NONE => T | SOME (lbl,v) => P v) /\
  (!a b. P a /\ P b ==> P (join a b)) /\
  (!inst a. P a ==> P (transfer ctx inst a)) /\
  (!src dst a. P a ==> P (edge ctx src dst a)) /\
  (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v) ==>
  !k v. FLOOKUP
    (df_process_block dir bottom join transfer edge ctx entry cfg bbs lbl st).
      ds_boundary k = SOME v ==> P v
Proof
  strip_tac >> simp[df_process_block_def] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >- metis_tac[] >>
  rpt gen_tac >> simp[FLOOKUP_UPDATE] >> IF_CASES_TAC
  >- (strip_tac >> gvs[] >>
      qpat_assum `!a b. P a /\ P b ==> P (join a b)` irule >>
      conj_tac
      >- (simp[df_boundary_def] >>
          Cases_on `FLOOKUP st.ds_boundary k` >> simp[] >> metis_tac[]) >>
      `P (df_joined_val dir bottom join edge ctx entry cfg st k)` by
        (irule df_joined_val_P >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      drule_all df_fold_block_P >> simp[]) >>
  metis_tac[]
QED

Theorem le_df_worklist_bilateral[local]:
  P bottom /\
  (case entry of NONE => T | SOME (lbl,v) => P v) /\
  (!a b. P a /\ P b ==> P (join a b)) /\
  (!inst a. P a ==> P (transfer ctx inst a)) /\
  (!src dst a. P a ==> P (edge ctx src dst a)) /\
  (!lbl st. Q st ==> leq st
    (df_process_block dir bottom join transfer edge ctx entry cfg bbs lbl st)) /\
  (!lbl st. Q st ==> Q
    (df_process_block dir bottom join transfer edge ctx entry cfg bbs lbl st)) /\
  Q initial /\ (!lbl. P (df_boundary bottom initial lbl)) /\
  initial.ds_inst = FEMPTY /\ bounded_measure Q leq m b ==>
  (!lbl. P (df_boundary bottom
    (SND (wl_iterate
      (\lbl old new. df_boundary bottom new lbl <> df_boundary bottom old lbl)
      (df_process_block dir bottom join transfer edge ctx entry cfg bbs)
      deps wl initial)) lbl)) /\
  (SND (wl_iterate
      (\lbl old new. df_boundary bottom new lbl <> df_boundary bottom old lbl)
      (df_process_block dir bottom join transfer edge ctx entry cfg bbs)
      deps wl initial)).ds_inst = FEMPTY
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `wl_iterate changed process deps wl initial` >>
  `(\st. Q st /\ (!lbl. P (df_boundary bottom st lbl)) /\
    st.ds_inst = FEMPTY) (SND (wl_iterate changed process deps wl initial))`
    suffices_by simp[] >>
  irule wl_iterate_invariant >> simp[] >>
  conj_tac >- simp[Abbr `changed`, Abbr `process`, le_df_process_changed] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (qx_gen_tac `k` >>
          `!k v. FLOOKUP (process lbl st).ds_boundary k = SOME v ==> P v` by
            (simp[Abbr `process`] >>
             match_mp_tac le_df_process_boundary_bilateral >> simp[] >>
             rpt strip_tac >>
             qpat_x_assum `!lbl. P (df_boundary bottom st lbl)`
               (qspec_then `k` mp_tac) >> simp[df_boundary_def]) >>
          simp[df_boundary_def] >>
          Cases_on `FLOOKUP (process lbl st).ds_boundary k` >> simp[] >> metis_tac[])
      >- simp[Abbr `process`, le_df_process_inst]) >>
  qexistsl [`b`,`leq`,`m`] >>
  simp[Abbr `process`, bounded_measure_def] >> gvs[bounded_measure_def]
QED

Theorem le_df_initial_valid[local]:
  P bottom /\ (case entry of NONE => T | SOME (lbl,v) => P v) ==>
  (!lbl. P (df_boundary bottom
    (case entry of
       NONE => init_df_state bottom lbls
     | SOME (lbl,v) => (init_df_state bottom lbls) with
         ds_boundary := (init_df_state bottom lbls).ds_boundary |+ (lbl,v)) lbl)) /\
  (case entry of
       NONE => init_df_state bottom lbls
     | SOME (lbl,v) => (init_df_state bottom lbls) with
         ds_boundary := (init_df_state bottom lbls).ds_boundary |+ (lbl,v)).ds_inst = FEMPTY
Proof
  strip_tac >> Cases_on `entry` >> simp[init_df_state_def, df_boundary_def] >>
  TRY (PairCases_on `x`) >> gvs[] >>
  rpt strip_tac >>
  Cases_on `FLOOKUP (FOLDL (\m lbl. m |+ (lbl,bottom)) FEMPTY lbls) lbl` >>
  gvs[FLOOKUP_UPDATE] >> imp_res_tac foldl_init_flookup >> gvs[] >>
  Cases_on `x0 = lbl` >> gvs[]
QED

Theorem le_df_analyze_invariant_bilateral:
  !dir bottom join transfer edge ctx entry fn P leq m b Q.
  P bottom /\
  (case entry of NONE => T | SOME (lbl,v) => P v) /\
  (!a b. P a /\ P b ==> P (join a b)) /\
  (!inst a. P a ==> P (transfer ctx inst a)) /\
  (!src dst a. P a ==> P (edge ctx src dst a)) /\
  (!lbl st. Q st ==> leq st
    (df_process_block dir bottom join transfer edge ctx entry
      (cfg_analyze fn) fn.fn_blocks lbl st)) /\
  (!lbl st. Q st ==> Q
    (df_process_block dir bottom join transfer edge ctx entry
      (cfg_analyze fn) fn.fn_blocks lbl st)) /\
  (case entry of
     NONE => Q (init_df_state bottom (MAP (\bb. bb.bb_label) fn.fn_blocks))
   | SOME (lbl,v) => Q
       ((init_df_state bottom (MAP (\bb. bb.bb_label) fn.fn_blocks)) with
         ds_boundary := (init_df_state bottom (MAP (\bb. bb.bb_label) fn.fn_blocks)).
           ds_boundary |+ (lbl,v))) /\
  bounded_measure Q leq m b ==>
  (!lbl idx. P (df_at bottom
    (df_analyze dir bottom join transfer edge ctx entry fn) lbl idx)) /\
  (!lbl. P (df_boundary bottom
    (df_analyze dir bottom join transfer edge ctx entry fn) lbl))
Proof
  rpt gen_tac >> strip_tac >> reverse conj_tac
  >- (irule (SRULE [LET_THM] df_analyze_boundary_invariant_bilateral) >>
      simp[] >> qexistsl [`Q`,`b`,`leq`,`m`] >> simp[]) >>
  `!k v. FLOOKUP (df_analyze dir bottom join transfer edge ctx entry fn).ds_inst k =
    SOME v ==> P v` suffices_by
    (strip_tac >> rpt gen_tac >> simp[df_at_def] >>
     Cases_on `FLOOKUP (df_analyze dir bottom join transfer edge ctx entry fn).ds_inst
       (lbl,idx)` >> simp[] >> metis_tac[]) >>
  simp[df_analyze_def] >> match_mp_tac populate_inst_P >>
  qmatch_goalsub_abbrev_tac `wl_iterate changed process deps wl initial` >>
  `(!lbl. P (df_boundary bottom (SND (wl_iterate changed process deps wl initial)) lbl)) /\
    (SND (wl_iterate changed process deps wl initial)).ds_inst = FEMPTY`
    suffices_by
    (strip_tac >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!lbl. P (df_boundary bottom _ lbl)`
       (qspec_then `k` mp_tac) >> simp[df_boundary_def]) >>
  `(!lbl. P (df_boundary bottom initial lbl)) /\ initial.ds_inst = FEMPTY` by
    (simp[Abbr `initial`] >> irule le_df_initial_valid >> simp[]) >>
  simp[Abbr `changed`, Abbr `process`] >>
  irule le_df_worklist_bilateral >> simp[] >>
  qexistsl [`Q`,`b`,`leq`,`m`] >> simp[] >>
  simp[Abbr `initial`] >>
  Cases_on `entry` >> gvs[] >> PairCases_on `x` >> gvs[]
QED
