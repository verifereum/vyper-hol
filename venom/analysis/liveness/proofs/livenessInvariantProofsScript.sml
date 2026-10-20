Theory livenessInvariantProofs
Ancestors
  livenessBlockProofs livenessTransferProofs
Libs
  listTheory pred_setTheory finite_mapTheory pairTheory arithmeticTheory
  dfAnalyzeDefsTheory dfAnalyzeProofsTheory

Definition lv_processed_def:
  lv_processed (st : string list df_state) l <=> (l,0n) IN FDOM st.ds_inst
End

(* A slice is either untouched, or a complete last fold from its stored exit.
   Boundary maps may already contain empty initial entries before processing. *)
Definition lv_coherent_def:
  lv_coherent bbs (st : string list df_state) <=>
    (!l i. (l,i) IN FDOM st.ds_inst <=>
       lv_processed st l /\ i <= LENGTH (liveness_instrs bbs l)) /\
    (!l i. lv_processed st l /\ i <= LENGTH (liveness_instrs bbs l) ==>
       df_at [] st l i =
         THE (FLOOKUP (SND (df_fold_block Backward (liveness_transfer bbs) l
           (liveness_instrs bbs l)
           (df_at [] st l (LENGTH (liveness_instrs bbs l))))) (l,i))) /\
    (!l. df_boundary [] st l = df_at [] st l 0)
End

Theorem lv_block_domain:
  (l,i) IN FDOM (liveness_block bbs cfg lbl st).ds_inst <=>
    (l = lbl /\ i <= LENGTH (liveness_instrs bbs lbl)) \/
    (l,i) IN FDOM st.ds_inst
Proof
  simp[liveness_block_eq] >> pairarg_tac >> simp[] >>
  drule df_fold_block_fdom_backward >> strip_tac >>
  simp[FDOM_FUNION, GSYM ADD1, GSYM LESS_EQ_IFF_LESS_SUC]
QED

Theorem lv_processed_block:
  lv_processed (liveness_block bbs cfg lbl st) l <=> l = lbl \/ lv_processed st l
Proof
  simp[lv_processed_def, lv_block_domain]
QED

Theorem lv_coherent_init:
  lv_coherent bbs (init_df_state [] labels)
Proof
  simp[lv_coherent_def, lv_processed_def, init_df_state_def, df_at_def,
       df_boundary_def] >> gen_tac >>
  Cases_on `FLOOKUP (FOLDL (\m lbl. m |+ (lbl, []:string list)) FEMPTY labels) l` >>
  simp[] >> drule foldl_init_flookup >> simp[]
QED

Theorem lv_coherent_domain:
  lv_coherent bbs st ==>
  !l i. (l,i) IN FDOM st.ds_inst <=>
     lv_processed st l /\ i <= LENGTH (liveness_instrs bbs l)
Proof
  simp_tac pure_ss [lv_coherent_def] >> metis_tac[]
QED

Theorem lv_coherent_slot:
  lv_coherent bbs st /\ lv_processed st l /\
  i <= LENGTH (liveness_instrs bbs l) ==>
  df_at [] st l i = THE (FLOOKUP (SND (df_fold_block Backward
    (liveness_transfer bbs) l (liveness_instrs bbs l)
    (df_at [] st l (LENGTH (liveness_instrs bbs l))))) (l,i))
Proof
  simp_tac pure_ss [lv_coherent_def] >> metis_tac[]
QED

Theorem lv_coherent_boundary:
  lv_coherent bbs st ==> df_boundary [] st l = df_at [] st l 0
Proof
  simp_tac pure_ss [lv_coherent_def] >> metis_tac[]
QED

Theorem lv_coherent_block:
  lv_coherent bbs st ==> lv_coherent bbs (liveness_block bbs cfg lbl st)
Proof
  strip_tac >> simp[lv_coherent_def] >> rpt conj_tac
  >- (rpt gen_tac >> simp[lv_block_domain, lv_processed_block] >>
      metis_tac[lv_coherent_domain])
  >- (rpt strip_tac >> Cases_on `l = lbl` >> gvs[]
      >- simp[liveness_block_exit, liveness_block_read]
      >> gvs[lv_processed_block, liveness_block_other_inst] >>
      metis_tac[lv_coherent_slot])
  >> gen_tac >> Cases_on `l = lbl` >> gvs[]
  >- simp[liveness_block_boundary_entry]
  >> simp[liveness_block_other_boundary, liveness_block_other_inst] >>
  metis_tac[lv_coherent_boundary]
QED

Theorem lv_unprocessed_read:
  lv_coherent bbs st /\ ~lv_processed st l ==> df_at [] st l i = []
Proof
  rpt strip_tac >>
  `~((l,i) IN FDOM st.ds_inst)` by metis_tac[lv_coherent_domain] >>
  simp[df_at_def, FLOOKUP_DEF]
QED

Theorem lv_beyond_absent:
  lv_coherent bbs st /\ LENGTH (liveness_instrs bbs l) < i ==>
  FLOOKUP st.ds_inst (l,i) = NONE
Proof
  rpt strip_tac >>
  `~((l,i) IN FDOM st.ds_inst)` by
    (drule lv_coherent_domain >> disch_then (qspecl_then [`l`,`i`] mp_tac) >>
     simp[] >> decide_tac) >>
  simp[FLOOKUP_DEF]
QED

Theorem lv_processed_slot_exists:
  lv_coherent bbs st /\ lv_processed st l /\
  i <= LENGTH (liveness_instrs bbs l) ==>
  ?v. FLOOKUP st.ds_inst (l,i) = SOME v
Proof
  rpt strip_tac >>
  `(l,i) IN FDOM st.ds_inst` by metis_tac[lv_coherent_domain] >>
  Cases_on `FLOOKUP st.ds_inst (l,i)` >> gvs[FLOOKUP_DEF]
QED

Theorem lv_coherent_transfer:
  lv_coherent bbs st /\ lv_processed st l /\
  i < LENGTH (liveness_instrs bbs l) ==>
  df_at [] st l i = liveness_transfer bbs (EL i (liveness_instrs bbs l))
                      (df_at [] st l (SUC i))
Proof
  strip_tac >>
  `i <= LENGTH (liveness_instrs bbs l) /\
   SUC i <= LENGTH (liveness_instrs bbs l)` by decide_tac >>
  Cases_on `df_fold_block Backward (liveness_transfer bbs) l
    (liveness_instrs bbs l) (df_at [] st l (LENGTH (liveness_instrs bbs l)))` >>
  rename1 `df_fold_block _ _ _ _ _ = (entry,im)` >>
  `df_at [] st l i = THE (FLOOKUP im (l,i))` by
    metis_tac[lv_coherent_slot, SND] >>
  `df_at [] st l (SUC i) = THE (FLOOKUP im (l,SUC i))` by
    metis_tac[lv_coherent_slot, SND] >>
  drule backward_fold_transfer >>
  disch_then (qspec_then `i` mp_tac) >> simp[]
QED

Definition lv_subsolution_def:
  lv_subsolution bbs cfg st <=>
    !l. set (df_at [] st l (LENGTH (liveness_instrs bbs l))) SUBSET
        set (liveness_out bbs cfg l st)
End

Definition lv_bounded_def:
  lv_bounded bbs (st : string list df_state) <=>
    (!k vs v. FLOOKUP st.ds_inst k = SOME vs /\ MEM v vs ==>
              MEM v (fn_all_vars bbs)) /\
    (!l vs v. FLOOKUP st.ds_boundary l = SOME vs /\ MEM v vs ==>
              MEM v (fn_all_vars bbs))
End

Definition lv_inv_def:
  lv_inv bbs cfg st <=>
    lv_coherent bbs st /\ lv_subsolution bbs cfg st /\ lv_bounded bbs st
End

Theorem lv_read_inflation:
  lv_coherent bbs st /\ lv_subsolution bbs cfg st ==>
  set (df_at [] st l i) SUBSET set (df_at [] (liveness_block bbs cfg lbl st) l i)
Proof
  strip_tac >> Cases_on `l = lbl`
  >- (gvs[] >> Cases_on `lv_processed st l`
      >- (Cases_on `i <= LENGTH (liveness_instrs bbs l)`
          >- (drule_all lv_coherent_slot >> disch_then SUBST1_TAC >>
              simp[liveness_block_read] >> irule liveness_fold_slot_mono >>
              gvs[lv_subsolution_def])
          >> simp[liveness_block_beyond])
      >> `df_at [] st l i = []` by metis_tac[lv_unprocessed_read] >> simp[])
  >> simp[liveness_block_other_inst]
QED

Theorem lv_boundary_inflation:
  lv_coherent bbs st /\ lv_subsolution bbs cfg st ==>
  set (df_boundary [] st l) SUBSET
  set (df_boundary [] (liveness_block bbs cfg lbl st) l)
Proof
  strip_tac >>
  `lv_coherent bbs (liveness_block bbs cfg lbl st)` by metis_tac[lv_coherent_block] >>
  metis_tac[lv_coherent_boundary, lv_read_inflation]
QED

Theorem lv_out_inflation:
  lv_coherent bbs st /\ lv_subsolution bbs cfg st ==>
  set (liveness_out bbs cfg l st) SUBSET
  set (liveness_out bbs cfg l (liveness_block bbs cfg lbl st))
Proof
  strip_tac >> irule liveness_out_mono >> metis_tac[lv_read_inflation]
QED

Theorem lv_subsolution_block:
  lv_coherent bbs st /\ lv_subsolution bbs cfg st ==>
  lv_subsolution bbs cfg (liveness_block bbs cfg lbl st)
Proof
  strip_tac >> simp[lv_subsolution_def] >> gen_tac >> Cases_on `l = lbl`
  >- (gvs[] >> simp[liveness_block_exit] >> metis_tac[lv_out_inflation])
  >> simp[liveness_block_other_inst] >>
  irule SUBSET_TRANS >> qexists_tac `set (liveness_out bbs cfg l st)` >>
  conj_tac >- gvs[lv_subsolution_def] >> metis_tac[lv_out_inflation]
QED
Theorem lv_bounded_read:
  lv_bounded bbs st /\ MEM v (df_at [] st l i) ==> MEM v (fn_all_vars bbs)
Proof
  simp[lv_bounded_def, df_at_def] >>
  Cases_on `FLOOKUP st.ds_inst (l,i)` >> simp[] >> metis_tac[]
QED

Theorem lv_bounded_boundary:
  lv_bounded bbs st /\ MEM v (df_boundary [] st l) ==> MEM v (fn_all_vars bbs)
Proof
  simp[lv_bounded_def, df_boundary_def] >>
  Cases_on `FLOOKUP st.ds_boundary l` >> simp[] >> metis_tac[]
QED

Theorem lv_instrs_uses_bounded:
  MEM inst (liveness_instrs bbs l) /\ MEM v (inst_uses inst) ==>
  MEM v (fn_all_vars bbs)
Proof
  simp[liveness_instrs_def] >> Cases_on `lookup_block l bbs` >> simp[] >>
  metis_tac[lookup_block_mem, fn_all_vars_mem]
QED

Theorem lv_bounded_block:
  lv_bounded bbs st ==> lv_bounded bbs (liveness_block bbs cfg lbl st)
Proof
  strip_tac >>
  `!v. MEM v (liveness_out bbs cfg lbl st) ==> MEM v (fn_all_vars bbs)` by
    (rpt strip_tac >> irule liveness_out_bounded >> metis_tac[lv_bounded_read]) >>
  `!inst v. MEM inst (liveness_instrs bbs lbl) /\ MEM v (inst_uses inst) ==>
     MEM v (fn_all_vars bbs)` by metis_tac[lv_instrs_uses_bounded] >>
  `!v. MEM v (FST (df_fold_block Backward (liveness_transfer bbs) lbl
      (liveness_instrs bbs lbl) (liveness_out bbs cfg lbl st))) ==>
      MEM v (fn_all_vars bbs)` by
    (match_mp_tac liveness_fold_entry_bounded >> metis_tac[]) >>
  `!k vs v. FLOOKUP (SND (df_fold_block Backward (liveness_transfer bbs) lbl
      (liveness_instrs bbs lbl) (liveness_out bbs cfg lbl st))) k = SOME vs /\
      MEM v vs ==> MEM v (fn_all_vars bbs)` by
    (match_mp_tac liveness_fold_map_bounded >> metis_tac[]) >>
  simp[liveness_block_eq] >> pairarg_tac >> simp[] >>
  rename1 `df_fold_block _ _ _ _ _ = (entry,im)` >>
  gvs[lv_bounded_def] >> simp[FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `FLOOKUP im k` >> simp[] >> metis_tac[])
  >> rpt gen_tac >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem lv_subsolution_init:
  lv_subsolution bbs cfg (init_df_state [] labels)
Proof
  simp[lv_subsolution_def, init_df_state_def, df_at_def]
QED

Theorem lv_bounded_init:
  lv_bounded bbs (init_df_state [] labels)
Proof
  simp[lv_bounded_def, init_df_state_def] >> rpt strip_tac >>
  drule foldl_init_flookup >> simp[] >> strip_tac >> gvs[]
QED

Theorem lv_inv_init:
  lv_inv bbs cfg (init_df_state [] labels)
Proof
  simp[lv_inv_def, lv_coherent_init, lv_subsolution_init, lv_bounded_init]
QED

Theorem lv_inv_block:
  lv_inv bbs cfg st ==> lv_inv bbs cfg (liveness_block bbs cfg lbl st)
Proof
  simp[lv_inv_def] >> metis_tac[lv_coherent_block, lv_subsolution_block, lv_bounded_block]
QED

Theorem lv_inv_read_inflation:
  lv_inv bbs cfg st ==>
  set (df_at [] st l i) SUBSET set (df_at [] (liveness_block bbs cfg lbl st) l i)
Proof
  simp[lv_inv_def] >> metis_tac[lv_read_inflation]
QED

Theorem lv_inv_boundary_inflation:
  lv_inv bbs cfg st ==>
  set (df_boundary [] st l) SUBSET
  set (df_boundary [] (liveness_block bbs cfg lbl st) l)
Proof
  simp[lv_inv_def] >> metis_tac[lv_boundary_inflation]
QED


val _ = List.app (fn (_,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail "oracle in liveness coherence API")
  (DB.thms "livenessInvariantProofs");
