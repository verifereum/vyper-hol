Theory livenessBlockProofs
Ancestors
  livenessDefs dfAnalyzeProofs
Libs
  listTheory pred_setTheory finite_mapTheory pairTheory arithmeticTheory
  dfAnalyzeDefsTheory

Definition liveness_instrs_def:
  liveness_instrs bbs lbl =
    case lookup_block lbl bbs of NONE => [] | SOME bb => bb.bb_instructions
End

Definition liveness_out_def:
  liveness_out bbs cfg lbl st =
    FOLDL list_union []
      (MAP (\s. liveness_edge_transfer bbs s lbl (df_at [] st s 0))
           (cfg_succs_of cfg lbl))
End

Theorem liveness_block_eq:
  liveness_block bbs cfg lbl st =
    let (entry, im) = df_fold_block Backward (liveness_transfer bbs) lbl
                       (liveness_instrs bbs lbl) (liveness_out bbs cfg lbl st) in
    st with <| ds_inst := FUNION im st.ds_inst;
               ds_boundary := st.ds_boundary |+ (lbl, entry) |>
Proof
  simp[liveness_block_def, liveness_instrs_def, liveness_out_def]
QED

Theorem backward_fold_lookup:
  df_fold_block Backward transfer lbl instrs out = (entry, im) ==>
  !i. i <= LENGTH instrs ==> ?v. FLOOKUP im (lbl,i) = SOME v
Proof
  strip_tac >> drule df_fold_block_fdom_backward >> strip_tac >>
  rpt strip_tac >>
  ` (lbl,i) IN FDOM im` by (simp[] >> qexists_tac `i` >> simp[]) >>
  Cases_on `FLOOKUP im (lbl,i)` >> gvs[FLOOKUP_DEF]
QED

Theorem backward_fold_entry:
  df_fold_block Backward transfer lbl instrs out = (entry, im) ==>
  FLOOKUP im (lbl,0) = SOME entry
Proof
  strip_tac >> drule backward_fold_lookup >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  gvs[df_fold_block_def] >>
  drule df_fold_backward_at >> simp[] >> strip_tac >> gvs[]
QED

Theorem backward_fold_exit:
  df_fold_block Backward transfer lbl instrs out = (entry, im) ==>
  FLOOKUP im (lbl,LENGTH instrs) = SOME out
Proof
  simp[df_fold_block_def] >> strip_tac >>
  drule df_fold_backward_at >> simp[]
QED

Theorem backward_fold_transfer:
  df_fold_block Backward transfer lbl instrs out = (entry, im) /\
  i < LENGTH instrs ==>
  FLOOKUP im (lbl,i) =
    SOME (transfer (EL i instrs) (THE (FLOOKUP im (lbl,SUC i))))
Proof
  simp[df_fold_block_def] >> strip_tac >>
  drule df_fold_backward_at >> simp[]
QED

Theorem backward_fold_absent:
  df_fold_block Backward transfer lbl instrs out = (entry, im) /\
  (l <> lbl \/ LENGTH instrs < i) ==>
  FLOOKUP im (l,i) = NONE
Proof
  strip_tac >> drule df_fold_block_fdom_backward >> strip_tac >>
  `~((l,i) IN FDOM im)` by (simp[] >> metis_tac[]) >>
  simp[FLOOKUP_DEF]
QED

Theorem liveness_block_read:
  i <= LENGTH (liveness_instrs bbs lbl) ==>
  df_at [] (liveness_block bbs cfg lbl st) lbl i =
    THE (FLOOKUP (SND (df_fold_block Backward (liveness_transfer bbs) lbl
          (liveness_instrs bbs lbl) (liveness_out bbs cfg lbl st))) (lbl,i))
Proof
  strip_tac >> simp[liveness_block_eq] >> pairarg_tac >> simp[] >>
  drule backward_fold_lookup >> disch_then (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >> simp[df_at_def, df_flookup_funion]
QED

Theorem liveness_block_boundary_entry:
  df_boundary [] (liveness_block bbs cfg lbl st) lbl =
  df_at [] (liveness_block bbs cfg lbl st) lbl 0
Proof
  simp[liveness_block_eq] >> pairarg_tac >> simp[] >>
  drule backward_fold_entry >> strip_tac >>
  simp[df_boundary_def, df_at_def, FLOOKUP_UPDATE, df_flookup_funion]
QED

Theorem liveness_block_exit:
  df_at [] (liveness_block bbs cfg lbl st) lbl
    (LENGTH (liveness_instrs bbs lbl)) = liveness_out bbs cfg lbl st
Proof
  simp[liveness_block_eq] >> pairarg_tac >> simp[] >>
  drule backward_fold_exit >> strip_tac >>
  simp[df_at_def, df_flookup_funion]
QED
Theorem liveness_block_transfer:
  i < LENGTH (liveness_instrs bbs lbl) ==>
  df_at [] (liveness_block bbs cfg lbl st) lbl i =
    liveness_transfer bbs (EL i (liveness_instrs bbs lbl))
      (df_at [] (liveness_block bbs cfg lbl st) lbl (SUC i))
Proof
  strip_tac >> simp[liveness_block_read] >>
  Cases_on `df_fold_block Backward (liveness_transfer bbs) lbl
    (liveness_instrs bbs lbl) (liveness_out bbs cfg lbl st)` >> simp[] >>
  drule backward_fold_transfer >>
  disch_then (qspec_then `i` mp_tac) >> simp[]
QED

Theorem liveness_block_other_inst:
  l <> lbl ==>
  df_at [] (liveness_block bbs cfg lbl st) l i = df_at [] st l i
Proof
  strip_tac >> simp[liveness_block_eq] >> pairarg_tac >> simp[] >>
  drule backward_fold_absent >>
  disch_then (qspecl_then [`l`, `i`] mp_tac) >> simp[] >> strip_tac >>
  simp[df_at_def, df_flookup_funion]
QED

Theorem liveness_block_other_boundary:
  l <> lbl ==>
  df_boundary [] (liveness_block bbs cfg lbl st) l = df_boundary [] st l
Proof
  strip_tac >> simp[liveness_block_eq] >> pairarg_tac >>
  simp[df_boundary_def, FLOOKUP_UPDATE]
QED

Theorem liveness_block_beyond:
  LENGTH (liveness_instrs bbs lbl) < i ==>
  df_at [] (liveness_block bbs cfg lbl st) lbl i = df_at [] st lbl i
Proof
  strip_tac >> simp[liveness_block_eq] >> pairarg_tac >> simp[] >>
  drule backward_fold_absent >>
  disch_then (qspecl_then [`lbl`, `i`] mp_tac) >> simp[] >> strip_tac >>
  simp[df_at_def, df_flookup_funion]
QED
