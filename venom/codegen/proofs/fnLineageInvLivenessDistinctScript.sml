Theory fnLineageInvLivenessDistinct
Ancestors livenessDefs dfAnalyzeDefs finite_map list

Theorem liveness_backward_distinct:
 !insts bbs lbl idx acc im entry im'.
 ALL_DISTINCT acc /\
 (!key vs. FLOOKUP im key = SOME vs ==> ALL_DISTINCT vs) /\
 df_fold_backward (liveness_transfer bbs) lbl insts idx acc im = (entry, im') ==>
 ALL_DISTINCT entry /\
 (!key vs. FLOOKUP im' key = SOME vs ==> ALL_DISTINCT vs)
Proof
 Induct_on `insts`
 >- (simp[df_fold_backward_def] >> rpt strip_tac >>
     gvs[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]) >>
 rpt gen_tac >> strip_tac >>
 gvs[df_fold_backward_def] >> pairarg_tac >> gvs[] >>
 first_x_assum drule_all >> strip_tac >>
 `ALL_DISTINCT (liveness_transfer bbs h acc')` by
   simp[liveness_transfer_def, live_update_ALL_DISTINCT] >>
 simp[] >> rpt strip_tac >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]
QED

Theorem liveness_backward_block_distinct:
 !bbs lbl insts acc entry im.
 ALL_DISTINCT acc /\
 df_fold_block Backward (liveness_transfer bbs) lbl insts acc = (entry, im) ==>
 ALL_DISTINCT entry /\
 (!key vs. FLOOKUP im key = SOME vs ==> ALL_DISTINCT vs)
Proof
 rewrite_tac[df_fold_block_def, direction_case_def] >> rpt gen_tac >> strip_tac >>
 drule_at (Pat `df_fold_backward _ _ _ _ _ _ = _`) liveness_backward_distinct >>
 simp[] >> strip_tac >> simp[]
QED
