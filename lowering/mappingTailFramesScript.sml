Theory mappingTailFrames
Ancestors
  exprSimWordArgs exprSimProps loweringPosts freshWrites

Theorem expr_post_suffix_frames:
  expr_post ctx func cenv cx idx em sm sn s1 en kv key t /\
  wb_frame cenv en en sn t u /\ pure_frame cenv func en sn t u /\
  stmt_state_rel ctx func cenv cx em s1 /\ local_ptrs_reserved cenv sm /\
  MAP FDOM em.scopes = MAP FDOM en.scopes /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id ==>
  wb_frame cenv em en sm s1 u /\
  (~expr_has_effect idx ==> pure_frame cenv func em sm s1 u)
Proof
  strip_tac >>
  `wb_frame cenv em en sm s1 t` by
    (drule expr_post_frame >> simp[]) >>
  conj_tac
  >- (irule wb_frame_trans >> simp[] >>
      reverse conj_tac >- (qexistsl_tac [`en`, `sn`, `t`] >> simp[]) >>
      goal_assum (drule_at Any)) >>
  strip_tac >>
  `pure_frame cenv func em sm s1 t` by
    (drule_all expr_post_pure_frame >> simp[]) >>
  `!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b` by
    (qpat_assum `wb_frame cenv en _ sn t u` mp_tac >>
     pure_rewrite_tac[wb_frame_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!x w. not_fresh_at sm x /\ lookup_var x s1 = SOME w ==>
         lookup_var x t = SOME w` by
    (qpat_assum `wb_frame cenv em _ sm s1 t` mp_tac >>
     pure_rewrite_tac[wb_frame_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  match_mp_tac pure_frame_trans >> qexistsl_tac [`en`, `sn`, `t`] >> simp[]
QED
