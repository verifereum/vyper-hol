Theory bodyFullExtract32JoinFrame
Ancestors
  exprSimExtract32Post wordArgsPtr bodyPtrDefs exprSimProps exprSimWordArgs
  loweringPosts loweringStateRelDefs

Theorem extract32_join_wb_frame:
  expr_post H ctx func cenv cx src es sa sm s0 mid v src_op u /\
  expr_post H ctx func cenv cx off mid sm sb u ee w off_op t /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id ==>
  wb_frame cenv es ee sa s0 t
Proof
  strip_tac >>
  `wb_frame cenv es mid sa s0 u` by metis_tac[expr_post_frame] >>
  `wb_frame cenv mid ee sm u t` by metis_tac[expr_post_frame] >>
  metis_tac[wb_frame_trans]
QED

Theorem extract32_join_pure_frame:
  expr_post H ctx func cenv cx src es sa sm s0 mid v src_op u /\
  expr_post H ctx func cenv cx off mid sm sb u ee w off_op t /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_id <= sm.cs_next_id ==>
  ~expr_has_effect (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) ==>
  pure_frame cenv func es sa s0 t
Proof
  simp[expr_has_effect_thm] >> rpt strip_tac >>
  `pure_frame cenv func es sa s0 u` by metis_tac[expr_post_pure_frame] >>
  `pure_frame cenv func mid sm u t` by metis_tac[expr_post_pure_frame] >>
  `wb_frame cenv es mid sa s0 u` by metis_tac[expr_post_frame] >>
  `wb_frame cenv mid ee sm u t` by metis_tac[expr_post_frame] >>
  irule pure_frame_trans >> simp[] >> qexistsl_tac [`mid`,`sm`,`u`] >>
  fs[wb_frame_def]
QED
