(* Immutable target frames across an index at its actual source endpoint. *)
Theory popNestedImmutableIndexFrame
Ancestors
  exprSimPopImmutableTarget exprSimWordArgs loweringPosts exprBopSimProps

Theorem imm_target_post_index:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\
  imm_target_post ctx func cenv cx es sa sm s0 em pv ty rb t /\
  (!w. imm_place_at cenv cx em pv w ty ==> imm_place_at cenv cx ee pv w ty) /\
  (!l. FST rb <> Label l) /\
  expr_post ctx func cenv cx e em sm sn t ee v op u ==>
  imm_target_post ctx func cenv cx es sa sn s0 ee pv ty rb u
Proof
  strip_tac >>
  `wb_frame cenv es em sa s0 t` by
    (fs[imm_target_post_def, wb_frame_def] >> metis_tac[]) >>
  `wb_frame cenv em ee sm t u` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es ee sa s0 u` by metis_tac[wb_frame_trans] >>
  `?w. eval_operand (FST rb) t = SOME w /\ imm_place_at cenv cx em pv w ty`
    by fs[imm_target_post_def] >>
  `imm_place_at cenv cx ee pv w ty` by metis_tac[] >>
  `eval_operand (FST rb) u = SOME w` by
    (irule eval_operand_frame >> (conj_tac >- simp[]) >>
     qexistsl_tac [`sm`, `t`] >> fs[expr_post_def, imm_target_post_def]) >>
  `stmt_state_rel ctx func cenv cx ee u` by fs[expr_post_def] >>
  `!x. FST rb = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> fs[imm_target_post_def]) >>
  fs[imm_target_post_def, wb_frame_def] >> metis_tac[]
QED
