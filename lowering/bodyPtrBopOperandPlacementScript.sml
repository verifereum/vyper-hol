Theory bodyPtrBopOperandPlacement
Ancestors
  loweringPosts exprSimProps

Theorem bop_argument_placement_kept:
  expr_val_at cenv cx ty sa sb es v op s /\
  wb_frame cenv es es2 sb s t /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  eval_operand op t = eval_operand op s ==>
  expr_val_at cenv cx ty sa sb es' v op t
Proof
  strip_tac >>
  `!n b sz. local_region cenv es'.scopes t n b sz ==>
      local_region cenv es.scopes s n b sz` by
    (rpt strip_tac >> irule local_region_frame >>
     fs[wb_frame_def] >> metis_tac[]) >>
  `!n b sz. local_region cenv es.scopes s n b sz ==>
      local_region cenv es'.scopes t n b sz` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     fs[wb_frame_def] >> metis_tac[]) >>
  fs[expr_val_at_def, wb_frame_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      metis_tac[]) >>
  disj2_tac >> disj1_tac >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `sz` >> simp[]
QED
