(* A constructor-immutable subscript binds the selected base place and
   the selected index before entering its immutable array suffix. *)
Theory entryCreateTargetImmSubscriptBind
Ancestors
  bodyFullTargetSubscript bodyFullTargetDefs bodyFullPreds bodyFullShared
  bodyFullIfExpReach targetSubscriptSplit tuplePlaceSourceHead
  entryCreateFocusSpec entryCreateScopedBind entryCreateNativeFirstExit
  entryCreateRegionLift entryCreatePendingScope createSizeOperandCode
  exprSimDefs exprSimFullBundleProps exprSimHypsDefs bodySimAugPlaceLoad targetPlaceSim
  gasSummary gasOutcomeFull
  vyperInterpreter vyperState vyperStorageFootprint loweringPosts

Theorem immutable_target_index_ready[local]:
  body_base_target_full_ok cx (SubscriptTarget bt e) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  target_indices_pre cenv cx env (SubscriptTarget bt e) /\
  IS_SOME (type_place_target env bt) /\
  eval_target_place cx bt (es with gas_obs := gs) =
    (INL (ImmutablePlace NONE id path),mid) ==>
  eval_base_place cx bt (es with gas_obs := gs) =
    (INL (PlaceR (ImmutablePlace NONE id path)),mid) /\
  body_const_cells_agree [(NONE,tops)] cx env mid /\
  expr_sim_inv cenv cx env mid /\
  expr_body_pre cenv cx env e mid /\
  body_expr_full_ok cx e
Proof
  strip_tac >> conj_asm1_tac
  >- (irule tuple_place_target_base_inversion >> simp[]) >>
  conj_tac
  >- (irule body_const_cells_agree_base >>
      qpat_assum `eval_base_place _ _ _ = _` (irule_at Any) >> simp[]) >>
  conj_asm1_tac
  >- (irule aug_place_target_inv >>
      qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >>
      fs[target_indices_pre_def]) >>
  conj_tac >- fs[target_indices_pre_def] >>
  fs[body_base_target_full_ok_def] >> first_x_assum irule >> metis_tac[]
QED
