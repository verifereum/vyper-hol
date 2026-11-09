(* Source readiness at a counted memory-target endpoint. *)
Theory augAssignPlaceTargetReadiness
Ancestors
  augAssignPlaceMemoryTarget augAssignPlaceSourceMemory
  stmtSimAugAssignPlaceMemory loweringPosts exprSimHypsDefs

Theorem aug_place_memory_target_ready:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  expr_body_pre cenv cx env e es /\ target_indices_pre cenv cx env bt /\
  eval_target_place cx bt (es with gas_obs := gs) =
    (INL (MemoryPlace id path),mid) /\
  target_post ctx func cenv cx es sa sp s0 mid
    (PlaceR (MemoryPlace id path)) (Type ty) r t ==>
  expr_body_pre cenv cx env e mid /\
  ?cur tv. read_place cx (MemoryPlace id path) mid = (INL cur,mid) /\
    place_type_value cx (MemoryPlace id path) mid = (INL tv,mid) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e mid` by
    (irule aug_place_rhs_pre_target_gas_obs >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`gs`, `INL (MemoryPlace id path)`, `bt`] >> simp[]) >>
  simp[] >>
  `expr_sim_inv cenv cx env es /\ expr_sim_inv cenv cx env mid` by
    fs[expr_body_pre_def] >>
  `target_post ctx func cenv cx (es with gas_obs := gs) sa sp s0 mid
     (PlaceR (MemoryPlace id path)) (Type ty) r t` by
    (qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[target_post_def, locals_kept_def] >> metis_tac[]) >>
  qpat_assum `target_post _ _ _ _ (_ with gas_obs := _) _ _ _ _ _ _ _ _`
    (mp_then (Pat `target_post`) mp_tac aug_place_memory_source_ready) >>
  disch_then (drule_at (Pat `supported_stmt`)) >>
  disch_then (drule_at (Pat `type_stmt`)) >> simp[]
QED
