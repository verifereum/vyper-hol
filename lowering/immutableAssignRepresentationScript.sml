(* Positive physical footprints for immutable assignment. *)
Theory immutableAssignRepresentation
Ancestors
  immutableDeployPhysicalSource placeMemoryTypeInterfaces valueEncodingProps
  vyperTypeSystem exprSimHyps exprSimHypsDefs vyperTypeInvariants

Theorem immutable_assign_widened_memory_positive:
  assignable_type tenv sty /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv ==>
  0 < type_memory_size stv /\ 0 < type_memory_size dtv
Proof
  strip_tac >>
  drule_all assignable_type_slot_size_pos >> strip_tac >>
  `0 < type_memory_size stv` by simp[type_memory_size_slots] >>
  drule_all type_widens_to_zero_memory_size >> decide_tac
QED

Theorem immutable_assign_rhs_memory_positive:
  expr_body_pre ce cx env e es /\
  assignable_type env.type_defs (expr_type e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv ==>
  0 < type_memory_size stv
Proof
  strip_tac >>
  `?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv` by
    metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
    (irule immutable_rhs_physical_widens >> qexistsl_tac [`env`,`es`] >>
     simp[vyperTypeSystemTheory.type_widens_to_def]) >>
  gvs[] >>
  drule_all assignable_type_slot_size_pos >> strip_tac >>
  `0 < type_memory_size etv` by simp[type_memory_size_slots] >>
  drule_all type_widens_to_zero_memory_size >> decide_tac
QED
