(* Memory representation at the physical external-call argument layout. *)
Theory extcallLoweredRepresentation
Ancestors
  externalReturnSelectedSuffix exprSimIfExpCompat logArgumentTypeEval
  exprSimHypsDefs vyperTypeInvariants valueCopyBytes loweringPosts

Theorem extcall_nonword_lowered_memory:
  expr_body_pre ce cx env e es /\
  ~is_word_type (post_value_type ce e) /\
  ~is_word_type (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
  value_has_type ltv v /\ val_in_memory ptv v p mem ==>
  val_in_memory ltv v p mem
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es /\ well_typed_expr env e` by
    gvs[expr_body_pre_def] >>
  Cases_on `?a f args d. e = Call a (IntCall f) args d`
  >- (gvs[] >> drule_all return_intcall_post_lowered >>
      strip_tac >> gvs[] >>
      metis_tac[bytestring_val_in_memory_transfer]) >>
  `post_value_type ce e = expr_type e` by
    (irule post_value_type_not_int_call >> metis_tac[]) >>
  `env_consistent env cx es` by gvs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
      well_formed_type env.type_defs t` by
    metis_tac[consistent_variable_type_well_formed] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    gvs[expr_sim_inv_def] >>
  drule_all ifexp_lowered_type_classify >> strip_tac >> gvs[] >>
  metis_tac[bytestring_val_in_memory_transfer]
QED
