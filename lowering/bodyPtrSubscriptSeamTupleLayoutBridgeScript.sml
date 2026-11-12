(* Nonbytestring aggregates have the same physical type in the two interfaces. *)
Theory bodyPtrSubscriptSeamTupleLayoutBridge
Ancestors
  exprSimIfExpCompat exprSimHyps exprSimHypsDefs exprLowering loweringPosts
  vyperTyping vyperTypeInvariants exprSimDefs exprSimSource vyperAST

Theorem aggregate_lowered_post_type:
  !ce cx env e es.
    expr_body_pre ce cx env e es /\ ~is_word_type (expr_type e) /\
    ~is_bytestring_type (expr_type e) ==>
    lowered_value_type ce e = post_value_type ce e
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        env_consistent_def, env_context_consistent_def] >>
  drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `ce` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[]
  >- simp[post_value_type_lowered] >>
  gvs[post_value_type_def, expr_type_def]
QED
