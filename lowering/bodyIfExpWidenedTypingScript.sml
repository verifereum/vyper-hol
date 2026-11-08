(* Physical aggregate inputs to conditional layout normalization. *)
Theory bodyIfExpWidenedTyping
Ancestors
  exprSimIfExpCompat exprSimIfExp exprSimHyps exprSimHypsDefs
  valueEncodingTyping vyperTypeInvariants loweringPosts exprSimSource

Theorem ifexp_aggregate_source_typing:
  expr_body_pre ce cx env e es /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) ==>
  post_value_type ce e = lowered_value_type ce e /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e) /\
  ?stv dtv.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v
Proof
  strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
   env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        env_consistent_def, env_context_consistent_def] >>
  drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `ce` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[]
  >- (drule_all ifexp_body_pre_read_typed >> strip_tac >>
      `post_value_type ce e = expr_type e` by
        metis_tac[post_value_type_lowered] >>
      `type_widens_to (get_tenv cx) (expr_type e) (expr_type e)` by
        metis_tac[post_value_type_widens, expr_body_pre_def] >>
      simp[] >> metis_tac[cj 1 value_has_type_val_wf]) >>
  gvs[vyperASTTheory.expr_type_def] >>
  drule_all ifexp_intcall_copy_source >> strip_tac >>
  drule_all ifexp_intcall_read_physical_typed >> strip_tac >>
  drule_all ifexp_body_pre_read_typed >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def] >>
  metis_tac[cj 1 value_has_type_val_wf]
QED
