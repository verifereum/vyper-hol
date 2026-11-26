Theory bodyFullBaseTargetProjection
Ancestors bodyFullPreds

Theorem body_base_target_full_ok_attribute_projection:
  body_base_target_full_ok cx (AttributeTarget t id) = body_base_target_full_ok cx t
Proof
  PURE_REWRITE_TAC[body_base_target_full_ok_def] >> REFL_TAC
QED

Theorem body_base_target_full_ok_subscript_projection:
  body_base_target_full_ok cx (SubscriptTarget t e) =
    (body_base_target_full_ok cx t /\
     ((?s pv s1. eval_base_place cx t s = (INL pv, s1)) ==>
      body_expr_full_ok cx e))
Proof
  PURE_REWRITE_TAC[body_base_target_full_ok_def] >> REFL_TAC
QED
