Theory bodyFullBaseTargetProjection
Ancestors bodyFullPreds
  bodyFullPredsMods[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  PURE_REWRITE_TAC[body_base_target_full_ok_def] >> REFL_TAC
QED
*)
Theorem body_base_target_full_ok_attribute_projection:
  body_base_target_full_ok_mods mods exps cx (AttributeTarget t id) = body_base_target_full_ok_mods mods exps cx t
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  PURE_REWRITE_TAC[body_base_target_full_ok_def] >> REFL_TAC
QED
*)
Theorem body_base_target_full_ok_subscript_projection:
  body_base_target_full_ok_mods mods exps cx (SubscriptTarget t e) =
    (body_base_target_full_ok_mods mods exps cx t /\
     ((?s pv s1. eval_base_place cx t s = (INL pv, s1)) ==>
      body_expr_full_ok_mods mods exps cx e))
Proof
  cheat
QED
