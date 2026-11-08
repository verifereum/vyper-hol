(* Seam 2 joint induction, a family leaf of the agg step: array literals. *)
Theory bodyIntCallFamAggArray
Ancestors
  bodyIntCallJointContract bodyIntCallJointAggCore exprSimAggregateLayout
  exprSimSource exprSimHyps exprSimHypsDefs exprSimAggregateChildren
  vyperTypeInvariants

(* Public child typing bridge: no equality between the produced layout and
   the annotation is assumed, including for widened internal-call results. *)
Theorem intcall_array_child_layout:
  expr_body_pre ce cx env (Builtin ann (MakeArray (SOME et) bnd) args) es /\
  MEM e args /\ expr_sim_inv ce cx env ee ==>
  expr_type e = et /\
  type_widens_to (get_tenv cx) (post_value_type ce e) et /\
  ?tv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv
Proof
  strip_tac >>
  `expr_body_pre ce cx env e ee` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> simp[]) >>
  drule make_array_evaluated_layout >> strip_tac >>
  `expr_type e = et` by fs[listTheory.EVERY_MEM] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  simp[] >> conj_tac
  >- (drule post_value_type_widens >>
      fs[expr_body_pre_def] >> metis_tac[]) >>
  metis_tac[post_type_evaluates]
QED

Theorem intcall_array_literal_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a t n args. e = Builtin a (MakeArray (SOME t) n) args) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
