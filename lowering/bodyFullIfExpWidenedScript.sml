(* A ternary with an arm the lowering lays out differently from its source
   type, at the joint judgments: the twin of bodySimIfExpWidened's and
   bodyPtrIfExpWidened's case, with the same guard. *)
Theory bodyFullIfExpWidened
Ancestors
  bodyFullPreds bodySimFull bodySim exprSimHyps loweringPosts context
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeCallGraph

val _ = Parse.hide "body";

(* Admitted, as bodySimIfExpWidened.body_ifexp_widened_call_arm: the arm's
   simulation would have to describe its value at the lowered type, which
   is the internal-call simulation's work. *)
Theorem body_ifexp_widened_call_arm_full:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e3) /\
    body_expr_full_ok cx e1 ==>
    !D lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (IfExp v5 e1 e2 e3) es /\
      (?e. (e = e2 \/ e = e3) /\
           ~((int_calls_expr e = [] \/
              same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
             post_value_type cenv e = expr_type e)) ==>
      expr_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty (IfExp v5 e1 e2 e3) es /\
      expr_vv_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty (IfExp v5 e1 e2 e3) es
Proof
  cheat
QED
