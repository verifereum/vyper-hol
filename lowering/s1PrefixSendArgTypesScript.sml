Theory s1PrefixSendArgTypes
Ancestors
  exprSimSend exprSimPrecompiles exprBodyPreProps exprSimHypsDefs
  vyperInterpreter list

Theorem send_eval_args_typed:
  expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
  eval_exprs cx args (es with gas_obs := gs) = (INL vs,mid) ==>
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                      value_has_type tv v) args vs
Proof
  strip_tac >>
  drule expr_body_pre_static_facts >> strip_tac >>
  drule send_pre_types >> strip_tac >>
  `!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
          expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)` by
    (rpt strip_tac
     >- metis_tac[expr_body_pre_send_arg] >>
     fs[EVERY_MEM]) >>
  `expr_sim_inv cenv cx env (es with gas_obs := gs)` by simp[] >>
  metis_tac[stack_args_values_typed_body]
QED
