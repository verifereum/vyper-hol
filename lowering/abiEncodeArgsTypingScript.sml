Theory abiEncodeArgsTyping
Ancestors
  abiEncodeArgsCase exprSimAggregateSource vyperTypeABI exprSimHyps exprSimHypsDefs exprSimSource exprSimDefs exprSimProps loweringPosts

Theorem abi_encode_arg_success_typed:
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  expr_sim_inv ce cx env es' /\
  ?tv av. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    value_has_type tv v /\ vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av
Proof
  strip_tac >> drule_all expr_body_pre_eval >> strip_tac >> simp[] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[vyperTypeExprResultTheory.expr_result_typed_def,
      vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
      vyperTypeInvariantsTheory.value_result_typed_def] >>
  drule_all (cj 1 vyper_to_abi_total) >> metis_tac[]
QED

Theorem abi_encode_args_success_typed:
  !args es vs es'.
  EVERY (\e. !st. expr_sim_inv ce cx env st ==> expr_body_pre ce cx env e st) args /\
  expr_sim_inv ce cx env es /\ eval_exprs cx args es = (INL vs,es') ==>
  expr_sim_inv ce cx env es' /\
  ?avs. LIST_REL (\(e,v) av. ?tv.
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    value_has_type tv v /\ vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av)
    (ZIP (args,vs)) avs
Proof
  Induct
  >- (simp[Once vyperInterpreterTheory.evaluate_def,
           vyperStateTheory.return_def] >> rpt strip_tac >> gvs[] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule aggregate_eval_exprs_cons >> strip_tac >> gvs[] >>
  Cases_on `rr` >> gvs[] >>
  `expr_body_pre ce cx env h es` by metis_tac[] >>
  ` (do r <- eval_expr cx h; read_result cx r od) es = (INL v,es1)` by
    simp[vyperStateTheory.bind_def] >>
  drule_all abi_encode_arg_success_typed >> strip_tac >>
  qpat_x_assum `!es vs es'. _` drule_all >> strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem abi_encode_case_args_success_typed:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  eval_exprs cx args es = (INL vs,es') ==>
  expr_sim_inv ce cx env es' /\
  ?avs. LIST_REL (\(e,v) av. ?tv.
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    value_has_type tv v /\ vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av)
    (ZIP (args,vs)) avs
Proof
  strip_tac >> irule abi_encode_args_success_typed >>
  conj_tac
  >- (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
      irule abi_args_body_pre_arg >> metis_tac[]) >>
  qexists_tac `es` >> gvs[expr_body_pre_def]
QED
