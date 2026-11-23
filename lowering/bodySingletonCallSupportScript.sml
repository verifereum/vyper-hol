(* A well-typed singleton expression cannot name a qualified callee. *)
Theory bodySingletonCallSupport
Ancestors
  bodySim bodyInvCodeProps bodyTypedTargetScope bodyCallSupport
  exprSimHypsDefs whitelistCheckerDecls vyperTypeInvariants finite_map pair
  bodyStorageCases vyperTypeCallGraph supportedExprs supportedExprTraverse list

Theorem body_inv_typed_calls_main:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  well_typed_expr env e ==>
  EVERY (\c. FST c = NONE) (int_calls_expr e)
Proof
  strip_tac >>
  irule well_typed_expr_int_calls_main >>
  map_every qexists_tac [`cx`, `env`] >>
  fs[body_inv_def, expr_sim_inv_def, env_consistent_def,
     env_context_consistent_def]
QED

Theorem supported_singleton_expr_body_calls:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  well_typed_expr env e /\ supported_expr tops e ==>
  ~expr_has_evm_run e /\
  EVERY (\c. FST c = NONE) (int_calls_expr e) /\
  EVERY (\c. IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e)
Proof
  strip_tac >> drule_all_then assume_tac body_inv_typed_calls_main >>
  drule_then assume_tac supported_expr_main_calls >>
  drule_then assume_tac supported_expr_no_evm_run >>
  gvs[EVERY_MEM] >> metis_tac[]
QED


Theorem body_inv_typed_target_calls_main:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  IS_SOME (type_place_target env t) ==>
  EVERY (\c. FST c = NONE) (int_calls_target t)
Proof
  strip_tac >>
  drule_then assume_tac (cj 3 well_typed_int_calls_fn_sigs) >>
  `fn_sigs_consistent env.fn_sigs cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  rw[EVERY_MEM, FORALL_PROD] >>
  rename1 `MEM (src,name) (int_calls_target t)` >>
  Cases_on `src` >> simp[] >>
  qpat_assum `EVERY _ (int_calls_target t)`
    (drule_then assume_tac o SIMP_RULE bool_ss [EVERY_MEM]) >>
  `?sig. FLOOKUP env.fn_sigs (SOME x,name) = SOME sig` by simp[FLOOKUP_DEF] >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `fn_sigs_consistent _ _`
    (drule_then strip_assume_tac o REWRITE_RULE [fn_sigs_consistent_def]) >>
  drule_then assume_tac body_inv_qualified_module_absent >> gvs[]
QED

Theorem body_inv_expr_pre_calls:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es ==>
  EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
    (int_calls_expr e)
Proof
  strip_tac >> drule_then strip_assume_tac body_inv_main_code >>
  fs[expr_body_pre_split_def, expr_body_pre_mods_def, EVERY_MEM, FORALL_PROD,
     source_body_call_supported_def, supported_linked_callee_def] >>
  rpt strip_tac >> res_tac >> gvs[]
QED
