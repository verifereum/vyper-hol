(* Source and memory outcome of an empty deploy-time immutable assignment. *)
Theory immutableAssignEmptyOutcome
Ancestors
  immutableAssignEmpty immutableAssignState immutableAssignAdmissibility
  bodyMemoryPreds bodyAssignPlace memoryLocalRhsProps exprSimHypsDefs
  stmtSimDefs stmtLowering compileEnv loweringPosts
  vyperTypeInvariants vyperInterpreter vyperState
Libs monadsyntax

Theorem immutable_assign_empty_source[local]:
  env_consistent env cx es /\
  FLOOKUP env.bare_globals (src,id) = SOME ity /\
  well_typed_expr env e /\ is_empty_value_expr e /\
  has_length_word (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) ity /\
  evaluate_type (get_tenv cx) ity = SOME tv /\
  imms = (case ALOOKUP es.immutables cx.txn.target of NONE => [] | SOME m => m)
  ==>
  eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) es =
    (INL (),es with immutables :=
      (cx.txn.target,set_source_immutables src
        (get_source_immutables src imms |+ (id,(tv,default_value tv))) imms) ::
      ADELKEY cx.txn.target es.immutables)
Proof
  strip_tac >>
  `env_context_consistent env cx /\ env_immutables_consistent env cx es` by
    fs[env_consistent_def] >>
  `env.type_defs = get_tenv cx` by fs[env_context_consistent_def] >>
  drule_all env_context_consistent_bare_global_find_NONE >> strip_tac >>
  `?old. FLOOKUP (get_source_immutables src imms) id = SOME (tv,old)` by
    (fs[env_immutables_consistent_def] >>
     gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[optionTheory.SOME_11,pairTheory.PAIR]) >>
  `(do r <- eval_expr cx e; read_result cx r od) es = (INL (default_value tv),es)` by
    (irule memory_rhs_empty_read_destination >> simp[] >> metis_tac[]) >>
  Cases_on `eval_expr cx e es` >>
  gvs[bind_def, AllCaseEqs(), read_result_def, return_def] >>
  once_rewrite_tac[evaluate_def] >>
  simp[bind_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >>
  simp[bind_def, Ntimes evaluate_def 3, get_place_def,
       lookup_global_def, get_immutables_def, get_address_immutables_def,
       lift_option_type_def, return_def, write_place_def, assign_subscripts_def,
       lift_sum_def, set_immutable_def, set_address_immutables_def,
       get_source_immutables_def, evaluation_state_component_equality]
QED

Theorem immutable_assign_empty_stmt_mem:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  type_widens_to env.type_defs (expr_type e) ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\ ce.ce_is_ctor /\
  has_length_word (expr_type e) /\ is_empty_value_expr e ==>
  stmt_frag_mem d ctx func cx lc RetQ ce
    (stmt_env ce lc ty (Assign (BaseTarget (TopLevelNameTarget (ce.ce_module,id))) e))
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (ce.ce_module,id))) e)) es
Proof
  strip_tac >>
  `env_consistent env cx es /\ well_typed_expr env e` by
    fs[expr_body_pre_def,expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def,env_context_consistent_def] >>
  `?tv old imms.
     imms = (case ALOOKUP es.immutables cx.txn.target of NONE => [] | SOME m => m) /\
     FLOOKUP (get_source_immutables ce.ce_module imms) id = SOME (tv,old) /\
     evaluate_type (get_tenv cx) ity = SOME tv` by
    (fs[env_consistent_def,env_immutables_consistent_def] >>
     gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[pairTheory.PAIR]) >>
  `has_length_word ity` by metis_tac[type_widens_to_has_length_word] >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `compile_imm_store_word ce.ce_imm_alloca (Lit (n2w off)) (Lit 0w) sa = ((),sb) /\
   cenv' = ce` by
    (drule_all immutable_assign_empty_code >>
     disch_then (qspecl_then [`ty`,`sa`,`lc`] assume_tac) >>
     Cases_on `compile_imm_store_word ce.ce_imm_alloca (Lit (n2w off)) (Lit 0w) sa` >>
     gvs[stmt_env_def,declare_stmt_local_def,comp_bind_def,
         comp_ignore_bind_def,comp_return_def]) >>
  suspend "endpoint"
QED

Resume immutable_assign_empty_stmt_mem[endpoint]:
  FAIL_TAC "endpoint"
QED

Finalise immutable_assign_empty_stmt_mem
