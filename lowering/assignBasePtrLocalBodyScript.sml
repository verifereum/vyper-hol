(* Supported local memory branch; the widened aggregate call stays residual. *)
Theory assignBasePtrLocalBody
Ancestors assignBasePtrLocalBodyFacts assignBasePtrLocalFragment
  assignBasePtrLocalEmptyFragment bodyPtrPreds bodyPtrDefs bodySim
  memoryLocalRhsProps exprSimAggregateLayout vyperTypeArgFits
  exprSimHyps exprSimHypsDefs exprSimDefs loweringPosts stmtSimAugAssign
  supportedStmts supportedExprs vyperTypeSystem vyperTypeEnv
  vyperTypeCallGraph vyperTypeInvariants bodyExprPreFacts
  valueCopyBytes valueEncoding valueEncodingProps compileEnv
  allocLimits exprLoweringProps finite_map words gasContext
Libs monadsyntax

Theorem body_assign_local_memory_ptr:
  !cx id e ty d PG tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_ptr_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
    (expr_type e = ty \/ lowered_value_type cenv e = ty \/
     is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `supported_program tops /\
   cenv.ce_func_return_type = build_func_return_type tops /\
   get_module_code cx NONE = SOME tops` by gvs[body_inv_def] >>
  drule_all assign_base_local_rhs_pre >> strip_tac >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by metis_tac[] >>
  `type_memory_bytes cenv ty = type_memory_size entry.type` by
    metis_tac[expr_sim_inv_memory_size] >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- (`has_length_word ty` by metis_tac[type_widens_to_has_length_word] >>
      irule compile_assign_local_empty_stmt_frag_ptr >> simp[] >>
      qexists_tac `ty` >> simp[] >> gen_tac >>
      irule (CONV_RULE (DEPTH_CONV ETA_CONV) memory_rhs_empty_read_destination) >> simp[] >>
      qexistsl_tac [`env`, `ty`] >> simp[]) >>
  SUBGOAL_THEN ``expr_type e = ty \/ is_bytestring_type ty`` assume_tac
  >- metis_tac[] >>
  SUBGOAL_THEN ``(ty = expr_type e /\ ty = lowered_value_type cenv e) \/
     is_bytestring_type ty /\ is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e)`` assume_tac
  >- metis_tac[type_widens_to_def, arg_type_fits_bytestring_source] >>
  `~is_word_type (expr_type e)` by metis_tac[is_bytestring_word_type] >>
  suspend "layout"
QED

Resume body_assign_local_memory_ptr[layout]:
  `0 < type_memory_bytes cenv ty /\ type_memory_bytes cenv ty < 2 ** 64 /\
   0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
   type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv ty` by
    (drule_all assign_base_local_memory_sizes >> simp[]) >>
  drule expr_body_pre_type_evaluates >>
  disch_then (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME etv` >>
  `type_memory_bytes cenv (expr_type e) = type_memory_size etv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) < 2 ** 64` by decide_tac >>
  drule_all memory_rhs_lowered_runtime_layout >> strip_tac >>
  `type_memory_size entry.type + 64 < dimword (:256)` by
    metis_tac[allocation_limit_word_room] >>
  `type_memory_size etv < 2 ** 64` by
    (`alloc_limits_expr cenv e` by fs[expr_body_pre_def] >>
     drule alloc_limits_expr_type_alloc_ok >> fs[type_alloc_ok_def]) >>
  `0 < type_memory_size etv` by
    (drule_all lowered_value_type_memory_bound >> decide_tac) >>
  `0 < type_memory_size ltv /\ type_memory_size ltv < dimword (:256)` by
    (`type_memory_size ltv + 64 < dimword (:256)` by
       metis_tac[allocation_limit_word_room] >> decide_tac) >>
  `!gs v es1 ent.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
     lookup_scopes id es1.scopes = SOME ent ==>
     ent.type = entry.type /\ value_has_type entry.type v /\
     value_has_type etv v /\ value_has_type ltv v` by suspend "typed" >>
  irule compile_assign_local_memory_widen_stmt_frag_ptr >>
  `type_memory_size etv < 18446744073709551616` by
    (qpat_x_assum `type_memory_size etv < 2 ** 64` mp_tac >> simp[]) >>
  simp[SF CONJ_ss] >>
  conj_tac >- (qpat_x_assum `~(_ /\ _)` mp_tac >> simp[]) >>
  conj_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `(ty = _ /\ _) \/ _` mp_tac >> metis_tac[]) >>
  conj_tac >- (qexists_tac `tops` >> first_assum ACCEPT_TAC) >>
  qexists_tac `env` >> first_assum ACCEPT_TAC
QED

Resume body_assign_local_memory_ptr[typed]:
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `ent.type = entry.type` by
    metis_tac[CONV_RULE (DEPTH_CONV ETA_CONV) memory_rhs_read_local_type] >>
  `value_runtime_typed env ty v` by
    metis_tac[CONV_RULE (DEPTH_CONV ETA_CONV) memory_rhs_read_destination_typed] >>
  `value_runtime_typed env (expr_type e) v` by
    metis_tac[CONV_RULE (DEPTH_CONV ETA_CONV) memory_rhs_read_destination_typed,
              type_widens_to_def] >>
  `value_runtime_typed env (lowered_value_type cenv e) v` by
    metis_tac[CONV_RULE (DEPTH_CONV ETA_CONV) memory_rhs_read_lowered_typed] >>
  `expr_sim_inv cenv cx env (es with gas_obs := gs)` by simp[] >>
  metis_tac[memory_rhs_runtime_layout, optionTheory.SOME_11]
QED

Finalise body_assign_local_memory_ptr
