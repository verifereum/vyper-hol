(* HELD (#767): a memory-backed declaration of an internal call whose
   return type widens to the call's type other than as a bytestring
   (type_widens_to: a DynArray of a smaller bound, a tuple elementwise).
   The memory twin of bodySimDeclCases' body_annassign_widened_aggregate_call,
   admitted as that one is. *)
Theory bodyMemAnnAssignWidened
Ancestors
  bodyMemoryPreds bodyDeclWidenedMemory bodyDeclRoomShellMemory bodySimDeclCases
  bodyWidenedCopyMemory
  supportedExprTraverse allocLimitsProps memoryLocalRhsProps bodyExprPreFacts
  exprSimHyps exprSimSource exprSimAggregateLayout stmtSimDeclStore
  stmtSimReturn stmtSimAssign allocLimits supportedTypes typedCopyMetadata gasContext bodySim
  supportedStmtTraverse vyperTypeCallGraph supportedStmts exprSimHypsDefs
  vyperTypeInvariants vyperTypeExprSoundness exprOpenMain
  compileEnv vyperTypeSystem vyperTypeExprResult vyperTyping vyperInterpreter
  vyperState finite_map
Libs
  monadsyntax

Theorem body_annassign_widened_aggregate_call_mem:
  !d cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_mem_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
    ~(lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

(* HELD: a memory-backed declaration whose right-hand side, not an internal
   call, widens to the declared type other than as a bytestring.  The memory
   twin of bodySimDeclCases' body_annassign_widened_aggregate, admitted as
   that one is. *)
Theorem body_annassign_widened_aggregate_mem:
  !d cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_mem_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    body_stmt_safe tops (AnnAssign id typ e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
    lowered_value_type cenv e = expr_type e /\ expr_type e <> typ /\
    ~is_bytestring_type typ /\ ~(has_length_word typ /\ is_empty_value_expr e) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt gen_tac >> strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   type_widens_to env.type_defs (expr_type e) typ /\
   id NOTIN FDOM env.var_types` by gvs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?dtv. evaluate_type (get_tenv cx) typ = SOME dtv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `body_expr_mem_ok cx e` by
    (first_x_assum irule >> qexistsl_tac [`es`, `es`, `get_tenv cx`, `dtv`] >>
     simp[lift_option_type_def, return_def]) >>
  `expr_body_pre cenv cx env e es` by
    (qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
      SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
        supported_assignment_exists_def, supported_iterator_exists_def,
        supported_assert_exists_def, supported_raise_exists_def,
        supported_expr_exists_def, int_calls_stmt_def, int_calls_atarget_def,
        int_calls_iterator_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
        listTheory.EVERY_APPEND, listTheory.EVERY_CONJ,
        DE_MORGAN_THM, GSYM expr_has_evm_run_def]) >>
     qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
      SIMP_RULE std_ss [stmt_exprs_ok_def, alloc_limits_stmt_def,
        alloc_limits_iterator_def, alloc_limits_assert_def, alloc_limits_raise_def,
        alloc_limits_expr_def]) >>
     imp_res_tac alloc_limits_expr_not_extcode >>
     `cx_tops cx = tops` by (irule cx_tops_module >> fs[body_inv_def]) >>
     irule stmt_expr_body_pre >>
     gvs[body_inv_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >> qexists_tac `[]` >> simp[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  `~is_word_type (expr_type e)` by metis_tac[type_widens_to_def, exprSimLayoutTransportTheory.compatible_word_type] >>
  drule expr_body_pre_type_evaluates >>
  disch_then (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME stv` >>
  `type_memory_bytes cenv typ = type_memory_size dtv /\
   type_memory_bytes cenv (expr_type e) = type_memory_size stv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv typ < 2 ** 64 /\
   type_memory_bytes cenv (expr_type e) < 2 ** 64` by
    (gvs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
     drule alloc_limits_expr_type_alloc_ok >> simp[type_alloc_ok_def]) >>
  `type_memory_size dtv + 64 < dimword (:256) /\
   type_memory_size stv + 64 < dimword (:256)` by
    metis_tac[allocation_limit_word_room] >>
  irule compile_annassign_room_rel_stmt_frag_mem >>
  simp[PULL_EXISTS] >> rpt conj_tac
  >~ [`declare_local _ _ _ _ = _ ==> _ /\ expr_vv_sim_mem _ _ _ _ _ _ _ /\ _`] >- suspend "rhs"
  >~ [`acyclic_struct_metadata _`] >- fs[body_inv_def]
  >~ [`expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`]
    >- suspend "continuation"
  >~ [`value_has_type _ _ /\ value_has_type _ _`] >- suspend "typing"
  >> fs[body_inv_def]
QED

Resume body_annassign_widened_aggregate_mem[rhs]:
  rpt gen_tac >> strip_tac >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `same_frame cenv c` by (drule_then irule declare_local_same_frame >> simp[]) >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
  `stmt_exprs_ok c (AnnAssign id typ e)` by metis_tac[stmt_exprs_ok_same_frame] >>
  `expr_body_pre c cx env e es` by
    (qpat_x_assum `expr_body_pre cenv cx env e es` mp_tac >>
     `alloc_limits_expr c e = alloc_limits_expr cenv e` by
       (irule (cj 1 alloc_limits_struct_fields) >> (qpat_x_assum `same_frame cenv c` mp_tac >>
        simp[same_frame_def] >> strip_tac >>
        qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[])) >>
     simp[expr_body_pre_def]) >>
  `lowered_value_type c e = lowered_value_type cenv e` by
    (irule lowered_value_type_frame >>
     drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
     qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  `lowered_value_type c e = expr_type e` by simp[] >>
  conj_tac >- metis_tac[loweringPostsTheory.post_value_type_lowered] >>
  conj_tac >- metis_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `monad_bind _ _ _ = _` mp_tac >>
  simp[bind_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[exprLoweringTheory.lower_value_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  `~block_is_terminated cs'` by
    (irule compile_expr_open_general >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     qexistsl_tac [`ctx`, `env`, `tops`] >>
     simp[]) >>
  metis_tac[exprOpenTerminalsTheory.unwrap_value_open]
QED

Resume body_annassign_widened_aggregate_mem[typing]:
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `value_runtime_typed env typ v /\ value_runtime_typed env (expr_type e) v` by
    (conj_tac >> irule memory_rhs_read_destination_typed >>
     qexistsl_tac [`cenv`, `cx`, `e`, `es with gas_obs := gs`, `es1`] >>
     simp[type_widens_to_def, bind_def] >> gvs[bind_def]) >>
  gvs[value_runtime_typed_def]
QED

Resume body_annassign_widened_aggregate_mem[continuation]:
  rpt gen_tac >> strip_tac >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `same_frame cenv c` by (drule_then irule declare_local_same_frame >> simp[]) >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `!ty. type_memory_bytes c ty = type_memory_bytes cenv ty` by
    (rpt gen_tac >> irule type_memory_bytes_struct_fields >>
     fs[same_frame_def] >> qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  `lowered_value_type c e = lowered_value_type cenv e` by
    (irule lowered_value_type_frame >>
     drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
     qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  `lowered_value_type c e = expr_type e` by simp[] >>
  irule annassign_widened_post_path_mem >>
  simp[arithmeticTheory.ADD_COMM] >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[arithmeticTheory.ADD_COMM] >>
  qexistsl_tac [`es`, `inst`, `salloc`, `sA`] >>
  simp[loweringPostsTheory.post_value_type_lowered] >>
  rpt conj_tac
  >~ [`gas_marked_path T _ _ _ _ _`] >- suspend "typedcopy"
  >~ [`~is_bytestring_type (expr_type e)`]
    >- metis_tac[type_widens_to_def, memoryLocalRhsPropsTheory.arg_type_fits_bytestring_target]
  >> metis_tac[]
QED

Resume body_annassign_widened_aggregate_mem[typedcopy]:
  rpt gen_tac >> strip_tac >>
  irule (BETA_RULE typed_memory_rank_frontier_forward_mem) >>
  simp[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  simp[arithmeticTheory.ADD_COMM, valueTypingMemoryPropsTheory.value_has_type_memory_wf, venomStateTheory.eval_operand_def] >>
  qexistsl_tac [`stv`, `get_tenv cx`] >>
  `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
  drule externalReturnSelectedResourcesTheory.return_site_copy_metadata >> strip_tac >>
  fs[body_inv_def] >>
  metis_tac[expr_sim_inv_memory_size, valueTypingMemoryPropsTheory.value_has_type_memory_wf]
QED

Finalise body_annassign_widened_aggregate_mem
