(* HELD (#767): a memory-backed declaration of an internal call whose
   return type widens to the call's type other than as a bytestring
   (type_widens_to: a DynArray of a smaller bound, a tuple elementwise).
   The memory twin of bodySimDeclCases' body_annassign_widened_aggregate_call,
   admitted as that one is. *)
Theory bodyMemAnnAssignWidened
Ancestors
  bodyMemoryPreds widenedLocalContinuationMem widenedLocalOutcomeMem
  widenedAssignValueParts widenedLocalRuntimeMem
  bodyExprPreFacts supportedStmtTraverse supportedStmts vyperTypeInvariants
  vyperTypeSystem vyperTypeExprResult vyperTyping bodySim exprSimHypsDefs
  gasContext supportedTypes vyperInterpreter vyperTypeCallGraph vyperState
  bodyDeclMemoryCounted bodyDeclCopyMemory stmtSimDeclCompose stmtSimDecl
  stmtSimDeclMem exprLoweringProps exprSimProps stmtSimProps stmtSimDefs
  bodySimDeclCases exprSimIfExpCompat exprSimSource compileEnv fragExec
  stmtSimDeclSource exprSimMemorySource exprSimMemDefs widenedValueReadOutcomeMem
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
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
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
  rpt gen_tac >> strip_tac >>
  `supported_expr tops e /\ supported_copy_types typ (expr_type e)` by
    gvs[supported_stmt_def] >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   type_widens_to env.type_defs (expr_type e) typ /\
   id NOTIN FDOM env.var_types` by gvs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `body_expr_mem_ok cx e` by
    (first_x_assum irule >> simp[lift_option_type_def, return_def]) >>
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac supported_expr_body_calls >>
     `cx_tops cx = tops` by (irule cx_tops_module >> fs[body_inv_def]) >>
     irule stmt_expr_body_pre >>
     gvs[body_inv_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >> qexists_tac `[]` >> simp[]) >>
  suspend "compile"
QED

Resume body_annassign_widened_aggregate_call_mem[compile]:
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z` by
    (rpt strip_tac >> `FLOOKUP cenv.ce_vars id = NONE` by
       (irule declared_name_unbound >> metis_tac[]) >> gvs[]) >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule stmt_env_annassign >> strip_tac >>
  rename1 `declare_local cenv id typ sa = (c, st)` >>
  `same_frame cenv c` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `stmt_exprs_ok c (AnnAssign id typ e)` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
  `expr_body_pre c cx env e es` by
    (drule_then strip_assume_tac supported_expr_body_calls >>
     `cx_tops cx = tops` by (irule cx_tops_module >> fs[body_inv_def]) >>
     irule stmt_expr_body_pre >>
     gvs[body_inv_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >> qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim_mem ctx func c cx (expr_type e) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  suspend "parts"
QED

Resume body_annassign_widened_aggregate_call_mem[parts]:
  `!id t. FLOOKUP env.var_types id = SOME t ==>
     well_formed_type env.type_defs t` by
    metis_tac[expr_body_pre_var_types_well_formed] >>
  `sfields_tenv_consistent cenv.ce_struct_fields env.type_defs` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `cenv` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  `~(has_length_word typ /\
     is_empty_value_expr (Call ty (IntCall fid) args drv))` by
    simp[stmtLoweringTheory.is_empty_value_expr_def] >>
  drule_all annassign_copy_parts_mem >> strip_tac >>
  `cs_extends sA sB` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sB sb` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`
       (mp_tac o AP_TERM ``SND : unit # compile_state -> compile_state``) >>
     metis_tac[externalEntryShapeTheory.compile_assign_value_labels,
               pairTheory.SND]) >>
  `cs_extends sA sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code (sa with cs_next_var := sa.cs_next_var + 1) sb func` by
    gvs[fn_has_code_def, emitted_blocks_def] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `fn_has_code sA sB func /\ fn_has_code sB sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sa sA func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[finite_mapTheory.FLOOKUP_DEF]) >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    gvs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def] >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  `STRING #"%" (toString sa.cs_next_var) =
   STRING #"%" (toString sa.cs_next_var)` by simp[] >>
  drule_all annassign_setup_body_gas_path_mem >>
  disch_then (qx_choose_then `salloc` strip_assume_tac) >>
  `gas_admissible
     (bind (eval_expr cx (Call ty (IntCall fid) args drv)) (read_result cx))
     expr_res_ok es` by
    (irule annassign_admissible_rhs >> metis_tac[]) >>
  `gas_admissible (eval_expr cx (Call ty (IntCall fid) args drv))
     expr_vv_res_ok es` by metis_tac[forced_expr_admissible_raw] >>
  `cs_extends sA sV` by
    (qpat_assum `compile_expr _ _ _ _ = _`
       (mp_tac o MATCH_MP (cj 1 compile_expr_grows)) >> simp[]) >>
  `cs_extends sV sB` by
    (drule exprSimUnwrapTheory.unwrap_value_extends >> simp[]) >>
  `fn_has_code sA sV func` by
    (drule_all fn_has_code_split >> simp[]) >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`sA`, `sV`, `vv`, `salloc`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  cheat
QED

Finalise body_annassign_widened_aggregate_call_mem
