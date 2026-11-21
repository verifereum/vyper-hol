(* Proof-only typing and layout boundaries for aggregate storage assignment. *)
Theory bodyMemAssignTopCopyFacts
Ancestors
  supportedExprTraverse allocLimits allocLimitsProps
  bodyStorageCases[qualified,ignore_grammar]
  bodyMemAssignTopCopyIndex allocaFootprint[qualified] allocaHistoryFragment[qualified] bodySimStmtFacts exprSimHyps
  vyperTypeEnv vyperStorageLayoutSafety supportedProgram
  supportedTypes supportedExprs supportedStmts supportedStmtTraverse
  bodySim bodyExprPreFacts exprSimHypsDefs stmtSimDefs bodyStorageMetadata
  vyperLookup vyperContext vyperState vyperTypeInvariants
  vyperTypeSystem vyperTypeCallGraph vyperLookupStorage
  compileEnv exprLoweringProps exprLowering valueEncodingProps stmtLowering
  list rich_list finite_map words vyperAST memoryLocalRhsProps
  exprSimSource bodyMemoryPreds exprSimDefs loweringPosts valueEncoding
  vyperTypeExprResult vyperTypeExprSoundness
  exprSimMemDefs venomMemDefs vyperValue exprSimProps
Libs
  monadsyntax

(* stmt_expr_body_pre's const-name premise, discharged from body_inv. *)
val irule_body_pre = bodyConstNameLib.irule_body_pre;

Theorem topcopy_rhs_pre_supported:
  !tops ctx cenv cx e env es ret_ty nsid env'.
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) =
      SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) ==>
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  drule_all body_inv_stmt_const_name_free >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >>
  strip_tac >>
  `well_typed_expr env e` by
    gvs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
  drule_then assume_tac supported_expr_no_evm_run >>
  drule_then assume_tac bodyStorageCasesTheory.supported_expr_main_calls >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, alloc_limits_stmt_def,
      alloc_limits_iterator_def, alloc_limits_assert_def, alloc_limits_raise_def,
      alloc_limits_expr_def]) >>
  imp_res_tac alloc_limits_expr_not_extcode >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by
    (irule gasContextTheory.cx_tops_module >> fs[body_inv_def]) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)` by
    fs[body_inv_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, int_calls_stmt_def,
      int_calls_atarget_def, int_calls_expr_def, EVERY_CONJ] >>
  qexists_tac `[]` >> simp[]
QED

Theorem topcopy_rhs_pre:
  !tops ctx cenv cx e env es ret_ty nsid env'.
    body_stmt_safe tops (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) =
      SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) ==>
    expr_body_pre cenv cx env e es
Proof
  metis_tac[topcopy_rhs_pre_supported]
QED

Theorem find_var_decl_storage_some[local]:
  !ts vis mut id ty init.
    MEM (VariableDecl vis mut id ty init) ts /\
    (mut = Storage \/ mut = Transient) ==>
    find_var_decl_by_name id ts <> NONE
Proof
  Induct >> simp[] >> Cases >> rw[find_var_decl_by_name_def] >> metis_tac[]
QED

Theorem env_assignable_find_NONE[local]:
  !env cx st src id ty.
    env_consistent env cx st /\
    FLOOKUP env.bare_global_assignable (src, id) = SOME ty ==>
    ?ts. get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE
Proof
  rw[env_consistent_def, env_context_consistent_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem topcopy_target:
  !tops ctx cenv cx src id mut ty ast_slot env es ret_ty e env'.
    body_inv tops ctx cenv cx /\
    supported_variable_decl tops (src,id) = SOME (Private,mut,ty,SOME ast_slot) /\
    (mut = Storage \/ mut = Transient) /\ expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) =
      SOME env' ==>
    src = NONE /\ get_module_code cx NONE = SOME tops /\
    cenv.ce_hashmap_info (NONE,id) = NONE /\
    cenv.ce_module_var_type (NONE,id) = SOME ty /\
    ?tr id_str off tvt.
      find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,id_str) /\
      lookup_var_slot_from_layout cx tr NONE id_str = SOME off /\
      evaluate_type (get_tenv cx) ty = SOME tvt
Proof
  rpt gen_tac >> strip_tac >> (
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[find_var_decl_storage_some] >>
  Cases_on `type_place_target env (TopLevelNameTarget (NONE,id))` >>
  gvs[type_stmt_def, atarget_accepts_def] >>
  rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `t = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  metis_tac[])
QED

Theorem topcopy_rhs_memory:
  body_expr_mem_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es ==>
  expr_sim_mem ctx func cenv cx (expr_type e) e es
Proof
  metis_tac[body_expr_mem_ok_def]
QED

Theorem topcopy_rhs_value_typed:
  !cenv cx env e es tv gs v es1.
    expr_body_pre cenv cx env e es /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    (do result <- eval_expr cx e; read_result cx result od)
      (es with gas_obs := gs) = (INL v, es1) ==>
    value_has_type tv v
Proof
  rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        env_consistent_def, env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
      value_runtime_typed_def]
QED

Theorem topcopy_memory_size:
  expr_sim_inv cenv cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  0 < type_memory_bytes cenv ty ==>
  type_memory_bytes cenv ty = type_memory_size tv /\
  0 < type_slot_size tv
Proof
  strip_tac >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  gvs[type_memory_size_slots]
QED

Theorem topcopy_val_store_size:
  ~is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
  val_store_size tv v = type_memory_size tv
Proof
  rpt strip_tac >> Cases_on `v` >> simp[val_store_size_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV b` >> Cases_on `b` >> simp[] >>
  Cases_on `ty` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def]
QED

Theorem topcopy_source_bound:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  expr_store_bound cx ty v op s /\ eval_operand op s = SOME b /\
  0 < type_memory_size tv ==>
  w2n b + type_memory_size tv <= s.vs_alloca_next
Proof
  strip_tac >> drule_all topcopy_val_store_size >> disch_tac >>
  gvs[expr_store_bound_def]
QED
