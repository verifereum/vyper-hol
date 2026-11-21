(* Proof-only typing and layout boundaries for aggregate storage assignment. *)
Theory bodyMemAssignTopCopyFacts
Ancestors
  stmtExprAllocationPreProps bodyInvCodeProps compileUnit alist
  augAssignPtrToplevelMetadata linkedStorageMetadataProps exprBodyPreProps
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

Theorem topcopy_rhs_pre_supported_mods:
  contract_inv mods exps ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
     occurs_abi_decode_target target (main_module mods)) /\ supported_expr (main_module mods) e /\
  expr_sim_inv_mods mods cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) =
    SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
  call_evaluation_safe cx
    (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
  ~supported_expr_exists (unallocated_bare_global_root cenv env) e ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  `well_typed_expr env e` by
    gvs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
  mp_tac (Q.INST [`ctx` |-> `ctx`, `exps` |-> `exps`]
                  stmt_expr_body_pre_main_alloc_mods) >>
  fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def, supported_assignment_exists_def,
     alloc_limits_stmt_def, int_calls_stmt_def, int_calls_atarget_def,
     int_calls_expr_def]
QED

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
  mp_tac (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`, `s` |-> `Assign (BaseTarget (TopLevelNameTarget nsid)) e`]
          body_inv_stmt_expr_pre_singleton) >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >>
  disch_then irule >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`,
                   `ctx` |-> `ctx`, `ret_ty` |-> `ret_ty`, `env'` |-> `env'`, `nsid` |-> `nsid`] topcopy_rhs_pre_supported_mods) >>
  simp[main_module_def, ALOOKUP_def]
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

Theorem topcopy_target_mods:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  supported_variable_decl tops (NONE,id) = SOME (Private,mut,ty,SOME ast_slot) /\
  (mut = Storage \/ mut = Transient) /\ expr_sim_inv_mods mods cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) =
    SOME env' ==>
  get_module_code cx src = SOME tops /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME ty /\
  ?tr id_str off tvt.
    find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME off /\
    evaluate_type (get_tenv cx) ty = SOME tvt
Proof
  strip_tac >>
  drule_then strip_assume_tac supported_variable_decl_mem >>
  drule_then assume_tac contract_inv_module_codes >>
  `get_module_code cx src = SOME tops` by simp[] >>
  drule_all_then strip_assume_tac contract_inv_variable_metadata >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[find_var_decl_storage_some] >>
  `FLOOKUP env.bare_global_assignable (src,id) = NONE` by
    (Cases_on `FLOOKUP env.bare_global_assignable (src,id)` >> simp[] >>
     drule_all_then strip_assume_tac augassign_env_assignable_find_none >> gvs[]) >>
  Cases_on `type_place_target env (TopLevelNameTarget (src,id))` >>
  gvs[type_stmt_def, atarget_accepts_def] >>
  rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget] >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac body_inv_storage_var_types_mods >> gvs[] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  metis_tac[]
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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (SUBST_ALL_TAC o CONJUNCT1) supported_variable_decl_mem >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`, `ctx` |-> `ctx`,
                   `src` |-> `NONE`,
                   `ret_ty` |-> `ret_ty`, `ast_slot` |-> `ast_slot`,
                   `mut` |-> `mut`, `env'` |-> `env'`, `e` |-> `e`]
          topcopy_target_mods) >>
  fs[ALOOKUP_def, expr_sim_inv_split_def]
QED

Theorem topcopy_rhs_memory:
  body_expr_mem_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es ==>
  expr_sim_mem ctx func cenv cx (expr_type e) e es
Proof
  metis_tac[body_expr_mem_ok_def]
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
