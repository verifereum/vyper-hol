(* Proof-only typing and layout boundaries for aggregate storage assignment. *)
Theory bodyMemAssignTopCopyFacts
Ancestors
  bodyMemAssignTopWord bodySimStmtCases exprSimHyps
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

Theorem topcopy_rhs_pre:
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
  `well_typed_expr env e` by
    gvs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by
    (irule gasContextTheory.cx_tops_module >> fs[body_inv_def]) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)` by
    fs[body_inv_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, int_calls_stmt_def,
      int_calls_atarget_def, int_calls_expr_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem topcopy_region:
  !cx mid id tr off tvt.
    storage_layout_safe cx /\
    storage_var_info cx mid id = SOME (tr,off,tvt) /\
    0 < type_slot_size tvt ==>
    off + type_slot_size tvt <= dimword (:256) /\
    (!mid' n' subs' k' tv'.
      declared_storage_region cx mid' n' subs' = SOME (tr,k',tv') /\
      (k',tv') <> (n2w off,tvt) ==>
      ranges_disjoint off (type_slot_size tvt) (w2n k') (type_slot_size tv'))
Proof
  rpt gen_tac >> strip_tac >>
  `off + type_slot_size tvt <= dimword (:256)` by
    (drule storage_layout_safe_layout >>
     simp[well_formed_layout_def] >> metis_tac[]) >>
  `off < dimword (:256)` by decide_tac >>
  `w2n (n2w off : 256 word) = off` by simp[] >>
  drule declared_storage_region_ordinary >> strip_tac >>
  simp[] >> rpt strip_tac >>
  `(mid,id,[]) <> (mid',n',subs')` by
    (strip_tac >> gvs[]) >>
  drule_all storage_layout_safe_region_separation >> simp[]
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

Theorem topcopy_scalar_fit_equal[local]:
  !tops fuel t u.
    supported_scalar_type t /\
    supported_nested_type supported_full_word_type fuel tops u /\
    arg_type_fits t u ==> t = u
Proof
  Cases_on `t` >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def] >>
  rename1 `supported_word_type (BaseT bt)` >> Cases_on `u` >>
  simp[arg_type_fits_def] >>
  rename1 `arg_type_fits _ (BaseT ub)` >>
  Cases_on `bt` >> Cases_on `ub` >>
  simp[supported_word_type_def, supported_string_type_def,
       arg_type_fits_def, Once supported_nested_type_def,
       supported_full_word_type_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `b` >>
  gvs[arg_type_fits_def, supported_word_type_def, supported_string_type_def]
QED

Theorem topcopy_scalars_fit_equal[local]:
  !ts us tops fuel.
    EVERY supported_scalar_type ts /\
    EVERY (supported_nested_type supported_full_word_type fuel tops) us /\
    arg_types_fit ts us ==> ts = us
Proof
  Induct >> Cases_on `us` >> simp[arg_type_fits_def] >>
  rpt strip_tac >> drule_all topcopy_scalar_fit_equal >> strip_tac >>
  gvs[] >> first_x_assum irule >> metis_tac[]
QED

Theorem topcopy_value_fit_equal:
  !tops t u.
    supported_value_type tops t /\ supported_storage_type tops u /\
    (!et n. u <> ArrayT et (Dynamic n)) /\ arg_type_fits t u ==> t = u
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `supported_scalar_type t`
  >- metis_tac[topcopy_scalar_fit_equal, supported_storage_type_def] >>
  Cases_on `t` >>
  gvs[supported_value_type_def] >> Cases_on `u` >>
  gvs[arg_type_fits_def]
  >~ [`arg_types_fit ts us`]
  >- (gvs[supported_storage_type_def, Once supported_nested_type_def,
          supported_full_word_type_def] >>
      metis_tac[topcopy_scalars_fit_equal]) >>
  Cases_on `b` >> Cases_on `b'` >> gvs[arg_type_fits_def] >>
  fs[supported_storage_type_def] >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  simp[Once supported_nested_type_def, supported_full_word_type_def] >>
  strip_tac >>
  metis_tac[topcopy_scalar_fit_equal, supported_scalar_type_def]
QED

Theorem topcopy_rhs_lowered_type:
  !cenv e tops ctx cx env es.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    supported_storage_type tops (expr_type e) /\
    (!elem n. expr_type e <> ArrayT elem (Dynamic n)) ==>
    lowered_value_type cenv e = expr_type e
Proof
  ho_match_mp_tac exprLoweringTheory.lowered_value_type_ind >> rpt conj_tac
  >- (simp[expr_type_def] >> metis_tac[topcopy_not_bytestring, is_bytestring_type_def])
  >- (simp[expr_type_def] >> metis_tac[topcopy_not_bytestring, is_bytestring_type_def])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
      simp[expr_body_pre_def, well_typed_expr_def, expr_type_def] >>
      strip_tac >> gvs[expr_type_def] >>
      drule topcopy_not_bytestring >>
      gvs[vyperTypeSystemTheory.well_typed_builtin_app_def,
          is_bytestring_type_def])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
      simp[expr_body_pre_def, well_typed_expr_def,
           type_builtin_result_ok_def, expr_type_def] >> strip_tac >>
      gvs[expr_type_def] >>
      drule topcopy_not_bytestring >> simp[is_bytestring_type_def])
  >- (rpt gen_tac >> strip_tac >>
      rename1 `Call ct (IntCall func_id) cargs cdflt` >>
      `supported_program tops /\
       cenv.ce_func_return_type = build_func_return_type tops /\
       get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
      `well_typed_expr env (Call ct (IntCall func_id) cargs cdflt)` by
        gvs[expr_body_pre_def] >>
      qpat_x_assum `supported_expr _ _` mp_tac >>
      simp[supportedExprsTheory.supported_expr_def, supported_pure_expr_def,
           supported_effect_expr_def] >> strip_tac >>
      Cases_on `cdflt` >> gvs[supported_effect_expr_def, optionTheory.IS_SOME_EXISTS] >>
      PairCases_on `x` >>
      `?sig. FLOOKUP env.fn_sigs func_id = SOME sig` by
        (Cases_on `func_id` >>
         gvs[well_typed_expr_def, optionTheory.IS_SOME_EXISTS]) >>
      drule_all supported_internal_signature_return >> strip_tac >>
      drule_all supported_internal_return_admissible >> strip_tac >>
      drule_all supported_internal_return_type >> strip_tac >>
      qpat_x_assum `well_typed_expr _ _` mp_tac >>
      Cases_on `func_id` >>
      simp[well_typed_expr_def, expr_type_def] >> strip_tac >>
      gvs[exprLoweringTheory.lowered_value_type_def, expr_type_def] >>
      gvs[supported_return_type_def, type_widens_to_def]
      >- (Cases_on `ct` >> gvs[arg_type_fits_def]) >>
      metis_tac[topcopy_value_fit_equal]) >>
  simp[exprLoweringTheory.lowered_value_type_def]
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

Theorem topcopy_index_bound:
  w2n b + 32*n <= s.vs_alloca_next /\ i < n ==>
  w2n (b + n2w i * 32w : 256 word) + 32 <= s.vs_alloca_next
Proof
  strip_tac >>
  `b + n2w i * 32w = n2w (w2n b + 32*i)` by
    simp[GSYM word_add_n2w, GSYM word_mul_n2w, arithmeticTheory.MULT_COMM,
         WORD_MULT_COMM] >>
  asm_rewrite_tac[] >>
  `w2n (n2w (w2n b + 32*i) : 256 word) <= w2n b + 32*i` by
    simp[w2n_n2w, arithmeticTheory.MOD_LESS_EQ] >>
  decide_tac
QED
