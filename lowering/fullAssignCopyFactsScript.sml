(* Canonical source typing boundaries for aggregate storage assignment.
   These proofs have no dependency on a completed expression simulation. *)
Theory fullAssignCopyFacts
Ancestors
  bodyExprPreFacts bodyStorageMetadata exprOpenCases exprSimSource
  supportedProgram supportedNames supportedDecls supportedTypes supportedExprs
  supportedExprTraverse supportedStmtTraverse allocLimitsProps allocLimits
  bodySim exprSimHyps exprSimHypsDefs exprSimProps stmtSimDefs
  compileVyper compileEnv exprLowering exprLoweringProps loweringPosts loweringShapeProps
  vyperTypeSystem vyperTypeArgFits vyperTyping vyperTypeEnv vyperTypeCallGraph
  vyperTypeExprResult vyperTypeExprSoundness vyperStorageLayoutSafety
  vyperLookupStorage vyperLookup vyperContext vyperState vyperTypeInvariants vyperInterpreter
  vyperValue valueEncodingProps valueEncoding exprSimMemDefs venomMemDefs
  stmtLowering context emitHelper emitHelperProps stmtSimAssignStorageFacts
  exprOpenPrimitives venomInst
  list rich_list finite_map words vyperAST
Libs monadsyntax

Theorem build_func_return_type_distinct:
  !tops vis mut nr rr name args dflts ret stmts.
    ALL_DISTINCT (supported_function_names tops) /\ vis <> External /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops ==>
    build_func_return_type tops name = ret
Proof
  Induct >> simp[] >> Cases >>
  simp[build_func_return_type_def, supported_function_names_def] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  `MEM name (supported_function_names tops)` by
    (simp[MEM_supported_function_names] >> metis_tac[]) >>
  `name <> s` by (strip_tac >> gvs[]) >> rw[]
QED

Theorem supported_internal_function_lookup:
  !tops id mut nr rr args dflts ret body.
    supported_function_decl tops id Internal =
      SOME (mut, nr, rr, args, dflts, ret, body) ==>
    FST id = NONE /\
    lookup_function NONE (SND id) Internal tops =
      SOME (mut, nr, args, dflts, ret, body) /\
    MEM (FunctionDecl Internal mut nr rr (SND id) args dflts ret body) tops
Proof
  Induct >> Cases_on `id` >> simp[supported_function_decl_def] >>
  Cases_on `h` >> simp[supported_function_decl_def, vyperInterpreterTheory.lookup_function_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[vyperInterpreterTheory.lookup_function_def] >>
  Cases_on `v` >> simp[vyperInterpreterTheory.lookup_function_def]
QED

Theorem supported_internal_return_type:
  !tops id mut nr rr args dflts ret body cenv.
    supported_program tops /\
    supported_function_decl tops id Internal =
      SOME (mut, nr, rr, args, dflts, ret, body) /\
    cenv.ce_func_return_type = build_func_return_type tops ==>
    cenv.ce_func_return_type (nsid_to_string id) = ret
Proof
  rpt strip_tac >> drule supported_internal_function_lookup >> strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    metis_tac[supported_program_names, supported_declaration_names_unique] >>
  Cases_on `id` >> gvs[nsid_to_string_def] >>
  irule build_func_return_type_distinct >> simp[] >>
  qexistsl_tac [`args`, `dflts`, `mut`, `nr`, `rr`, `body'`, `Internal`] >> simp[]
QED

Theorem supported_internal_signature_return:
  !tops id mut nr rr args dflts ret body cenv cx env es sig.
    supported_program tops /\
    supported_function_decl tops id Internal =
      SOME (mut, nr, rr, args, dflts, ret, body) /\
    cenv.ce_func_return_type = build_func_return_type tops /\
    get_module_code cx NONE = SOME tops /\
    expr_sim_inv cenv cx env es /\
    FLOOKUP env.fn_sigs id = SOME sig ==>
    cenv.ce_func_return_type (nsid_to_string id) = sig.ret_ty
Proof
  rpt strip_tac >>
  `cenv.ce_func_return_type (nsid_to_string id) = ret` by
    (drule_all supported_internal_return_type >> simp[]) >>
  drule supported_internal_function_lookup >> strip_tac >>
  `vyperTypeInvariants$fn_sigs_consistent env.fn_sigs cx` by
    gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[vyperTypeInvariantsTheory.fn_sigs_consistent_def] >>
  Cases_on `id` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  gvs[lookup_callable_function_def] >> metis_tac[]
QED

Theorem supported_internal_return_admissible:
  !tops id mut nr rr args dflts ret body.
    supported_program tops /\
    supported_function_decl tops id Internal =
      SOME (mut,nr,rr,args,dflts,ret,body) ==>
    supported_return_type tops ret
Proof
  rpt strip_tac >> drule supported_internal_function_lookup >> strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_function_header_contract, supported_function_return_def]
QED

Theorem assign_base_storage_scalar_fit_equal[local]:
  !tops fuel t u.
    supported_scalar_type t /\
    supported_nested_type supported_full_word_type fuel tops u /\
    arg_type_fits t u ==> t = u
Proof
  Cases_on `t` >>
  simp[supported_scalar_type_def, supported_word_type_def, supported_string_type_def] >>
  rename1 `supported_word_type (BaseT bt)` >> Cases_on `u` >>
  simp[arg_type_fits_def] >> rename1 `arg_type_fits _ (BaseT ub)` >>
  Cases_on `bt` >> Cases_on `ub` >>
  simp[supported_word_type_def, supported_string_type_def,
       arg_type_fits_def, Once supported_nested_type_def, supported_full_word_type_def] >>
  rpt strip_tac >> gvs[] >> Cases_on `b` >>
  gvs[arg_type_fits_def, supported_word_type_def, supported_string_type_def]
QED

Theorem assign_base_storage_scalars_fit_equal[local]:
  !ts us tops fuel.
    EVERY supported_scalar_type ts /\
    EVERY (supported_nested_type supported_full_word_type fuel tops) us /\
    arg_types_fit ts us ==> ts = us
Proof
  Induct >> Cases_on `us` >> simp[arg_type_fits_def] >>
  rpt strip_tac >> drule_all assign_base_storage_scalar_fit_equal >> strip_tac >>
  gvs[] >> first_x_assum irule >> metis_tac[]
QED

Theorem assign_base_storage_value_fit_equal[local]:
  !tops t u.
    supported_value_type tops t /\ supported_storage_type tops u /\
    (!et n. u <> ArrayT et (Dynamic n)) /\ arg_type_fits t u ==> t = u
Proof
  rpt gen_tac >> strip_tac >> Cases_on `supported_scalar_type t`
  >- metis_tac[assign_base_storage_scalar_fit_equal, supported_storage_type_def] >>
  Cases_on `t` >> gvs[supported_value_type_def] >> Cases_on `u` >> gvs[arg_type_fits_def]
  >~ [`arg_types_fit ts us`]
  >- (gvs[supported_storage_type_def, Once supported_nested_type_def,
          supported_full_word_type_def] >> metis_tac[assign_base_storage_scalars_fit_equal]) >>
  Cases_on `b` >> Cases_on `b'` >> gvs[arg_type_fits_def] >>
  fs[supported_storage_type_def] >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  simp[Once supported_nested_type_def, supported_full_word_type_def] >>
  strip_tac >> metis_tac[assign_base_storage_scalar_fit_equal, supported_scalar_type_def]
QED

Theorem assign_base_storage_not_bytestring:
  !tops t. supported_storage_type tops t ==> ~is_bytestring_type t
Proof
  Cases_on `t` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_bytestring_type_def, supported_storage_type_def,
       Once supported_nested_type_def, supported_full_word_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_bytestring_type_def, supported_storage_type_def,
       Once supported_nested_type_def, supported_full_word_type_def]
QED

Theorem assign_base_storage_rhs_lowered_type:
  !cenv e tops ctx cx env es.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    supported_storage_type tops (expr_type e) /\
    (!elem n. expr_type e <> ArrayT elem (Dynamic n)) ==>
    lowered_value_type cenv e = expr_type e
Proof
  ho_match_mp_tac lowered_value_type_ind >> rpt conj_tac
  >- (simp[expr_type_def] >>
      metis_tac[assign_base_storage_not_bytestring, is_bytestring_type_def])
  >- (simp[expr_type_def] >>
      metis_tac[assign_base_storage_not_bytestring, is_bytestring_type_def])
  >- (rpt gen_tac >> strip_tac >>
      `~is_bytestring_type ty` by metis_tac[assign_base_storage_not_bytestring, expr_type_def] >>
      gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
         expr_type_def, is_bytestring_type_def])
  >- (rpt strip_tac >>
      qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
      simp[expr_body_pre_def, well_typed_expr_def,
           type_builtin_result_ok_def, expr_type_def] >> strip_tac >>
      gvs[expr_type_def] >> drule assign_base_storage_not_bytestring >>
      simp[is_bytestring_type_def])
  >- suspend "internal_call" >>
  simp[lowered_value_type_def]
QED

Resume assign_base_storage_rhs_lowered_type[internal_call]:
  rpt gen_tac >> strip_tac >>
  rename1 `expr_body_pre cenv cx env (Call ann (IntCall func_id) args kw) es` >>
  `supported_program tops /\
   cenv.ce_func_return_type = build_func_return_type tops /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `well_typed_expr env (Call ann (IntCall func_id) args kw)` by gvs[expr_body_pre_def] >>
  qpat_x_assum `supported_expr _ _` mp_tac >>
  simp[supportedExprsTheory.supported_expr_def, supported_pure_expr_def,
       supported_effect_expr_def] >> strip_tac >>
  Cases_on `kw` >> gvs[supported_effect_expr_def, optionTheory.IS_SOME_EXISTS] >>
  PairCases_on `x` >>
  `?sig. FLOOKUP env.fn_sigs func_id = SOME sig` by
    (Cases_on `func_id` >> gvs[well_typed_expr_def, optionTheory.IS_SOME_EXISTS]) >>
  drule_all supported_internal_signature_return >> strip_tac >>
  drule_all supported_internal_return_admissible >> strip_tac >>
  drule_all supported_internal_return_type >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >> Cases_on `func_id` >>
  simp[well_typed_expr_def, expr_type_def] >> strip_tac >>
  gvs[lowered_value_type_def, expr_type_def] >>
  gvs[supported_return_type_def, type_widens_to_def]
  >- (Cases_on `ann` >> gvs[arg_type_fits_def]) >>
  metis_tac[assign_base_storage_value_fit_equal]
QED

Finalise assign_base_storage_rhs_lowered_type

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
  rpt strip_tac >>
  `well_typed_expr env e` by
    gvs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
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
      int_calls_atarget_def, int_calls_expr_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem body_assign_copy_target_vis:
  !tops ctx cenv cx src id vis mut ty ast_slot env es ret_ty e env'.
    body_inv tops ctx cenv cx /\
    supported_variable_decl tops (src,id) = SOME (vis,mut,ty,SOME ast_slot) /\
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
  drule supported_variable_decl_runtime_lookup >> simp[] >> strip_tac >> gvs[] >>
  drule supported_variable_decl_mem >> strip_tac >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  Cases_on `type_place_target env (TopLevelNameTarget (NONE,id))` >>
  gvs[type_stmt_def, atarget_accepts_def] >>
  rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (gvs[env_consistent_def, env_context_consistent_def] >>
      first_x_assum drule >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `t = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[])
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
  strip_tac >> drule_all expr_sim_inv_memory_size >> strip_tac >>
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

Theorem topcopy_no_length_word:
  !tops t. supported_storage_type tops t /\
    (!elem n. t <> ArrayT elem (Dynamic n)) ==> ~has_length_word t
Proof
  rpt gen_tac >> strip_tac >>
  drule assign_base_storage_not_bytestring >>
  Cases_on `t` >> simp[has_length_word_def, is_bytestring_type_def] >>
  Cases_on `b` >> gvs[has_length_word_def, is_bytestring_type_def]
QED

Theorem stmt_env_assign:
  !cenv lctx ty g e sa c sf.
    stmt_env cenv lctx ty (Assign g e) sa = (c, sf) ==>
    c = cenv /\ compile_stmt cenv lctx ty (Assign g e) sa = ((), sf)
Proof
  rpt gen_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty (Assign g e) sa` >>
  rename1 `(u, _)` >> Cases_on `u` >> simp[]
QED

Theorem assign_storage_copy_code_parts:
  !cenv lctx ty nsid e sa sf c tr slot vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e)
      sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    cenv.ce_module_var_type nsid = SOME vtyp /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    lowered_value_type cenv e = expr_type e ==>
    c = cenv /\
    ?vv sV sB op.
      compile_expr cenv (expr_type e) e sa = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op, sB) /\
      compile_assign_value cenv (Lit slot)
        (if tr then LocTransient else LocStorage) op (is_word_type vtyp)
        (vv_location vv) vtyp (lowered_value_type cenv e)
        (type_memory_bytes cenv vtyp) sB = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_get_target_ptr_toplevel >> strip_tac >>
  drule stmt_env_assign >> strip_tac >>
  qpat_x_assum `c = cenv` SUBST_ALL_TAC >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [Once compile_stmt_def, exprLoweringTheory.expr_can_mutate_def,
     stmtLoweringTheory.target_to_expr_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv, sV)` >>
  Cases_on `unwrap_value cenv vv sV` >>
  rename1 `unwrap_value _ _ _ = (op, sB)` >>
  simp[] >> strip_tac >> simp[lower_value_def, comp_bind_def]
QED

Theorem word_copy_loop_op_open:
  !src dst n loc ctor sa u sb.
    compile_word_copy_loop_op src dst n LocMemory loc ctor sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_word_copy_loop_op_def, compile_word_copy_loop_base_def,
    comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[new_block_def, block_is_terminated_def]
QED

Theorem mem_to_slots_open[local]:
  !b src slot w s u t.
    (if b then compile_memory_to_transient else compile_memory_to_storage)
      src slot w s = (u,t) ==>
    ~block_is_terminated t
Proof
  Cases >>
  simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
       compile_word_copy_loop_def] >>
  metis_tac[word_copy_loop_op_open]
QED

Theorem emit_void_store_open[local]:
  !b args s u t.
    emit_void (if b then TSTORE else SSTORE) args s = (u,t) ==>
    ~block_is_terminated t
Proof
  rpt strip_tac >> drule emit_void_terminated >> Cases_on `b` >>
  simp[is_terminator_def]
QED

Theorem copy_elements_open[local]:
  !cenv src slot elem cnt tr s u t.
    compile_copy_elements_to_slots cenv src slot elem cnt tr s = (u,t) ==>
    ~block_is_terminated t
Proof
  rpt gen_tac >>
  simp[Once compile_store_slots_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[new_block_def, block_is_terminated_def]
QED

Theorem abi_dynamic_shape[local]:
  !sf ty.
    is_abi_dynamic sf ty /\ ~is_bytestring_type ty ==>
    (?elem bd. ty = ArrayT elem bd) \/
    (?tys. ty = TupleT tys /\ tys <> []) \/
    (?nsid fields. ty = StructT nsid /\
       FLOOKUP sf (nsid_to_string nsid) = SOME fields /\ fields <> [])
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp[is_abi_dynamic_def, is_bytestring_type_def]
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> simp[is_abi_dynamic_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      simp[is_abi_dynamic_def, is_bytestring_type_def])
  >- (rename1 `EXISTS _ tys` >> Cases_on `tys` >> simp[]) >>
  CASE_TAC >> simp[] >> rename1 `MAP _ fields` >> Cases_on `fields` >> simp[]
QED

Theorem store_slots_open:
  (!cenv src slot ty tr s u t.
     compile_store_slots cenv src slot ty tr s = (u,t) /\
     acyclic_struct_metadata cenv.ce_struct_fields ==>
     ~block_is_terminated t) /\
  (!cenv src slot members mem_off slot_off tr s u t.
     compile_store_slots_members cenv src slot members mem_off slot_off tr s =
       (u,t) /\
     acyclic_struct_metadata cenv.ce_struct_fields /\
     (members = [] ==> ~block_is_terminated s) ==>
     ~block_is_terminated t) /\
  (!cenv src slot elem cnt tr s u t.
     compile_copy_elements_to_slots cenv src slot elem cnt tr s = (u,t) ==>
     ~block_is_terminated t)
Proof
  ho_match_mp_tac compile_store_slots_ind >> rpt conj_tac >> rpt strip_tac
  >- (qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
      simp_tac std_ss [Once compile_store_slots_def, LET_THM] >>
      IF_CASES_TAC
      >- (IF_CASES_TAC >>
          simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
          rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
          metis_tac[emit_void_store_open, mem_to_slots_open]) >>
      IF_CASES_TAC
      >- (simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
          rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
          metis_tac[word_copy_loop_op_open]) >>
      IF_CASES_TAC >- gvs[] >>
      `is_abi_dynamic cenv.ce_struct_fields ty` by gvs[] >>
      drule_all abi_dynamic_shape >> strip_tac >> gvs[]
      >- (Cases_on `bd` >>
          simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
          rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
          metis_tac[emit_void_store_open, copy_elements_open])
      >- (strip_tac >> first_x_assum drule >> simp[])
      >- (strip_tac >> first_x_assum drule >> gvs[get_struct_fields_def]))
  >- gvs[Once compile_store_slots_def, comp_return_def]
  >- (qpat_x_assum `compile_store_slots_members _ _ _ (_::_) _ _ _ _ = _`
        mp_tac >>
      simp[Once compile_store_slots_def, comp_bind_def,
           comp_ignore_bind_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> metis_tac[])
  >- metis_tac[copy_elements_open]
QED

Theorem compile_assign_storage_endpoint_open:
  !cenv dst src tr sloc dty sty bytes sa sf.
    compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
      src F sloc dty sty bytes sa = ((),sf) /\
    acyclic_struct_metadata cenv.ce_struct_fields ==>
    ~block_is_terminated sf
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[compile_assign_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  metis_tac[cj 1 store_slots_open]
QED

Theorem assign_base_nonbytes_footprint:
  !ty tenv tv v.
    ~is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
    val_footprint tv v = type_memory_size tv
Proof
  Cases_on `ty` >> simp[is_bytestring_type_def, evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[is_bytestring_type_def] >>
  Cases_on `v` >> simp[val_footprint_def]
QED

Theorem eval_assign_toplevel_action:
  !cx src id e ts tr typ id_str slot tvt.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt ==>
    eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. ignore_bind (record_storage_event (StorageRoot tr slot tvt))
             (write_storage_slot cx tr (n2w slot) tvt v))
Proof
  rpt gen_tac >> strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e x` >> rename1 `eval_expr cx e x = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  Cases_on `read_result cx x' es1` >>
  rename1 `read_result cx _ es1 = (r2, es2)` >>
  Cases_on `r2` >> simp[] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, bind_def,
       lift_option_type_def, return_def, LET_THM, get_place_def,
       write_place_def, ignore_bind_def, record_storage_event_def]
QED
