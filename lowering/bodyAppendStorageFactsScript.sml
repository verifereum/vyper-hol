(* Boundary facts for the supported storage/transient Append case. *)
Theory bodyAppendStorageFacts
Ancestors
  bodySim allocLimits supportedExprForms supportedTypes vyperValue vyperTypeSystem
  compileVyper compileEnv loweringStateRelDefs vyperAST words supportedDecls vyperInterpreter
  vyperState bodyStorageMetadata exprOpenCases vyperTypeEnv
  exprSimHypsDefs finite_map vyperTypeInvariants
  supportedStmts supportedProgram
  alist bodyInvCodeProps linkedStorageMetadataProps

Theorem body_append_element_alloc_bound:
  stmt_exprs_ok cenv (Append target e) ==>
  type_memory_bytes cenv (expr_type e) < 2 ** 64
Proof
  strip_tac >>
  `alloc_limits_expr cenv e` by
    gvs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  Cases_on `is_word_type (expr_type e)`
  >- (Cases_on `expr_type e` >> gvs[is_word_type_def, type_memory_bytes_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[is_word_type_def, type_memory_bytes_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, type_memory_bytes_def]) >>
  Cases_on `e` >>
  gvs[Once alloc_limits_expr_def, type_alloc_ok_def, expr_type_def]
QED

Theorem supported_append_element_layout:
  supported_full_word_type elem ==>
  is_word_type elem /\
  ?tv. evaluate_type tenv elem = SOME tv /\ type_slot_size tv = 1
Proof
  rw[supported_full_word_type_def] >>
  simp[is_word_type_def, evaluate_type_def, type_slot_size_def]
QED

Theorem append_capacity_word_bound:
  supported_full_word_type elem /\
  assignable_type tenv (ArrayT elem (Dynamic n)) ==>
  0 < n /\ n + 1 < dimword(:256)
Proof
  strip_tac >>
  drule supported_append_element_layout >>
  disch_then (qspec_then `tenv` strip_assume_tac) >>
  gvs[assignable_type_def, well_formed_type_def, evaluate_type_def,
      type_slot_size_def, bound_length_def]
QED

Theorem append_storage_target_eval:
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,key) /\
  lookup_var_slot_from_layout cx tr src key = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  eval_target_place cx (TopLevelNameTarget (src,id)) es =
    (INL (StoragePlace tr (n2w slot) tv),
     es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tv])
Proof
  strip_tac >>
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[lookup_global_def, bind_def, ignore_bind_def, lift_option_type_def,
       record_storage_event_def, return_def, get_place_def, LET_THM]
QED

Theorem body_append_root_metadata_mods:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  supported_variable_decl tops (NONE,id) =
    SOME (vis,mut,ArrayT elem (Dynamic n),slot) ==>
  cenv.ce_module_var_type (src,id) = SOME (ArrayT elem (Dynamic n)) /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_dynarray_capacity (src,id) = n
Proof
  strip_tac >> drule_then strip_assume_tac supported_variable_decl_mem >>
  metis_tac[contract_inv_variable_metadata, body_append_capacity_lookup_mods]
QED

Theorem body_append_root_metadata:
  body_inv tops ctx cenv cx /\
  supported_variable_decl tops nid =
    SOME (vis,mut,ArrayT elem (Dynamic n),slot) ==>
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic n)) /\
  cenv.ce_hashmap_info nid = NONE /\
  cenv.ce_module_dynarray_capacity nid = n
Proof
  Cases_on `nid` >> strip_tac >>
  drule_then strip_assume_tac supported_variable_decl_mem >> gvs[] >>
  drule_then assume_tac body_inv_contract >>
  metis_tac[SIMP_RULE (srw_ss()) [ALOOKUP_def]
    (Q.INST [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`]
      body_append_root_metadata_mods)]
QED

Theorem append_typed_storage_target:
  env_consistent env cx es /\
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops <> NONE /\
  type_place_target env (TopLevelNameTarget (src,id)) = SOME (Type ty) ==>
  ?tr key slot tv.
    find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,key) /\
    lookup_var_slot_from_layout cx tr src key = SOME slot /\
    evaluate_type (get_tenv cx) ty = SOME tv
Proof
  simp[type_place_target_TopLevelNameTarget] >> rpt strip_tac
  >- (gvs[env_consistent_def, env_context_consistent_def] >>
      qpat_x_assum `!src id ty. FLOOKUP env.bare_global_assignable _ = SOME _ ==> _`
        drule >> strip_tac >> gvs[]) >>
  drule_all env_consistent_toplevel_storage_static >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

Theorem supported_append_storage_decl:
  FST nid = NONE /\ supported_storage_dynamic_array tops nid ==>
  ?vis mut elem n slot.
    supported_variable_decl tops nid =
      SOME (vis,mut,ArrayT elem (Dynamic n),SOME slot) /\
    (mut = Storage \/ mut = Transient) /\ supported_storage_type tops elem
Proof
  strip_tac >>
  Cases_on `supported_variable_decl tops nid` >>
  gvs[supported_storage_dynamic_array_def] >>
  PairCases_on `x` >> Cases_on `x1` >> Cases_on `x2` >> Cases_on `x3` >>
  gvs[supported_storage_dynamic_array_def] >>
  rename1 `ArrayT elem bd` >> Cases_on `bd` >> gvs[] >> metis_tac[]
QED

Theorem body_append_runtime_metadata_mods:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  supported_storage_dynamic_array tops (NONE,id) /\
  env_consistent env cx es /\
  type_place_target env (TopLevelNameTarget (src,id)) = SOME (Type ty) ==>
  ?elem n tr key slot tv.
    ty = ArrayT elem (Dynamic n) /\
    cenv.ce_module_var_type (src,id) = SOME ty /\
    cenv.ce_module_dynarray_capacity (src,id) = n /\
    find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,key) /\
    lookup_var_slot_from_layout cx tr src key = SOME slot /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (StoragePlace tr (n2w slot) tv),
       es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tv])
Proof
  REWRITE_TAC [GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_then strip_assume_tac (SIMP_RULE (srw_ss()) []
    (Q.INST [`nid` |-> `(NONE,id)`] supported_append_storage_decl)) >>
  drule_all_then strip_assume_tac body_append_root_metadata_mods >>
  `get_module_code cx src = SOME tops` by metis_tac[contract_inv_module_codes] >>
  drule_then strip_assume_tac supported_variable_decl_mem >>
  drule supported_variable_decl_runtime_lookup >> simp[] >> strip_tac >>
  `find_var_decl_by_name id tops <> NONE` by simp[] >>
  drule_all_then strip_assume_tac append_typed_storage_target >>
  drule_then strip_assume_tac find_var_decl_storage_mem >>
  drule_all_then strip_assume_tac contract_inv_variable_metadata >>
  `ty = ArrayT elem (Dynamic n)` by metis_tac[optionTheory.SOME_11] >>
  gvs[] >> drule_all_then strip_assume_tac append_storage_target_eval >> simp[]
QED

Theorem append_storage_compiler_location:
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,key) /\
  lookup_var_slot_from_layout cx tr src key = SOME slot ==>
  FLOOKUP cenv.ce_module_vars (src,id) =
    SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))
Proof
  Cases_on `tr` >>
  simp[storage_vars_rel_def, transient_vars_rel_def] >> rpt strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  simp[var_decl_transient_def]
QED

Theorem append_typing_target:
  type_stmt env ret_ty (Append tgt e) = SOME env' ==>
  ?elem n.
    type_place_target env tgt = SOME (Type (ArrayT elem (Dynamic n))) /\
    well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) elem /\
    assignable_type env.type_defs elem
Proof
  simp[Once type_stmt_def, AllCaseEqs()] >> metis_tac[]
QED

(* A word type takes no wider type (type_widens_to). *)
Theorem type_widens_to_word:
  !tenv t u. type_widens_to tenv t u /\ is_word_type u ==> t = u
Proof
  metis_tac[compileEnvTheory.type_widens_to_word]
QED
