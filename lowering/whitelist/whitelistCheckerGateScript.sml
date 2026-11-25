(* Whitelist removal: every single-module program check_contract accepts is
   in the supported_* gate.

   TOP-LEVEL: check_contract_supported_program (runtime check and the
   layouts the call relation fixes) and check_contract_supported_program_deploy
   (deployment check). The four top theorems discharge their gate through
   these, so neither is assumed whole: each conjunct of the gate has its own
   lemma below.

   - Storage, transient and hashmap slots: the checker reads them from the
     layouts and ignores the AST annotation, so headers and bodies (whose
     storage clauses ask for the annotation) take layouts_agree, which the
     call and deployment relations carry; the checker allocates every
     variable (check_contract_main_module_allocated). Types come from
     assignable_type.
   - Function bodies and defaults: from check_function_body. The statement
     and expression layers carry the typing environment of the body, which
     extends the artifact's and binds exactly the arguments, locals and loop
     variables; custom-error reasons come from custom_errors_stmt_ok.
   - Defaults and constants: they read only constants and immutables
     (runtime_constant_expr), so they type in the artifact environment cut
     down to those keys, which meets checker_env_ok without layouts_agree
     (whitelistCheckerConsts). *)
Theory whitelistCheckerGate
Ancestors
  list rich_list pair alist finite_map pred_set vyperAST vyperTypeSystem vyperTypeContract
  vyperTypeContractContext vyperContext
  e2eDefs e2eDeployDefs
  supportedTypes supportedDecls supportedNames supportedExprs supportedExprForms
  supportedStmts
  supportedStmtTraverse supportedProgram
  whitelistCheckerDecls whitelistCheckerDeploy whitelistCheckerTypes
  whitelistCheckerProgram whitelistCheckerExprs whitelistCheckerStmts
  whitelistCheckerFnSigs
  whitelistCheckerCallGraphProps whitelistAllocatedHeaderProps
  whitelistCheckedBareGlobalProps whitelistLinkedConstProps whitelistEventTypeProps
  relation vyperTypeContractStaticMaps vyperTypeCallGraph
  vyperTypeCallGraphSoundness vyperTypeEventLookup placeTypingBuildProps
  supportedNameRoot supportedGetterProps compileVyper constSubst constSubstMods
  constSubstStmtsPreserve loweringShapeSource bodyExprPreFacts
  constSubstCorrect whitelistCheckerConsts
  vyperTypeExternalDefaults

(* ===== Runtime gate ===== *)

Triviality checker_supported_declaration_header:
  check_toplevel_decl [(NONE, tops)] art NONE tl /\
  (case tl of
     VariableDecl _ Storage _ _ slot => IS_SOME slot
   | VariableDecl _ Transient _ _ slot => IS_SOME slot
   | HashMapDecl _ _ _ _ _ slot => IS_SOME slot
   | _ => T) ==>
  supported_declaration_header tops tl
Proof
  Cases_on `tl` >>
  simp[check_toplevel_decl_def, supported_declaration_header_def,
       type_env_all_modules_def, FUNION_FEMPTY_2, GSYM type_env_def]
  >- (rename1 `supported_function_return tops vis ret` >>
      Cases_on `vis` >>
      simp[function_header_ok_def, supported_function_return_def,
           supported_return_type_def] >>
      metis_tac[assignable_type_supported_place])
  >- (Cases_on `v0` >> Cases_on `o'` >>
      simp[check_toplevel_decl_def, supported_declaration_header_def,
           type_env_all_modules_def, FUNION_FEMPTY_2, GSYM type_env_def, supported_storage_type_def,
           GSYM supported_place_type_def, supported_value_type_def,
           assignable_type_supported_place])
  >- (rename1 `IS_SOME slot` >> Cases_on `slot` >>
      simp[check_toplevel_decl_def, supported_declaration_header_def,
           type_env_all_modules_def, FUNION_FEMPTY_2, GSYM type_env_def] >>
      metis_tac[checker_hashmap_key_supported, checker_hashmap_value_supported])
  >- (simp[EVERY_MEM, FORALL_PROD, NULL_EQ] >>
      metis_tac[assignable_type_supported_place])
  >> simp[FILTER_MAP, combinTheory.I_o_ID, EVERY_MEM, FORALL_PROD]
  >> rw[]
  >> metis_tac[assignable_type_supported_event, checker_indexed_event_type_supported]
QED

Triviality checked_single_decl_any:
  check_contract mode layouts addr [(NONE, tops)] = SOME art /\ MEM tl tops ==>
  check_toplevel_decl [(NONE, tops)] art NONE tl
Proof
  strip_tac >> irule check_contract_toplevel_decl_MEM_checked >> simp[] >>
  metis_tac[]
QED

Triviality checked_single_header:
  check_contract mode am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\ MEM tl tops ==>
  supported_declaration_header tops tl
Proof
  strip_tac >> drule_all checked_single_decl_any >> strip_tac >>
  drule check_contract_main_module_allocated >>
  simp[module_allocated_def, EVERY_MEM] >>
  disch_then (drule_then assume_tac) >>
  metis_tac[layouts_agree_allocated_header, checker_supported_declaration_header]
QED

Theorem check_contract_supported_declaration_headers:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx ==>
  supported_declaration_headers tops
Proof
  rw[supported_declaration_headers_def, EVERY_MEM] >>
  metis_tac[checked_single_header]
QED

Theorem check_contract_supported_internal_function_names:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  ALL_DISTINCT (supported_internal_function_names tops)
Proof
  strip_tac >>
  drule check_contract_function_names_same_vis_distinct >>
  disch_then (qspec_then `Internal` mp_tac) >> simp[] >>
  `!ts. supported_internal_function_names ts =
        supported_function_names
          (FILTER (\t. ?m nr rr n a d r b.
                     t = FunctionDecl Internal m nr rr n a d r b) ts)`
    suffices_by simp[] >>
  Induct >> simp[supported_internal_function_names_def,
                 supported_function_names_def] >>
  Cases >> simp[supported_function_names_def] >> rw[] >>
  gvs[supported_function_names_def] >>
  rename1 `vis <> Internal` >> Cases_on `vis` >> gvs[]
QED

(* ===== The function-entry environment ===== *)

Triviality checked_single_vtype_keys:
  check_contract mode layouts addr [(NONE, tops)] = SOME art ==>
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))
Proof
  strip_tac >>
  `contract_namespaces_ok F [(NONE, tops)]`
    by metis_tac[check_contract_runtime_namespaces] >>
  drule contract_namespaces_ok_module_toplevel_vtype_keys >> simp[]
QED

Triviality checker_variable_decl_facts:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  MEM (VariableDecl vis mut id ty init) tops /\
  supported_declaration_header tops (VariableDecl vis mut id ty init) ==>
  supported_place_root tops (NONE,id) /\ build_hashmap_info tops (NONE,id) = NONE /\
  ((mut = Storage \/ mut = Transient) ==> supported_storage_value tops (NONE,id) ty) /\
  (mut = Immutable ==> supported_immutable_type tops (NONE,id) = SOME ty) /\
  (!e. mut = Constant e ==> supported_constant_type tops (NONE,id) = SOME ty)
Proof
  strip_tac >> drule_all supported_variable_decl_distinct_mem >>
  drule_all build_hashmap_info_variable >>
  Cases_on `mut` >> Cases_on `init` >>
  gvs[supported_declaration_header_def, supported_place_root_def,
      supported_storage_value_def, supported_immutable_type_def,
      supported_constant_type_def]
QED

Triviality checker_hashmap_decl_facts:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  MEM (HashMapDecl vis tr id kt vt slot) tops /\
  supported_declaration_header tops (HashMapDecl vis tr id kt vt slot) ==>
  supported_place_root tops (NONE,id) /\
  build_hashmap_info tops (NONE,id) = SOME (tr,kt,vt)
Proof
  strip_tac >> drule_all getter_hashmap_member_lookup >>
  drule_all getter_hashmap_excludes_variable >>
  drule_all build_hashmap_info_hashmap >>
  Cases_on `slot` >> gvs[supported_place_root_def, supported_declaration_header_def]
QED

Triviality checked_single_vtype_ok:
  check_contract mode am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\
  FLOOKUP art.cta_toplevel_vtypes k = SOME vt ==>
  checker_vtype_ok tops k vt
Proof
  strip_tac >> drule checked_single_vtype_keys >>
  drule check_contract_nonsig_maps >> rpt strip_tac >>
  gvs[FLOOKUP_DRESTRICT_SOME] >> drule single_module_vtypes_sound >>
  rpt strip_tac >> gvs[] >>
  drule_all checked_single_header >> drule_all checked_single_decl_any >>
  rpt strip_tac
  >- (drule_all checker_variable_decl_facts >> Cases_on `mut` >>
      gvs[checker_vtype_ok_def, check_toplevel_decl_def, type_env_all_modules_def,
          FUNION_FEMPTY_2, GSYM type_env_def]) >>
  drule_all checker_hashmap_decl_facts >>
  gvs[checker_vtype_ok_def, check_toplevel_decl_def, check_value_type_def,
      type_env_all_modules_def, FUNION_FEMPTY_2, GSYM type_env_def]
QED

Triviality checked_single_fn_sig_ret:
  check_contract mode layouts addr [(NONE, tops)] = SOME art /\
  FLOOKUP art.cta_fn_sigs k = SOME sig ==>
  sig.ret_ty = NoneT \/ assignable_type (type_env tops) sig.ret_ty
Proof
  strip_tac >> drule check_contract_artifact_fields >> strip_tac >>
  gvs[FLOOKUP_DRESTRICT_SOME] >> PairCases_on `k` >>
  drule_all build_contract_type_artifact_fn_sigs_declared_sound >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_all checked_single_decl_any >>
  simp[check_toplevel_decl_def, type_env_all_modules_def, FUNION_FEMPTY_2,
       GSYM type_env_def]
QED

Triviality checked_runtime_fn_sig_internal:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  FLOOKUP art.cta_fn_sigs k = SOME sig ==>
  IS_SOME (supported_function_decl tops k Internal)
Proof
  strip_tac >> drule check_contract_artifact_fields >> strip_tac >>
  gvs[FLOOKUP_DRESTRICT_SOME] >> PairCases_on `k` >>
  drule_all build_contract_type_artifact_fn_sigs_declared_sound >>
  strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `vis` >> gvs[include_fn_sig_def] >>
  metis_tac[supported_function_decl_internal_MEM]
QED

Triviality checked_single_event_fields:
  check_contract mode layouts addr [(NONE, tops)] = SOME art /\
  FLOOKUP art.cta_event_fields k = SOME fields ==>
  supported_event_fields tops k = SOME fields
Proof
  strip_tac >> drule check_contract_runtime_namespaces >>
  simp[contract_namespaces_ok_def, contract_keys_def] >> strip_tac >>
  qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
  simp[check_contract_def, live_artifact_def] >> strip_tac >> gvs[] >>
  PairCases_on `k` >> drule single_module_event_fields >> strip_tac >> gvs[] >>
  irule supported_event_fields_event_keys >> simp[]
QED

Triviality checked_single_assignable:
  check_contract mode am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\
  FLOOKUP art.cta_bare_global_assignable k = SOME ty ==>
  FLOOKUP art.cta_bare_globals k = SOME ty /\ supported_place_root tops k /\
  supported_immutable_type tops k = SOME ty
Proof
  strip_tac >>
  `contract_namespaces_ok mode [(NONE, tops)] /\
   contract_namespaces_ok F [(NONE, tops)]`
    by metis_tac[check_contract_artifact_fields, check_contract_runtime_namespaces] >>
  drule checked_single_vtype_keys >> drule check_contract_nonsig_maps >>
  rpt strip_tac >> PairCases_on `k` >> gvs[] >>
  drule_all build_contract_type_artifact_bare_global_assignable_sound >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_all checked_single_header >> strip_tac >>
  drule_all checker_variable_decl_facts >> strip_tac >> fs[] >>
  irule build_contract_type_artifact_bare_globals_complete >> simp[] >>
  metis_tac[]
QED

Triviality checked_single_storage_value:
  check_contract mode am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\
  FLOOKUP art.cta_bare_globals k = NONE /\
  FLOOKUP art.cta_toplevel_vtypes k = SOME (Type ty) ==>
  supported_storage_value tops k ty
Proof
  strip_tac >>
  `contract_namespaces_ok F [(NONE, tops)]`
    by metis_tac[check_contract_runtime_namespaces] >>
  `ALOOKUP [(NONE, tops)] (NONE:num option) = SOME tops` by simp[] >>
  drule checked_single_vtype_keys >> drule check_contract_nonsig_maps >>
  rpt strip_tac >> gvs[FLOOKUP_DRESTRICT_SOME] >>
  drule single_module_vtypes_sound >> strip_tac >> gvs[] >>
  drule_all checked_single_header >> strip_tac >>
  drule_all checker_variable_decl_facts >> strip_tac >>
  Cases_on `mut` >> gvs[] >>
  drule build_contract_type_artifact_bare_globals_complete >>
  simp[PULL_EXISTS] >> disch_then drule >> simp[]
QED

Triviality checked_base_env_ok:
  check_contract mode am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\
  env.type_defs = type_env tops /\ env.var_types = FEMPTY /\
  env.toplevel_vtypes = art.cta_toplevel_vtypes /\
  env.bare_globals = art.cta_bare_globals /\
  env.event_fields = art.cta_event_fields /\
  (!k sig. FLOOKUP env.fn_sigs k = SOME sig ==>
     FLOOKUP art.cta_fn_sigs k = SOME sig /\
     IS_SOME (supported_function_decl tops k Internal)) /\
  (!k ty. FLOOKUP env.bare_global_assignable k = SOME ty ==>
     FLOOKUP art.cta_bare_global_assignable k = SOME ty) ==>
  checker_env_ok tops env /\ checker_stmt_env_ok tops env
Proof
  strip_tac >> simp[checker_env_ok_def, checker_stmt_env_ok_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >~ [`MEM (StructDecl _ _) _`]
  >- (drule_all checked_single_decl_any >>
      simp[check_toplevel_decl_def, type_env_all_modules_def, FUNION_FEMPTY_2,
           GSYM type_env_def, EVERY_MEM, FORALL_PROD] >> metis_tac[])
  >~ [`checker_vtype_ok`] >- metis_tac[checked_single_vtype_ok]
  >~ [`sig.ret_ty`] >- (res_tac >> metis_tac[checked_single_fn_sig_ret])
  >~ [`supported_immutable_type`]
  >- (res_tac >> metis_tac[checked_single_assignable])
  >~ [`supported_storage_value`] >- metis_tac[checked_single_storage_value]
  >~ [`FLOOKUP _ _ = SOME (Type _)`] >- metis_tac[checked_bare_global_vtype] >>
  metis_tac[checked_single_event_fields]
QED

Triviality checker_envs_foldl_extend:
  !args env. checker_env_ok tops env /\ checker_stmt_env_ok tops env /\
    EVERY (\(_,ty). assignable_type (type_env tops) ty) args ==>
    checker_env_ok tops (FOLDL (\env (id,ty). extend_local env id ty b) env args) /\
    checker_stmt_env_ok tops (FOLDL (\env (id,ty). extend_local env id ty b) env args)
Proof
  Induct >> simp[] >> Cases >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >>
  simp[checker_stmt_env_ok_extend_local] >>
  irule checker_env_ok_extend_local >> simp[]
QED

Triviality foldl_extend_local_fn_sigs:
  !args env. (FOLDL (\env (id,ty). extend_local env id ty b) env args) with fn_sigs := X =
    FOLDL (\env (id,ty). extend_local env id ty b) (env with fn_sigs := X) args
Proof
  Induct >> simp[] >> Cases >> simp[extend_local_def]
QED

(* The entry environment of a body, with its signatures and assignable
   immutables cut to fs and asg. *)
Triviality checked_entry_env_ok:
  check_contract mode am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\
  EVERY (\(_,ty). assignable_type (type_env tops) ty) args /\
  (!k sig. FLOOKUP fs k = SOME sig ==>
     FLOOKUP art.cta_fn_sigs k = SOME sig /\
     IS_SOME (supported_function_decl tops k Internal)) /\
  (!k ty. FLOOKUP asg k = SOME ty ==>
     FLOOKUP art.cta_bare_global_assignable k = SOME ty) ==>
  checker_env_ok tops (FOLDL (\env (id,ty). extend_local env id ty b)
    (artifact_env art [(NONE, tops)] NONE with
       <| fn_sigs := fs; bare_global_assignable := asg |>) args) /\
  checker_stmt_env_ok tops (FOLDL (\env (id,ty). extend_local env id ty b)
    (artifact_env art [(NONE, tops)] NONE with
       <| fn_sigs := fs; bare_global_assignable := asg |>) args)
Proof
  strip_tac >> irule checker_envs_foldl_extend >> simp[] >>
  irule checked_base_env_ok >>
  simp[artifact_env_def, type_env_all_modules_def, FUNION_FEMPTY_2,
       GSYM type_env_def] >>
  qexistsl [`am`, `art`, `mode`, `tx`] >> simp[] >> metis_tac[]
QED

Triviality checked_runtime_entry_env_ok:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\
  EVERY (\(_,ty). assignable_type (type_env tops) ty) args ==>
  checker_env_ok tops (function_entry_env art [(NONE, tops)] NONE vis args) /\
  checker_stmt_env_ok tops (function_entry_env art [(NONE, tops)] NONE vis args)
Proof
  strip_tac >>
  `function_entry_env art [(NONE, tops)] NONE vis args =
   FOLDL (\env (id,ty). extend_local env id ty (vis = Internal))
     (artifact_env art [(NONE, tops)] NONE with
        <| fn_sigs := art.cta_fn_sigs;
           bare_global_assignable := art.cta_bare_global_assignable |>) args`
    by simp[function_entry_env_def, artifact_env_def] >>
  pop_assum SUBST1_TAC >> irule checked_entry_env_ok >> simp[] >>
  metis_tac[checked_runtime_fn_sig_internal]
QED

(* A body the checker types, in an environment meeting the bridge
   invariant whose locals are the arguments, is in the body gate. *)
Triviality checked_body_supported:
  checker_env_ok tops env /\ checker_stmt_env_ok tops env /\
  FDOM env.var_types = set (MAP FST args) /\ ALL_DISTINCT (MAP FST args) /\
  type_stmts env ret fbody = SOME env' /\
  IS_SOME (type_stmts env ret
    (subst_consts_stmts (module_consts_env tops []) fbody)) /\
  custom_errors_stmts_ok [(NONE, tops)] fbody ==>
  supported_function_body tops (vis:function_visibility) args fbody
Proof
  strip_tac >> drule (cj 2 type_stmt_bindings_fresh) >> strip_tac >>
  `supported_stmts tops (args ++ supported_stmts_bindings T fbody ++
                         supported_stmts_bindings F fbody) fbody` by
    (drule_then irule (cj 2 type_stmts_supported) >> rw[SUBSET_DEF] >> fs[]) >>
  simp[supported_function_body_def] >> gvs[EVERY_MEM] >>
  metis_tac[supported_stmts_body_safe]
QED

Theorem check_contract_supported_function_body:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy ==>
  supported_function_body tops vis args fbody
Proof
  strip_tac >> drule_all check_contract_single_body >>
  simp[check_function_body_def, params_ok_def, consts_env_mods_singleton,
       subst_consts_mods_singleton, type_env_all_modules_def, FUNION_FEMPTY_2,
       GSYM type_env_def, optionTheory.IS_SOME_EXISTS] >>
  strip_tac >> drule_all checked_runtime_entry_env_ok >>
  disch_then (qspec_then `vis` strip_assume_tac) >>
  irule checked_body_supported >>
  qpat_assum `type_stmts _ _ fbody = _` (irule_at Any) >>
  fs[function_entry_env_var_types_fdom]
QED

(* ===== Defaults and constants ===== *)

(* Defaults and constant initialisers type in the artifact environment, whose
   storage entries need layouts_agree to be in the gate. They read only
   constants and immutables, so they type in the environment cut down to
   those, which is in the gate unconditionally. *)

Triviality checker_const_imm_header:
  check_toplevel_decl [(NONE, tops)] art NONE (VariableDecl vis mut id ty init) /\
  (mut = Immutable \/ ?e. mut = Constant e) ==>
  supported_declaration_header tops (VariableDecl vis mut id ty init)
Proof
  rpt strip_tac >> gvs[] >> drule checker_supported_declaration_header >> simp[]
QED

Triviality checked_bare_global_vtype_ok:
  check_contract mode layouts addr [(NONE, tops)] = SOME art /\
  FLOOKUP art.cta_bare_globals k = SOME ty ==>
  checker_vtype_ok tops k (Type ty)
Proof
  strip_tac >> drule checked_single_vtype_keys >> strip_tac >>
  `contract_namespaces_ok F [(NONE, tops)]`
    by metis_tac[check_contract_runtime_namespaces] >>
  drule check_contract_nonsig_maps >> strip_tac >> PairCases_on `k` >>
  gvs[] >> drule_all build_contract_type_artifact_bare_globals_sound >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_all checked_single_decl_any >> strip_tac >>
  drule checker_const_imm_header >> simp[] >> strip_tac >>
  drule_all checker_variable_decl_facts >>
  gvs[checker_vtype_ok_def, check_toplevel_decl_def, type_env_all_modules_def,
      FUNION_FEMPTY_2, GSYM type_env_def]
QED

Triviality checked_declared_bare_global:
  check_contract mode layouts addr [(NONE, tops)] = SOME art /\
  (declared_constant [(NONE, tops)] src id \/
   declared_immutable [(NONE, tops)] src id) ==>
  (src,id) IN FDOM art.cta_bare_globals
Proof
  strip_tac >>
  `contract_namespaces_ok F [(NONE, tops)]`
    by metis_tac[check_contract_runtime_namespaces] >>
  drule check_contract_nonsig_maps >> strip_tac >>
  gvs[declared_constant_def, declared_immutable_def] >>
  drule build_contract_type_artifact_bare_globals_complete >>
  simp[FLOOKUP_DEF] >> metis_tac[]
QED

Triviality checked_const_env_ok:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  checker_env_ok tops (artifact_env art [(NONE, tops)] NONE with
    toplevel_vtypes :=
      DRESTRICT (artifact_env art [(NONE, tops)] NONE).toplevel_vtypes
        (FDOM art.cta_bare_globals))
Proof
  strip_tac >>
  simp[checker_env_ok_def, artifact_env_def, type_env_all_modules_def,
       FUNION_FEMPTY_2, GSYM type_env_def, FLOOKUP_DRESTRICT] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >~ [`MEM (StructDecl _ _) _`]
  >- (drule_all checked_single_decl_any >>
      simp[check_toplevel_decl_def, type_env_all_modules_def, FUNION_FEMPTY_2,
           GSYM type_env_def, EVERY_MEM, FORALL_PROD] >> metis_tac[])
  >~ [`checker_vtype_ok`]
  >- (gvs[AllCaseEqs()] >>
      `?ty. FLOOKUP art.cta_bare_globals k = SOME ty` by gvs[FLOOKUP_DEF] >>
      drule_all checked_bare_global_vtype >> strip_tac >> gvs[] >>
      metis_tac[checked_bare_global_vtype_ok])
  >~ [`sig.ret_ty`]
  >- metis_tac[checked_single_fn_sig_ret, checked_runtime_fn_sig_internal] >>
  `k IN FDOM art.cta_bare_globals` by gvs[FLOOKUP_DEF] >>
  simp[] >> metis_tac[checked_bare_global_vtype]
QED

Triviality checked_main_typed_env:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  main_typed_env (artifact_env art [(NONE, tops)] NONE with
    toplevel_vtypes :=
      DRESTRICT (artifact_env art [(NONE, tops)] NONE).toplevel_vtypes
        (FDOM art.cta_bare_globals))
Proof
  rw[main_typed_env_def, artifact_env_def, type_env_all_modules_def,
     FUNION_FEMPTY_2, GSYM type_env_def, FLOOKUP_DRESTRICT]
  >- metis_tac[type_env_key_main] >>
  gvs[AllCaseEqs()] >>
  `?ty. FLOOKUP art.cta_bare_globals k = SOME ty` by gvs[FLOOKUP_DEF] >>
  drule_all checked_bare_global_vtype >> strip_tac >> gvs[] >>
  drule_all checked_bare_global_vtype_ok >> rw[checker_vtype_ok_def] >>
  irule well_formed_type_namespace >> qexists_tac `type_env tops` >>
  simp[assignable_type_well_formed] >> metis_tac[type_env_key_main]
QED

Triviality checked_const_typed_supported:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  well_typed_expr (artifact_env art [(NONE, tops)] NONE) e /\
  runtime_constant_expr [(NONE, tops)] e ==>
  supported_pure_expr tops e /\ ~supported_expr_exists expr_nonmain_type_root e
Proof
  strip_tac >>
  `!src id. declared_constant [(NONE, tops)] src id \/
            declared_immutable [(NONE, tops)] src id ==>
            (src,id) IN FDOM art.cta_bare_globals`
    by metis_tac[checked_declared_bare_global] >>
  `well_typed_expr (artifact_env art [(NONE, tops)] NONE with
     toplevel_vtypes :=
       DRESTRICT (artifact_env art [(NONE, tops)] NONE).toplevel_vtypes
         (FDOM art.cta_bare_globals)) e`
    by (drule (cj 1 well_typed_vtypes_restrict) >> simp[]) >>
  qpat_x_assum `well_typed_expr (artifact_env _ _ _) _` kall_tac >>
  drule checked_const_env_ok >> drule checked_main_typed_env >> rpt strip_tac >>
  drule_all (cj 1 well_typed_expr_supported) >>
  drule_all (cj 1 runtime_constant_main_types) >> simp[]
QED

Theorem check_contract_supported_defaults:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy ==>
  EVERY (supported_default_expression tops) dflts /\
  supported_pure_exprs tops dflts
Proof
  strip_tac >> drule_all check_contract_single_body >>
  simp[check_function_body_def, defaults_env_function_entry_env] >> strip_tac >>
  `!e. MEM e dflts ==>
     supported_pure_expr tops e /\ ~supported_expr_exists expr_nonmain_type_root e`
    by (rpt gen_tac >> strip_tac >> irule checked_const_typed_supported >>
        fs[EVERY_MEM, frame_well_typed_exprs_every] >> metis_tac[]) >>
  simp[supported_pure_exprs_every, EVERY_MEM, supported_default_expression_def,
       supported_expr_def]
QED

Theorem check_contract_supported_consts:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  EVERY (supported_pure_expr tops o SND) (module_consts_env tops [])
Proof
  strip_tac >>
  irule (Q.INST [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`]
    check_contract_linked_supported_consts) >>
  metis_tac[ALOOKUP_def]
QED

Theorem check_contract_supported_declaration_bodies:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx ==>
  EVERY (supported_declaration_body tops) tops
Proof
  rw[EVERY_MEM] >> rename1 `MEM tl tops` >>
  Cases_on `tl` >> simp[supported_declaration_body_def] >>
  metis_tac[check_contract_supported_function_body,
            check_contract_supported_defaults]
QED

(* TOP-LEVEL *)
Theorem check_contract_supported_program:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx ==>
  supported_program tops
Proof
  metis_tac[supported_program_def, check_contract_supported_declaration_headers,
            check_contract_supported_declaration_names,
            check_contract_supported_internal_function_names,
            check_contract_supported_declaration_bodies,
            check_contract_supported_consts]
QED

(* ===== Deployment gate ===== *)

(* A constructor calls only internal functions: its own signature is the
   only other one in the deploy artifact, and calling it is a self-edge. *)
Triviality checked_deploy_callee_internal:
  check_contract T layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl Deploy mut nr rr name args dflts ret fbody) tops /\
  MEM c (int_calls_stmts fbody) /\ FLOOKUP art.cta_fn_sigs c = SOME sig ==>
  IS_SOME (supported_function_decl tops c Internal)
Proof
  strip_tac >> drule check_contract_artifact_fields >> strip_tac >>
  gvs[FLOOKUP_DRESTRICT_SOME] >> PairCases_on `c` >>
  drule_all build_contract_type_artifact_fn_sigs_declared_sound >>
  strip_tac >> gvs[] >> Cases_on `vis` >> gvs[include_fn_sig_def]
  >~ [`MEM (FunctionDecl Internal _ _ _ _ _ _ _ _) _`]
  >- metis_tac[supported_function_decl_internal_MEM] >>
  `MEM ((NONE,name),(NONE,c1)) (contract_call_edges [(NONE:num option, tops)])` by
    (irule contract_call_edges_function >> simp[function_int_calls_def] >>
     metis_tac[]) >>
  `name = c1` by (imp_res_tac checked_single_decl_any >>
                  gvs[check_toplevel_decl_def, function_header_ok_def]) >>
  gvs[] >> drule checked_no_self_call >>
  disch_then (qspec_then `(NONE,c1)` mp_tac) >> fs[]
QED

Triviality checked_deploy_calls_internal:
  check_contract T layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl Deploy mut nr rr name args dflts ret fbody) tops /\
  type_stmts (function_entry_env art [(NONE, tops)] NONE vis args) rt fbody =
    SOME env' ==>
  set (int_calls_stmts fbody) SUBSET
    {k | IS_SOME (supported_function_decl tops k Internal)}
Proof
  strip_tac >> drule (cj 2 type_stmt_int_calls_fn_sigs) >>
  rw[EVERY_MEM, SUBSET_DEF, function_entry_env_fn_sigs] >>
  metis_tac[checked_deploy_callee_internal, flookup_thm]
QED

(* Substituting constants adds no internal call. *)
Triviality checked_subst_int_calls:
  check_contract mode layouts addr [(NONE, tops)] = SOME art ==>
  int_calls_stmts (subst_consts_stmts (module_consts_env tops []) ss) =
  int_calls_stmts ss
Proof
  strip_tac >> irule (cj 2 subst_consts_stmt_int_calls) >> rpt strip_tac >>
  `ALOOKUP [(NONE, tops)] (NONE:num option) = SOME tops` by simp[] >>
  drule_all checked_module_consts_env_replacement_constant >>
  metis_tac[constant_expr_no_internal_calls]
QED

(* The entry environment with its signatures cut to the internal ones. *)
Triviality checked_deploy_entry_env_ok:
  check_contract T am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\
  EVERY (\(_,ty). assignable_type (type_env tops) ty) args ==>
  checker_env_ok tops (function_entry_env art [(NONE, tops)] NONE vis args with
    fn_sigs := DRESTRICT (function_entry_env art [(NONE, tops)] NONE vis args).fn_sigs
                 {k | IS_SOME (supported_function_decl tops k Internal)}) /\
  checker_stmt_env_ok tops (function_entry_env art [(NONE, tops)] NONE vis args with
    fn_sigs := DRESTRICT (function_entry_env art [(NONE, tops)] NONE vis args).fn_sigs
                 {k | IS_SOME (supported_function_decl tops k Internal)}) /\
  FDOM (function_entry_env art [(NONE, tops)] NONE vis args).var_types =
    set (MAP FST args)
Proof
  strip_tac >> simp[function_entry_env_fn_sigs, function_entry_env_var_types_fdom] >>
  `function_entry_env art [(NONE, tops)] NONE vis args with
     fn_sigs := DRESTRICT art.cta_fn_sigs
                  {k | IS_SOME (supported_function_decl tops k Internal)} =
   FOLDL (\env (id,ty). extend_local env id ty (vis = Internal))
     (artifact_env art [(NONE, tops)] NONE with
        <| fn_sigs := DRESTRICT art.cta_fn_sigs
                        {k | IS_SOME (supported_function_decl tops k Internal)};
           bare_global_assignable := art.cta_bare_global_assignable |>) args`
    by simp[function_entry_env_def, artifact_env_def, foldl_extend_local_fn_sigs] >>
  pop_assum SUBST1_TAC >> irule checked_entry_env_ok >>
  simp[FLOOKUP_DRESTRICT] >> metis_tac[]
QED

(* checked_body_supported, after cutting the signatures to a set holding
   every internal callee. *)
Triviality checked_body_supported_restrict:
  checker_env_ok tops (env with fn_sigs := DRESTRICT env.fn_sigs ks) /\
  checker_stmt_env_ok tops (env with fn_sigs := DRESTRICT env.fn_sigs ks) /\
  FDOM env.var_types = set (MAP FST args) /\
  set (int_calls_stmts fbody) SUBSET ks /\
  int_calls_stmts (subst_consts_stmts (module_consts_env tops []) fbody) =
    int_calls_stmts fbody /\
  ALL_DISTINCT (MAP FST args) /\
  type_stmts env ret fbody = SOME env' /\
  type_stmts env ret (subst_consts_stmts (module_consts_env tops []) fbody) =
    SOME env'' /\
  custom_errors_stmts_ok [(NONE, tops)] fbody ==>
  supported_function_body tops (vis:function_visibility) args fbody
Proof
  strip_tac >>
  `type_stmts (env with fn_sigs := DRESTRICT env.fn_sigs ks) ret fbody =
     SOME (env' with fn_sigs := DRESTRICT env'.fn_sigs ks) /\
   IS_SOME (type_stmts (env with fn_sigs := DRESTRICT env.fn_sigs ks) ret
     (subst_consts_stmts (module_consts_env tops []) fbody)) /\
   FDOM (env with fn_sigs := DRESTRICT env.fn_sigs ks).var_types =
     set (MAP FST args)` by fs[cj 2 type_stmt_fn_sigs_restrict] >>
  drule_all checked_body_supported >> simp[]
QED

Theorem check_contract_deploy_function_body:
  check_contract T am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\
  MEM (FunctionDecl Deploy mut nr rr name args dflts ret fbody) tops ==>
  EVERY (supported_value_type tops o SND) args /\
  supported_function_body tops Deploy args fbody
Proof
  strip_tac >>
  `ALOOKUP [(NONE, tops)] (NONE:num option) = SOME tops` by simp[] >>
  drule_all check_contract_deploy_function_body_MEM >>
  simp[check_function_body_def, params_ok_def, consts_env_mods_singleton,
       subst_consts_mods_singleton, type_env_all_modules_def, FUNION_FEMPTY_2,
       GSYM type_env_def, optionTheory.IS_SOME_EXISTS] >>
  strip_tac >>
  drule_all checked_deploy_calls_internal >> strip_tac >>
  drule_all checked_deploy_entry_env_ok >>
  disch_then (qspec_then `Deploy` strip_assume_tac) >>
  drule checked_subst_int_calls >> disch_then (qspec_then `fbody` assume_tac) >>
  drule_all checked_body_supported_restrict >>
  disch_then (qspec_then `Deploy` assume_tac) >> simp[] >>
  fs[EVERY_MEM, FORALL_PROD, supported_value_type_def] >>
  metis_tac[assignable_type_supported_place]
QED

(* TOP-LEVEL *)
Theorem check_contract_supported_program_deploy:
  check_contract T am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx ==>
  supported_program_deploy tops
Proof
  rw[supported_program_deploy_def, EVERY_MEM] >> rename1 `MEM tl tops` >>
  Cases_on `tl` >> simp[supported_deploy_declaration_def] >>
  rename1 `FunctionDecl vis` >> Cases_on `vis` >> simp[] >>
  metis_tac[check_contract_deploy_function_body]
QED

(* ===== The gate from the top theorems' typing premises ===== *)

(* TOP-LEVEL *)
Theorem source_typing_ok_supported_program:
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx ==>
  supported_program tops
Proof
  rw[source_typing_ok_def, source_deployment_rel_def] >>
  metis_tac[check_contract_supported_program]
QED

(* TOP-LEVEL *)
Theorem deploy_typing_ok_supported_programs:
  deploy_typing_ok tops am tx /\ layouts_agree tops am tx ==>
  supported_program tops /\ supported_program_deploy tops
Proof
  rw[deploy_typing_ok_constants_ready] >>
  metis_tac[check_contract_supported_program,
            check_contract_supported_program_deploy]
QED
