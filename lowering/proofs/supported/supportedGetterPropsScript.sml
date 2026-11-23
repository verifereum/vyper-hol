(* Supported bodies and parameter types for the selected external entry,
   including synthesized getters of admitted public declarations. *)
Theory supportedGetterProps
Ancestors
  supportedProgram supportedDecls supportedExprForms supportedExprs
  supportedNames supportedTypes supportedPlaceAssignable supportedStmts supportedStmtTraverse supportedExprTraverse
  e2eDefs vyperTypeContractGetter vyperTypeContractContext bodyStorageMetadata
  compileEnv exprLowering vyperGetter vyperInterpreter list pair finite_map
  placeTypingBuildProps bodyStorageCases constSubstCorrect constSubst constSubstMods
  constSubstStmtsPreserve
  vyperTypeContractStaticMaps vyperTypeConstantFold vyperTypeSystem vyperAST
  vyperValue vyperContext compileVyper alist vyperTypeContract vyperTypeCallGraph

val _ = Parse.hide "body";

Theorem supported_nested_leaf_mono[local]:
  !leaf fuel tops ty.
    supported_nested_type leaf fuel tops ty ==>
    !leaf'. (!t. leaf t ==> leaf' t) ==>
      supported_nested_type leaf' fuel tops ty
Proof
  recInduct supported_nested_type_ind >> rpt strip_tac >>
  qpat_x_assum `supported_nested_type leaf fuel tops ty` mp_tac >>
  once_rewrite_tac[supported_nested_type_def] >>
  Cases_on `ty` >> gvs[AllCaseEqs(), EVERY_MEM] >>
  rpt strip_tac >> simp[]
  >~ [`ArrayT elem bd`] >- (Cases_on `bd` >> gvs[] >> metis_tac[]) >>
  Cases_on `supported_struct_fields tops p` >> gvs[] >> metis_tac[]
QED

Theorem supported_storage_place[local]:
  supported_storage_type tops ty ==> supported_place_type tops ty
Proof
  simp[supported_storage_type_def, supported_place_type_def] >> strip_tac >>
  drule supported_nested_leaf_mono >> disch_then irule >>
  metis_tac[supported_full_word_is_word, supported_scalar_type_def]
QED

Theorem supported_place_array_element:
  supported_place_type tops (ArrayT ty bd) ==> supported_place_type tops ty
Proof
  Cases_on `bd` >> simp[supported_place_type_def] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [supported_nested_type_def])) >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def]
QED

Theorem supported_getter_subscript[local]:
  !tops vt e kt vn.
  supported_place_expr tops e /\ supported_subscript_place tops e /\
  ~qualified_place_root e /\
  int_calls_expr e = [] /\
  supported_place_type tops kt /\
  (supported_place_info tops e = MapPT kt vt \/
   ?bt bd. supported_place_info tops e = ValPT (ArrayT bt bd) /\ vt = Type bt) ==>
  supported_place_expr tops (Subscript (getter_vtype_annotation vt) e (Name kt vn)) /\
  int_calls_expr (Subscript (getter_vtype_annotation vt) e (Name kt vn)) = [] /\
  supported_place_info tops (Subscript (getter_vtype_annotation vt) e (Name kt vn)) =
    value_type_place vt
Proof
  Cases_on `vt` >> rpt strip_tac >>
  gvs[getter_vtype_annotation_def, supported_pure_expr_def,
      supported_subscript_place_def,
      int_calls_expr_def, supported_place_info_def, place_type_def, value_type_place_def,
      supported_hashmap_value_def] >>
  metis_tac[supported_storage_place, supported_place_array_element]
QED

Theorem supported_build_getter_path[local]:
  !e kt vt n. !args ret exp tops.
  build_getter e kt vt n = (args,ret,exp) /\
  supported_place_expr tops e /\ supported_subscript_place tops e /\
  ~qualified_place_root e /\
  int_calls_expr e = [] /\
  supported_place_type tops kt /\
  (supported_place_info tops e = MapPT kt vt \/
   ?bt bd. supported_place_info tops e = ValPT (ArrayT bt bd) /\ vt = Type bt) ==>
  supported_pure_expr tops exp /\
  EVERY (supported_place_type tops o SND) args /\
  int_calls_expr exp = []
Proof
  recInduct build_getter_ind >> conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `build_getter e kt v n = _` (fn th =>
    case strip_comb (lhs (concl th)) of
      (_, [_,_,vt,_]) =>
        mp_tac (SPECL [``tops:toplevel list``, vt, ``e:expr``, ``kt:type``,
          ``num_to_dec_string n``] supported_getter_subscript)
    | _ => NO_TAC) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [build_getter_def]) >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  all_tac
  >>~- ([`(\(a,b,c). ((toString n,kt)::a,b,c))
                 (build_getter _ _ (Type _) _) = _`],
    pairarg_tac >> gvs[] >> rename1 `is_ArrayT elemty` >> Cases_on `elemty` >>
    gvs[vyperASTTheory.is_ArrayT_def, vyperASTTheory.ArrayT_type_def,
        getter_vtype_annotation_def, value_type_place_def,
        supported_hashmap_value_def] >>
    rename1 `Subscript (ArrayT elem bound) _ _` >>
    `supported_place_type tops (ArrayT elem bound)` by
      (fs[supported_subscript_place_def, supported_hashmap_value_def] >>
       metis_tac[supported_storage_place, supported_place_array_element]) >>
    `supported_place_type tops (BaseT (UintT 256))` by
      simp[supported_place_type_def, Once supported_nested_type_def,
           supported_scalar_type_def, supported_word_type_def, supported_int_width_def] >>
    first_x_assum drule >>
    simp[supported_subscript_place_def, supported_hashmap_value_def,
         qualified_place_root_def] >>
    strip_tac >> simp[]) >>
  all_tac
  >>~- ([`~is_ArrayT ty`],
    gvs[getter_vtype_annotation_def, supported_hashmap_value_def] >>
    gvs[supported_pure_expr_def, supported_storage_place,
        supported_subscript_place_def] >>
    fs[supported_hashmap_value_def] >>
    metis_tac[supported_storage_place, supported_place_array_element]) >>
  pairarg_tac >> gvs[getter_vtype_annotation_def, value_type_place_def,
                     supported_hashmap_value_def, supported_subscript_place_def] >>
  `supported_place_type tops typ` by
    fs[supported_place_type_def, Once supported_nested_type_def,
       supported_hashmap_key_type_def] >>
  first_x_assum (qspec_then `tops` mp_tac) >>
  simp[supported_subscript_place_def, qualified_place_root_def]
QED

Theorem getter_variable_member_lookup[local]:
  !ts vis mut id ty slot.
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) ts)) /\
  MEM (VariableDecl vis mut id ty slot) ts ==>
  supported_variable_decl ts ((NONE:num option),id) = SOME (vis,mut,ty,slot)
Proof
  Induct >- simp[] >> Cases >>
  simp[supported_variable_decl_def, vyperTypeContractTheory.toplevel_vtype_keys_toplevel_def,
       ALL_DISTINCT_APPEND] >> rpt strip_tac >> gvs[] >>
  gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  qpat_x_assum `!y. _` (qspec_then `VariableDecl vis mut id ty slot` mp_tac) >>
  simp[vyperTypeContractTheory.toplevel_vtype_keys_toplevel_def] >>
  strip_tac >> simp[] >> metis_tac[]
QED

Theorem getter_hashmap_member_lookup:
  !ts vis tr id kt vt slot.
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) ts)) /\
  MEM (HashMapDecl vis tr id kt vt slot) ts ==>
  supported_hashmap_decl ts ((NONE:num option),id) = SOME (vis,tr,kt,vt,slot)
Proof
  Induct >- simp[] >> Cases >>
  simp[supported_variable_decl_def, supported_hashmap_decl_def,
       vyperTypeContractTheory.toplevel_vtype_keys_toplevel_def,
       ALL_DISTINCT_APPEND] >> rpt strip_tac >> gvs[] >>
  gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  qpat_x_assum `!y. _` (qspec_then `HashMapDecl vis tr id kt vt slot` mp_tac) >>
  simp[vyperTypeContractTheory.toplevel_vtype_keys_toplevel_def] >>
  strip_tac >> simp[] >> metis_tac[]
QED

Theorem getter_variable_key_absent[local]:
  ~MEM (NONE,id) (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) ts)) ==>
  supported_variable_decl ts ((NONE:num option),id) = NONE
Proof
  strip_tac >> Cases_on `supported_variable_decl ts ((NONE:num option),id)` >> simp[] >>
  PairCases_on `x` >> drule supported_variable_decl_mem >> strip_tac >>
  drule vyperTypeContractStaticMapsTheory.module_toplevel_vtype_key_MEM_Variable >>
  disch_then (qspec_then `NONE` mp_tac) >> simp[]
QED

Theorem getter_hashmap_excludes_variable:
  !ts vis tr id kt vt slot.
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) ts)) /\
  MEM (HashMapDecl vis tr id kt vt slot) ts ==>
  supported_variable_decl ts ((NONE:num option),id) = NONE
Proof
  Induct >- simp[] >> Cases >>
  simp[supported_variable_decl_def,
       vyperTypeContractTheory.toplevel_vtype_keys_toplevel_def,
       ALL_DISTINCT_APPEND] >> rpt strip_tac >> gvs[] >>
  imp_res_tac getter_variable_key_absent >> gvs[] >>
  gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[vyperTypeContractTheory.toplevel_vtype_keys_toplevel_def, listTheory.MEM]
QED

Theorem supported_getter_return_body[local]:
  ALL_DISTINCT (MAP FST args) /\ supported_pure_expr tops exp /\
  int_calls_expr exp = [] ==>
  supported_function_body tops External args [Return (SOME exp)]
Proof
  simp[supported_function_body_def, supported_function_bindings_def,
       supported_stmt_bindings_def, supported_stmt_def, supported_expr_def,
       body_stmts_safe_iff, supported_stmt_expr_exists_def, int_calls_stmt_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       GSYM expr_has_evm_run_def, int_calls_expr_def] >>
  metis_tac[supported_expr_no_evm_run, supported_expr_def]
QED

Theorem checked_constant_replacement_lookup:
  source_typing_ok tops am tx /\
  MEM (VariableDecl vis (Constant init) name ty slot) tops ==>
  ?r. ALOOKUP (module_consts_env tops []) name = SOME r /\ expr_type r = ty
Proof
  strip_tac >> fs[source_typing_ok_def] >>
  drule checked_module_consts_env_agrees >>
  simp[] >> disch_then drule >> strip_tac >>
  `MEM name (MAP FST (module_consts_env tops []))` by
    (fs[const_prefix_syntax_def] >> metis_tac[const_decl_names_MEM]) >>
  `?r. ALOOKUP (module_consts_env tops []) name = SOME r` by
    (Cases_on `ALOOKUP (module_consts_env tops []) name` >>
     gvs[ALOOKUP_NONE]) >>
  pop_assum strip_assume_tac >>
  drule checked_module_consts_env_replacement_annotation >>
  simp[] >> disch_then drule >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     qexists_tac `[(NONE,tops)]` >>
     simp[] >> metis_tac[check_contract_runtime_namespaces]) >>
  imp_res_tac getter_variable_member_lookup >> gvs[] >> metis_tac[]
QED

Theorem closed_constant_type_place[local]:
  !e env.
    constant_expr [(NONE,tops)] e /\ const_local_refs e = [] ==>
    type_place_expr env e = NONE /\
    supported_place_info tops e = ValPT (expr_type e) /\
    ~qualified_place_root e
Proof
  completeInduct_on `expr_size e` >>
  gen_tac >> disch_tac >> gen_tac >> strip_tac >>
  Cases_on `e` >>
  gvs[constant_expr_def, const_local_refs_def, well_typed_expr_def,
      supported_place_info_def, place_type_def, expr_type_def, qualified_place_root_def]
  >- (PairCases_on `p` >> Cases_on `p0` >>
      gvs[constant_expr_def, const_local_refs_def, declared_constant_def]) >>
  qpat_x_assum `!m. _` (qspec_then `expr_size e'` mp_tac) >>
  simp[expr_size_def, supported_place_info_def] >>
  disch_then (qspec_then `e'` mp_tac) >> simp[] >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  Cases_on `well_typed_expr env e0` >> gvs[]
QED

Theorem array_constant_supported_place[local]:
  constant_expr [(NONE,tops)] e /\ const_local_refs e = [] /\
  well_typed_expr env e /\ supported_pure_expr tops e /\
  expr_type e = ArrayT ty bd ==>
  supported_place_expr tops e /\ supported_place_type tops (ArrayT ty bd)
Proof
  map_every qid_spec_tac [`bd`, `ty`, `env`] >>
  completeInduct_on `expr_size e` >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  Cases_on `e` >>
  all_tac >>~- ([`constant_expr _ (TopLevelName _ p)`],
    PairCases_on `p` >> Cases_on `p0` >>
    gvs[constant_expr_def, const_local_refs_def, declared_constant_def]) >>
  gvs[constant_expr_def, const_local_refs_def, supported_pure_expr_def,
      well_typed_expr_def, expr_type_def] >> rpt strip_tac >> gvs[]
  >- (Cases_on `l` >> gvs[well_typed_literal_def])
  >- (Cases_on `b` >>
      gvs[constant_builtin_def, well_typed_builtin_app_def,
          supported_builtin_form_def, supported_literal_elements_def,
          is_numeric_type_def, is_int_type_def] >>
      all_tac >>~- ([`well_typed_binop _ op`],
        Cases_on `op` >>
        gvs[constant_binop_def, well_typed_binop_def, is_numeric_type_def,
            is_int_type_def, is_flag_type_def, is_bool_type_def]) >>
      all_tac >>~- ([`well_typed_builtin_app _ (MakeArray _ _) _`],
        Cases_on `o'` >> Cases_on `b'` >> gvs[well_typed_builtin_app_def]) >>
      rename1 `const_local_exprs [arg] = []` >>
      qpat_x_assum `!m. _` (qspec_then `expr_size arg` mp_tac) >>
      (impl_tac >- decide_tac) >>
      disch_then (qspec_then `arg` mp_tac) >> simp[] >>
      disch_then (qspecl_then [`env`, `ty`, `bd`] mp_tac) >>
      gvs[const_local_refs_def, well_typed_expr_def, supported_pure_expr_def]) >>
  Cases_on `t0` >> Cases_on `l` >>
  gvs[constant_type_builtin_def, type_builtin_result_ok_def,
      well_typed_type_builtin_args_def, supported_type_builtin_form_def,
      supported_value_type_def, supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def, supported_numeric_type_def] >>
  Cases_on `bd` >> gvs[] >>
  simp[supported_place_type_def, Once supported_nested_type_def,
       supported_scalar_type_def, supported_word_type_def, supported_string_type_def] >>
  simp[Once supported_nested_type_def, supported_scalar_type_def]
QED

Theorem build_getter_subst:
  !e kt vt n args ret exp.
    build_getter e kt vt n = (args,ret,exp) ==>
    !E. build_getter (subst_consts_expr E e) kt vt n =
      (args,ret,subst_consts_expr E exp)
Proof
  recInduct build_getter_ind >> conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [build_getter_def]) >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[Once build_getter_def, subst_consts_expr_def] >>
  gvs[subst_consts_expr_def]
QED

Theorem public_constant_getter_body_support[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  MEM (VariableDecl (Public vis) (Constant init) name ty slot) tops /\
  external_getter_tuple NONE (VariableDecl (Public vis) (Constant init) name ty slot) =
    SOME (mut,nr,args,[],ret,fbody) /\ ALL_DISTINCT (MAP FST args) ==>
  supported_function_body tops External args
    (subst_consts_stmts (module_consts_env tops []) fbody)
Proof
  strip_tac >>
  drule_all checked_constant_replacement_lookup >> strip_tac >>
  drule_all supported_program_const_replacement >> strip_tac >>
  `EVERY (no_neg_exp_expr o SND) (module_consts_env tops [])` by
    (Cases_on `classify_functions tops` >>
     rename1 `classify_functions tops = (exts,tail)` >> PairCases_on `tail` >>
     metis_tac[lower_vyper_runtime_unit_consts_guard]) >>
  `?art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
    well_typed_expr (artifact_env art [(NONE,tops)] NONE) r /\
    constant_expr [(NONE,tops)] r /\ const_local_refs r = []` by
    (fs[source_typing_ok_def] >>
     `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
     drule_all checked_module_consts_env_replacement_typed >>
     drule_all checked_module_consts_env_replacement >>
     metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `int_calls_expr r = []` by metis_tac[cj 1 constant_expr_no_internal_calls] >>
  qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
  simp[external_getter_tuple_def, getter_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[subst_consts_stmt_def, subst_consts_expr_def] >>
  all_tac >>~- ([`supported_function_body tops External [] [Return (SOME r)]`],
    irule supported_getter_return_body >> simp[]) >>
  rpt (pairarg_tac >> gvs[subst_consts_stmt_def, subst_consts_expr_def]) >>
  Cases_on `expr_type r` >>
  gvs[vyperASTTheory.is_ArrayT_def, vyperASTTheory.ArrayT_type_def] >>
  drule build_getter_subst >>
  disch_then (qspec_then `module_consts_env tops []` mp_tac) >>
  simp[subst_consts_expr_def] >>
  strip_tac >>
  rename1 `expr_type r = ArrayT elem bd` >>
  `supported_place_expr tops r /\ supported_place_type tops (ArrayT elem bd)` by
    metis_tac[array_constant_supported_place] >>
  `supported_place_info tops r = ValPT (expr_type r) /\ ~qualified_place_root r` by
    metis_tac[closed_constant_type_place] >>
  `supported_place_type tops (BaseT (UintT 256))` by
    simp[supported_place_type_def, Once supported_nested_type_def,
         supported_scalar_type_def, supported_word_type_def, supported_int_width_def] >>
  irule supported_getter_return_body >> simp[] >>
  qpat_x_assum `build_getter r _ _ _ = _`
    (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
       (Q.SPECL [`r`, `BaseT (UintT 256)`, `Type elem`, `0`, `args`, `ret`,
         `subst_consts_expr (module_consts_env tops []) exp`, `tops`]
         supported_build_getter_path))) >>
  simp[supported_subscript_place_def]
QED

Theorem subst_getter_body_without_replacement[local]:
  is_public_getter_decl name decl /\
  external_getter_tuple NONE decl = SOME (mut,nr,args,dflts,ret,fbody) /\
  ALOOKUP E name = NONE ==>
  subst_consts_stmts E fbody = fbody
Proof
  Cases_on `decl` >>
  simp[is_public_getter_decl_def, external_getter_tuple_def] >>
  Cases_on `v` >>
  simp[is_public_getter_decl_def, external_getter_tuple_def, getter_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[subst_consts_stmt_def, subst_consts_expr_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule build_getter_subst >>
  disch_then (qspec_then `E` mp_tac) >>
  simp[subst_consts_expr_def, subst_consts_stmt_def]
QED

Theorem supported_selected_external_getter_body[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  MEM decl tops /\ is_public_getter_decl tx.function_name decl /\
  external_getter_tuple NONE decl = SOME (mut,nr,args,[],ret,fbody) ==>
  supported_function_body tops External args
    (subst_consts_stmts (module_consts_env tops []) fbody)
Proof
  strip_tac >>
  drule_all supported_program_declaration >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    (qpat_x_assum `source_typing_ok _ _ _` mp_tac >>
     simp[source_typing_ok_def, vyperTypeContractTheory.check_contract_def] >>
     strip_tac >>
     drule vyperTypeContractStaticMapsTheory.contract_namespaces_ok_module_toplevel_vtype_keys >>
     simp[]) >>
  `ALL_DISTINCT (MAP FST args)` by
    (qpat_x_assum `source_typing_ok _ _ _` mp_tac >>
     simp[source_typing_ok_def] >> strip_tac >>
     `module_allocated am.layouts tx.target NONE tops` by
       (drule check_contract_main_module_allocated >> simp[]) >>
     drule_at (Pat `external_getter_tuple _ _ = _`) checked_public_getter_body_typing_package >>
     simp[] >> disch_then drule >> simp[] >> metis_tac[]) >>
  `!id. IS_SOME (ALOOKUP (module_consts_env tops []) id) ==>
    ?v c ty slot.
      supported_variable_decl tops (NONE,id) = SOME (v,Constant c,ty,slot)` by
    (fs[source_typing_ok_def] >>
     drule checked_module_consts_env_names_constant >> simp[]) >>
  Cases_on `?vis init ty slot.
    decl = VariableDecl (Public vis) (Constant init) tx.function_name ty slot`
  >- (gvs[] >> metis_tac[public_constant_getter_body_support]) >>
  `ALOOKUP (module_consts_env tops []) tx.function_name = NONE` by
    (Cases_on `ALOOKUP (module_consts_env tops []) tx.function_name` >>
     gvs[] >>
     `?const_vis init ty slot.
       supported_variable_decl tops (NONE,tx.function_name) =
         SOME (const_vis,Constant init,ty,slot)` by
       (qpat_x_assum `!id. IS_SOME (ALOOKUP _ id) ==> _`
          (qspec_then `tx.function_name` mp_tac) >>
        simp[]) >>
     pop_assum strip_assume_tac >>
     Cases_on `decl` >> gvs[is_public_getter_decl_def]
     >- (rename1 `MEM (VariableDecl getter_vis _ _ _ _) tops` >>
         Cases_on `getter_vis` >> gvs[is_public_getter_decl_def] >>
         drule_all getter_variable_member_lookup >> gvs[]) >>
     rename1 `MEM (HashMapDecl getter_vis _ _ _ _ _) tops` >>
     Cases_on `getter_vis` >> gvs[is_public_getter_decl_def] >>
     drule_all getter_hashmap_excludes_variable >> gvs[]) >>
  drule_all subst_getter_body_without_replacement >> strip_tac >> gvs[] >>
  Cases_on `decl` >>
  gvs[supported_declaration_header_def, is_public_getter_decl_def,
      external_getter_tuple_def]
  >- (drule_all getter_variable_member_lookup >> strip_tac >>
      drule_all build_maps_variable >> strip_tac >>
      Cases_on `v` >> Cases_on `v0` >> Cases_on `o'` >>
      gvs[is_public_getter_decl_def, external_getter_tuple_def] >>
      `supported_place_type tops t` by
        metis_tac[supported_storage_place, supported_value_type_def] >>
      `supported_place_type tops (BaseT (UintT 256))` by
        simp[supported_place_type_def, Once supported_nested_type_def,
             supported_scalar_type_def, supported_word_type_def, supported_int_width_def] >>
      (Cases_on `is_ArrayT t` >>
       gvs[getter_def, AllCaseEqs()]
       >- (pairarg_tac >> gvs[] >>
           Cases_on `t` >>
           gvs[vyperASTTheory.is_ArrayT_def, vyperASTTheory.ArrayT_type_def] >>
           drule supported_build_getter_path >>
           disch_then (qspec_then `tops` mp_tac) >>
           (impl_tac >-
             (simp[supported_pure_expr_def, supported_place_root_def,
                   supported_subscript_place_def, supported_place_info_def,
                   qualified_place_root_def,
                   place_type_def, supported_storage_value_def, supported_value_type_def,
                   int_calls_expr_def,
                   supported_hashmap_value_def] >>
              Cases_on `b'` >> gvs[supported_storage_array_depth] >>
              metis_tac[supported_storage_place])) >>
           strip_tac >> simp[EVERY_MAP] >>
           metis_tac[supported_getter_return_body]) >>
       simp[] >> irule supported_getter_return_body >>
       simp[supported_pure_expr_def, supported_storage_value_def,
            supported_immutable_type_def, int_calls_expr_def] >>
       metis_tac[supported_storage_place])) >>
  drule_all getter_hashmap_member_lookup >> strip_tac >>
  drule_all getter_hashmap_excludes_variable >> strip_tac >>
  Cases_on `v` >> Cases_on `o'` >>
  gvs[is_public_getter_decl_def, external_getter_tuple_def] >>
  drule_all build_hashmap_info_hashmap >> strip_tac >>
  gvs[getter_def] >> pairarg_tac >> gvs[] >>
  drule supported_build_getter_path >>
  disch_then (qspec_then `tops` mp_tac) >>
  (impl_tac >-
    (simp[supported_pure_expr_def, supported_place_root_def,
          supported_subscript_place_def, supported_place_info_def,
          qualified_place_root_def,
          place_type_def, int_calls_expr_def] >>
     fs[supported_place_type_def, Once supported_nested_type_def,
        supported_hashmap_key_type_def])) >>
  strip_tac >> simp[EVERY_MAP] >>
  metis_tac[supported_getter_return_body]
QED

(* Visibility changes getter generation; ordinary source lookup uses the
   visibility-independent find_var_decl_by_name. A getter is a Return of a
   top-level read or a subscript chain, with distinct generated argument names. *)
Theorem supported_selected_external_body:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  supported_function_body tops External args
    (subst_consts_stmts (module_consts_env tops []) fbody)
Proof
  strip_tac >> drule lookup_function_External_cases >> strip_tac
  >- (drule_all supported_program_declaration >>
      simp[supported_declaration_body_def] >> strip_tac >>
      qpat_assum `source_typing_ok tops am tx` (mp_tac o REWRITE_RULE [source_typing_ok_def]) >>
      disch_then (qx_choosel_then [`art`, `A`] strip_assume_tac) >>
      mp_tac (Q.INST
        [`mode` |-> `F`, `layouts` |-> `am.layouts`, `addr` |-> `tx.target`,
         `vis` |-> `External`, `name` |-> `tx.function_name`, `dflts` |-> `dflts`,
         `rr` |-> `raw`,
         `ss` |-> `fbody`, `imms` |-> `account_immutables am tx.target`,
         `env` |-> `function_entry_env art [(NONE,tops)] NONE External args`]
        (INST_TYPE [alpha |-> ``:160 word``] (SPEC_ALL checked_const_substituted_function))) >>
      simp[supported_pure_exprs_every]) >>
  `dflts = []` by (drule vyperReadOnlySyntaxTheory.external_getter_defaults >> simp[]) >>
  metis_tac[supported_selected_external_getter_body]
QED

Theorem closed_constant_typing[local]:
  env'.type_defs = env.type_defs ==>
  !tops.
  (!e. constant_expr [(NONE,tops)] e /\ const_local_refs e = [] /\
    well_typed_expr env e ==> well_typed_expr env' e) /\
  (!es. EVERY (constant_expr [(NONE,tops)]) es /\ const_local_exprs es = [] /\
    well_typed_exprs env es ==> well_typed_exprs env' es) /\
  (!fs. EVERY (constant_expr [(NONE,tops)]) (MAP SND fs) /\
    const_local_fields fs = [] /\ well_typed_named_exprs env fs ==>
    well_typed_named_exprs env' fs)
Proof
  strip_tac >> gen_tac >> ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, const_local_refs_def, well_typed_expr_def, SF ETA_ss] >>
  rpt strip_tac >> gvs[SF ETA_ss]
  >- (PairCases_on `ns` >> Cases_on `ns0` >>
      gvs[constant_expr_def, const_local_refs_def, declared_constant_def])
  >- (disj1_tac >> metis_tac[constant_subscript_base_exact]) >>
  qspecl_then [`e`, `env`] mp_tac closed_constant_type_place >> simp[]
QED

Theorem value_build_getter_typing[local]:
  !e kt vt n args ret exp env ty.
    build_getter e kt vt n = (args,ret,exp) /\ vt = Type ty /\
    well_typed_expr env e /\ subscript_base_type_exact env e /\
    subscript_type_ok (expr_type e) (Name kt (num_to_dec_string n)) ty /\
    well_formed_type env.type_defs ty /\
    (!id pt. MEM (id,pt) args ==> FLOOKUP env.var_types id = SOME pt) ==>
    well_typed_expr env exp /\ expr_type exp = ret
Proof
  recInduct build_getter_ind >> conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `build_getter _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [build_getter_def]) >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[]
  >- (pairarg_tac >> gvs[] >>
      rename1 `is_ArrayT ty` >> Cases_on `ty` >>
      gvs[is_ArrayT_def, ArrayT_type_def] >>
      first_x_assum (qspec_then `env` mp_tac) >>
      simp[well_typed_expr_def, subscript_base_type_exact_def, expr_type_def,
           subscript_type_ok_def, is_int_type_def] >>
      metis_tac[supportedPlaceAssignableTheory.well_formed_array_element]) >>
  simp[well_typed_expr_def, expr_type_def] >> metis_tac[]
QED

Theorem constant_public_getter_typing[local]:
  external_getter_tuple NONE (VariableDecl (Public vis) (Constant init) name ty slot) =
    SOME (mut,nr,args,[]:expr list,ret,fbody) /\
  ALOOKUP E name = SOME r /\ expr_type r = ty /\
  well_typed_expr env r /\ constant_expr [(NONE,tops)] r /\
  well_formed_type env.type_defs ty /\
  (!id pt. MEM (id,pt) args ==> FLOOKUP env.var_types id = SOME pt) /\
  type_stmts env ret fbody = SOME env' ==>
  type_stmts env ret (subst_consts_stmts E fbody) = SOME env'
Proof
  strip_tac >>
  `subscript_base_type_exact env r` by
    metis_tac[constant_subscript_base_exact] >>
  qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
  simp[external_getter_tuple_def, getter_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[subst_consts_stmt_def, subst_consts_expr_def, type_stmt_def,
      AllCaseEqs(), expr_type_def, type_widens_to_def] >>
  rpt (pairarg_tac >>
       gvs[subst_consts_stmt_def, subst_consts_expr_def, type_stmt_def, AllCaseEqs()]) >>
  Cases_on `expr_type r` >> gvs[is_ArrayT_def, ArrayT_type_def] >>
  drule build_getter_subst >>
  disch_then (qspec_then `E` mp_tac) >>
  simp[subst_consts_expr_def] >> strip_tac >>
  qpat_x_assum `build_getter (TopLevelName _ _) _ _ _ = _` kall_tac >>
  drule value_build_getter_typing >>
  disch_then (qspec_then `env` mp_tac) >>
  simp[subscript_type_ok_def, expr_type_def, is_int_type_def, type_widens_to_def] >>
  drule supportedPlaceAssignableTheory.well_formed_array_element >> simp[]
QED

Theorem type_stmt_subst_consts_result:
  type_stmt env ret s = SOME env1 /\
  type_stmt env ret (subst_consts_stmt E s) = SOME env2 ==>
  env1 = env2
Proof
  Cases_on `s` >>
  TRY (rename1 `Return opt` >> Cases_on `opt`) >>
  TRY (rename1 `Raise reason` >> Cases_on `reason`) >>
  TRY (rename1 `Assert e reason` >> Cases_on `reason`) >>
  rw[subst_consts_stmt_def, subst_consts_expr_def, subst_consts_areason_def,
     subst_consts_rreason_def, type_stmt_def, AllCaseEqs()]
QED

Theorem type_stmts_subst_consts_result[local]:
  !ss env ret E env1 env2.
    type_stmts env ret ss = SOME env1 /\
    type_stmts env ret (subst_consts_stmts E ss) = SOME env2 ==>
    env1 = env2
Proof
  Induct >> simp[subst_consts_stmt_def, type_stmt_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >>
  drule_all type_stmt_subst_consts_result >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem compiled_selected_external_body_typing:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] (account_immutables am tx.target)
    NONE tops FEMPTY = SOME A /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  env = function_entry_env art [(NONE,tops)] NONE External args /\
  (!id pt. MEM (id,pt) args ==> FLOOKUP env.var_types id = SOME pt) /\
  type_stmts env ret fbody = SOME env' ==>
  type_stmts env ret (subst_consts_stmts (module_consts_env tops []) fbody) = SOME env'
Proof
  strip_tac >>
  `env.type_defs = type_env_all_modules [(NONE,tops)]` by
    simp[function_entry_env_def, artifact_env_def, FOLDL_extend_local_args_static] >>
  drule lookup_function_External_cases >> strip_tac
  >- (`module_allocated am.layouts tx.target NONE tops` by
        (drule check_contract_main_module_allocated >> simp[]) >>
      `check_function_body am.layouts tx.target [(NONE,tops)] art NONE
         External mut nr args dflts ret fbody` by
        (irule check_contract_runtime_function_body_MEM >> simp[] >>
         qexistsl [`tx.function_name`, `raw`] >> simp[]) >>
      `IS_SOME (type_stmts env ret
         (subst_consts_stmts (module_consts_env tops []) fbody))` by
        gvs[check_function_body_def, consts_env_mods_singleton, subst_consts_mods_singleton] >>
      fs[optionTheory.IS_SOME_EXISTS] >> metis_tac[type_stmts_subst_consts_result]) >>
  `dflts = []` by (drule vyperReadOnlySyntaxTheory.external_getter_defaults >> simp[]) >>
  Cases_on `ALOOKUP (module_consts_env tops []) tx.function_name`
  >- metis_tac[subst_getter_body_without_replacement] >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  drule_all checked_module_consts_env_replacement >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     qexists_tac `[(NONE,tops)]` >>
     simp[] >> metis_tac[check_contract_runtime_namespaces]) >>
  `?nr0. decl = VariableDecl (Public nr0) (Constant init) tx.function_name ty slot` by
    (Cases_on `decl` >> gvs[is_public_getter_decl_def]
     >- (rename1 `is_public_getter_decl _ (VariableDecl getter_vis _ _ _ _)` >>
         Cases_on `getter_vis` >> gvs[is_public_getter_decl_def] >>
         imp_res_tac getter_variable_member_lookup >> gvs[]) >>
     rename1 `MEM (HashMapDecl getter_vis _ _ _ _ _) tops` >>
     Cases_on `getter_vis` >> gvs[is_public_getter_decl_def] >>
     imp_res_tac getter_variable_member_lookup >>
     drule_all getter_hashmap_excludes_variable >> gvs[]) >>
  pop_assum strip_assume_tac >>
  `EVERY (no_neg_exp_expr o SND) (module_consts_env tops [])` by
    (Cases_on `classify_functions tops` >>
     rename1 `classify_functions tops = (exts,tail)` >> PairCases_on `tail` >>
     metis_tac[lower_vyper_runtime_unit_consts_guard]) >>
  drule_all checked_module_consts_env_replacement_typed >> strip_tac >>
  `well_typed_expr env x` by
    (`env.type_defs = (artifact_env art [(NONE,tops)] NONE).type_defs` by
       simp[artifact_env_def] >>
     qpat_x_assum `env.type_defs = _.type_defs`
       (qspec_then `tops`
          (qspec_then `x` mp_tac o CONJUNCT1) o MATCH_MP closed_constant_typing) >>
     simp[]) >>
  irule constant_public_getter_typing >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  simp[well_formed_type_def] >>
  qexistsl [`args`, `init`, `mut`, `tx.function_name`, `nr`, `slot`, `tops`, `nr0`] >>
  gvs[]
QED
