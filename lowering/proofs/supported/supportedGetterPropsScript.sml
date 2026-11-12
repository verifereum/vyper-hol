(* Supported bodies and parameter types for the selected external entry,
   including synthesized getters of admitted public declarations. *)
Theory supportedGetterProps
Ancestors
  supportedProgram supportedDecls supportedExprForms supportedExprs
  supportedNames supportedTypes supportedStmts supportedStmtTraverse
  e2eDefs vyperTypeContractGetter vyperTypeContractContext bodyStorageMetadata
  compileEnv exprLowering vyperGetter vyperInterpreter list pair finite_map
  placeTypingBuildProps bodyStorageCases

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

Theorem supported_build_getter_place_return[local]:
  !e kt vt n.
    !args ret exp tops.
      supported_hashmap_value tops vt /\
      build_getter e kt vt n = (args,ret,exp) ==>
      supported_place_type tops ret
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [build_getter_def]) >>
  simp[supported_hashmap_value_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- (pairarg_tac >> gvs[] >> Cases_on `vt` >>
      gvs[vyperASTTheory.is_ArrayT_def, vyperASTTheory.ArrayT_type_def,
          supported_hashmap_value_def] >>
      Cases_on `b` >> gvs[supported_storage_array_depth] >>
      metis_tac[supported_hashmap_value_def])
  >- metis_tac[supported_storage_place, supported_hashmap_value_def]
  >> pairarg_tac >> gvs[supported_hashmap_value_def] >> metis_tac[]
QED

Theorem supported_public_getter_return:
  supported_declaration_header tops decl /\
  is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) ==>
  supported_place_type tops ret
Proof
  Cases_on `decl` >>
  simp[is_public_getter_decl_def, external_getter_tuple_def] >>
  Cases_on `v` >>
  simp[is_public_getter_decl_def, external_getter_tuple_def] >>
  rpt strip_tac >>
  gvs[supported_declaration_header_def, AllCaseEqs(), getter_def]
  >- (Cases_on `v0` >> Cases_on `o'` >> gvs[] >>
      metis_tac[supported_storage_place])
  >- (Cases_on `v0` >> Cases_on `o'` >> gvs[] >>
      pairarg_tac >> gvs[] >> Cases_on `t` >>
      gvs[vyperASTTheory.is_ArrayT_def, vyperASTTheory.ArrayT_type_def] >>
      rename1 `supported_storage_type tops (ArrayT elem bd)` >>
      Cases_on `bd` >> gvs[supported_storage_array_depth] >>
      metis_tac[supported_build_getter_place_return, supported_hashmap_value_def]) >>
  Cases_on `o'` >> gvs[] >> pairarg_tac >> gvs[] >>
  metis_tac[supported_build_getter_place_return]
QED

Theorem supported_types_namespace_every[local]:
  !tys. supported_types_namespace tys = EVERY supported_type_namespace tys
Proof
  Induct >> simp[supported_type_namespace_def]
QED

Theorem supported_nested_namespace[local]:
  !leaf fuel tops ty.
    supported_nested_type leaf fuel tops ty ==>
    (!t. leaf t ==> supported_type_namespace t) ==>
    supported_type_namespace ty
Proof
  recInduct supported_nested_type_ind >> rpt strip_tac >>
  Cases_on `leaf ty` >- metis_tac[] >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  once_rewrite_tac[supported_nested_type_def] >>
  Cases_on `ty` >> gvs[supported_type_namespace_def,
    supported_types_namespace_every, EVERY_MEM] >> rpt strip_tac >> simp[]
  >~ [`ArrayT elem bd`] >- (Cases_on `bd` >> gvs[] >>
      metis_tac[supported_type_namespace_def]) >>
  rename1 `supported_main_nsid id` >> PairCases_on `id` >>
  Cases_on `id0` >> gvs[supported_main_nsid_def,
    supported_struct_fields_other_module] >> metis_tac[]
QED

Theorem supported_place_namespace[local]:
  supported_place_type tops ty ==> supported_type_namespace ty
Proof
  simp[supported_place_type_def] >> strip_tac >>
  drule supported_nested_namespace >> disch_then irule >>
  Cases >> simp[supported_scalar_type_def, supported_word_type_def,
                 supported_string_type_def, supported_type_namespace_def]
QED

Theorem supported_getter_subscript[local]:
  !tops vt e kt vn.
  supported_hashmap_value tops vt ==>
  supported_place_expr tops e /\ supported_subscript_place tops e /\
  ~supported_expr_exists expr_nonmain_type_root e /\
  supported_place_type tops kt /\
  (supported_place_info tops e = MapPT kt vt \/
   ?bt bd. supported_place_info tops e = ValPT (ArrayT bt bd) /\ vt = Type bt) ==>
  supported_place_expr tops (Subscript (getter_vtype_annotation vt) e (Name kt vn)) /\
  ~supported_expr_exists expr_nonmain_type_root
    (Subscript (getter_vtype_annotation vt) e (Name kt vn)) /\
  supported_place_info tops (Subscript (getter_vtype_annotation vt) e (Name kt vn)) =
    value_type_place vt
Proof
  Cases_on `vt` >> rpt strip_tac >>
  gvs[getter_vtype_annotation_def, supported_pure_expr_def,
      supportedExprTraverseTheory.supported_expr_exists_def,
      expr_nonmain_type_root_def, vyperASTTheory.expr_type_def,
      supported_place_info_def, place_type_def, value_type_place_def,
      supported_hashmap_value_def] >>
  metis_tac[supported_place_namespace, supported_storage_place,
            supported_type_namespace_def]
QED

Theorem supported_build_getter_path[local]:
  !e kt vt n. !args ret exp tops.
  build_getter e kt vt n = (args,ret,exp) /\
  supported_place_expr tops e /\ supported_subscript_place tops e /\
  ~supported_expr_exists expr_nonmain_type_root e /\
  supported_place_type tops kt /\ supported_hashmap_value tops vt /\
  (supported_place_info tops e = MapPT kt vt \/
   ?bt bd. supported_place_info tops e = ValPT (ArrayT bt bd) /\ vt = Type bt) ==>
  supported_pure_expr tops exp /\
  EVERY (supported_place_type tops o SND) args /\
  ~supported_expr_exists expr_nonmain_type_root exp
Proof
  recInduct build_getter_ind >> conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule supported_getter_subscript >>
  disch_then (qspecl_then [`e`, `kt`, `num_to_dec_string n`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
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
    rename1 `supported_storage_type tops (ArrayT elem arrbd)` >>
    `supported_storage_type tops elem` by
      (Cases_on `arrbd` >> gvs[supported_storage_array_depth]) >>
    `supported_place_type tops (ArrayT elem arrbd)` by
      metis_tac[supported_storage_place] >>
    `supported_place_type tops (BaseT (UintT 256))` by
      simp[supported_place_type_def, Once supported_nested_type_def,
           supported_scalar_type_def, supported_word_type_def, supported_int_width_def] >>
    first_x_assum drule >>
    simp[supported_subscript_place_def, supported_hashmap_value_def] >>
    strip_tac >> simp[]) >>
  all_tac
  >>~- ([`~is_ArrayT ty`],
    gvs[getter_vtype_annotation_def, supported_hashmap_value_def] >>
    simp[supported_pure_expr_def, supported_storage_place]) >>
  pairarg_tac >> gvs[getter_vtype_annotation_def, value_type_place_def,
                     supported_hashmap_value_def] >>
  `supported_place_type tops typ` by
    (simp[supported_place_type_def, Once supported_nested_type_def,
          supported_scalar_type_def, supported_word_type_def] >>
     Cases_on `typ` >> gvs[supported_hashmap_key_type_def,
       supported_integer_type_def, supported_string_type_def,
       supported_word_type_def] >> Cases_on `b` >>
     gvs[supported_integer_type_def, supported_string_type_def,
         supported_word_type_def]) >>
  first_x_assum (qspec_then `tops` mp_tac) >>
  simp[supported_subscript_place_def]
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

Theorem getter_hashmap_member_lookup[local]:
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

Theorem getter_hashmap_excludes_variable[local]:
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
  ~supported_expr_exists expr_nonmain_type_root exp ==>
  supported_function_body tops External args [Return (SOME exp)]
Proof
  strip_tac >>
  `supported_stmts tops args [Return (SOME exp)]` by
    simp[supported_stmt_def, supported_expr_def] >>
  `body_stmts_safe tops [Return (SOME exp)]` by
    (rw[body_stmts_safe_iff] >>
     drule (CONJUNCT2 supported_stmts_storage_syntax) >> simp[]) >>
  simp[supported_function_body_def, supported_function_bindings_def,
       supported_stmt_bindings_def, supported_stmt_def,
       supported_stmt_expr_exists_def, supported_expr_def,
       supportedExprTraverseTheory.supported_expr_exists_def]
QED

(* Visibility changes getter generation; ordinary source lookup uses the
   visibility-independent find_var_decl_by_name. A getter is a Return of a
   top-level read or a subscript chain, with distinct generated argument names. *)
Theorem supported_selected_external_body:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) ==>
  supported_function_body tops External args fbody /\
  (ret = NoneT \/ supported_place_type tops ret)
Proof
  strip_tac >> drule lookup_function_External_cases >> strip_tac
  >- (drule_all supported_program_declaration >>
      simp[supported_declaration_body_def, supported_declaration_header_def,
           supported_function_return_def,
           EVERY_MAP, combinTheory.o_DEF]) >>
  drule_all supported_program_declaration >> strip_tac >>
  `supported_place_type tops ret` by (drule_all supported_public_getter_return >> simp[]) >>
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
  Cases_on `decl` >>
  gvs[supported_declaration_header_def, is_public_getter_decl_def,
      external_getter_tuple_def]
  >- (drule_all getter_variable_member_lookup >> strip_tac >>
      drule_all build_maps_variable >> strip_tac >>
      Cases_on `v` >> Cases_on `v0` >> Cases_on `o'` >>
      gvs[is_public_getter_decl_def, external_getter_tuple_def] >>
      `supported_place_type tops t` by metis_tac[supported_storage_place] >>
      `supported_type_namespace t` by metis_tac[supported_place_namespace] >>
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
                   place_type_def, supported_storage_value_def,
                   supportedExprTraverseTheory.supported_expr_exists_def,
                   expr_nonmain_type_root_def, vyperASTTheory.expr_type_def,
                   supported_hashmap_value_def] >>
              Cases_on `b'` >> gvs[supported_storage_array_depth] >>
              metis_tac[supported_storage_place, supported_place_namespace])) >>
           strip_tac >> simp[EVERY_MAP] >>
           metis_tac[supported_getter_return_body]) >>
       simp[] >> irule supported_getter_return_body >>
       simp[supported_pure_expr_def, supported_storage_value_def,
            supportedExprTraverseTheory.supported_expr_exists_def,
            expr_nonmain_type_root_def, vyperASTTheory.expr_type_def] >>
       metis_tac[supported_storage_place, supported_place_namespace])) >>
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
          place_type_def, supportedExprTraverseTheory.supported_expr_exists_def,
          expr_nonmain_type_root_def, vyperASTTheory.expr_type_def] >>
     simp[supported_place_type_def, Once supported_nested_type_def,
          supported_scalar_type_def, supported_word_type_def] >>
     Cases_on `t` >> gvs[supported_hashmap_key_type_def,
       supported_integer_type_def, supported_string_type_def,
       supported_word_type_def, supported_type_namespace_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[supported_integer_type_def, supported_string_type_def,
         supported_word_type_def])) >>
  strip_tac >> simp[EVERY_MAP] >>
  metis_tac[supported_getter_return_body]
QED
