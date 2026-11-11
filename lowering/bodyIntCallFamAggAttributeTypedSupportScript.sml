(* Typed value-place support boundaries for the Attribute child. *)
Theory bodyIntCallFamAggAttributeTypedSupport
Ancestors
  bodyIntCallFamAggAttributeHeaders bodySim exprSimAttribute
  exprSimHypsDefs supportedExprs supportedExprForms supportedDecls
  supportedTypes supportedProgram bodyStorageMetadata vyperTypeContractStaticMaps
  vyperTypeGlobalLookupSoundness vyperState vyperAST list option

Theorem supported_hashmap_decl_origin:
  !tops src id vis tr kt vt slot.
    supported_hashmap_decl tops (src,id) = SOME (vis,tr,kt,vt,slot) ==>
    src = NONE /\ MEM (HashMapDecl vis tr id kt vt slot) tops
Proof
  Induct >> simp[supported_hashmap_decl_def] >>
  rpt gen_tac >> Cases_on `h` >> simp[supported_hashmap_decl_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem supported_storage_typed_value:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  well_typed_expr env (TopLevelName ty (src,id)) /\
  supported_variable_decl tops (src,id) = SOME (Private,mut,declared,SOME slot) /\
  (mut = Storage \/ mut = Transient) /\ supported_storage_type tops declared ==>
  supported_storage_value tops (src,id) ty
Proof
  strip_tac >> drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `?tr. find_var_decl_by_name id tops = SOME (StorageVarDecl tr declared,id)` by
    (gvs[] >> metis_tac[find_var_decl_by_name_SOME_storage_var_Storage,
                        find_var_decl_by_name_SOME_storage_var_Transient]) >>
  drule_all TopLevelName_storage_decl_type_eq >> strip_tac >> gvs[] >>
  simp[supported_storage_value_def] >> Cases_on `mut` >> gvs[]
QED

Theorem supported_hashmap_typed_value_impossible:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  well_typed_expr env (TopLevelName ty (src,id)) /\
  supported_hashmap_decl tops (src,id) = SOME (vis,tr,kt,vt,slot) ==> F
Proof
  strip_tac >> drule supported_hashmap_decl_origin >> strip_tac >> gvs[] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `find_var_decl_by_name id tops = SOME (HashMapVarDecl tr kt vt,id)` by
    metis_tac[find_var_decl_by_name_SOME_hashmap] >>
  irule TopLevelName_Type_HashMapVarDecl_impossible >>
  fs[expr_sim_inv_def] >> metis_tac[]
QED

Theorem supported_place_root_typed_value:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  well_typed_expr env (TopLevelName ty id) /\ supported_place_root tops id ==>
  supported_storage_value tops id ty
Proof
  PairCases_on `id` >> strip_tac >>
  fs[supported_place_root_def] >>
  Cases_on `supported_variable_decl tops (id0,id1)`
  >- (Cases_on `supported_hashmap_decl tops (id0,id1)` >> gvs[] >>
      PairCases_on `x` >> metis_tac[supported_hashmap_typed_value_impossible]) >>
  PairCases_on `x` >> rename1 `SOME (vis,mut,declared,slot)` >>
  Cases_on `vis` >> Cases_on `mut` >> Cases_on `slot` >> gvs[] >>
  metis_tac[supported_storage_typed_value]
QED

Theorem supported_typed_place_expr:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  well_typed_expr env e /\ supported_place_type tops (expr_type e) /\
  supported_place_expr tops e ==> supported_pure_expr tops e
Proof
  strip_tac >> Cases_on `e` >>
  gvs[supported_pure_expr_def, expr_type_def]
  >> metis_tac[supported_place_root_typed_value]
QED

Theorem supported_typed_effect_place_expr:
  supported_place_type tops (expr_type e) /\
  supported_effect_place_expr tops e ==> supported_effect_expr tops e
Proof
  Cases_on `e` >>
  simp[supported_effect_expr_def, supported_pure_expr_def, expr_type_def]
QED

Theorem supported_attribute_child:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env (Attribute ann obj fld) es /\
  supported_expr tops (Attribute ann obj fld) ==> supported_expr tops obj
Proof
  strip_tac >> drule attr_pre_base >> strip_tac >>
  `supported_place_type tops (expr_type obj)` by
    (asm_rewrite_tac[] >> irule supported_place_struct_header >>
     fs[body_inv_def, supported_program_def, supported_expr_def,
        supported_pure_expr_def, supported_effect_expr_def,
        supported_field_place_def] >>
     Cases_on `supported_struct_fields tops sid` >> gvs[]) >>
  fs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def] >>
  metis_tac[supported_typed_place_expr, supported_typed_effect_place_expr,
            expr_body_pre_def]
QED
