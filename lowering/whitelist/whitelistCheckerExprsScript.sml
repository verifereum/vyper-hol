(* Whitelist removal, expressions: an expression the checker types in a
   function body's environment is in the supported_* expression gate.

   TOP-LEVEL: checker_env_ok (what the typing environment of a checked body
   holds about the main module), well_typed_expr_supported (typed
   expressions are supported_pure_expr), assignable_type_supported_place.

   The environment invariant is stated on the environment's own maps, so it
   survives extend_local and holds of the defaults' environment once the
   storage roots are dropped (whitelistCheckerGate builds each instance). *)
Theory whitelistCheckerExprs
Ancestors
  list rich_list pair alist finite_map pred_set vyperAST vyperValue
  vyperContext vyperTypeSystem vyperTypeContract vyperTypeArgFits
  vyperTypeCallGraph exprLowering compileEnv placeTypingProps
  supportedTypes supportedDecls supportedExprForms supportedExprs
  whitelistCheckerTypes supportedGetterProps whitelistStructFieldProps
  whitelistExprTypeProps whitelistNestedTypeProps whitelistHashmapValueProps

(* ===== Types ===== *)

Theorem assignable_type_supported_nested[local]:
  !tenv ty. assignable_type tenv ty ==>
    !fuel tops leaf.
      CARD (FDOM tenv) <= fuel /\
      (!id args. FLOOKUP tenv id = SOME (StructArgs args) ==>
                 supported_struct_fields tops id = SOME args) /\
      (!t. supported_scalar_type t ==> leaf t) ==>
      supported_nested_type leaf fuel tops ty
Proof
  rpt strip_tac >> drule linked_nested_with_fuel >>
  disch_then irule >> simp[] >> qexists_tac `FDOM tenv` >>
  simp[] >> disj2_tac >> metis_tac[flookup_thm]
QED

Theorem assignable_type_supported_place:
  assignable_type (type_env tops) ty ==> supported_place_type tops ty
Proof
  rw[supported_place_type_def] >>
  drule assignable_type_supported_nested >>
  disch_then irule >>
  simp[type_env_struct_fields, type_env_def, type_env_card_le]
QED

Theorem assignable_type_supported_event:
  assignable_type (type_env tops) ty ==>
  supported_nested_type supported_event_leaf_type (LENGTH tops) tops ty
Proof
  strip_tac >> drule assignable_type_supported_nested >>
  disch_then irule >>
  simp[type_env_struct_fields, type_env_def, type_env_card_le,
       supported_event_leaf_type_def]
QED

Theorem checker_hashmap_key_supported:
  well_formed_type tenv ty /\ hashmap_key_type ty ==>
  supported_hashmap_key_type ty
Proof
  Cases_on `ty` >> simp[hashmap_key_type_def, supported_hashmap_key_type_def]
  >- (rename1 `BaseT bt` >> strip_tac >>
      drule well_formed_base_scalar >> strip_tac >>
      Cases_on `bt` >> gvs[hashmap_key_type_def, supported_scalar_type_def,
                             supported_word_type_def]) >>
  simp[supported_scalar_type_def]
QED

Theorem checker_hashmap_value_supported:
  !vt. check_value_type (type_env tops) vt ==> supported_hashmap_value tops vt
Proof
  rpt strip_tac >>
  irule (Q.INST [`tenv` |-> `type_env tops`, `imported_only` |-> `F`]
    checked_hashmap_value_supported) >>
  simp[assignable_type_supported_place] >> metis_tac[checker_hashmap_key_supported]
QED

Theorem type_env_struct_MEM:
  !tops id args.
    FLOOKUP (type_env tops) id = SOME (StructArgs args) ==>
    ?name. id = (NONE, name) /\ MEM (StructDecl name args) tops
Proof
  simp[type_env_def] >> Induct >> simp[type_env_for_module_def] >> Cases >>
  rw[type_env_for_module_def, FLOOKUP_UPDATE] >> res_tac >> gvs[]
QED

Theorem well_formed_struct_fields[local]:
  well_formed_type tenv (StructT nsid) /\
  FLOOKUP tenv nsid = SOME (StructArgs args) ==>
  !x. MEM x args ==> well_formed_type (tenv \\ nsid) (SND x)
Proof
  rw[well_formed_type_def, evaluate_type_def, evaluate_types_OPT_MMAP] >>
  Cases_on `OPT_MMAP (evaluate_type (tenv \\ nsid)) (MAP SND args)` >> fs[] >>
  `IS_SOME (OPT_MMAP (evaluate_type (tenv \\ nsid)) (MAP SND args))` by simp[] >>
  fs[IS_SOME_OPT_MMAP, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

(* Assignability survives dropping declarations the type does not use. *)
Theorem assignable_type_submap:
  !tenv ty. assignable_type tenv ty ==>
    !tenv'. tenv' SUBMAP tenv /\ well_formed_type tenv' ty ==>
            assignable_type tenv' ty
Proof
  ho_match_mp_tac assignable_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`TupleT tys`]
  >- (rpt strip_tac >> fs[assignable_type_def, EVERY_MEM] >>
      `IS_SOME (OPT_MMAP (evaluate_type tenv') tys)` by
        (qpat_x_assum `well_formed_type tenv' _` mp_tac >>
         simp[well_formed_type_def, evaluate_type_def, evaluate_types_OPT_MMAP] >>
         Cases_on `OPT_MMAP (evaluate_type tenv') tys` >> simp[]) >>
      fs[IS_SOME_OPT_MMAP, EVERY_MEM, MEM_MAP, PULL_EXISTS,
         well_formed_type_def] >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[])
  >~ [`ArrayT elem bd`]
  >- (rpt strip_tac >> fs[assignable_type_def] >>
      first_x_assum irule >> simp[] >>
      Cases_on `evaluate_type tenv' elem` >>
      fs[well_formed_type_def, evaluate_type_def])
  >~ [`StructT nsid`]
  >- (rpt strip_tac >>
      Cases_on `FLOOKUP tenv nsid` >> fs[assignable_type_def] >>
      rename1 `FLOOKUP tenv nsid = SOME desc` >> Cases_on `desc` >> fs[] >>
      rename1 `FLOOKUP tenv nsid = SOME (StructArgs args)` >>
      `FLOOKUP tenv' nsid = SOME (StructArgs args)` by
        (Cases_on `FLOOKUP tenv' nsid` >>
         fs[well_formed_type_def, evaluate_type_def, SUBMAP_FLOOKUP_EQN] >>
         res_tac >> fs[]) >>
      imp_res_tac well_formed_struct_fields >>
      `tenv' \\ nsid SUBMAP tenv \\ nsid` by
        fs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
      fs[EVERY_MEM] >> metis_tac[])
  >> simp[assignable_type_def]
QED

(* ===== The typing-environment invariant ===== *)

(* What a top-level name the environment types holds of the gate: a value
   root is a slotted storage value, an admitted immutable or a constant, and
   a map root is a slotted HashMap the compiler's map table describes. *)
Definition checker_vtype_ok_def:
  checker_vtype_ok tops k (Type ty) =
    (assignable_type (type_env tops) ty /\ supported_place_root tops k /\
     build_hashmap_info tops k = NONE /\
     (supported_storage_value tops k ty \/
      supported_immutable_type tops k = SOME ty \/
      supported_constant_type tops k = SOME ty)) /\
  checker_vtype_ok tops k (HashMapT kt vt) =
    (check_value_type (type_env tops) (HashMapT kt vt) /\
     supported_place_root tops k /\
     ?tr. build_hashmap_info tops k = SOME (tr,kt,vt))
End

Definition checker_env_ok_def:
  checker_env_ok tops env <=>
    env.type_defs = type_env tops /\
    (!name fields. MEM (StructDecl name fields) tops ==>
       fields <> [] /\ EVERY (assignable_type (type_env tops) o SND) fields) /\
    (!x ty. FLOOKUP env.var_types x = SOME ty ==>
       assignable_type (type_env tops) ty) /\
    (!k vt. FLOOKUP env.toplevel_vtypes k = SOME vt ==>
       checker_vtype_ok tops k vt) /\
    (!k ty. FLOOKUP env.bare_globals k = SOME ty ==>
       FLOOKUP env.toplevel_vtypes k = SOME (Type ty)) /\
    (!k sig. FLOOKUP env.fn_sigs k = SOME sig ==>
       IS_SOME (supported_function_decl tops k Internal) /\
       (sig.ret_ty = NoneT \/ assignable_type (type_env tops) sig.ret_ty))
End

Theorem checker_env_ok_extend_local:
  checker_env_ok tops env /\ assignable_type (type_env tops) ty ==>
  checker_env_ok tops (extend_local env id ty b)
Proof
  rw[checker_env_ok_def, extend_local_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem checker_env_place_info[local]:
  checker_env_ok tops env ==>
  place_map_tables_agree_on_defined
    ((ARB : compile_env) with ce_hashmap_info := build_hashmap_info tops) env /\
  (!nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==>
     build_hashmap_info tops nsid = NONE)
Proof
  rw[checker_env_ok_def, place_map_tables_agree_on_defined_def]
  >- (first_x_assum drule >> Cases_on `vt` >>
      rw[checker_vtype_ok_def] >> simp[])
  >> qpat_x_assum `!k ty. FLOOKUP env.bare_globals _ = _ ==> _` drule >>
  strip_tac >>
  qpat_x_assum `!k vt. FLOOKUP env.toplevel_vtypes _ = _ ==> _` drule >>
  simp[checker_vtype_ok_def]
QED

Theorem checker_env_struct_assignable[local]:
  checker_env_ok tops env /\
  well_formed_type (type_env tops) (StructT nsid) ==>
  assignable_type (type_env tops) (StructT nsid)
Proof
  rw[checker_env_ok_def] >>
  `?args. FLOOKUP (type_env tops) nsid = SOME (StructArgs args)` by
    (Cases_on `FLOOKUP (type_env tops) nsid` >>
     gvs[well_formed_type_def, evaluate_type_def] >>
     rename1 `SOME desc` >> Cases_on `desc` >> gvs[evaluate_type_def]) >>
  drule_then strip_assume_tac type_env_struct_MEM >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac well_formed_struct_fields >>
  fs[assignable_type_def, EVERY_MEM] >> rpt strip_tac >>
  irule assignable_type_submap >> simp[] >>
  qexists_tac `type_env tops` >> simp[SUBMAP_DOMSUB]
QED

(* ===== Result types ===== *)

(* An array or tuple result has a supported place type: subscripting it
   reads a place the gate admits. *)
Definition checker_agg_ok_def:
  checker_agg_ok tops ty <=>
    ((?elem bd. ty = ArrayT elem bd) \/ (?tys. ty = TupleT tys)) ==>
    supported_place_type tops ty
End

Theorem checker_agg_ok_place[local]:
  supported_place_type tops ty ==> checker_agg_ok tops ty
Proof
  simp[checker_agg_ok_def]
QED

Theorem checker_agg_ok_assignable[local]:
  assignable_type (type_env tops) ty ==> checker_agg_ok tops ty
Proof
  metis_tac[checker_agg_ok_place, assignable_type_supported_place]
QED

Theorem checker_agg_ok_base[local]:
  checker_agg_ok tops (BaseT bt) /\ checker_agg_ok tops (FlagT id) /\
  checker_agg_ok tops (StructT id) /\ checker_agg_ok tops NoneT
Proof
  simp[checker_agg_ok_def]
QED

Theorem valid_conversion_not_agg[local]:
  valid_conversion s t ==> checker_agg_ok tops t
Proof
  strip_tac >> drule valid_conversion_nonaggregate >>
  Cases_on `t` >> simp[checker_agg_ok_def]
QED

Theorem well_typed_binop_not_agg[local]:
  ~well_typed_binop (TupleT tys) op t1 t2 /\
  ~well_typed_binop (ArrayT elem bd) op t1 t2
Proof
  Cases_on `op` >> simp[well_typed_binop_def]
QED

Theorem raw_call_return_agg_ok[local]:
  checker_agg_ok tops (raw_call_return_type flags)
Proof
  rw[raw_call_return_type_def, checker_agg_ok_def, supported_place_type_def] >>
  simp[Once supported_nested_type_def] >>
  simp[Once supported_nested_type_def] >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def]
QED

(* ===== Builtins ===== *)

Theorem well_typed_builtin_args_length[local]:
  well_typed_builtin_app ty blt ts /\ (!s b. blt <> MakeArray s b) ==>
  builtin_args_length_ok blt (LENGTH ts)
Proof
  Cases_on `blt` >> rw[well_typed_builtin_app_def, builtin_args_length_ok_def] >>
  simp[]
QED

Theorem well_typed_builtin_args_length_form[local]:
  well_typed_builtin_app ty blt (MAP expr_type es) /\
  (!s b. blt <> MakeArray s b) ==>
  supported_builtin_form tops ty blt es
Proof
  rpt strip_tac >> drule_all well_typed_builtin_args_length >>
  Cases_on `blt` >> gvs[supported_builtin_form_def, supported_binop_def] >>
  gvs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute] >>
  rpt strip_tac >> gvs[]
QED

Theorem uint256_pair_place[local]:
  supported_place_type tops (ArrayT (BaseT (UintT 256)) (Fixed 2))
Proof
  simp[supported_place_type_def, Once supported_nested_type_def] >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_int_width_def]
QED

Theorem item_type_not_agg[local]:
  env_item_type it <> TupleT tys /\ env_item_type it <> ArrayT elem bd /\
  account_item_type ai <> TupleT tys /\ account_item_type ai <> ArrayT elem bd
Proof
  Cases_on `it` >> Cases_on `ai` >>
  simp[env_item_type_def, account_item_type_def]
QED

Theorem well_typed_builtin_agg_ok[local]:
  well_typed_builtin_app ty blt ts /\ (!s b. blt <> MakeArray s b) /\
  blt <> NamedConst ==>
  checker_agg_ok tops ty
Proof
  Cases_on `ty` >> simp[checker_agg_ok_def] >>
  Cases_on `blt` >>
  simp[well_typed_builtin_app_def, well_typed_binop_not_agg, uint256_pair_place,
       item_type_not_agg]
QED

Theorem well_typed_builtin_supported_form:
  well_typed_builtin_app ty blt (MAP expr_type es) /\
  (!s b. blt = MakeArray s b ==> assignable_type (type_env tops) ty) /\
  (blt = NamedConst ==> checker_agg_ok tops ty) ==>
  supported_builtin_form tops ty blt es /\ checker_agg_ok tops ty
Proof
  strip_tac >>
  Cases_on `?s b. blt = MakeArray s b`
  >- (gvs[] >> drule_then assume_tac assignable_type_supported_place >>
      simp[checker_agg_ok_place] >>
      Cases_on `s` >> Cases_on `b` >>
      gvs[supported_builtin_form_def, well_typed_builtin_app_def]) >>
  conj_tac >- metis_tac[well_typed_builtin_args_length_form] >>
  Cases_on `blt = NamedConst` >- gvs[] >>
  irule well_typed_builtin_agg_ok >> metis_tac[]
QED

Theorem numeric_agg_ok[local]:
  supported_numeric_type ty ==> checker_agg_ok tops ty
Proof
  Cases_on `ty` >>
  simp[checker_agg_ok_def, supported_numeric_type_def, supported_integer_type_def]
QED

Theorem well_typed_type_builtin_supported_form:
  type_builtin_result_ok (type_env tops) tb ty target (MAP expr_type es) /\
  well_typed_type_builtin_args tb target (MAP expr_type es) /\
  well_formed_type (type_env tops) ty ==>
  supported_type_builtin_form tops ty tb target es /\ checker_agg_ok tops ty
Proof
  strip_tac >> irule (Q.INST [`tenv` |-> `type_env tops`] typed_type_builtin_form) >>
  simp[checker_agg_ok_base, numeric_agg_ok,
       assignable_type_supported_place, checker_agg_ok_assignable] >>
  metis_tac[valid_conversion_not_agg]
QED

(* ===== Places ===== *)

Theorem subscript_place_vtype[local]:
  checker_env_ok tops env /\ type_place_expr env be = SOME vt /\
  check_value_type (type_env tops) vt /\
  subscript_vtype vt kty = SOME vt' ==>
  supported_subscript_place tops be
Proof
  rw[supported_subscript_place_def, supported_place_info_def] >>
  drule_then strip_assume_tac checker_env_place_info >>
  drule_all place_type_checked_place_on_defined >> rw[] >>
  Cases_on `vt` >> gvs[value_type_place_def, subscript_vtype_def]
  >- (rename1 `Type ty` >> Cases_on `ty` >>
      gvs[subscript_vtype_def, check_value_type_def] >>
      metis_tac[assignable_type_supported_place])
  >> gvs[check_value_type_def, AllCaseEqs()] >>
  metis_tac[checker_hashmap_key_supported, checker_hashmap_value_supported]
QED

Theorem subscript_place_value[local]:
  checker_env_ok tops env /\ well_typed_expr env be /\
  checker_agg_ok tops (expr_type be) /\
  subscript_type_ok (expr_type be) key ty ==>
  supported_subscript_place tops be /\ supported_place_type tops ty
Proof
  strip_tac >>
  `place_type ((ARB : compile_env) with ce_hashmap_info := build_hashmap_info tops)
     be = ValPT (expr_type be)` by
    (drule_then strip_assume_tac checker_env_place_info >>
     irule place_type_well_typed_on_defined >> simp[] >> metis_tac[]) >>
  simp[supported_subscript_place_def, supported_place_info_def] >>
  Cases_on `expr_type be` >> gvs[subscript_type_ok_def, checker_agg_ok_def]
  >~ [`ArrayT`] >- metis_tac[supported_place_array_element]
  >> Cases_on `key` >> gvs[] >> BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  metis_tac[supported_place_type_tuple_el]
QED

(* ===== The expression bridge ===== *)



(* ===== Expression cases ===== *)

Theorem checker_env_bare_toplevel:
  checker_env_ok tops env /\ FLOOKUP env.bare_globals k = SOME ty ==>
  FLOOKUP env.toplevel_vtypes k = SOME (Type ty)
Proof
  rw[checker_env_ok_def]
QED

Theorem checker_toplevel_name_place:
  checker_env_ok tops env /\ FLOOKUP env.toplevel_vtypes k = SOME vt ==>
  supported_place_root tops k /\ check_value_type (type_env tops) vt
Proof
  strip_tac >> fs[checker_env_ok_def] >>
  qpat_x_assum `!k vt. FLOOKUP env.toplevel_vtypes _ = _ ==> _` drule >>
  Cases_on `vt` >> rw[checker_vtype_ok_def, check_value_type_def]
QED

Theorem checker_toplevel_name_pure[local]:
  checker_env_ok tops env /\
  (FLOOKUP env.toplevel_vtypes k = SOME (Type ty) \/
   FLOOKUP env.bare_globals k = SOME ty) ==>
  supported_pure_expr tops (TopLevelName ty k) /\ checker_agg_ok tops ty
Proof
  strip_tac >> imp_res_tac checker_env_bare_toplevel >>
  fs[checker_env_ok_def] >>
  qpat_x_assum `!k vt. FLOOKUP env.toplevel_vtypes _ = _ ==> _` drule >>
  rw[checker_vtype_ok_def, supported_pure_expr_def, checker_agg_ok_assignable]
QED

Theorem well_typed_place_from_pure[local]:
  checker_env_ok tops env /\ well_typed_expr env e /\
  supported_pure_expr tops e ==> supported_place_expr tops e
Proof
  Cases_on `e` >> simp[supported_pure_expr_def] >> rpt strip_tac
  >- (gvs[well_typed_expr_def, checker_env_ok_def] >>
      metis_tac[assignable_type_supported_place])
  >> rename1 `TopLevelName _ k` >> Cases_on `k` >>
  gvs[well_typed_expr_def] >>
  metis_tac[checker_toplevel_name_place, checker_env_bare_toplevel]
QED

Theorem checker_subscript_pure_value[local]:
  checker_env_ok tops env /\ supported_pure_expr tops e2 /\
  well_typed_expr env e1 /\ supported_pure_expr tops e1 /\
  checker_agg_ok tops (expr_type e1) /\ subscript_type_ok (expr_type e1) e2 ty ==>
  supported_pure_expr tops (Subscript ty e1 e2) /\ checker_agg_ok tops ty
Proof
  strip_tac >> simp[supported_pure_expr_def] >>
  drule_all subscript_place_value >> strip_tac >>
  drule_all well_typed_place_from_pure >> simp[checker_agg_ok_place]
QED

Theorem checker_subscript_pure_place[local]:
  checker_env_ok tops env /\ supported_pure_expr tops e2 /\
  type_place_expr env e1 = SOME vt /\ supported_place_expr tops e1 /\
  check_value_type (type_env tops) vt /\
  subscript_vtype vt (expr_type e2) = SOME (Type ty) ==>
  supported_pure_expr tops (Subscript ty e1 e2) /\ checker_agg_ok tops ty
Proof
  strip_tac >> simp[supported_pure_expr_def] >>
  drule_all subscript_place_vtype >> drule_all check_value_type_subscript_child >>
  rw[check_value_type_def] >>
  metis_tac[assignable_type_supported_place, checker_agg_ok_place]
QED

Theorem checker_subscript_place[local]:
  checker_env_ok tops env /\ supported_pure_expr tops e2 /\
  type_place_expr env e1 = SOME vt /\ supported_place_expr tops e1 /\
  check_value_type (type_env tops) vt /\ subscript_vtype vt kty = SOME vt' ==>
  supported_place_expr tops (Subscript ty e1 e2) /\
  check_value_type (type_env tops) vt'
Proof
  strip_tac >> simp[supported_pure_expr_def] >>
  metis_tac[subscript_place_vtype, check_value_type_subscript_child]
QED

Theorem checker_attribute_assignable[local]:
  checker_env_ok tops env /\ attribute_type (type_env tops) t fid = SOME ty ==>
  assignable_type (type_env tops) ty
Proof
  Cases_on `t` >> simp[attribute_type_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> drule type_env_struct_MEM >> strip_tac >> gvs[checker_env_ok_def] >>
  first_x_assum drule >> rw[EVERY_MEM] >>
  imp_res_tac ALOOKUP_MEM >> res_tac >> fs[]
QED

Theorem checker_attribute_pure[local]:
  checker_env_ok tops env /\ well_typed_expr env e /\
  supported_pure_expr tops e /\
  attribute_type_ok env.type_defs (expr_type e) fid ty ==>
  supported_pure_expr tops (Attribute ty e fid) /\ checker_agg_ok tops ty
Proof
  strip_tac >>
  `env.type_defs = type_env tops` by fs[checker_env_ok_def] >>
  gvs[supported_pure_expr_def] >>
  drule_all well_typed_place_from_pure >>
  imp_res_tac well_typed_attribute_field_place >>
  fs[attribute_type_ok_def] >> drule_all checker_attribute_assignable >>
  simp[assignable_type_supported_place, checker_agg_ok_assignable]
QED

Theorem checker_structlit_pure[local]:
  checker_env_ok tops env /\
  well_formed_type env.type_defs (StructT nsid) /\
  FLOOKUP env.type_defs nsid = SOME (StructArgs args) /\
  MAP FST kes = MAP FST args /\
  EVERY (supported_pure_expr tops o SND) kes ==>
  supported_pure_expr tops (StructLit (StructT nsid) nsid kes)
Proof
  strip_tac >>
  `env.type_defs = type_env tops` by fs[checker_env_ok_def] >>
  gvs[supported_pure_expr_def, supported_struct_elements_def,
      supported_pure_fields_every] >>
  drule_then strip_assume_tac type_env_struct_MEM >>
  drule_then assume_tac type_env_struct_fields >>
  gvs[supported_main_nsid_def] >>
  conj_tac >- metis_tac[checker_env_struct_assignable,
                        assignable_type_supported_place] >>
  irule structlit_fields_lookup >> simp[]
QED

Theorem checker_builtin_pure[local]:
  checker_env_ok tops env /\ well_typed_builtin_app ty blt (MAP expr_type es) /\
  (!s b. blt = MakeArray s b ==> assignable_type env.type_defs ty) /\
  (blt = NamedConst ==> checker_agg_ok tops ty) /\
  EVERY (supported_pure_expr tops) es ==>
  supported_pure_expr tops (Builtin ty blt es) /\ checker_agg_ok tops ty
Proof
  strip_tac >>
  `env.type_defs = type_env tops` by fs[checker_env_ok_def] >>
  fs[supported_pure_expr_def, supported_pure_exprs_every] >>
  irule well_typed_builtin_supported_form >> gvs[]
QED

Theorem checker_type_builtin_pure[local]:
  checker_env_ok tops env /\
  type_builtin_result_ok env.type_defs tb ty target (MAP expr_type es) /\
  well_typed_type_builtin_args tb target (MAP expr_type es) /\
  well_formed_type env.type_defs ty /\
  EVERY (supported_pure_expr tops) es ==>
  supported_pure_expr tops (TypeBuiltin ty tb target es) /\ checker_agg_ok tops ty
Proof
  strip_tac >>
  `env.type_defs = type_env tops` by fs[checker_env_ok_def] >>
  fs[supported_pure_expr_def, supported_pure_exprs_every] >>
  irule well_typed_type_builtin_supported_form >> gvs[]
QED

Theorem checker_pop_agg[local]:
  checker_env_ok tops env /\ assignable_type env.type_defs (ArrayT ty bd) ==>
  checker_agg_ok tops ty
Proof
  rw[checker_env_ok_def] >> gvs[assignable_type_def] >>
  simp[checker_agg_ok_assignable]
QED

Theorem checker_env_fn_sig_internal[local]:
  checker_env_ok tops env /\ FLOOKUP env.fn_sigs k = SOME sig ==>
  IS_SOME (supported_function_decl tops k Internal)
Proof
  rw[checker_env_ok_def] >> res_tac
QED

Theorem checker_intcall_agg[local]:
  checker_env_ok tops env /\ FLOOKUP env.fn_sigs k = SOME sig /\
  type_widens_to env.type_defs sig.ret_ty ty ==> checker_agg_ok tops ty
Proof
  strip_tac >> fs[checker_env_ok_def] >>
  qpat_x_assum `!k sig. FLOOKUP env.fn_sigs _ = _ ==> _` drule >> rw[] >>
  gvs[checker_agg_ok_base] >>
  metis_tac[type_widens_to_assignable_type, checker_agg_ok_assignable]
QED

Theorem checker_ret_agg[local]:
  checker_env_ok tops env /\ (ty <> NoneT ==> assignable_type env.type_defs ty) ==>
  checker_agg_ok tops ty
Proof
  rw[checker_env_ok_def] >> Cases_on `ty = NoneT` >>
  gvs[checker_agg_ok_base, checker_agg_ok_assignable]
QED

Theorem literal_agg_ok[local]:
  well_typed_literal ty l ==> checker_agg_ok tops ty
Proof
  Cases_on `ty` >> simp[checker_agg_ok_base] >>
  Cases_on `l` >> simp[well_typed_literal_def]
QED

Theorem checker_named_const_operand_agg_ok[local]:
  checker_env_ok tops env /\ well_typed_expr env e /\ named_const_operand e ==>
  checker_agg_ok tops (expr_type e)
Proof
  strip_tac >>
  `env.type_defs = type_env tops` by fs[checker_env_ok_def] >>
  Cases_on `e` >> gvs[oneline named_const_operand_def]
  >~ [`expr_type (Literal _ _)`] >-
    (gvs[well_typed_expr_def, expr_type_def] >> drule literal_agg_ok >> simp[])
  >~ [`expr_type (Builtin _ bi _)`] >-
    (Cases_on `bi` >> gvs[well_typed_expr_def, expr_type_def] >>
     simp[checker_agg_ok_assignable]) >>
  rename1 `expr_type (TypeBuiltin _ tb _ args)` >>
  Cases_on `tb` >> Cases_on `args` >> gvs[expr_type_def] >>
  qpat_x_assum `well_typed_expr _ (TypeBuiltin _ _ _ _)` mp_tac >>
  pure_rewrite_tac[well_typed_expr_def] >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all well_typed_type_builtin_supported_form >> simp[]
QED

Theorem every_pure_eta[local]:
  EVERY (\a. supported_pure_expr tops a) l <=> EVERY (supported_pure_expr tops) l
Proof
  simp[EVERY_MEM]
QED

Theorem well_typed_expr_supported:
  (!env e. well_typed_expr env e ==>
     checker_env_ok tops env ==>
     supported_pure_expr tops e /\ checker_agg_ok tops (expr_type e)) /\
  (!env e. IS_SOME (type_place_expr env e) ==>
     checker_env_ok tops env ==>
     supported_place_expr tops e /\
     check_value_type (type_env tops) (THE (type_place_expr env e))) /\
  (!env tgt. IS_SOME (type_place_target env tgt) ==>
     checker_env_ok tops env ==>
     EVERY (supported_pure_expr tops) (target_indices tgt)) /\
  (!env es. well_typed_exprs env es ==>
     checker_env_ok tops env ==>
     EVERY (supported_pure_expr tops) es) /\
  (!env opt. well_typed_opt env opt ==>
     checker_env_ok tops env ==>
     case opt of NONE => T | SOME e => supported_pure_expr tops e) /\
  (!env kes. well_typed_named_exprs env kes ==>
     checker_env_ok tops env ==>
     EVERY (supported_pure_expr tops o SND) kes)
Proof
  ho_match_mp_tac well_typed_expr_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`supported_pure_expr _ (Name _ _)`]
  >- (rw[well_typed_expr_def, supported_pure_expr_def, every_pure_eta, expr_type_def] >>
      fs[checker_env_ok_def] >> metis_tac[checker_agg_ok_assignable])
  >~ [`supported_pure_expr _ (TopLevelName _ _)`]
  >- (simp[well_typed_expr_def, expr_type_def] >>
      metis_tac[checker_toplevel_name_pure])
  >~ [`supported_pure_expr _ (FlagMember _ _ _)`]
  >- rw[well_typed_expr_def, supported_pure_expr_def, every_pure_eta, expr_type_def,
        checker_agg_ok_base]
  >~ [`supported_pure_expr _ (IfExp _ _ _ _)`]
  >- (rw[well_typed_expr_def, supported_pure_expr_def, every_pure_eta, expr_type_def] >> res_tac >> fs[])
  >~ [`supported_pure_expr _ (Literal _ _)`]
  >- (rw[well_typed_expr_def, supported_pure_expr_def, every_pure_eta, expr_type_def] >>
      metis_tac[literal_agg_ok])
  >~ [`supported_pure_expr _ (StructLit _ _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def, expr_type_def,
        checker_agg_ok_base] >>
      res_tac >> drule_all checker_structlit_pure >> simp[])
  >~ [`supported_pure_expr _ (Subscript _ _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,  expr_type_def] >>
      res_tac >> gvs[] >>
      (drule_all checker_subscript_pure_value ORELSE
       drule_all checker_subscript_pure_place) >> simp[])
  >~ [`supported_pure_expr _ (Attribute _ _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,
        expr_type_def] >>
      res_tac >> drule_all checker_attribute_pure >> simp[])
  >~ [`supported_pure_expr _ (Builtin _ _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,
        expr_type_def] >>
      res_tac >>
      `!s b. blt = MakeArray s b ==> assignable_type env.type_defs ty` by
        (rw[] >> fs[]) >>
      `(blt = NamedConst ==> checker_agg_ok tops ty)` by
        (strip_tac >> gvs[] >> Cases_on `es` >> gvs[builtin_operands_ok_def] >>
         rename1 `_ (e::rest)` >> Cases_on `rest` >>
         gvs[builtin_operands_ok_def, well_typed_expr_def, well_typed_builtin_app_def] >>
         drule_all checker_named_const_operand_agg_ok >> simp[]) >>
      drule_all checker_builtin_pure >> simp[])
  >~ [`supported_pure_expr _ (TypeBuiltin _ _ _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,
        expr_type_def] >>
      res_tac >> fs[] >> drule_all checker_type_builtin_pure >>
      simp[])
  >~ [`supported_pure_expr _ (Pop _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,
        expr_type_def, supported_pure_expr_def, every_pure_eta] >>
      res_tac >> fs[] >> drule_all checker_pop_agg >> simp[])
  >~ [`supported_pure_expr _ (Call _ (IntCall _) _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,  expr_type_def, supported_pure_expr_def, every_pure_eta,
        supported_pure_exprs_every] >>
      res_tac >> fs[] >>
      drule_all_then assume_tac checker_intcall_agg >>
      drule_all_then assume_tac checker_env_fn_sig_internal >>
      Cases_on `src_id_opt` >> gvs[])
  >~ [`supported_pure_expr _ (Call _ (ExtCall _ _ _ _) _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,  expr_type_def, supported_pure_expr_def, every_pure_eta,
        supported_pure_exprs_every] >>
      res_tac >> fs[] >> metis_tac[checker_ret_agg])
  >~ [`supported_pure_expr _ (Call _ _ _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,
        expr_type_def, supported_pure_expr_def, every_pure_eta, supported_pure_exprs_every,
        raw_call_return_agg_ok, checker_agg_ok_base] >>
      res_tac >> fs[])
  >~ [`supported_pure_expr _ (Call _ _ _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,
        expr_type_def, supported_pure_expr_def, every_pure_eta, supported_pure_exprs_every,
        raw_call_return_agg_ok, checker_agg_ok_base] >>
      res_tac >> fs[])
  >~ [`supported_pure_expr _ (Call _ _ _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,
        expr_type_def, supported_pure_expr_def, every_pure_eta, supported_pure_exprs_every,
        raw_call_return_agg_ok, checker_agg_ok_base] >>
      res_tac >> fs[])
  >~ [`supported_pure_expr _ (Call _ _ _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,
        expr_type_def, supported_pure_expr_def, every_pure_eta, supported_pure_exprs_every,
        raw_call_return_agg_ok, checker_agg_ok_base] >>
      res_tac >> fs[])
  >~ [`supported_pure_expr _ (Call _ _ _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,
        expr_type_def, supported_pure_expr_def, every_pure_eta, supported_pure_exprs_every,
        raw_call_return_agg_ok, checker_agg_ok_base] >>
      res_tac >> fs[])
  >~ [`supported_pure_expr _ (Call _ _ _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,
        expr_type_def, supported_pure_expr_def, every_pure_eta, supported_pure_exprs_every,
        raw_call_return_agg_ok, checker_agg_ok_base] >>
      res_tac >> fs[])
  >~ [`supported_pure_expr _ (Call _ _ _ _)`]
  >- (rpt strip_tac >> gvs[well_typed_expr_def,
        expr_type_def, supported_pure_expr_def, every_pure_eta, supported_pure_exprs_every,
        raw_call_return_agg_ok, checker_agg_ok_base] >>
      res_tac >> fs[])
  >~ [`supported_place_expr _ (TopLevelName _ _)`]
  >- (rpt strip_tac >> fs[well_typed_expr_def] >>
      BasicProvers.EVERY_CASE_TAC >> fs[supported_pure_expr_def, every_pure_eta] >>
      drule_all checker_toplevel_name_place >> simp[])
  >~ [`supported_place_expr _ (Subscript _ _ _)`]
  >- (rpt strip_tac >> fs[well_typed_expr_def] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >> res_tac >> fs[] >>
      drule_all checker_subscript_place >> simp[])
  >~ [`type_place_target _ (SubscriptTarget _ _)`]
  >- (rpt strip_tac >> fs[well_typed_expr_def,  target_indices_def] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >> res_tac >> fs[])
  >~ [`type_place_target _ (AttributeTarget _ _)`]
  >- (rpt strip_tac >> fs[well_typed_expr_def,
        target_indices_def] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >> res_tac >> fs[])
  >~ [`well_typed_exprs _ (_::_)`]
  >- (rpt strip_tac >> fs[well_typed_expr_def] >> res_tac >> fs[])
  >~ [`well_typed_opt _ (SOME _)`]
  >- (rpt strip_tac >> fs[well_typed_expr_def] >>
      res_tac >> fs[])
  >~ [`well_typed_named_exprs _ (_::_)`]
  >- (rpt strip_tac >> fs[well_typed_expr_def] >> res_tac >> fs[])
  >> simp[well_typed_expr_def, target_indices_def]
QED
