(* Standalone facts for the cases of the mutual evaluator proof. *)

Theory vyperTypeEvalCaseProofs
Ancestors
  list rich_list sorting pred_set prim_rec arithmetic finite_map option pair sum
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperCreate vyperCreateFrame vyperCallFrame vyperInterpreter vyperCallOutcomeFrame vyperState vyperContext vyperStorage vyperTyping vyperLookup
  vyperImmutableMetadataFrame[ignore_grammar]
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeEnvExtension vyperTypeEnvPreservation vyperTypeScopePop
  vyperTypeABI vyperTypeBindArguments vyperTypeExprResult vyperTypeStmtResult
  vyperTypeCallOutcome[ignore_grammar] vyperCallOutcome[ignore_grammar]
  vyperTypeArgFits vyperTypeExtCallSoundness vyperTypeGlobalLookupSoundness vyperTypeAssignContext vyperTypeBuiltins vyperTypeExprSoundness vyperTypeAssignSoundness
  vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
  vyperEvalMisc vyperStatePreservation vyperAssignPreservesType vyperTypeStatePreservation
  vyperTypeCallGraph vyperTypeCallStackSoundness vyperEvalExprPreservesScopesDom vyperPlaceResultTyping vyperPlaceTyping
  vyperPlaceWriteSoundness vyperTargetPlaceWrite vyperPlaceMutationSoundness
  vyperAugAssignWriteSoundness vyperSystemControl
  vyperTypeEvalProofs
Libs
  wordsLib markerLib intLib

Theorem type_place_expr_IfExp_NONE:
  !env ty cond e_true e_false.
    type_place_expr env (IfExp ty cond e_true e_false) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

(* ===== Struct literal helpers ===== *)

Theorem well_typed_named_exprs_MAP_SND_stmt:
  !env kes. well_typed_named_exprs env kes ==> well_typed_exprs env (MAP SND kes)
Proof
  gen_tac >> Induct >> simp[well_typed_expr_def] >>
  Cases >> simp[well_typed_expr_def]
QED

Theorem struct_has_type_zip_same_names_stmt:
  !names tvs vs.
    LENGTH names = LENGTH tvs /\ LENGTH tvs = LENGTH vs /\
    LIST_REL value_has_type tvs vs ==>
    struct_has_type (ZIP (names,tvs)) (ZIP (names,vs))
Proof
  Induct >> simp[Once value_has_type_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `tvs` >> Cases_on `vs` >> gvs[Once value_has_type_def]
QED

Theorem OPT_MMAP_evaluate_type_mono_stmt:
  !types tenv nid tvs.
    OPT_MMAP (evaluate_type (tenv \\ nid)) types = SOME tvs ==>
    OPT_MMAP (evaluate_type tenv) types = SOME tvs
Proof
  Induct >> simp[OPT_MMAP_def] >>
  rpt gen_tac >>
  Cases_on `evaluate_type (tenv \\ nid) h` >> simp[] >>
  Cases_on `OPT_MMAP (evaluate_type (tenv \\ nid)) types` >> simp[] >>
  strip_tac >> gvs[] >>
  imp_res_tac evaluate_type_mono >> simp[] >>
  first_x_assum (qspecl_then [`tenv`, `nid`] mp_tac) >> simp[]
QED

(* A struct literal's field values, typed at the field expressions' types,
   have the declared field types those types fit. *)
Theorem struct_lit_value_has_type:
  evaluate_type tenv (StructT nsid) = SOME stv /\
  FLOOKUP tenv nsid = SOME (StructArgs args) /\
  arg_types_fit (MAP (expr_type o SND) kes) (MAP SND args) /\
  LIST_REL (\e tv. evaluate_type tenv (expr_type e) = SOME tv) (MAP SND kes) tvs /\
  LIST_REL value_has_type tvs vs ==>
  value_has_type stv (StructV (ZIP (MAP FST args,vs)))
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type _ (StructT _) = SOME _` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  strip_tac >> gvs[value_has_type_def] >>
  drule OPT_MMAP_evaluate_type_mono_stmt >> strip_tac >>
  drule OPT_MMAP_LIST_REL >> strip_tac >>
  `LIST_REL (\t tv. evaluate_type tenv t = SOME tv)
     (MAP (expr_type o SND) kes) tvs` by
    (qpat_x_assum `LIST_REL _ (MAP SND kes) tvs` mp_tac >>
     simp[LIST_REL_MAP1, combinTheory.o_DEF]) >>
  rename1 `LIST_REL _ (MAP SND args) ftvs` >>
  `values_have_types ftvs vs` by
    metis_tac[vyperTypeArgFitsTheory.arg_type_fits_value_has_type,
              vyperTypeDefaultsTheory.values_have_types_LIST_REL] >>
  irule struct_has_type_zip_same_names_stmt >>
  gvs[GSYM vyperTypeDefaultsTheory.values_have_types_LIST_REL] >>
  imp_res_tac LIST_REL_LENGTH >> gvs[LENGTH_MAP] >>
  metis_tac[vyperTypeDefaultsTheory.values_have_types_LIST_REL, LIST_REL_LENGTH]
QED

Theorem struct_lit_expr_result_typed:
  well_formed_type env.type_defs (StructT nsid) /\
  FLOOKUP env.type_defs (nsid) = SOME (StructArgs args) /\
  MAP FST kes = MAP FST args /\
  arg_types_fit (MAP (expr_type o SND) kes) (MAP SND args) /\
  exprs_runtime_typed env (MAP SND kes) vs ==>
  eval_result_typed (env,cx,st)
    (Value (StructV (ZIP (MAP FST args,vs)))) (Type (StructT nsid))
Proof
  rw[exprs_runtime_typed_def, eval_result_typed_def] >>
  gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  metis_tac[struct_lit_value_has_type]
QED

Theorem type_place_expr_StructLit_NONE_stmt:
  !env ty sid kes.
    type_place_expr env (StructLit ty sid kes) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

(* ===== Subscript expression helpers ===== *)

Theorem select_ordinary_subscript_sound:
  !env cx st base ct ie rt idx res st'.
  env_consistent env cx st /\ state_well_typed st /\
  eval_result_typed (env,cx,st) base (Type ct) /\ live_memory_result st base /\
  subscript_type_ok ct ie rt /\ subscript_index_matches ct ie idx /\
  value_runtime_typed env (expr_type ie) idx /\
  select_result cx ct base (ValueSubscript idx) st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  (case res of INL pv => eval_result_typed (env,cx,st') pv (Type rt) | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  Cases_on `ct` >>
  gvs[subscript_type_ok_def, subscript_index_matches_def, AllCaseEqs()]
  >- (gvs[eval_result_typed_def] >>
      drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
      `LENGTH tvs = LENGTH l` by metis_tac[LIST_REL_LENGTH] >>
      `evaluate_type (get_tenv cx) (EL (Num n) l) = SOME (EL (Num n) tvs)` by
        gvs[LIST_REL_EL_EQN] >>
      `well_formed_type_value (TupleTV tvs)` by
        metis_tac[evaluate_type_well_formed_type_value] >>
      `subscript_type (TupleTV tvs) (ValueSubscript (IntV n)) = SOME (EL (Num n) tvs)` by
        simp[subscript_type_def, oEL_THM] >>
      `subscripts_type (TupleTV tvs) [ValueSubscript (IntV n)] = SOME (EL (Num n) tvs)` by
        simp[subscripts_type_def] >>
      Cases_on `base'` >> gvs[select_result_def]
       >- (rename1 `value_has_type (TupleTV tvs) vv` >>
           Cases_on `evaluate_subscripts (TupleTV tvs) vv [ValueSubscript (IntV n)]` >>
           gvs[bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def] >>
           simp[no_type_error_result_def]
           >- (drule_all vyperPlaceStatePreservationTheory.evaluate_subscripts_type >> simp[]) >>
           metis_tac[evaluate_subscripts_typed_error]) >>
       rename1 `runtime_place_typed cx st p (TupleTV tvs)` >>
       drule_all extend_live_tuple_place_sound >> strip_tac >>
       `st' = st` by metis_tac[vyperPlaceFramesTheory.extend_place_PlaceR_state] >>
       Cases_on `res` >> gvs[]) >>
  qpat_x_assum `value_runtime_typed _ _ _` mp_tac >>
  simp[value_runtime_typed_def] >> strip_tac >>
  drule_all int_typed_value_is_IntV >> strip_tac >> gvs[] >>
  gvs[eval_result_typed_def] >>
  drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
  `well_formed_type_value (ArrayTV elem_tv b)` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  Cases_on `base'` >> gvs[select_result_def]
  >- (rename1 `value_has_type (ArrayTV elem_tv b) vv` >>
      Cases_on `evaluate_subscripts (ArrayTV elem_tv b) vv [ValueSubscript (IntV i)]` >>
      gvs[bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def] >>
      drule_all array_subscript_place_check >> simp[no_type_error_result_def] >>
      strip_tac >>
      `subscripts_type (ArrayTV elem_tv b) [ValueSubscript (IntV i)] = SOME elem_tv` by
        simp[subscripts_type_def] >>
      drule_all vyperPlaceStatePreservationTheory.evaluate_subscripts_type >> simp[]) >>
  drule_all extend_live_array_place_sound >> strip_tac >>
  `st' = st` by metis_tac[vyperPlaceFramesTheory.extend_place_PlaceR_state] >>
  Cases_on `res` >> gvs[]
QED

Theorem select_projection_subscript_sound:
  !env cx st bp bvt ct ie out idx res st'.
  env_consistent env cx st /\ state_well_typed st /\
  eval_result_typed (env,cx,st) bp bvt /\ live_memory_result st bp /\
  well_formed_vtype env.type_defs bvt /\ vtype_annotation_ok bvt ct /\
  subscript_vtype bvt (expr_type ie) = SOME out /\
  value_runtime_typed env (expr_type ie) idx /\
  select_result cx ct bp (ValueSubscript idx) st = (res,st') ==>
  st' = st with storage_trace := st'.storage_trace /\ no_type_error_result res /\
  (case res of INL pv => eval_result_typed (env,cx,st') pv out | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `bvt`
  >- (rename1 `Type input_ty` >> Cases_on `input_ty` >>
      gvs[subscript_vtype_def, vtype_annotation_ok_def] >>
      `subscript_type_ok (ArrayT t b) ie t /\
       subscript_index_matches (ArrayT t b) ie idx` by
        simp[subscript_type_ok_def, subscript_index_matches_def] >>
      drule_all select_ordinary_subscript_sound >> strip_tac >> gvs[]) >>
  gvs[eval_result_typed_def] >>
  gvs[select_result_def, vtype_annotation_ok_def] >>
  conj_tac
  >- metis_tac[vyperPlaceFramesTheory.extend_place_state] >>
  drule_all extend_target_hashmap_place_sound >>
  simp[eval_result_typed_def]
QED

Theorem value_has_type_TupleTV_dest_stmt[local]:
  !tvs v. value_has_type (TupleTV tvs) v ==>
          ?vs. v = ArrayV (TupleV vs) /\ values_have_types tvs vs
Proof
  Cases_on `v` >> gvs[value_has_type_inv] >>
  Cases_on `a` >> gvs[value_has_type_inv]
QED

Theorem type_place_expr_well_formed_vtype_stmt:
  !env cx st e vt.
    env_consistent env cx st /\ type_place_expr env e = SOME vt ==>
    well_formed_vtype env.type_defs vt
Proof
  measureInduct_on `expr_size e` >>
  rpt strip_tac >>
  Cases_on `e` >>
  gvs[Once well_typed_expr_def, AllCaseEqs()]
  >- (PairCases_on `p` >>
      qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
      simp[well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
      gvs[env_consistent_def, env_context_consistent_def] >>
      first_x_assum drule >> simp[]) >>
  qpat_x_assum `!y. expr_size y < _ ==> _` (qspec_then `e'` mp_tac) >>
  (impl_tac >- simp[expr_size_def]) >>
  disch_then (qspecl_then [`env`,`cx`,`st`,`vt'`] mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[subscript_vtype_well_formed_stmt]
QED

Theorem type_place_expr_annotation_ok_stmt:
  !env e vt. type_place_expr env e = SOME vt ==> vtype_annotation_ok vt (expr_type e)
Proof
  Cases_on `e` >> simp[expr_type_def] >> rpt strip_tac >>
  TRY (PairCases_on `p`) >>
  qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
  simp[Once well_typed_expr_def, vtype_annotation_ok_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem hashmap_place_expr_no_early_read[local]:
  !env e kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
    ~base_through_dynarray e
Proof
  measureInduct_on `expr_size e` >> rpt strip_tac >> Cases_on `e` >>
  gvs[Once well_typed_expr_def, AllCaseEqs(), base_through_dynarray_def] >>
  (Cases_on `vt'`
   >- (rename1 `subscript_vtype (Type bt) _ = _` >>
       Cases_on `bt` >> gvs[subscript_vtype_def, AllCaseEqs()]) >>
   gvs[subscript_vtype_def, AllCaseEqs()] >>
   drule type_place_expr_annotation_ok_stmt >>
   simp[vtype_annotation_ok_def] >> strip_tac >> gvs[] >>
   qpat_x_assum `!y. _` (qspec_then `e'` mp_tac) >>
   simp[expr_size_def] >> metis_tac[])
QED

Theorem place_optional_read_result_live_typed:
  type_place_expr env e = SOME vt /\
  state_well_typed st /\ eval_result_typed (env,cx,st) pv vt /\
  live_memory_result st pv /\
  (if subscript_reads_base cx e e' then bind (read_result cx pv) (\v. return (Value v))
   else return pv) st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  (case res of INL out => eval_result_typed (env,cx,st') out vt /\
                         live_memory_result st' out | INR _ => T)
Proof
  Cases_on `vt` >> strip_tac
  >- (drule_all optional_read_result_live_typed >> simp[]) >>
  drule hashmap_place_expr_no_early_read >> strip_tac >>
  `~subscript_reads_base cx e e'` by
    metis_tac[subscript_reads_base_through_dynarray] >>
  gvs[return_def, no_type_error_result_def]
QED

Theorem eval_expr_subscript_index_matches_stmt:
  !ct ie rt cx st tv st1 idx st2.
    subscript_type_ok ct ie rt /\
    eval_expr cx ie st = (INL tv,st1) /\
    read_result cx tv st1 = (INL idx,st2) ==>
    subscript_index_matches ct ie idx
Proof
  rpt gen_tac >> Cases_on `ct` >> simp[subscript_index_matches_def] >>
  rpt strip_tac >>
  gvs[subscript_type_ok_tuple] >>
  gvs[Once evaluate_def, evaluate_literal_def, return_def, read_result_def]
QED

(* ===== Attribute expression helpers ===== *)

Theorem select_attribute_sound:
  !env cx st bp ct id rt res st'.
  env_consistent env cx st /\ state_well_typed st /\
  eval_result_typed (env,cx,st) bp (Type ct) /\ live_memory_result st bp /\
  attribute_type env.type_defs ct id = SOME rt /\
  select_result cx ct bp (AttrSubscript id) st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  (case res of INL pv => eval_result_typed (env,cx,st') pv (Type rt) | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  Cases_on `bp`
  >- (gvs[eval_result_typed_def] >>
      drule_all attribute_type_runtime_step >> strip_tac >>
      `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
      `subscripts_type tv [AttrSubscript id] = SOME field_tv` by
        simp[subscripts_type_def] >>
      Cases_on `evaluate_subscripts tv v [AttrSubscript id]` >>
      gvs[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
          return_def, raise_def] >> simp[no_type_error_result_def]
      >- (drule_all vyperPlaceStatePreservationTheory.evaluate_subscripts_type >> simp[]) >>
      metis_tac[evaluate_subscripts_typed_error])
  >- (rename1 `PlaceR p` >>
      `?tv. evaluate_type env.type_defs ct = SOME tv /\ runtime_place_typed cx st p tv` by
        gvs[eval_result_typed_def] >>
      drule_all attribute_type_runtime_step >> strip_tac >>
      gvs[select_result_def] >>
      `st' = st` by metis_tac[vyperPlaceFramesTheory.extend_place_PlaceR_state] >>
      `no_type_error_result res` by metis_tac[extend_live_place_attribute_no_type_error] >>
      Cases_on `res` >> simp[] >>
      `eval_result_typed (env,cx,st) (PlaceR p) (Type ct)` by
        (simp[eval_result_typed_def] >> metis_tac[]) >>
      `attribute_type env.type_defs ct id = SOME rt` by simp[] >>
      drule_all extend_place_attribute_success_typed >> simp[]) >>
  gvs[eval_result_typed_def]
QED

(* ===== Builtin and type-builtin expression helpers ===== *)

Theorem eval_exprs_failure_builtin_case:
  ((case
      case (INR x,st) of
        (INL vs,s'') =>
          (case evaluate_builtin cx s''.accounts ty bt (MAP expr_type es) vs of
             INL v => return v
           | INR e => raise (Error e)) s''
      | (INR e,s'') => (INR e,s'')
    of
      (INL v,s'') => (INL (Value v),s'')
    | (INR e,s'') => (INR e,s'')) = (res,st')) <=>
  res = INR x /\ st' = st
Proof
  simp[] >> metis_tac[]
QED

Theorem eval_exprs_failure_type_builtin_case:
  ((case (INR x,st) of
      (INL vs,s'') =>
        (case
           (case evaluate_type_builtin cx tb target_ty (MAP expr_type es) vs of
              INL v => return v
            | INR e => raise (Error e)) s''
         of
           (INL v,s'') => (INL (Value v),s'')
         | (INR e,s'') => (INR e,s''))
    | (INR e,s'') => (INR e,s'')) = (res,st')) <=>
  res = INR x /\ st' = st
Proof
  simp[] >> metis_tac[]
QED

Theorem type_builtin_exprs_runtime_no_type_error_stmt_adapter:
  env.type_defs = get_tenv cx /\
  type_builtin_result_ok env.type_defs tb result_ty target_ty (MAP expr_type es) /\
  well_typed_type_builtin_args tb target_ty (MAP expr_type es) /\
  well_formed_type env.type_defs result_ty /\
  exprs_runtime_typed env es vs /\
  context_well_typed cx ==>
  !msg. evaluate_type_builtin cx tb target_ty (MAP expr_type es) vs <> INR (TypeError msg)
Proof
  rw[exprs_runtime_typed_def] >>
  `MAP (evaluate_type (get_tenv cx)) (MAP expr_type es) = MAP SOME tvs` by
    gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP] >>
  `?result_tv. evaluate_type (get_tenv cx) result_ty = SOME result_tv` by
    gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  mp_tac (Q.INST [`ts` |-> `MAP expr_type es`]
            well_typed_type_builtin_no_type_error) >>
  gvs[]
QED

Theorem type_builtin_exprs_runtime_success_type_stmt_adapter:
  env.type_defs = get_tenv cx /\
  type_builtin_result_ok env.type_defs tb result_ty target_ty (MAP expr_type es) /\
  well_typed_type_builtin_args tb target_ty (MAP expr_type es) /\
  well_formed_type env.type_defs result_ty /\
  exprs_runtime_typed env es vs /\
  context_well_typed cx /\
  evaluate_type_builtin cx tb target_ty (MAP expr_type es) vs = INL v ==>
  value_runtime_typed env result_ty v
Proof
  rw[exprs_runtime_typed_def, value_runtime_typed_def] >>
  `MAP (evaluate_type (get_tenv cx)) (MAP expr_type es) = MAP SOME tvs` by
    gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP] >>
  `?result_tv. evaluate_type (get_tenv cx) result_ty = SOME result_tv` by
    gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  qexists_tac `result_tv` >> simp[] >>
  irule well_typed_type_builtin_success_type >>
  qexistsl_tac [`cx`, `result_ty`, `target_ty`, `tb`, `MAP expr_type es`, `tvs`, `vs`] >>
  gvs[]
QED

Theorem Len_live_result_sound:
  state_well_typed st /\ well_typed_builtin_app ty Len [arg_ty] /\
  eval_result_typed (env,cx,st) pv (Type arg_ty) /\ live_memory_result st pv /\
  result_array_length cx pv st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  (case res of INL n => eval_result_typed (env,cx,st) (Value (IntV (&n))) (Type ty) | INR _ => T)
Proof
  strip_tac >>
  Cases_on `?tr slot tv bd. pv = PlaceR (StoragePlace tr slot (ArrayTV tv bd))`
  >- (gvs[] >>
      gvs[eval_result_typed_def, runtime_place_typed_storage] >>
      Cases_on `bd` >>
      gvs[result_array_length_def, return_def, bind_def, get_storage_backend_def,
          get_accounts_def, get_transient_storage_def, AllCaseEqs(),
          no_type_error_result_def]
      >- (Cases_on `arg_ty` >>
          gvs[evaluate_type_def, AllCaseEqs(), well_typed_builtin_app_def,
              value_has_type_def, type_slot_size_def] >>
          `n <= n * type_slot_size tv` by simp[] >> decide_tac)
      >- (drule vyperStorageBackendTheory.get_storage_backend_state >> strip_tac >> gvs[] >>
          `w2n (lookup_storage slot storage) < dimword(:256)` by
            simp_tac(srw_ss())[wordsTheory.w2n_lt] >>
          gvs[well_typed_builtin_app_def, evaluate_type_def, value_has_type_def]) >>
      metis_tac[get_storage_backend_no_error]) >>
  `result_array_length cx pv = do v <- read_result cx pv; result_array_length cx (Value v) od` by
    (Cases_on `pv`
     >- simp[FUN_EQ_THM, result_array_length_def, read_result_def, return_def, bind_def]
     >- (rename1 `PlaceR p` >> namedCases_on `p` ["tr slot ptv", "mid path", "src iid path"]
         >- (Cases_on `ptv` >>
             gvs[result_array_length_def, FUN_EQ_THM, bind_def, read_result_def, return_def]) >>
         simp[result_array_length_def, FUN_EQ_THM, bind_def, read_result_def, return_def]) >>
     simp[FUN_EQ_THM, result_array_length_def, read_result_def, raise_def, bind_def]) >>
  qpat_x_assum `result_array_length cx pv st = _` mp_tac >>
  asm_rewrite_tac[] >> simp_tac(srw_ss())[bind_def] >>
  Cases_on `read_result cx pv st` >>
  rename1 `read_result cx pv st = (rr,rs)` >>
  drule_all live_result_read_typed >> strip_tac >> gvs[] >>
  Cases_on `rr`
  >- (rename1 `read_result cx pv st = (INL v,st)` >>
      simp_tac(srw_ss())[] >> strip_tac >>
      `st' = st` by metis_tac[result_array_length_state] >> gvs[] >>
      gvs[value_runtime_typed_def] >>
      `value_result_typed (Value v) tv` by simp[value_result_typed_def] >>
      Cases_on `res` >> simp[no_type_error_result_def]
      >- (`well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
          `x < dimword(:256)` by (drule_all Len_result_fits_uint256 >> simp[]) >>
          gvs[well_typed_builtin_app_def, eval_result_typed_def,
              evaluate_type_def, value_has_type_def]) >>
      `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
      Cases_on `y` >> simp[no_type_error_result_def] >>
      Cases_on `e` >> simp[no_type_error_result_def] >>
      metis_tac[Len_result_array_length_no_type_error]) >>
  simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]
QED

Theorem code_slice_operand_typing:
  code_slice_source bt es = SOME (ct,addr) /\
  well_typed_exprs env es ==>
  well_typed_exprs env (TL es) /\
  well_typed_exprs env [addr] /\
  well_typed_expr env (Builtin ct (Acc Code) [addr])
Proof
  rw[code_slice_source_SOME] >>
  gvs[Once well_typed_expr_def] >>
  gvs[Once well_typed_expr_def] >>
  gvs[Once well_typed_expr_def]
QED

Theorem code_slice_operand_call_safe:
  code_slice_source bt es = SOME (ct,addr) /\
  call_evaluation_safe cx (int_calls_exprs es) ==>
  call_evaluation_safe cx (int_calls_exprs (TL es)) /\
  call_evaluation_safe cx (int_calls_exprs [addr])
Proof
  rw[code_slice_source_SOME] >>
  irule call_evaluation_safe_mono >>
  goal_assum (drule_at Any) >>
  simp[int_calls_expr_def, MEM_APPEND] >> metis_tac[]
QED

Theorem code_access_runtime_typed[local]:
  env.type_defs = get_tenv cx /\
  well_typed_expr env (Builtin ct (Acc Code) [addr]) /\
  exprs_runtime_typed env [addr] avs ==>
  ?tv tvs. evaluate_type (get_tenv cx) ct = SOME tv /\
    well_typed_builtin_app ct (Acc Code) [expr_type addr] /\
    MAP (evaluate_type (get_tenv cx)) [expr_type addr] = MAP SOME tvs /\
    LIST_REL value_has_type tvs avs
Proof
  simp[exprs_runtime_typed_def] >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  qexists_tac `tvs` >> gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP]
QED

Theorem code_access_runtime_success:
  env.type_defs = get_tenv cx /\
  well_typed_expr env (Builtin ct (Acc Code) [addr]) /\
  exprs_runtime_typed env [addr] avs /\
  context_well_typed cx /\ accounts_well_typed acc /\
  evaluate_builtin cx acc ct (Acc Code) [expr_type addr] avs = INL v ==>
  value_runtime_typed env ct v
Proof
  strip_tac >> drule_all code_access_runtime_typed >> strip_tac >>
  simp[value_runtime_typed_def] >>
  drule_at (Pos last) well_typed_builtin_app_success_type >>
  simp[] >> disch_then (qspec_then `tvs` mp_tac) >> simp[]
QED

Theorem code_access_runtime_no_type_error:
  env.type_defs = get_tenv cx /\
  well_typed_expr env (Builtin ct (Acc Code) [addr]) /\
  exprs_runtime_typed env [addr] avs /\
  context_well_typed cx /\ accounts_well_typed acc ==>
  !msg. evaluate_builtin cx acc ct (Acc Code) [expr_type addr] avs <> INR (TypeError msg)
Proof
  strip_tac >> drule_all code_access_runtime_typed >> strip_tac >>
  irule well_typed_builtin_app_no_type_error >> simp[] >>
  metis_tac[]
QED

Theorem exprs_runtime_typed_code_slice_cons:
  code_slice_source bt es = SOME (ct,addr) /\
  value_runtime_typed env ct v /\ exprs_runtime_typed env (TL es) vs ==>
  exprs_runtime_typed env es (v::vs)
Proof
  rw[code_slice_source_SOME, exprs_runtime_typed_def, value_runtime_typed_def] >>
  qexists_tac `tv::tvs` >> gvs[expr_type_def]
QED

Theorem code_access_self_runtime_eval:
  env.type_defs = get_tenv cx /\
  well_typed_expr env (Builtin ct (Acc Code) [addr]) /\
  exprs_runtime_typed env [addr] avs ==>
  evaluate_code_source cx acc T ct (expr_type addr) avs =
    INL (BytesV cx.txn.code)
Proof
  strip_tac >> drule_all code_access_runtime_typed >> strip_tac >>
  gvs[well_typed_builtin_app_def, evaluate_type_def, MAP_EQ_CONS] >>
  rename1 `value_has_type (BaseTV AddressT) av` >>
  Cases_on `av` >> gvs[value_has_type_def, evaluate_code_source_def]
QED

Theorem code_slice_self_builtin_eval:
  env.type_defs = get_tenv cx /\
  code_slice_source bt es = SOME (ct, addr) /\
  well_typed_expr env (Builtin ct (Acc Code) [addr]) /\
  well_typed_builtin_app ty bt (MAP expr_type es) /\
  well_formed_type env.type_defs ty /\
  exprs_runtime_typed env (TL es) tail_vs ==>
  (?n.
     bt = Slice n /\
     ty = BaseT (BytesT (Dynamic n)) /\
     (!msg. evaluate_builtin cx acc ty bt (MAP expr_type es)
              (BytesV cx.txn.code :: tail_vs) <> INR (TypeError msg)) /\
     (!v. evaluate_builtin cx acc ty bt (MAP expr_type es)
            (BytesV cx.txn.code :: tail_vs) = INL v ==>
          value_runtime_typed env ty v))
Proof
  strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  gvs[code_slice_source_SOME, well_typed_builtin_app_def, account_item_type_def,
      expr_type_def, exprs_runtime_typed_def, well_formed_type_def,
      evaluate_type_def, IS_SOME_EXISTS, MAP_EQ_CONS] >>
  rename1 `[BytesV cx.txn.code; sv; lv]` >>
  Cases_on `sv` >> Cases_on `lv` >>
  gvs[value_has_type_def, evaluate_builtin_def] >>
  conj_tac
  >- (gen_tac >> irule evaluate_slice_BytesV_no_type_error >> simp[]) >>
  rpt strip_tac >>
  drule evaluate_slice_BytesV_success_type >> strip_tac >>
  gvs[value_runtime_typed_def, evaluate_type_def, value_has_type_def]
QED

(* ===== Internal call helpers ===== *)

Theorem defaults_env_empty_frame_consistent:
  !env_body cx st.
    env_context_consistent env_body cx /\
    env_immutables_consistent env_body cx st ==>
    env_consistent (defaults_env env_body) cx (st with scopes := [FEMPTY])
Proof
  rw[defaults_env_def, env_consistent_def, env_context_consistent_def,
     env_scopes_consistent_def, env_immutables_consistent_def,
     lookup_scopes_def] >>
  gvs[] >>
  metis_tac[]
QED

Theorem default_frame_eval_result:
  !cx es st prev res st'.
    finally
      (do set_scopes [FEMPTY]; eval_exprs cx es od)
      (set_scopes prev) st = (res,st') ==>
    ?framed_st.
      eval_exprs cx es (st with scopes := [FEMPTY]) = (res,framed_st) /\
      st' = (framed_st with scopes := prev)
Proof
  rw[finally_def, bind_def, ignore_bind_def, set_scopes_def,
     return_def, raise_def] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  Cases_on `q` >>
  gvs[ignore_bind_def, set_scopes_def, return_def, raise_def]
QED

Theorem state_well_typed_restore_scopes[local]:
  !st scopes_src.
    state_well_typed st /\ state_well_typed scopes_src ==>
    state_well_typed (st with scopes := scopes_src.scopes)
Proof
  rw[state_well_typed_def]
QED

Theorem env_consistent_restore_intcall_default_frame[local]:
  !env env_body cx src_id_opt fn base_st framed_st.
    env_consistent env cx base_st /\
    env_consistent (defaults_env env_body)
      (cx with stk updated_by CONS (src_id_opt,fn)) framed_st /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    env_consistent env cx (framed_st with scopes := base_st.scopes)
Proof
  rw[env_consistent_def]
  >- (qpat_x_assum `env_scopes_consistent env cx base_st` mp_tac >>
      simp[env_scopes_consistent_def] >> metis_tac[]) >>
  gvs[env_immutables_consistent_def, defaults_env_def,
      get_tenv_stk_irrelevant, get_module_code_stk_irrelevant] >>
  metis_tac[]
QED

Theorem intcall_defaults_frame_sound:
  env_consistent env cx base_st /\ state_well_typed base_st /\
  env_body.type_defs = get_tenv cx /\
  env_body.bare_globals = env.bare_globals /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  (!r fs. eval_exprs (cx with stk updated_by CONS (src_id_opt,fn)) needed
               (base_st with scopes := [FEMPTY]) = (r,fs) ==>
     state_well_typed fs /\
     env_consistent (defaults_env env_body)
       (cx with stk updated_by CONS (src_id_opt,fn)) fs /\
     accounts_well_typed fs.accounts /\ no_type_error_result r /\
     (case r of INL vs => exprs_runtime_typed (defaults_env env_body) needed vs
              | INR _ => T)) /\
  finally (do set_scopes [FEMPTY];
              eval_exprs (cx with stk updated_by CONS (src_id_opt,fn)) needed od)
    (set_scopes base_st.scopes) base_st = (res,st') ==>
  st'.scopes = base_st.scopes /\ state_well_typed st' /\
  env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
  no_type_error_result res /\
  (case res of INL vs => exprs_runtime_typed (defaults_env env_body) needed vs
             | INR _ => T)
Proof
  strip_tac >> drule default_frame_eval_result >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `state_well_typed (framed_st with scopes := base_st.scopes)` by
    (irule state_well_typed_restore_scopes >> simp[]) >>
  `env_consistent env cx (framed_st with scopes := base_st.scopes)` by
    (metis_tac[env_consistent_restore_intcall_default_frame]) >>
  gvs[]
QED

Theorem intcall_safe_cast_NoneTV_NoneV[local]:
  safe_cast NoneTV NoneV = SOME NoneV
Proof
  simp[Once safe_cast_def]
QED

Theorem intcall_finally_try_handle_success_rv[local]:
  !fn_m cleanup pushed_st rv st_final.
    finally (try (do fn_m; return NoneV od) handle_function)
      cleanup pushed_st = (INL rv,st_final) ==>
    (rv = NoneV /\ (?st_bdy. fn_m pushed_st = (INL (),st_bdy))) \/
    (?v st_bdy. rv = v /\ fn_m pushed_st = (INR (ReturnException v),st_bdy))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[finally_def] >>
  Cases_on `try (do fn_m; return NoneV od) handle_function pushed_st` >>
  rename1 `_ = (try_res,try_st)` >>
  Cases_on `try_res` >> gvs[ignore_bind_apply] >>
  Cases_on `cleanup try_st` >> rename1 `_ = (cl_res,cl_st)` >>
  Cases_on `cl_res` >> gvs[return_def, raise_def] >>
  gvs[try_def] >>
  Cases_on `(do fn_m; return NoneV od) pushed_st` >>
  rename1 `_ = (inner_res,inner_st)` >>
  Cases_on `inner_res` >> gvs[return_def]
  >- (gvs[ignore_bind_apply, return_def] >>
      Cases_on `fn_m pushed_st` >> rename1 `_ = (fn_res,fn_st)` >>
      Cases_on `fn_res` >> gvs[return_def, raise_def])
  >- (Cases_on `y` >>
      gvs[handle_function_def, return_def, raise_def] >>
      Cases_on `fn_m pushed_st` >> Cases_on `q` >>
      gvs[return_def, raise_def, ignore_bind_apply])
QED

Theorem intcall_finally_try_handle_success_cleanup[local]:
  !fn_m cleanup pushed_st rv st_final.
    finally (try (do fn_m; return NoneV od) handle_function)
      cleanup pushed_st = (INL rv,st_final) ==>
    (rv = NoneV /\
     (?st_bdy. fn_m pushed_st = (INL (),st_bdy) /\
               cleanup st_bdy = (INL (),st_final))) \/
    (?v st_bdy. rv = v /\ fn_m pushed_st = (INR (ReturnException v),st_bdy) /\
                cleanup st_bdy = (INL (),st_final))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[finally_def] >>
  Cases_on `try (do fn_m; return NoneV od) handle_function pushed_st` >>
  rename1 `_ = (try_res,try_st)` >>
  Cases_on `try_res` >> gvs[ignore_bind_apply] >>
  Cases_on `cleanup try_st` >> rename1 `_ = (cl_res,cl_st)` >>
  Cases_on `cl_res` >> gvs[return_def, raise_def] >>
  gvs[try_def] >>
  Cases_on `(do fn_m; return NoneV od) pushed_st` >>
  rename1 `_ = (inner_res,inner_st)` >>
  Cases_on `inner_res` >> gvs[return_def]
  >- (gvs[ignore_bind_apply, return_def] >>
      Cases_on `fn_m pushed_st` >> rename1 `_ = (fn_res,fn_st)` >>
      Cases_on `fn_res` >> gvs[return_def, raise_def])
  >- (Cases_on `y` >>
      gvs[handle_function_def, return_def, raise_def] >>
      Cases_on `fn_m pushed_st` >> Cases_on `q` >>
      gvs[return_def, raise_def, ignore_bind_apply])
QED

Theorem intcall_finally_try_handle_inr_body_cleanup_cases[local]:
  !fn_m cleanup pushed_st y fin_st.
    finally (try (do fn_m; return NoneV od) handle_function)
      cleanup pushed_st = (INR y,fin_st) ==>
    (?st_bdy.
       fn_m pushed_st = (INL (),st_bdy) /\
       cleanup st_bdy = (INR y,fin_st)) \/
    (?body_exn st_bdy cleanup_res.
       fn_m pushed_st = (INR body_exn,st_bdy) /\
       cleanup st_bdy = (cleanup_res,fin_st))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[finally_def] >>
  Cases_on `try (do fn_m; return NoneV od) handle_function pushed_st` >>
  rename1 `_ = (try_res,try_st)` >>
  Cases_on `try_res` >> gvs[ignore_bind_apply] >>
  Cases_on `cleanup try_st` >> rename1 `_ = (cl_res,cl_st)` >>
  Cases_on `cl_res` >> gvs[return_def, raise_def] >>
  gvs[try_def] >>
  Cases_on `(do fn_m; return NoneV od) pushed_st` >>
  rename1 `_ = (inner_res,inner_st)` >>
  Cases_on `inner_res` >> gvs[return_def]
  >- (gvs[ignore_bind_apply, return_def] >>
      Cases_on `fn_m pushed_st` >> rename1 `_ = (fn_res,fn_st)` >>
      Cases_on `fn_res` >> gvs[return_def, raise_def]) >>
  Cases_on `fn_m pushed_st` >> rename1 `_ = (fn_res,fn_st)` >>
  Cases_on `fn_res` >>
  gvs[bind_apply, bind_def, return_def, raise_def, ignore_bind_apply] >>
  rename1 `handle_function body_exn _ = _` >>
  Cases_on `body_exn` >>
  gvs[handle_function_def, bind_apply, bind_def, return_def, raise_def,
      ignore_bind_apply]
QED

Theorem lift_safe_cast_value_has_type_no_type_error[local]:
  !tv v msg st res st'.
    value_has_type tv v /\
    lift_option_type (safe_cast tv v) msg st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  `safe_cast tv v = SOME v` by (irule safe_cast_well_typed >> simp[]) >>
  gvs[lift_option_type_def, return_def, raise_def, no_type_error_result_def]
QED

Theorem env_consistent_restore_intcall_body_frame[local]:
  !env env_body cx src_id_opt fn base_st framed_st.
    env_consistent env cx base_st /\
    env_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) framed_st /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    env_consistent env cx (framed_st with scopes := base_st.scopes)
Proof
  rw[env_consistent_def]
  >- (qpat_x_assum `env_scopes_consistent env cx base_st` mp_tac >>
      simp[env_scopes_consistent_def] >> metis_tac[]) >>
  gvs[env_immutables_consistent_def, get_tenv_stk_irrelevant,
      get_module_code_stk_irrelevant] >>
  metis_tac[]
QED

Theorem env_consistent_same_scopes_immutables[local]:
  !env cx st st'.
    env_consistent env cx st /\
    st'.scopes = st.scopes /\
    st'.immutables = st.immutables ==>
    env_consistent env cx st'
Proof
  rw[env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def] >> metis_tac[]
QED

Theorem intcall_cleanup_frame_restore_sound[local]:
  !env env_body cx src_id_opt fn args_st st_bdy fin_st.
    env_consistent env cx args_st /\
    env_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) st_bdy /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    state_well_typed args_st /\
    state_well_typed st_bdy /\
    accounts_well_typed st_bdy.accounts /\
    fin_st.scopes = args_st.scopes /\
    fin_st.immutables = st_bdy.immutables /\
    fin_st.accounts = st_bdy.accounts ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt strip_tac >>
  `state_well_typed fin_st` by gvs[state_well_typed_def] >>
  `env_consistent env cx (st_bdy with scopes := args_st.scopes)` by
    (qspecl_then [`env`, `env_body`, `cx`, `src_id_opt`, `fn`,
                  `args_st`, `st_bdy`] mp_tac
       env_consistent_restore_intcall_body_frame >> simp[]) >>
  `env_consistent env cx fin_st` by
    (qspecl_then [`env`, `cx`, `st_bdy with scopes := args_st.scopes`,
                  `fin_st`] mp_tac env_consistent_same_scopes_immutables >>
     simp[]) >>
  simp[]
QED

Theorem intcall_cleanup_after_body_preserves_caller_frame[local]:
  !env env_body cx src_id_opt fn args_st st_bdy cleanup_res fin_st nr is_view.
    env_consistent env cx args_st /\
    env_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) st_bdy /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    state_well_typed args_st /\
    state_well_typed st_bdy /\
    accounts_well_typed st_bdy.accounts /\
    (do pop_function args_st.scopes;
        if nr /\ ~is_view then
          case cx.nonreentrant_slot of
          | NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()
     od) st_bdy = (cleanup_res,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt strip_tac >>
  drule intcall_cleanup_after_pop_preserves_frame >>
  simp[] >> strip_tac >>
  qspecl_then [`env`, `env_body`, `cx`, `src_id_opt`, `fn`,
                `args_st`, `st_bdy`, `fin_st`] mp_tac
    intcall_cleanup_frame_restore_sound >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[]
QED

Theorem intcall_default_finally_inr_preserves_frame[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    type_stmts env_body NoneT body = SOME env_after /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts /\
    functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> strip_tac >>
  drule intcall_finally_try_handle_inr_body_cleanup_cases >>
  strip_tac
  >- (
    first_x_assum (qspecl_then [`env_body`, `NoneT`, `env_after`,
                                 `lock_st with scopes := [call_env]`,
                                 `INL ()`, `st_bdy`] mp_tac) >>
    simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
    strip_tac >>
    drule type_stmts_env_preserved_static >> strip_tac >>
    qspecl_then [`env`, `env_after`, `cx`, `env_body.current_src`, `fn`,
                  `args_st`, `st_bdy`, `INR y`, `fin_st`, `nr`,
                  `fm = View \/ fm = Pure`] irule
      intcall_cleanup_after_body_preserves_caller_frame >>
    qexistsl [`args_st`, `env_after`, `env_body`, `fm`, `fn`, `nr`,
              `st_bdy`, `y`] >>
    gvs[]) >>
  first_x_assum (qspecl_then [`env_body`, `NoneT`, `env_after`,
                               `lock_st with scopes := [call_env]`,
                               `INR body_exn`, `st_bdy`] mp_tac) >>
  simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
  strip_tac >> gvs[] >>
  qspecl_then [`env`, `env_exn`, `cx`, `env_body.current_src`, `fn`,
                `args_st`, `st_bdy`, `cleanup_res`, `fin_st`, `nr`,
                `fm = View \/ fm = Pure`] irule
    intcall_cleanup_after_body_preserves_caller_frame >>
  qexistsl [`args_st`, `cleanup_res`, `env_body`, `env_exn`, `fm`, `fn`,
            `nr`, `st_bdy`] >>
  gvs[env_extends_def]
QED

Theorem intcall_default_finally_inr_preserves_frame_from_caller_ctx[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    type_stmts env_body NoneT body = SOME env_after /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    context_well_typed cx /\
    accounts_well_typed lock_st.accounts /\
    functions_well_typed cx /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                `y`, `fin_st`] mp_tac
    intcall_default_finally_inr_preserves_frame >>
  impl_tac >-
    (simp[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant] >>
     rpt strip_tac >>
     qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
       (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
     (impl_tac >-
       (simp[context_well_typed_stk_irrelevant,
             functions_well_typed_stk_irrelevant] >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[]) >>
  simp[]
QED

Theorem intcall_default_success_post_push_outer_inr_frame_ret[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after ret y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) ==>
    type_stmts env_body ret body = SOME env_after ==>
    (ret = NoneT \/ stmts_no_fallthrough body) ==>
    env_consistent env cx args_st ==>
    state_well_typed args_st ==>
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) ==>
    state_well_typed (lock_st with scopes := [call_env]) ==>
    context_well_typed cx ==>
    accounts_well_typed lock_st.accounts ==>
    functions_well_typed cx ==>
    env_body.type_defs = get_tenv cx ==>
    env_body.bare_globals = env.bare_globals ==>
    env_body.bare_global_assignable = env.bare_global_assignable ==>
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    finally_unless_halt
      (finally
        (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                 return NoneV od) handle_function)
        (pop_function args_st.scopes))
      (if nr /\ ~(fm = View \/ fm = Pure) then
         case cx.nonreentrant_slot of
         | NONE => return ()
         | SOME slot => release_nonreentrant_lock cx.txn.target slot
       else return ())
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> ntac 14 strip_tac >>
  strip_tac >> drule finally_unless_halt_pop_release_cases >>
  disch_then (qx_choose_then `release` assume_tac) >>
  qpat_x_assum `finally_unless_halt _ _ _ = _` kall_tac >>
  gvs[]
  >- (
    qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                  `call_env`, `fn`, `fm`, `release`, `body'`, `env_after`,
                  `y`, `fin_st`] mp_tac
      intcall_default_finally_inr_preserves_frame_from_caller_ctx >>
    impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
                   simp[context_well_typed_stk_irrelevant,
                        functions_well_typed_stk_irrelevant])) >>
    simp[]) >>
  drule intcall_finally_try_handle_inr_body_cleanup_cases >>
  strip_tac
  >- (
    drule (cj 2 no_fallthrough_eval_no_success) >>
    disch_then (qspecl_then [`cx with stk updated_by CONS (env_body.current_src,fn)`,
                             `lock_st with scopes := [call_env]`, `st_bdy`] mp_tac) >>
    simp[]) >>
  qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
    (qspecl_then [`env_body`, `ret`, `env_after`,
                  `lock_st with scopes := [call_env]`,
                  `INR body_exn`, `st_bdy`] mp_tac) >>
  simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
  strip_tac >> gvs[] >>
  qspecl_then [`env`, `env_exn`, `cx`, `env_body.current_src`, `fn`,
                `args_st`, `st_bdy`, `cleanup_res`, `fin_st`, `release`,
                `fm = View \/ fm = Pure`] irule
    intcall_cleanup_after_body_preserves_caller_frame >>
  qexistsl [`args_st`, `cleanup_res`, `env_body`, `env_exn`, `fm`, `fn`,
            `release`, `st_bdy`] >>
  gvs[env_extends_def]
QED

Theorem intcall_post_push_tail_no_type_error[local]:
  !cxf body pushed_st prev nr is_view cx rtv ret env_body env_after res st'.
    evaluate_type env_body.type_defs ret = SOME rtv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    (!res_body st_body.
       eval_stmts cxf body pushed_st = (res_body,st_body) ==>
       no_type_error_result res_body /\
       (case res_body of
        | INL _ => T
        | INR exn => return_exception_typed env_body ret exn)) /\
    (do
       rv <- finally_unless_halt
         (finally (try (do eval_stmts cxf body; return NoneV od) handle_function)
           (pop_function prev))
         (if nr /\ ~is_view then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ());
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) pushed_st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  gvs[bind_apply] >>
  Cases_on
    `finally_unless_halt
       (finally (try (do eval_stmts cxf body'; return NoneV od) handle_function)
         (pop_function prev))
       (if nr /\ ~is_view then
          case cx.nonreentrant_slot of
          | NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()) pushed_st` >>
  rename1 `_ = (fin_res,fin_st)` >>
  dxrule finally_unless_halt_pop_cases >>
  (reverse strip_tac >- gvs[no_type_error_result_def]) >>
  Cases_on `fin_res` >> gvs[]
  >- (
    rename1 `finally _ _ pushed_st = (INL rv,st_final)` >>
    `!v st_bdy. eval_stmts cxf body' pushed_st = (INR (ReturnException v),st_bdy) ==>
                value_has_type NoneTV v` by (
      rpt strip_tac >>
      qpat_x_assum `!res_body st_body. eval_stmts cxf body' pushed_st = (res_body,st_body) ==> _`
        (qspecl_then [`INR (ReturnException v)`, `st_bdy`] mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (fn th => assume_tac (CONJUNCT2 th)) >>
      gvs[return_exception_typed_def, value_runtime_typed_def]) >>
    drule intcall_finally_try_handle_success_rv >>
    strip_tac >>
    `value_has_type NoneTV rv` by gvs[] >>
    Cases_on `lift_option_type (safe_cast NoneTV rv) "IntCall cast ret" st_final` >>
    rename1 `_ = (cast_res,cast_st)` >>
    `no_type_error_result cast_res` by
      metis_tac[lift_safe_cast_value_has_type_no_type_error] >>
    Cases_on `cast_res` >> gvs[return_def, no_type_error_result_def]) >>
  gvs[finally_def, ignore_bind_def, bind_def, return_def, raise_def,
      prod_CASE_rator, sum_CASE_rator] >>
  gvs[AllCaseEqs(), no_type_error_result_def] >>
  `!exn st'. eval_stmts cxf body' pushed_st = (INR exn,st') ==>
      exn <> BreakException /\ exn <> ContinueException` by
    metis_tac[stmts_no_control_escape_eval_stmts_no_loop_control] >>
  Cases_on `eval_stmts cxf body' pushed_st` >>
  Cases_on `q` >>
  TRY (drule (cj 2 no_fallthrough_eval_no_success) >>
       disch_then (qspecl_then [`cxf`, `pushed_st`, `r`] mp_tac) >>
       simp[] >> NO_TAC) >>
  TRY (rename1 `eval_stmts cxf body' pushed_st = (INR y,_)` >>
       Cases_on `y`) >>
  gvs[try_def, handle_function_def, pop_function_def, set_scopes_def,
      release_nonreentrant_lock_def, ignore_bind_def, record_storage_event_def, get_transient_storage_def, update_transient_def,
      bind_def, return_def, raise_def, no_type_error_result_def, AllCaseEqs()] >>
  Cases_on `nr /\ ~is_view` >>
  gvs[release_nonreentrant_lock_def, ignore_bind_def, record_storage_event_def, get_transient_storage_def, update_transient_def,
      bind_def, return_def, raise_def, no_type_error_result_def, AllCaseEqs()] >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[release_nonreentrant_lock_def, ignore_bind_def, record_storage_event_def, get_transient_storage_def, update_transient_def,
      bind_def, return_def, raise_def, no_type_error_result_def, AllCaseEqs()] >>
  `value_has_type rtv v` by
    gvs[return_exception_typed_def, value_runtime_typed_def] >>
  `safe_cast rtv v = SOME v` by
    (irule safe_cast_well_typed >> simp[]) >>
  gvs[lift_option_type_def, return_def, raise_def, no_type_error_result_def]
QED

Theorem intcall_pushed_body_tail_no_type_error_from_body_ih[local]:
  (!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body0 = SOME env2 /\
      env_consistent env1 cxf st0 /\ state_well_typed st0 /\
      context_well_typed cxf /\ accounts_well_typed st0.accounts /\
      functions_well_typed cxf /\ eval_stmts cxf body0 st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
      no_type_error_result res0 /\
      case res0 of
        INL v => env_consistent env2 cxf st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\ env_consistent env_exn cxf st0' /\
            return_exception_typed env_exn ret_ty1 exn) /\
  evaluate_type env_body.type_defs ret = SOME rtv /\
  type_stmts env_body ret body0 = SOME env_after /\
  (ret = NoneT \/ stmts_no_fallthrough body0) /\
  stmts_no_control_escape body0 /\
  env_consistent env_body cxf pushed_st /\ state_well_typed pushed_st /\
  context_well_typed cxf /\ accounts_well_typed pushed_st.accounts /\
  functions_well_typed cxf /\
  (do
     rv <- finally_unless_halt
       (finally (try (do eval_stmts cxf body0; return NoneV od) handle_function)
         (pop_function prev))
       (if nr /\ ~is_view then
          case cx.nonreentrant_slot of
          | NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ());
     crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
     return (Value crv)
   od) pushed_st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  irule intcall_post_push_tail_no_type_error >>
  qexistsl_tac [`body0`, `cx`, `cxf`, `env_after`, `env_body`, `is_view`,
                `nr`, `prev`, `pushed_st`, `ret`, `rtv`, `st'`] >>
  simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
    (qspecl_then [`env_body`, `ret`, `env_after`, `pushed_st`,
                  `res_body`, `st_body`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `res_body` >> gvs[] >>
  metis_tac[env_extends_return_exception_typed]
QED

Theorem intcall_current_src_pushed_body_tail_no_type_error[local]:
  !cx env_body fn body ret rtv env_after pushed_st prev nr is_view res st'.
    (!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body = SOME env2 /\
      env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
      state_well_typed st0 /\
      context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      accounts_well_typed st0.accounts /\
      functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
      no_type_error_result res0 /\
      case res0 of
        INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\
            env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
            return_exception_typed env_exn ret_ty1 exn) /\
  evaluate_type env_body.type_defs ret = SOME rtv /\
  type_stmts env_body ret body = SOME env_after /\
  (ret = NoneT \/ stmts_no_fallthrough body) /\
  stmts_no_control_escape body /\
  env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn)) pushed_st /\
  state_well_typed pushed_st /\ context_well_typed cx /\
  accounts_well_typed pushed_st.accounts /\ functions_well_typed cx /\
  (do
     rv <- finally_unless_halt
       (finally (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                return NoneV od) handle_function) (pop_function prev))
       (if nr /\ ~is_view then
          case cx.nonreentrant_slot of
          | NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ());
     crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
     return (Value crv)
   od) pushed_st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  irule intcall_pushed_body_tail_no_type_error_from_body_ih >>
  qexistsl_tac [`body'`, `cx`, `cx with stk updated_by CONS (env_body.current_src,fn)`,
                `env_after`, `env_body`, `is_view`, `nr`, `prev`,
                `pushed_st`, `ret`, `rtv`, `st'`] >>
  simp[context_well_typed_stk_irrelevant,
       functions_well_typed_stk_irrelevant] >>
  rpt strip_tac >>
  qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
    (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
  simp[context_well_typed_stk_irrelevant,
       functions_well_typed_stk_irrelevant]
QED

Theorem intcall_current_src_pushed_body_tail_no_type_error_irule[local]:
  !cx env_body fn body ret rtv env_after pushed_st prev nr is_view res st'.
    (!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body = SOME env2 /\
      env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
      state_well_typed st0 /\
      context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      accounts_well_typed st0.accounts /\
      functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
      no_type_error_result res0 /\
      case res0 of
        INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\
            env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
            return_exception_typed env_exn ret_ty1 exn) ==>
    evaluate_type env_body.type_defs ret = SOME rtv ==>
    type_stmts env_body ret body = SOME env_after ==>
    (ret = NoneT \/ stmts_no_fallthrough body) ==>
    stmts_no_control_escape body ==>
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn)) pushed_st ==>
    state_well_typed pushed_st ==>
    context_well_typed cx ==>
    accounts_well_typed pushed_st.accounts ==>
    functions_well_typed cx ==>
    (do
       rv <- finally_unless_halt
         (finally (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                  return NoneV od) handle_function) (pop_function prev))
         (if nr /\ ~is_view then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ());
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) pushed_st = (res,st') ==>
    no_type_error_result res
Proof
  rpt gen_tac >> disch_tac >>
  rpt (disch_tac ORELSE gen_tac) >>
  qspecl_then [`cx`, `env_body`, `fn`, `body'`, `ret`, `rtv`,
                `env_after`, `pushed_st`, `prev`, `nr`, `is_view`,
                `res`, `st'`] mp_tac
    intcall_current_src_pushed_body_tail_no_type_error >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  simp[]
QED

Theorem intcall_default_success_post_push_no_type_error[local]:
  !cx env env_body args_st dflt_st lock_st call_env fn fm nr ret body env_after rtv res st'.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
         INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    evaluate_type env_body.type_defs ret = SOME rtv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    env_consistent env cx args_st /\ state_well_typed dflt_st /\
    context_well_typed cx /\ accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\ env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (dflt_st with scopes := [call_env]) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => do
             acquire_nonreentrant_lock cx.txn.target slot
               ((fm = View \/ fm = Pure) \/ cx.txn.is_static);
             if (fm = View \/ fm = Pure) then return () else check_not_static cx
           od
     else return ()) dflt_st = (INL (),lock_st) /\
    (do
       rv <- finally_unless_halt
         (finally (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                  return NoneV od) handle_function) (pop_function args_st.scopes))
         (if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ());
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) (lock_st with scopes := [call_env]) = (res,st') ==>
    no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_live_pushed_body_preconditions >>
  strip_tac >>
  qspecl_then [`cx`, `env_body`, `fn`, `body'`, `ret`, `rtv`,
                `env_after`, `lock_st with scopes := [call_env]`,
                `args_st.scopes`, `nr`, `fm = View \/ fm = Pure`, `res`, `st'`]
    mp_tac intcall_current_src_pushed_body_tail_no_type_error_irule >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- (first_assum ACCEPT_TAC ORELSE simp[])) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  first_x_assum irule >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem intcall_safe_cast_expr_result_typed[local]:
  !env loc src_id_opt fn es extra ret_ty ret_tv rv crv.
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
    type_widens_to env.type_defs ret_ty (expr_type (Call loc (IntCall (src_id_opt,fn)) es extra)) /\
    evaluate_type env.type_defs ret_ty = SOME ret_tv /\
    value_has_type ret_tv rv /\
    safe_cast ret_tv rv = SOME crv ==>
    expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) (Value crv)
Proof
  rpt strip_tac >>
  `value_has_type ret_tv crv` by
    (drule_all safe_cast_preserves_well_typed >> simp[]) >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  simp[expr_result_typed_def, expr_runtime_typed_def,
       value_result_typed_def] >>
  metis_tac[well_typed_expr_not_hashmap_place]
QED

Theorem intcall_default_success_post_push_sound[local]:
  !cx env loc src_id_opt es extra env_body args_st dflt_st lock_st call_env fn fm nr ret body env_after rtv res st'.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       call_evaluation_safe
         (cx with stk updated_by CONS (env_body.current_src,fn))
         (int_calls_stmts body) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
    type_widens_to env.type_defs ret (expr_type (Call loc (IntCall (src_id_opt,fn)) es extra)) /\
    evaluate_type env_body.type_defs ret = SOME rtv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    env_consistent env cx args_st /\ state_well_typed args_st /\
    state_well_typed dflt_st /\
    context_well_typed cx /\ accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (int_calls_stmts body) /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\ env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (dflt_st with scopes := [call_env]) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => do
             acquire_nonreentrant_lock cx.txn.target slot
               ((fm = View \/ fm = Pure) \/ cx.txn.is_static);
             if (fm = View \/ fm = Pure) then return () else check_not_static cx
           od
     else return ()) dflt_st = (INL (),lock_st) /\
    (do
       rv <- finally_unless_halt
         (finally (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                  return NoneV od) handle_function) (pop_function args_st.scopes))
         (if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ());
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) (lock_st with scopes := [call_env]) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  drule_all intcall_live_pushed_body_preconditions >>
  strip_tac >>
  `no_type_error_result res` by (
    irule intcall_default_success_post_push_no_type_error >>
    qexistsl_tac [`args_st`, `body'`, `call_env`, `cx`, `dflt_st`, `env`,
                  `env_after`, `env_body`, `fm`, `fn`, `lock_st`, `nr`,
                  `ret`, `rtv`, `st'`] >>
    simp[] >>
    rpt strip_tac >>
    qhdtm_assum `bool$!`
      (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[]) >>
  gvs[bind_apply] >>
  Cases_on
    `finally_unless_halt
       (finally (try
          do
            eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body';
            return NoneV
          od handle_function) (pop_function args_st.scopes))
       (if nr /\ ~(fm = View \/ fm = Pure) then
          (case cx.nonreentrant_slot of
             NONE => return ()
           | SOME slot => release_nonreentrant_lock cx.txn.target slot)
        else return ()) (lock_st with scopes := [call_env])` >>
  rename1 `_ = (fin_res,fin_st)` >>
  Cases_on `fin_res` >> gvs[]
  >- (
    dxrule finally_unless_halt_pop_success >> strip_tac >>
    rename1 `finally _ _ _ = (INL rv,fin_st)` >>
    drule intcall_finally_try_handle_success_cleanup >>
    disch_then strip_assume_tac >>
    gvs[] >~ [`eval_stmts _ _ _ = (INL (),_)`] >- (
      qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
        (qspecl_then [`env_body`, `NoneT`, `env_after`,
                      `lock_st with scopes := [call_env]`, `INL ()`, `st_bdy`] mp_tac) >>
      simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
      strip_tac >>
      qpat_x_assum `do pop_function args_st.scopes; _ od st_bdy = (INL (),fin_st)` mp_tac >>
      qspecl_then [`cx`, `nr`, `fm = View \/ fm = Pure`, `args_st.scopes`,
                    `st_bdy`, `INL ()`, `fin_st`] mp_tac
        intcall_cleanup_after_pop_preserves_frame >>
      simp[] >> strip_tac >> strip_tac >>
      `env_after.type_defs = get_tenv cx /\
       env_after.bare_globals = env.bare_globals /\
       env_after.bare_global_assignable = env.bare_global_assignable /\
       env_after.toplevel_vtypes = env.toplevel_vtypes` by
        (drule type_stmts_env_preserved_static >> simp[]) >>
      `state_well_typed fin_st /\ env_consistent env cx fin_st /\
       accounts_well_typed fin_st.accounts` by (
        qspecl_then [`env`, `env_after`, `cx`, `env_body.current_src`, `fn`,
                      `args_st`, `st_bdy`, `fin_st`] mp_tac
          intcall_cleanup_frame_restore_sound >>
        (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
        strip_tac >> simp[]) >>
      gvs[intcall_safe_cast_NoneTV_NoneV, lift_option_type_def,
          return_def, raise_def, expr_result_typed_def, expr_runtime_typed_def,
          value_result_typed_def, evaluate_type_def]) >>
    qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
      (qspecl_then [`env_body`, `NoneT`, `env_after`,
                    `lock_st with scopes := [call_env]`,
                    `INR (ReturnException rv)`, `st_bdy`] mp_tac) >>
    simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
    strip_tac >>
    qpat_x_assum `do pop_function args_st.scopes; _ od st_bdy = (INL (),fin_st)` mp_tac >>
    qspecl_then [`cx`, `nr`, `fm = View \/ fm = Pure`, `args_st.scopes`,
                  `st_bdy`, `INL ()`, `fin_st`] mp_tac
      intcall_cleanup_after_pop_preserves_frame >>
    simp[] >> strip_tac >> strip_tac >>
    gvs[] >>
    `env_exn.type_defs = get_tenv cx /\
     env_exn.bare_globals = env.bare_globals /\
     env_exn.bare_global_assignable = env.bare_global_assignable /\
     env_exn.toplevel_vtypes = env.toplevel_vtypes` by
      (gvs[env_extends_def]) >>
    `state_well_typed fin_st /\ env_consistent env cx fin_st /\
     accounts_well_typed fin_st.accounts` by (
      qspecl_then [`env`, `env_exn`, `cx`, `env_body.current_src`, `fn`,
                    `args_st`, `st_bdy`, `fin_st`] mp_tac
        intcall_cleanup_frame_restore_sound >>
      (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
      strip_tac >> simp[]) >>
    `rv = NoneV` by
      gvs[return_exception_typed_def, value_runtime_typed_def, evaluate_type_def] >>
    gvs[intcall_safe_cast_NoneTV_NoneV, lift_option_type_def,
        return_def, raise_def, expr_result_typed_def, expr_runtime_typed_def,
        value_result_typed_def, evaluate_type_def])
  >- (
    `(!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body' = SOME env2 /\
      env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
      state_well_typed st0 /\
      context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      accounts_well_typed st0.accounts /\
      functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body' st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
      case res0 of
      | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\
            env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
            return_exception_typed env_exn ret_ty1 exn)` by (
      rpt strip_tac >>
      qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
        (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
      simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant]) >>
    `state_well_typed fin_st /\ env_consistent env cx fin_st /\
     accounts_well_typed fin_st.accounts` by
      (qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                    `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                    `NoneT`,
                    `y`, `fin_st`] mp_tac
         intcall_default_success_post_push_outer_inr_frame_ret >>
       impl_tac >- first_assum ACCEPT_TAC >>
       rpt (impl_tac >- (first_assum ACCEPT_TAC ORELSE
                         simp[context_well_typed_stk_irrelevant,
                              functions_well_typed_stk_irrelevant])) >>
       simp[]) >>
    gvs[] ) >>
  all_tac >~ [`finally_unless_halt _ _ _ = (INL _,_)`] >- (
    dxrule finally_unless_halt_pop_success >> strip_tac >>
    drule intcall_finally_try_handle_success_cleanup >>
    disch_then strip_assume_tac >> gvs[]
    >- (
      drule (cj 2 no_fallthrough_eval_no_success) >>
      disch_then (qspecl_then [`cx with stk updated_by CONS (env_body.current_src,fn)`,
                               `lock_st with scopes := [call_env]`, `st_bdy`] mp_tac) >>
      simp[]) >>
    qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
      (qspecl_then [`env_body`, `ret`, `env_after`,
                    `lock_st with scopes := [call_env]`,
                    `INR (ReturnException v)`, `st_bdy`] mp_tac) >>
    simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
    strip_tac >>
    qpat_x_assum `do pop_function args_st.scopes; _ od st_bdy = (INL (),fin_st)` mp_tac >>
    qspecl_then [`cx`, `nr`, `fm = View \/ fm = Pure`, `args_st.scopes`,
                  `st_bdy`, `INL ()`, `fin_st`] mp_tac
      intcall_cleanup_after_pop_preserves_frame >>
    simp[] >> strip_tac >> strip_tac >>
    gvs[] >>
    `env_exn.type_defs = get_tenv cx /\
     env_exn.bare_globals = env.bare_globals /\
     env_exn.bare_global_assignable = env.bare_global_assignable /\
     env_exn.toplevel_vtypes = env.toplevel_vtypes` by
      (gvs[env_extends_def]) >>
    `state_well_typed fin_st /\ env_consistent env cx fin_st /\
     accounts_well_typed fin_st.accounts` by (
      qspecl_then [`env`, `env_exn`, `cx`, `env_body.current_src`, `fn`,
                    `args_st`, `st_bdy`, `fin_st`] mp_tac
        intcall_cleanup_frame_restore_sound >>
      (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
      strip_tac >> simp[]) >>
    `value_has_type rtv v` by
      gvs[return_exception_typed_def, value_runtime_typed_def] >>
    `safe_cast rtv v = SOME v` by
      (irule safe_cast_well_typed >> simp[]) >>
    gvs[lift_option_type_def, return_def, raise_def] >>
    `env.type_defs = get_tenv cx` by
      gvs[env_consistent_def, env_context_consistent_def] >>
    qspecl_then [`env`, `loc`, `src_id_opt`, `fn`, `es`, `extra`, `ret`, `rtv`,
                  `v`, `v`] mp_tac intcall_safe_cast_expr_result_typed >>
    simp[]) >>
  all_tac >~ [`finally_unless_halt _ _ _ = (INR _,_)`] >- (
    `(!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body' = SOME env2 /\
      env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
      state_well_typed st0 /\
      context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      accounts_well_typed st0.accounts /\
      functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body' st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
      case res0 of
      | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\
            env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
            return_exception_typed env_exn ret_ty1 exn)` by (
      rpt strip_tac >>
      qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
        (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
      simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant]) >>
    qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                  `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                  `ret`,
                  `y`, `fin_st`] mp_tac
      intcall_default_success_post_push_outer_inr_frame_ret >>
    impl_tac >- first_assum ACCEPT_TAC >>
    rpt (impl_tac >- (first_assum ACCEPT_TAC ORELSE
                      simp[context_well_typed_stk_irrelevant,
                           functions_well_typed_stk_irrelevant])) >>
    simp[])
QED

Theorem intcall_lock_no_type_error_result[local]:
  !cx nr is_view st res st'.
    (nr ==> cx.nonreentrant_slot <> NONE) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => do
             acquire_nonreentrant_lock cx.txn.target slot
               (is_view \/ cx.txn.is_static);
             if is_view then return () else check_not_static cx
           od
     else return ()) st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  Cases_on `nr` >> gvs[return_def, raise_def, no_type_error_result_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[raise_def, no_type_error_result_def, acquire_nonreentrant_lock_def, ignore_bind_def, record_storage_event_def,
      get_transient_storage_def, update_transient_def, bind_def, ignore_bind_def,
      return_def, raise_def] >>
  Cases_on `lookup_storage (n2w x) (lookup_transient_storage cx.txn.target st.tStorage) = 1w` >>
  gvs[raise_def, return_def, update_transient_def, no_type_error_result_def] >>
  Cases_on `is_view` >> Cases_on `cx.txn.is_static` >>
  gvs[raise_def, return_def, update_transient_def, no_type_error_result_def]
QED

Theorem intcall_lock_attempt_sound_frame:
  !env cx nr is_view dflt_st lock_res lock_st.
    env_consistent env cx dflt_st /\ state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    (nr ==> cx.nonreentrant_slot <> NONE) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => do
             acquire_nonreentrant_lock cx.txn.target slot
               (is_view \/ cx.txn.is_static);
             if is_view then return () else check_not_static cx
           od
     else return ()) dflt_st = (lock_res,lock_st) ==>
    state_well_typed lock_st /\ accounts_well_typed lock_st.accounts /\
    no_type_error_result lock_res /\
    (case lock_res of INL _ => T | INR _ => env_consistent env cx lock_st)
Proof
  rpt strip_tac >>
  `no_type_error_result lock_res` by
    (irule intcall_lock_no_type_error_result >> goal_assum drule >> simp[]) >>
  Cases_on `lock_res`
  >- (Cases_on `x` >>
      drule intcall_lock_state_preserves_frame >>
      strip_tac >>
      gvs[state_well_typed_def]) >>
  gvs[no_type_error_result_def] >>
  Cases_on `nr` >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[raise_def, acquire_nonreentrant_lock_def, ignore_bind_def, record_storage_event_def, get_transient_storage_def,
      update_transient_def, bind_def, ignore_bind_def, return_def,
      no_type_error_result_def] >>
  Cases_on `lookup_storage (n2w x) (lookup_transient_storage cx.txn.target dflt_st.tStorage) = 1w` >>
  gvs[raise_def, return_def, update_transient_def, state_well_typed_def] >>
  Cases_on `is_view` >> Cases_on `cx.txn.is_static` >>
  gvs[raise_def, return_def, update_transient_def, state_well_typed_def]
QED

Theorem env_consistent_type_defs_get_tenv:
  !env cx st. env_consistent env cx st ==> env.type_defs = get_tenv cx
Proof
  simp[env_consistent_def, env_context_consistent_def]
QED

Theorem intcall_successful_defaults_lock_success_sound_from_body_ih[local]:
  !cx env loc res st' src_id_opt fn es extra env_body args_st dflt_st lock_st
     call_env fn_name fm nr ret body env_after ret_tv.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn_name)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn_name)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn_name)) /\
       call_evaluation_safe
         (cx with stk updated_by CONS (env_body.current_src,fn_name))
         (int_calls_stmts body) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn_name)) body st0 =
         (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn_name)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn_name)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn_name)) es extra) /\
    type_widens_to env.type_defs ret (expr_type (Call loc (IntCall (src_id_opt,fn_name)) es extra)) /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    env_consistent env cx args_st /\ state_well_typed args_st /\
    state_well_typed dflt_st /\
    context_well_typed cx /\ accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn_name))
      (int_calls_stmts body) /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\ env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn_name)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body cx (dflt_st with scopes := [call_env]) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => do
             acquire_nonreentrant_lock cx.txn.target slot
               ((fm = View \/ fm = Pure) \/ cx.txn.is_static);
             if (fm = View \/ fm = Pure) then return () else check_not_static cx
           od
     else return ()) dflt_st = (INL (),lock_st) /\
    (do rv <- finally_unless_halt
          (finally (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn_name)) body;
                   return NoneV od) handle_function) (pop_function args_st.scopes))
          (if nr /\ ~(fm = View \/ fm = Pure) then
             case cx.nonreentrant_slot of
             | NONE => return ()
             | SOME slot => release_nonreentrant_lock cx.txn.target slot
           else return ());
        crv <- lift_option_type (safe_cast ret_tv rv) "IntCall cast ret";
        return (Value crv) od) (lock_st with scopes := [call_env]) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn_name)) es extra) tv
    | INR _ => T
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  MATCH_MP_TAC (Q.SPECL [`cx`, `env`, `loc`, `src_id_opt`, `es`, `extra`,
                         `env_body`, `args_st`, `dflt_st`, `lock_st`,
                         `call_env`, `fn_name`, `fm`, `nr`, `ret`, `body'`,
                         `env_after`, `ret_tv`, `res`, `st'`]
    intcall_default_success_post_push_sound) >>
  (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
  (CONJ_TAC THEN1 (qpat_assum `well_typed_expr _ _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `type_widens_to _ ret _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (
    qpat_assum `env_body.type_defs = get_tenv cx` (fn th =>
      simp[th] >> qpat_assum `evaluate_type (get_tenv cx) ret = SOME ret_tv` ACCEPT_TAC))) >>
  (CONJ_TAC THEN1 (qpat_assum `type_stmts _ _ _ = SOME _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
  (CONJ_TAC THEN1 (qpat_assum `stmts_no_control_escape _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_consistent env cx args_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `state_well_typed args_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `state_well_typed dflt_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `context_well_typed cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `accounts_well_typed dflt_st.accounts` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `functions_well_typed cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1
    (qpat_assum `call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn_name))
      (int_calls_stmts body')` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.type_defs = get_tenv cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.fn_sigs = env.fn_sigs` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.bare_globals = env.bare_globals` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.bare_global_assignable = env.bare_global_assignable` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.toplevel_vtypes = env.toplevel_vtypes` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.flag_members = env.flag_members` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_immutables_consistent _ _ _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `scope_well_typed call_env` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (
    qpat_assum `env_scopes_consistent env_body cx (dflt_st with scopes := [call_env])` mp_tac >>
    simp[env_scopes_consistent_stk_irrelevant])) >>
  (CONJ_TAC THEN1 (qpat_assum `(if _ then _ else _) dflt_st = _` mp_tac >> simp[])) >>
  first_assum ACCEPT_TAC
QED

(* Local adapter updated for its sole SCC consumer. The old continuation was
   finally handled_body (do pop_function args_st.scopes; release od);
   scope restoration must run on Halt, but release must not. *)
Theorem intcall_post_read_continuation_sound:
  !cx env loc res st' src_id_opt fn es extra env_body args_st dflt_st lock_st
    call_env fm nr ret body env_after ret_tv lock_res.
  (!env1 ret_ty1 env2 st0 res0 st0'.
     type_stmts env1 ret_ty1 body = SOME env2 /\
     env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
     state_well_typed st0 /\
     context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
     accounts_well_typed st0.accounts /\
     functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
     call_evaluation_safe (cx with stk updated_by CONS (env_body.current_src,fn))
       (int_calls_stmts body) /\
     eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 =
       (res0,st0') ==>
     state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
     no_type_error_result res0 /\
     (case res0 of
      | INL _ => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn => ?env_exn. env_extends env1 env_exn /\
          env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
          return_exception_typed env_exn ret_ty1 exn)) /\
  well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
  type_widens_to env.type_defs ret (expr_type (Call loc (IntCall (src_id_opt,fn)) es extra)) /\
  evaluate_type (get_tenv cx) ret = SOME ret_tv /\
  type_stmts env_body ret body = SOME env_after /\
  (ret = NoneT \/ stmts_no_fallthrough body) /\ stmts_no_control_escape body /\
  env_consistent env cx args_st /\ state_well_typed args_st /\
  env_consistent env cx dflt_st /\ state_well_typed dflt_st /\
  context_well_typed cx /\ accounts_well_typed dflt_st.accounts /\ functions_well_typed cx /\
  call_evaluation_safe (cx with stk updated_by CONS (env_body.current_src,fn))
    (int_calls_stmts body) /\
  env_body.type_defs = get_tenv cx /\ env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\ env_body.flag_members = env.flag_members /\
  env_immutables_consistent env_body
    (cx with stk updated_by CONS (env_body.current_src,fn)) dflt_st /\
  scope_well_typed call_env /\
  env_scopes_consistent env_body cx (dflt_st with scopes := [call_env]) /\
  (nr ==> cx.nonreentrant_slot <> NONE) /\
  (if nr then case cx.nonreentrant_slot of
     NONE => raise (Error (TypeError "nonreentrant slot missing"))
   | SOME slot => do
         acquire_nonreentrant_lock cx.txn.target slot
           ((fm = View \/ fm = Pure) \/ cx.txn.is_static);
         if (fm = View \/ fm = Pure) then return () else check_not_static cx
       od
   else return ()) dflt_st = (lock_res,lock_st) /\
  (case lock_res of
   | INL _ =>
       (do rv <- finally_unless_halt
             (finally
               (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                        return NoneV od) handle_function)
               (pop_function args_st.scopes))
             (if nr /\ ~(fm = View \/ fm = Pure) then
                case cx.nonreentrant_slot of NONE => return ()
                | SOME slot => release_nonreentrant_lock cx.txn.target slot
              else return ());
           crv <- lift_option_type (safe_cast ret_tv rv) "IntCall cast ret";
           return (Value crv) od) (lock_st with scopes := [call_env])
   | INR exn => (INR exn,lock_st)) = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  (case res of INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
             | INR _ => T)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  Cases_on `lock_res`
  >- (Cases_on `x` >>
      qpat_x_assum `(case INL _ of INL _ => _ | INR _ => _) = _`
        (assume_tac o REWRITE_RULE [sum_case_def]) >>
      drule_all intcall_successful_defaults_lock_success_sound_from_body_ih >> simp[]) >>
  drule_all intcall_lock_attempt_sound_frame >> strip_tac >>
  gvs[no_type_error_result_def]
QED

(* ===== Internal call final placement helper ===== *)

Theorem type_place_expr_Call_IntCall_NONE:
  !env ty src_id_opt fn es drv.
    type_place_expr env (Call ty (IntCall (src_id_opt,fn)) es drv) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

Theorem raw_log_well_typed_args:
  well_typed_expr env (Call ann RawLog es dflt) ==>
  well_typed_exprs env es /\ dflt = NONE /\ ann = NoneT /\ LENGTH es = 2 /\
  (?bd. EL 0 (MAP expr_type es) = ArrayT (BaseT (BytesT (Fixed 32))) bd /\
        bound_at_most bd 4) /\
  (?bd'. EL 1 (MAP expr_type es) = BaseT (BytesT bd'))
Proof
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  gvs[bound_at_most_def]
QED

Theorem typed_result_read_sound:
  state_well_typed st /\
  eval_result_typed (env,cx,st) pv (Type ty) /\ live_memory_result st pv /\
  read_result cx pv st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  case res of INL v => value_runtime_typed env ty v | INR _ => T
Proof
  rpt strip_tac >> imp_res_tac read_result_state >> gvs[] >>
  Cases_on `res` >> simp[no_type_error_result_def] >>
  metis_tac[read_live_result_success_type, read_typed_result_error]
QED

Theorem live_place_read_sound:
  state_well_typed st /\ runtime_place_typed cx st p tv /\
  live_memory_result st (PlaceR p) /\ read_place cx p st = (res,st') ==>
  st' = st /\ no_type_error_result res /\
  case res of INL v => value_has_type tv v | INR _ => T
Proof
  rpt gen_tac >> strip_tac >> imp_res_tac read_place_preserves_state >> gvs[] >>
  Cases_on `res` >> simp[no_type_error_result_def]
  >- (drule_all read_live_place_success_type >> simp[]) >>
  drule_all read_place_typed_error >> simp[]
QED

Theorem typed_target_place_write_sound:
  env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
  accounts_well_typed st.accounts /\
  eval_result_typed (env,cx,st) (PlaceR p) (Type ty) /\
  writable_place_result cx st (PlaceR p) /\ value_runtime_typed env ty v /\
  write_place cx p v st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  `runtime_consistent env cx st` by simp[runtime_consistent_def] >>
  gvs[value_runtime_typed_def, eval_result_typed_def, writable_place_result_def] >>
  drule_all write_place_sound >> simp[runtime_consistent_def]
QED

Theorem value_runtime_typed_tuple_components:
  value_runtime_typed env (TupleT tys) v ==>
  ?vs. v = ArrayV (TupleV vs) /\ LIST_REL (value_runtime_typed env) tys vs
Proof
  rw[value_runtime_typed_def] >> drule evaluate_type_TupleT_cases >> strip_tac >>
  gvs[] >> drule value_has_type_TupleTV_dest_stmt >> strip_tac >> gvs[] >>
  simp[LIST_REL_EL_EQN, value_runtime_typed_def] >>
  fs[vyperTypeDefaultsTheory.values_have_types_LIST_REL, LIST_REL_EL_EQN] >> metis_tac[]
QED

(* Assignability is an additional proved SCC conclusion. The original typing
   and public compatibility contracts keep their original preconditions. *)
Theorem subscript_vtype_result_step_type:
  subscript_vtype bvt (expr_type e) = SOME out /\
  value_runtime_typed env (expr_type e) key ==>
  target_path_step_type env bvt (ValueSubscript key) out
Proof
  strip_tac >> Cases_on `bvt` >> gvs[subscript_vtype_def]
  >- (Cases_on `t` >> gvs[subscript_vtype_def] >>
      Cases_on `expr_type e` >>
      gvs[is_int_type_def, value_runtime_typed_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `key` >> gvs[value_has_type_def, target_path_step_type_def]) >>
  Cases_on `expr_type e` >>
  gvs[hashmap_key_type_def, value_runtime_typed_def, evaluate_type_def, AllCaseEqs(), LET_THM] >>
  Cases_on `key` >>
  gvs[value_has_type_def, target_path_step_type_def, hashmap_key_type_def,
      value_runtime_typed_def, evaluate_type_def, value_has_type_def]
QED
