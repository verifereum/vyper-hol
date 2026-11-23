(* Source read boundaries for framed array subscript simulation. *)
Theory exprSimSubscriptArraySource
Ancestors
  exprSimSource exprSimHypsDefs vyperState vyperInterpreter vyperValue
  vyperPlaceResultTyping vyperPlaceStatePreservation vyperTypeEnvPreservation
  vyperTypeInvariants vyperTypeSystem vyperPlaceTyping vyperArray
  vyperAST placeTypingProps allocLimits supportedExprTraverse
  vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperBareGlobalName vyperStoragePlaceProvenance vyperCallFrame vyperCreateFrame
  integer option pair list rich_list finite_map exprSimAttributeFields
  exprSimTopLevelProps

Theorem read_result_nonstorage_frame:
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  s'.scopes = s.scopes /\ s'.immutables = s.immutables ==>
  FST (read_result cx r s') = FST (read_result cx r s)
Proof
  strip_tac >> Cases_on `r`
  >- simp[read_result_def, return_def]
  >- (Cases_on `p`
      >- metis_tac[]
      >- (rename1 `PlaceR (MemoryPlace id path)` >>
          simp[read_result_def, read_place_def, get_scopes_def, bind_def,
               lift_option_type_def, lift_sum_def, return_def, raise_def] >>
          Cases_on `lookup_scopes id s.scopes` >>
          simp[return_def, raise_def] >>
          rename1 `lookup_scopes id s.scopes = SOME entry` >>
          Cases_on `read_memory_path entry path` >> simp[return_def, raise_def])
      >> simp[read_result_def, read_place_def, get_immutables_def,
              get_address_immutables_def, bind_def, lift_option_type_def,
              lift_sum_def, return_def, raise_def] >>
      rpt (CASE_TAC >> simp[return_def, raise_def, bind_def]))
  >> simp[read_result_def, raise_def]
QED

(* Without an overlap the source does not read the base before the index
   (subscript_reads_base). *)
Theorem eval_expr_subscript_bind:
  ~subscript_reads_base cx obj idx ==>
  eval_expr cx (Subscript ann obj idx) =
  bind (eval_expr cx obj) (\r.
    bind (bind (eval_expr cx idx) (read_result cx)) (\v.
      select_result cx (expr_type obj) r (ValueSubscript v)))
Proof
  strip_tac >> simp[Once evaluate_def, bind_assoc] >>
  simp[FUN_EQ_THM, bind_def, return_def]
QED

Theorem lookup_scopes_popped_keys_indexed:
  popped_keys_indexed scs /\ lookup_scopes id scs = SOME entry ==>
  EVERY (\k. ?p i etv n. k = p ++ [ValueSubscript i] /\
             subscripts_type entry.type p = SOME (ArrayTV etv (Dynamic n)))
    (MAP FST entry.popped)
Proof
  strip_tac >> drule lookup_scopes_EL >> strip_tac >>
  gvs[popped_keys_indexed_def, EVERY_EL] >>
  first_x_assum drule >> disch_then drule >> simp[]
QED

Theorem indexed_history_no_fixed_child:
  EVERY (\k. ?p i etv n. k = p ++ [ValueSubscript i] /\
             subscripts_type tv p = SOME (ArrayTV etv (Dynamic n)))
    (MAP FST hist) /\
  subscripts_type tv path = SOME (ArrayTV et (Fixed bound)) ==>
  !i v. ~MEM (path ++ [ValueSubscript i],v) hist
Proof
  simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >>
  first_x_assum (qspec_then `path ++ [ValueSubscript i]` mp_tac) >>
  (impl_tac >- (qexists_tac `(path ++ [ValueSubscript i],v)` >> simp[])) >>
  strip_tac >> gvs[GSYM SNOC_APPEND, SNOC_11]
QED

Theorem prefix_snoc_not_equal[local]:
  !path pre sb.
    IS_PREFIX (path ++ [sb]) pre /\ pre <> path ++ [sb] ==>
    IS_PREFIX path pre
Proof
  Induct >> Cases_on `pre` >> simp[IS_PREFIX] >> rpt strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem snapshot_snoc_evaluate[local]:
  subscripts_type tv path = SOME ptv /\ IS_PREFIX path pre /\
  subscripts_type tv pre = SOME htv ==>
  evaluate_subscripts htv saved (DROP (LENGTH pre) (path ++ [sb])) =
    case evaluate_subscripts htv saved (DROP (LENGTH pre) path) of
    | INL v => evaluate_subscripts ptv v [sb]
    | INR err => INR err
Proof
  simp[IS_PREFIX_APPEND] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  gvs[vyperPlaceStatePreservationTheory.subscripts_type_append] >>
  Cases_on `evaluate_subscripts htv saved l`
  >- (drule_all evaluate_subscripts_append >> simp[]) >>
  drule_all exprSimPopNestedLocalPathTheory.evaluate_subscripts_append_err >> simp[]
QED

Theorem read_popped_snoc:
  !hist tv path ptv v sb w.
    subscripts_type tv path = SOME ptv /\
    read_popped tv path hist = SOME v /\
    evaluate_subscripts ptv v [sb] = INL w /\
    (!saved. ~MEM (path ++ [sb],saved) hist) ==>
    read_popped tv (path ++ [sb]) hist = SOME w
Proof
  Induct >- simp[read_popped_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  `h0 <> path ++ [sb]` by metis_tac[MEM] >>
  `!saved. ~MEM (path ++ [sb],saved) hist` by metis_tac[MEM] >>
  Cases_on `IS_PREFIX path h0`
  >- (Cases_on `subscripts_type tv h0`
      >- (gvs[read_popped_def] >> first_x_assum drule_all >> simp[]) >>
      rename1 `subscripts_type tv h0 = SOME htv` >>
      drule_all_then assume_tac snapshot_snoc_evaluate >>
      Cases_on `evaluate_subscripts htv h1 (DROP (LENGTH h0) path)` >>
      gvs[read_popped_def] >>
      `IS_PREFIX (path ++ [sb]) h0` by
        (gvs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
      simp[Once read_popped_def] >>
      first_x_assum drule_all >> simp[]) >>
  `~IS_PREFIX (path ++ [sb]) h0` by metis_tac[prefix_snoc_not_equal] >>
  gvs[read_popped_def] >> first_x_assum drule_all >> simp[]
QED

Theorem read_memory_path_snoc:
  subscripts_type entry.type path = SOME ptv /\
  read_memory_path entry path = INL v /\
  evaluate_subscripts ptv v [sb] = INL w /\
  (!saved. ~MEM (path ++ [sb],saved) entry.popped) ==>
  read_memory_path entry (path ++ [sb]) = INL w
Proof
  strip_tac >> Cases_on `evaluate_subscripts entry.type entry.value path`
  >- (gvs[read_memory_path_def] >>
      drule_all evaluate_subscripts_append >>
      disch_then (qspec_then `[sb]` assume_tac) >> simp[read_memory_path_def]) >>
  gvs[read_memory_path_def, AllCaseEqs()] >>
  drule_all read_popped_snoc >> strip_tac >>
  drule_all exprSimPopNestedLocalPathTheory.evaluate_subscripts_append_err >>
  disch_then (qspec_then `[sb]` assume_tac) >> simp[read_memory_path_def]
QED

Theorem select_memory_result:
  lookup_scopes id es.scopes = SOME entry /\
  subscripts_type entry.type path = SOME ptv /\
  read_memory_path entry path = INL v ==>
  select_result cx ty (PlaceR (MemoryPlace id path)) sb es =
    bind (lift_sum (evaluate_subscripts ptv v [sb]))
      (\_. return (PlaceR (MemoryPlace id (path ++ [sb])))) es
Proof
  strip_tac >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, get_scopes_def, bind_def, ignore_bind_def,
       lift_option_type_def, lift_sum_def, return_def, extend_memory_place_def] >>
  Cases_on `evaluate_subscripts ptv v [sb]` >> simp[return_def, raise_def]
QED

Theorem read_memory_child_result:
  lookup_scopes id es.scopes = SOME entry /\
  subscripts_type entry.type path = SOME ptv /\
  read_memory_path entry path = INL v /\
  evaluate_subscripts ptv v [sb] = INL w /\
  (!saved. ~MEM (path ++ [sb],saved) entry.popped) ==>
  read_result cx (PlaceR (MemoryPlace id (path ++ [sb]))) es = (INL w,es)
Proof
  strip_tac >> drule_all read_memory_path_snoc >> strip_tac >>
  simp[read_result_def, read_place_def, get_scopes_def, bind_def,
       lift_option_type_def, lift_sum_def, return_def]
QED

Theorem select_value_result:
  evaluate_type (get_tenv cx) ty = SOME ptv ==>
  select_result cx ty (Value v) sb es =
    bind (lift_sum (evaluate_subscripts ptv v [sb])) (\w. return (Value w)) es
Proof
  simp[select_result_def, bind_def, lift_option_type_def, return_def]
QED

Theorem select_immutable_result:
  get_immutables cx src es = (INL imms,es) /\
  FLOOKUP imms id = SOME (itv,iv) /\
  subscripts_type itv path = SOME ptv /\
  evaluate_subscripts itv iv path = INL v ==>
  select_result cx ty (PlaceR (ImmutablePlace src id path)) sb es =
    bind (lift_sum (evaluate_subscripts ptv v [sb]))
      (\_. return (PlaceR (ImmutablePlace src id (path ++ [sb])))) es
Proof
  strip_tac >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, return_def, extend_memory_place_def] >>
  Cases_on `evaluate_subscripts ptv v [sb]` >> simp[return_def, raise_def]
QED

Theorem read_immutable_child_result:
  get_immutables cx src es = (INL imms,es) /\
  FLOOKUP imms id = SOME (itv,iv) /\
  subscripts_type itv path = SOME ptv /\
  evaluate_subscripts itv iv path = INL v /\
  evaluate_subscripts ptv v [sb] = INL w ==>
  read_result cx (PlaceR (ImmutablePlace src id (path ++ [sb]))) es = (INL w,es)
Proof
  strip_tac >> drule_all evaluate_subscripts_append >>
  disch_then (qspec_then `[sb]` assume_tac) >>
  simp[read_result_def, read_place_def, bind_def, lift_option_type_def,
       lift_sum_def, return_def]
QED

Theorem select_fixed_memory_read:
  runtime_place_typed cx es (MemoryPlace id path) (ArrayTV et (Fixed n)) /\
  popped_keys_indexed es.scopes /\
  read_result cx (PlaceR (MemoryPlace id path)) es = (INL v,es) /\
  evaluate_subscripts (ArrayTV et (Fixed n)) v [ValueSubscript i] = INL w ==>
  select_result cx ty (PlaceR (MemoryPlace id path)) (ValueSubscript i) es =
    (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript i]))),es) /\
  read_result cx (PlaceR (MemoryPlace id (path ++ [ValueSubscript i]))) es = (INL w,es)
Proof
  strip_tac >> Cases_on `lookup_scopes id es.scopes` >>
  gvs[runtime_place_typed_def, place_type_value_def, read_result_def,
      read_place_def, get_scopes_def, bind_def, lift_option_type_def,
      lift_sum_def, return_def, raise_def] >>
  rename1 `lookup_scopes id es.scopes = SOME entry` >>
  Cases_on `subscripts_type entry.type path` >> gvs[return_def, raise_def] >>
  Cases_on `read_memory_path entry path` >> gvs[return_def, raise_def] >>
  drule_all lookup_scopes_popped_keys_indexed >> strip_tac >>
  drule_all indexed_history_no_fixed_child >> strip_tac >>
  conj_tac
  >- (drule_all_then assume_tac select_memory_result >>
      simp[bind_def, lift_sum_def, return_def]) >>
  `read_memory_path entry (path ++ [ValueSubscript i]) = INL w` by
    (irule read_memory_path_snoc >> conj_tac >- simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp[return_def]
QED

Theorem select_typed_immutable_read:
  runtime_place_typed cx es (ImmutablePlace src id path) ptv /\
  read_result cx (PlaceR (ImmutablePlace src id path)) es = (INL v,es) /\
  evaluate_subscripts ptv v [sb] = INL w ==>
  select_result cx ty (PlaceR (ImmutablePlace src id path)) sb es =
    (INL (PlaceR (ImmutablePlace src id (path ++ [sb]))),es) /\
  read_result cx (PlaceR (ImmutablePlace src id (path ++ [sb]))) es = (INL w,es)
Proof
  simp[runtime_place_typed_immutable] >> strip_tac >>
  gvs[read_result_def, read_place_def, bind_def, lift_option_type_def,
      lift_sum_def, return_def, AllCaseEqs()] >>
  Cases_on `evaluate_subscripts root a path` >> gvs[return_def, raise_def] >>
  conj_tac
  >- (drule_all_then assume_tac select_immutable_result >>
      simp[bind_def, lift_sum_def, return_def]) >>
  drule_all evaluate_subscripts_append >>
  disch_then (qspec_then `[sb]` assume_tac) >> simp[return_def]
QED

Theorem evaluate_array_subscript_result:
  evaluate_subscripts (ArrayTV et bd) (ArrayV av) [ValueSubscript (IntV i)] =
    case array_index (ArrayTV et bd) av i of
    | SOME w => INL w
    | NONE => INR (RuntimeError "evaluate_subscripts array_index")
Proof
  simp[evaluate_subscripts_def] >>
  Cases_on `array_index (ArrayTV et bd) av i` >> simp[evaluate_subscripts_def]
QED

Theorem select_value_read:
  evaluate_type (get_tenv cx) ty = SOME ptv /\
  evaluate_subscripts ptv v [sb] = INL w ==>
  select_result cx ty (Value v) sb es = (INL (Value w),es) /\
  read_result cx (Value w) es = (INL w,es)
Proof
  strip_tac >> drule_then assume_tac select_value_result >>
  simp[bind_def, lift_sum_def, return_def, read_result_def]
QED

Theorem expr_body_pre_place_metadata:
  expr_body_pre cenv cx env e es /\
  eval_expr cx e es = (INL (PlaceR p),es') ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
       runtime_place_typed cx es' p tv
Proof
  strip_tac >> drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  gvs[eval_result_typed_def]
QED

Theorem eval_expr_immutable_root_nonconstant:
  !e cx es src id path t.
    ~supported_expr_exists (const_name_root cx) e /\
    eval_expr cx e es = (INL (PlaceR (ImmutablePlace src id path)),t) ==>
    ~cx_const_name cx (src,id)
Proof
  measureInduct_on `expr_size e` >> Cases_on `e` >> rpt gen_tac
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
  >- (rename1 `TopLevelName ann nsid` >> PairCases_on `nsid` >>
      simp[Once evaluate_def, supported_expr_exists_def, const_name_root_def] >>
      metis_tac[lookup_global_immutable_root])
  >- (rename1 `FlagMember ann nsid mid` >> PairCases_on `nsid` >>
      simp[Once evaluate_def, lookup_flag_mem_def, bind_def,
           vyperMiscTheory.option_CASE_rator, lift_option_type_def,
           return_def, raise_def, AllCaseEqs()])
  >- suspend "ifexp"
  >- simp[Once evaluate_def, return_def]
  >- (rename1 `StructLit ann nsid fields` >> PairCases_on `nsid` >>
      simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()])
  >- suspend "subscript"
  >- suspend "attribute"
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
  >- suspend "pop"
  >> suspend "call"
QED
Resume eval_expr_immutable_root_nonconstant[ifexp]:
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  qpat_x_assum `conditional_result _ _ _ = _` mp_tac >>
  rename1 `conditional_result cx raw mid = _` >>
  Cases_on `raw` >> simp[conditional_result_def, return_def, raise_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >>
  simp[conditional_result_def, bind_def, return_def, AllCaseEqs()] >>
  simp[COND_RATOR, bind_def, return_def, AllCaseEqs()]
QED
Resume eval_expr_immutable_root_nonconstant[subscript]:
  rename1 `Subscript ann obj idx` >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), supported_expr_exists_def] >>
  rpt strip_tac >> rename1 `select_result cx _ raw _ _ = _` >>
  Cases_on `raw` >>
  gvs[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
      return_def, raise_def, AllCaseEqs()] >>
  drule extend_place_immutable_root >> strip_tac >> gvs[] >>
  qpat_x_assum `(if subscript_reads_base _ _ _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >> simp[bind_def, return_def, AllCaseEqs()] >> rpt strip_tac >>
  first_x_assum (qspec_then `obj` mp_tac) >> simp[expr_size_def] >> metis_tac[]
QED
Resume eval_expr_immutable_root_nonconstant[attribute]:
  rename1 `Attribute ann obj attr_id` >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), supported_expr_exists_def] >>
  rpt strip_tac >> rename1 `select_result cx _ raw _ _ = _` >>
  Cases_on `raw` >>
  gvs[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
      return_def, raise_def, AllCaseEqs()] >>
  drule extend_place_immutable_root >> strip_tac >> gvs[] >>
  first_x_assum (qspec_then `obj` mp_tac) >> simp[expr_size_def] >> metis_tac[]
QED
Resume eval_expr_immutable_root_nonconstant[pop]:
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  rename1 `pop_place cx bp _ = _` >> Cases_on `bp`
  >- (rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
      gvs[pop_place_def, bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
      rename1 `ArrayTV et bd` >> Cases_on `bd` >>
      gvs[pop_place_def, bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()]) >>
  gvs[pop_place_def, bind_def, ignore_bind_def, return_def, raise_def,
      UNCURRY, AllCaseEqs()]
QED
Resume eval_expr_immutable_root_nonconstant[call]:
  rename1 `Call ann call_target call_args call_default` >> Cases_on `call_target` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac
  >~ [`IntCall nsid`]
  >- (PairCases_on `nsid` >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def,
          raise_def, UNCURRY, AllCaseEqs()])
  >~ [`eval_send`]
  >- (drule eval_send_success_value >> simp[])
  >~ [`eval_ext_call`]
  >- (drule eval_ext_call_success_value >> simp[])
  >~ [`eval_raw_call`]
  >- (drule eval_raw_call_success_value >> simp[])
  >~ [`eval_raw_call`]
  >- (drule eval_raw_call_success_value >> simp[])
  >~ [`CreateTarget`]
  >- (rename1 `CreateTarget kind _ _ _` >> Cases_on `kind` >>
      gvs[vyperCreateTheory.eval_create_operands_def,
          bind_def, ignore_bind_def, return_def, raise_def,
          AllCaseEqs()] >>
      drule eval_create_success_value >> simp[])
QED
Finalise eval_expr_immutable_root_nonconstant

Theorem expr_body_pre_popped_keys_indexed:
  expr_body_pre cenv cx env e es /\ eval_expr cx e es = (res,es') ==>
  popped_keys_indexed es'.scopes
Proof
  strip_tac >> irule eval_expr_popped_keys_indexed >>
  goal_assum (drule_at Any) >>
  gvs[expr_body_pre_def, expr_sim_inv_def]
QED

Theorem evaluate_array_subscript_in_bounds:
  valid_index (ArrayTV et bd) av i ==>
  ?w. evaluate_subscripts (ArrayTV et bd) (ArrayV av) [ValueSubscript (IntV i)] = INL w
Proof
  strip_tac >> drule array_index_valid >>
  Cases_on `array_index (ArrayTV et bd) av i` >>
  simp[evaluate_array_subscript_result]
QED

Theorem evaluate_array_subscript_oob:
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) /\
  ~valid_index (ArrayTV et bd) av i ==>
  evaluate_subscripts (ArrayTV et bd) (ArrayV av) [ValueSubscript (IntV i)] =
    INR (RuntimeError "evaluate_subscripts array_index")
Proof
  strip_tac >> simp[evaluate_array_subscript_result] >>
  Cases_on `array_index (ArrayTV et bd) av i` >> simp[] >>
  drule array_index_bounds >> simp[] >> metis_tac[]
QED

Theorem select_nonstorage_place_error:
  (!tr slot vt. p <> StoragePlace tr slot vt) /\
  runtime_place_typed cx es p ptv /\
  read_result cx (PlaceR p) es = (INL v,es) /\
  evaluate_subscripts ptv v [sb] = INR err ==>
  select_result cx ty (PlaceR p) sb es = (INR (Error err),es)
Proof
  strip_tac >> Cases_on `p`
  >- metis_tac[]
  >- (gvs[runtime_place_typed_memory] >>
      gvs[read_result_def, read_place_def, get_scopes_def, bind_def,
          lift_option_type_def, lift_sum_def, return_def] >>
      Cases_on `read_memory_path entry l` >> gvs[return_def, raise_def] >>
      drule_all_then assume_tac select_memory_result >>
      simp[bind_def, lift_sum_def, raise_def]) >>
  gvs[runtime_place_typed_immutable] >>
  gvs[read_result_def, read_place_def, bind_def, lift_option_type_def,
      lift_sum_def, return_def] >>
  Cases_on `evaluate_subscripts root a l` >> gvs[return_def, raise_def] >>
  drule_all_then assume_tac select_immutable_result >>
  simp[bind_def, lift_sum_def, raise_def]
QED

Theorem type_place_expr_value_typed:
  type_place_expr env e = SOME (Type ty) /\
  well_formed_type env.type_defs ty /\ ty <> NoneT ==>
  well_typed_expr env e
Proof
  Cases_on `e` >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (PairCases_on `p` >>
      gvs[well_typed_expr_def, vtype_annotation_ok_def, AllCaseEqs()]) >>
  gvs[vtype_annotation_ok_def] >>
  simp[Once well_typed_expr_def] >>
  metis_tac[]
QED

(* Context coherence is needed only for the internal place wellformedness
   argument; unlike the shared local transport facts this boundary returns
   value-expression typing. *)
Theorem type_place_expr_context_value_typed:
  !env cx e ty.
    env_context_consistent env cx /\
    type_place_expr env e = SOME (Type ty) /\ ty <> NoneT ==>
    well_typed_expr env e
Proof
  rpt strip_tac >>
  `!ex vt. type_place_expr env ex = SOME vt ==>
          well_formed_vtype env.type_defs vt` by
    (measureInduct_on `expr_size ex` >> rpt strip_tac >>
     Cases_on `ex` >> gvs[Once well_typed_expr_def, AllCaseEqs()]
     >- (PairCases_on `p` >>
         qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
         simp[well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
         gvs[env_context_consistent_def] >>
         first_x_assum drule >> simp[]) >>
     qpat_x_assum `!y. expr_size y < _ ==> _` (qspec_then `e'` mp_tac) >>
     (impl_tac >- simp[expr_size_def]) >>
     disch_then (qspec_then `vt'` mp_tac) >> simp[] >> strip_tac >>
     Cases_on `vt'` >>
     gvs[subscript_vtype_def, well_formed_vtype_def, AllCaseEqs()] >>
     rename1 `subscript_vtype (Type base_ty) _ = SOME _` >>
     Cases_on `base_ty` >>
     gvs[subscript_vtype_def, well_formed_vtype_def,
         well_formed_type_def, evaluate_type_def, AllCaseEqs()] >>
     rename1 `evaluate_type env.type_defs elem_ty` >>
     Cases_on `evaluate_type env.type_defs elem_ty` >> gvs[]) >>
  irule type_place_expr_value_typed >> simp[] >>
  first_x_assum drule >> simp[well_formed_vtype_def]
QED

(* The parent subscript's precondition types its array base and keeps the
   invariant, whatever the base's own allocation bound. *)
Theorem expr_body_pre_array_subscript_base_typed:
  expr_body_pre cenv cx env (Subscript ann obj idx) s /\
  expr_type obj = ArrayT et bd ==>
  well_typed_expr env obj /\ expr_sim_inv cenv cx env s /\
  call_evaluation_safe cx (int_calls_expr obj)
Proof
  strip_tac >>
  `well_typed_expr env obj` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, Once well_typed_expr_def] >>
     strip_tac >> gvs[] >>
     drule vyperTypeSystemTheory.type_place_expr_vtype_annotation >> simp[] >>
     Cases_on `vt` >> gvs[vtype_annotation_ok_def] >>
     strip_tac >> gvs[] >>
     irule type_place_expr_context_value_typed >>
     conj_tac
     >- (qexists_tac `ArrayT et bd` >> simp[]) >>
     qexists_tac `cx` >>
     gvs[expr_sim_inv_def, env_consistent_def]) >>
  gvs[expr_body_pre_def, int_calls_expr_def] >>
  drule call_evaluation_safe_append_left >> simp[]
QED

(* What the base's simulation consumes from its own precondition, from the
   parent's alone. *)
Theorem expr_body_pre_array_subscript_base_admissible:
  expr_body_pre cenv cx env (Subscript ann obj idx) s /\
  expr_type obj = ArrayT et bd ==>
  gas_admissible (eval_expr cx obj) expr_vv_res_ok s /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type obj))
Proof
  strip_tac >>
  drule_all_then strip_assume_tac expr_body_pre_array_subscript_base_typed >>
  reverse conj_tac >- metis_tac[exprSimHypsTheory.expr_sim_inv_type_evaluates] >>
  rw[gasContextTheory.gas_admissible_def] >>
  `expr_sim_inv cenv cx env (s with gas_obs := gs)` by simp[] >>
  drule_all expr_sim_inv_eval_result >> strip_tac >>
  Cases_on `res` >> gvs[exprSimDefsTheory.expr_vv_res_ok_def]
  >- (rename1 `eval_result_typed _ tv _` >> Cases_on `tv` >>
      gvs[eval_result_typed_def]) >>
  drule (cj 1 vyperExprNoControlTheory.eval_expr_no_control) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  gvs[vyperExprNoControlTheory.no_control_exc_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def]
  >~ [`Error err`] >- (Cases_on `err` >> gvs[])
QED

Theorem copies_subscript_base_not_array_slot_base:
  copies_subscript_base cenv e idx ==> ~array_slot_base cenv e
Proof
  Cases_on `e` >>
  simp[array_slot_base_def, exprLoweringTheory.copies_subscript_base_def,
       vyperSubscriptOverlapTheory.subscript_overlap_def, base_through_dynarray_def]
QED

Theorem base_from_pop_not_array_slot_base:
  base_from_pop e ==> ~array_slot_base cenv e
Proof
  Cases_on `e` >> simp[base_from_pop_def, array_slot_base_def]
QED

(* A storage or transient array base carries no allocation bound of its
   own (array_slot_base in alloc_limits_expr), so its precondition follows
   only off that case or when its type is bounded anyway. *)
Theorem expr_body_pre_array_subscript_base:
  expr_body_pre cenv cx env (Subscript ann obj idx) s /\
  expr_type obj = ArrayT et bd /\
  (~array_slot_base cenv obj \/ type_alloc_ok cenv (expr_type obj)) ==>
  expr_body_pre cenv cx env obj s
Proof
  strip_tac >>
  drule_all_then strip_assume_tac expr_body_pre_array_subscript_base_typed >>
  `alloc_limits_expr cenv obj` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, alloc_limits_expr_def] >> strip_tac >>
     Cases_on `array_slot_base cenv obj` >> gvs[] >>
     Cases_on `obj` >> gvs[array_slot_base_def, alloc_limits_expr_def, expr_type_def]) >>
  gvs[expr_body_pre_def, byte_widths_expr_def, alloc_limits_expr_def,
      int_calls_expr_def, expr_has_evm_run_thm, EVERY_APPEND] >>
  rpt strip_tac >>
  TRY (qpat_x_assum `!target. supported_expr_exists _ (Subscript _ _ _) ==> _`
         (qspec_then `target` irule) >>
       simp[supported_expr_exists_def] >> NO_TAC) >>
  gvs[supported_expr_exists_def]
QED

Theorem expr_body_pre_array_subscript_slot_base:
  expr_body_pre cenv cx env (Subscript ann obj idx) s /\
  array_slot_base cenv obj ==>
  ~const_name_root cx obj
Proof
  Cases_on `obj` >> simp[array_slot_base_def] >> strip_tac >>
  gvs[expr_body_pre_def, supported_expr_exists_def]
QED

(* A base that evaluates to anything but a storage place, or compiles to a
   memory or code pointer, is not a storage or transient array variable. *)
Theorem expr_body_pre_array_subscript_base_eval:
  expr_body_pre cenv cx env (Subscript ann obj idx) s /\
  expr_type obj = ArrayT et bd /\
  eval_expr cx obj s' = (INL r,t) /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) ==>
  expr_body_pre cenv cx env obj s
Proof
  strip_tac >>
  `~array_slot_base cenv obj` suffices_by
    metis_tac[expr_body_pre_array_subscript_base] >>
  strip_tac >>
  drule_all_then strip_assume_tac expr_body_pre_array_subscript_base_typed >>
  drule_all_then assume_tac expr_body_pre_array_subscript_slot_base >>
  drule_all array_slot_base_eval_storage >> metis_tac[]
QED

Theorem expr_body_pre_array_subscript_base_located:
  expr_body_pre cenv cx env (Subscript ann obj idx) s /\
  expr_type obj = ArrayT et bd /\
  (vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory \/
   vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) ==>
  expr_body_pre cenv cx env obj s
Proof
  strip_tac >>
  `~array_slot_base cenv obj` suffices_by
    metis_tac[expr_body_pre_array_subscript_base] >>
  metis_tac[array_slot_base_compile_location]
QED

Theorem expr_body_pre_subscript_index:
  expr_body_pre cenv cx env (Subscript ann obj idx) s ==>
  expr_body_pre cenv cx env idx s
Proof
  strip_tac >>
  `well_typed_expr env idx` by
    (gvs[expr_body_pre_def, Once well_typed_expr_def]) >>
  `call_evaluation_safe cx (int_calls_expr idx)` by
    (gvs[expr_body_pre_def, int_calls_expr_def] >>
     drule call_evaluation_safe_append_right >> simp[]) >>
  gvs[expr_body_pre_def, byte_widths_expr_def, alloc_limits_expr_def,
      int_calls_expr_def, expr_has_evm_run_thm, EVERY_APPEND] >>
  rpt strip_tac >>
  TRY (qpat_x_assum `!target. supported_expr_exists _ (Subscript _ _ _) ==> _`
         (qspec_then `target` irule) >>
       simp[supported_expr_exists_def] >> NO_TAC) >>
  gvs[supported_expr_exists_def]
QED

Theorem expr_body_pre_array_subscript_index_after_base:
  expr_body_pre cenv cx env (Subscript ann obj idx) s /\
  expr_type obj = ArrayT et bd /\
  eval_expr cx obj s = (INL r,t) ==>
  expr_body_pre cenv cx env idx t
Proof
  strip_tac >>
  drule_all_then strip_assume_tac expr_body_pre_array_subscript_base_typed >>
  drule_then assume_tac expr_body_pre_subscript_index >>
  drule_all expr_sim_inv_eval_result >> strip_tac >>
  gvs[expr_body_pre_def]
QED
