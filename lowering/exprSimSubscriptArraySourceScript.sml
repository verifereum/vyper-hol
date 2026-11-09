(* Source read boundaries for framed array subscript simulation. *)
Theory exprSimSubscriptArraySource
Ancestors
  exprSimSource exprSimHypsDefs vyperState vyperInterpreter vyperValue
  vyperPlaceResultTyping vyperPlaceStatePreservation vyperTypeEnvPreservation
  vyperTypeInvariants vyperTypeSystem vyperPlaceTyping vyperArray
  vyperAST placeTypingProps allocLimits supportedExprTraverse
  vyperTypeCallGraph vyperTypeCallStackSoundness
  integer option list rich_list finite_map exprSimAttributeFields

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

Theorem eval_expr_subscript_bind:
  eval_expr cx (Subscript ann obj idx) =
  bind (eval_expr cx obj) (\r.
    bind (bind (eval_expr cx idx) (read_result cx)) (\v.
      select_result cx (expr_type obj) r (ValueSubscript v)))
Proof
  simp[Once evaluate_def, bind_assoc]
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
  drule_all evaluate_subscripts_append_err >> simp[]
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
  drule_all evaluate_subscripts_append_err >>
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

Theorem expr_body_pre_array_subscript_base:
  expr_body_pre cenv cx env (Subscript ann obj idx) s /\
  expr_type obj = ArrayT et bd ==>
  expr_body_pre cenv cx env obj s
Proof
  strip_tac >>
  `well_typed_expr env obj` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, Once well_typed_expr_def] >>
     strip_tac >> gvs[] >>
     drule type_place_expr_vtype_annotation >> simp[] >>
     Cases_on `vt` >> gvs[vtype_annotation_ok_def] >>
     strip_tac >> gvs[] >>
     irule type_place_expr_context_value_typed >>
     conj_tac
     >- (qexists_tac `ArrayT et bd` >> simp[]) >>
     qexists_tac `cx` >>
     gvs[expr_sim_inv_def, env_consistent_def]) >>
  gvs[expr_body_pre_def, byte_widths_expr_def, alloc_limits_expr_def,
      int_calls_expr_def, expr_has_evm_run_thm, EVERY_APPEND] >>
  rpt conj_tac
  >- (drule call_evaluation_safe_append_left >> simp[]) >>
  rpt strip_tac >>
  TRY (qpat_x_assum `!target. supported_expr_exists _ (Subscript _ _ _) ==> _`
         (qspec_then `target` irule) >>
       simp[supported_expr_exists_def] >> NO_TAC) >>
  gvs[supported_expr_exists_def]
QED

Theorem expr_body_pre_subscript_index:
  expr_body_pre cenv cx env (Subscript ann obj idx) s ==>
  expr_body_pre cenv cx env idx s
Proof
  strip_tac >>
  `well_typed_expr env idx` by
    (gvs[expr_body_pre_def, Once well_typed_expr_def]) >>
  gvs[expr_body_pre_def, byte_widths_expr_def, alloc_limits_expr_def,
      int_calls_expr_def, expr_has_evm_run_thm, EVERY_APPEND] >>
  conj_tac
  >- (drule call_evaluation_safe_append_right >> simp[]) >>
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
  drule_all_then assume_tac expr_body_pre_array_subscript_base >>
  drule_then assume_tac expr_body_pre_subscript_index >>
  drule_all expr_body_pre_eval_result >> strip_tac >>
  gvs[expr_body_pre_def]
QED
