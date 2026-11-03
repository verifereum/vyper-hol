(* Source selection boundaries for array read simulation. *)
Theory exprSimArraySubscript
Ancestors
  exprSimNoPop exprSimArrayIndex vyperPlaceResultTyping vyperState
  vyperTypeEnv exprSimHyps supportedExprTraverse exprSimAttribute
  vyperPlaceFrames vyperStatePreservation vyperInterpreter vyperArray

(* A current-value path takes priority over every historical snapshot. *)
Theorem read_memory_path_current_append:
  !entry path tv v suffix w.
    subscripts_type entry.type path = SOME tv /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    evaluate_subscripts tv v suffix = INL w ==>
    read_memory_path entry (path ++ suffix) = INL w
Proof
  rpt strip_tac >>
  drule_all evaluate_subscripts_append >>
  simp[read_memory_path_def]
QED

(* Evaluation alone does not imply that the declared subscript type exists. *)
Theorem evaluate_subscripts_untyped_success[local]:
  evaluate_subscripts NoneTV (ArrayV (TupleV [IntV 0]))
    [ValueSubscript (IntV 0)] = INL (IntV 0) /\
  subscript_type NoneTV (ValueSubscript (IntV 0)) = NONE
Proof
  EVAL_TAC >> simp[]
QED

Theorem read_memory_path_current_append_typed:
  !entry path tv v suffix w.
    value_has_type entry.type entry.value /\
    well_formed_type_value entry.type /\
    subscripts_type entry.type path = SOME tv /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    evaluate_subscripts tv v suffix = INL w ==>
    ?wtv. subscripts_type entry.type (path ++ suffix) = SOME wtv /\
      well_formed_type_value wtv /\ value_has_type wtv w /\
      evaluate_subscripts entry.type entry.value (path ++ suffix) = INL w /\
      read_memory_path entry (path ++ suffix) = INL w
Proof
  rpt strip_tac >>
  `evaluate_subscripts entry.type entry.value (path ++ suffix) = INL w` by
    (drule_all evaluate_subscripts_append >> simp[]) >>
  `read_memory_path entry (path ++ suffix) = INL w` by
    simp[read_memory_path_def] >>
  simp[] >>
  irule vyperPlaceStatePreservationTheory.evaluate_subscripts_declared_type_exists >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

(* Selection checks the current value before extending the local path. *)
Theorem select_result_current_memory_path:
  !cx ty s t id path entry tv v sb id' path'.
    EVERY scope_well_typed s.scopes /\
    lookup_scopes id s.scopes = SOME entry /\
    subscripts_type entry.type path = SOME tv /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    select_result cx ty (PlaceR (MemoryPlace id path)) sb s =
      (INL (PlaceR (MemoryPlace id' path')), t) ==>
    ?entry' tv' v'.
      lookup_scopes id' t.scopes = SOME entry' /\
      subscripts_type entry'.type path' = SOME tv' /\
      well_formed_type_value tv' /\ value_has_type tv' v' /\
      evaluate_subscripts entry'.type entry'.value path' = INL v' /\
      read_memory_path entry' path' = INL v'
Proof
  rpt strip_tac >>
  drule_all scope_well_typed_lookup_scopes >> strip_tac >>
  gvs[select_result_def, extend_place_def, place_type_value_def,
      read_place_def, get_scopes_def, bind_def, ignore_bind_def,
      lift_option_type_def, lift_sum_def, return_def, raise_def,
      read_memory_path_def, extend_memory_place_def, AllCaseEqs()] >>
  Cases_on `evaluate_subscripts tv v [sb]` >>
  gvs[return_def, raise_def] >>
  drule_all read_memory_path_current_append_typed >>
  strip_tac >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> gvs[read_memory_path_def]
QED

Theorem eval_raw_call_value:
  eval_raw_call cx flags addr data amount gas st = (INL res, st') ==>
  ?v. res = Value v
Proof
  simp[eval_raw_call_def, bind_def, ignore_bind_def, COND_RATOR,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem eval_ext_call_value:
  eval_ext_call cx static_flag skip_check sig opts vals st = (INL res, st') ==>
  ?v. res = Value v
Proof
  PairCases_on `sig` >> Cases_on `vals` >>
  simp[eval_ext_call_def, bind_def, ignore_bind_def, return_def, raise_def,
       vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem eval_create_value:
  eval_create cx kind salt rof tys vals code_size st = (INL res, st') ==>
  ?v. res = Value v
Proof
  simp[vyperCreateTheory.eval_create_def, vyperCreateTheory.create_soft_failure_def,
       bind_def, ignore_bind_def, COND_RATOR, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ _ of _ => _ | _ => _) _ = _` mp_tac >>
  simp[vyperMiscTheory.option_CASE_rator, AllCaseEqs(),
       bind_def, ignore_bind_def, COND_RATOR, return_def, raise_def] >>
  strip_tac >- simp[] >>
  rename1 `run_create_evm _ _ _ _ _ _ _ _ = SOME packed` >>
  PairCases_on `packed` >>
  gvs[bind_def, ignore_bind_def, COND_RATOR, return_def, raise_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()]
QED

Theorem eval_expr_nopop_current_memory_path:
  !e cx s t id path.
    EVERY scope_well_typed s.scopes /\ ~expr_has_pop e /\
    eval_expr cx e s = (INL (PlaceR (MemoryPlace id path)), t) ==>
    ?entry tv v.
      lookup_scopes id t.scopes = SOME entry /\
      subscripts_type entry.type path = SOME tv /\
      well_formed_type_value tv /\ value_has_type tv v /\
      evaluate_subscripts entry.type entry.value path = INL v /\
      read_memory_path entry path = INL v
Proof
  ho_match_mp_tac (vyperASTTheory.expr_induction |> Q.SPEC `P` |>
    Q.SPEC `\x. T` |> SIMP_RULE (srw_ss()) []) >>
  rpt conj_tac >> rpt gen_tac >>
  simp[expr_has_pop_def, supported_expr_exists_def, expr_pop_root_def] >>
  all_tac >~ [`eval_expr _ (Name _ _) _ = _`] >-
    suspend "Name" >~
  [`eval_expr _ (TopLevelName _ _) _ = _`] >- suspend "Global" >~
  [`eval_expr _ (FlagMember _ _ _) _ = _`] >- suspend "Flag" >~
  [`eval_expr _ (IfExp _ _ _ _) _ = _`] >- suspend "If" >~
  [`eval_expr _ (Literal _ _) _ = _`] >-
    (simp[Once vyperInterpreterTheory.evaluate_def, return_def]) >~
  [`eval_expr _ (StructLit _ _ _) _ = _`] >- suspend "Struct" >~
  [`eval_expr _ (Subscript _ _ _) _ = _`] >- suspend "Subscript" >~
  [`eval_expr _ (Attribute _ _ _) _ = _`] >- suspend "Attribute" >~
  [`eval_expr _ (Builtin _ _ _) _ = _`] >-
    (rpt strip_tac >> drule eval_expr_builtin_value >> simp[]) >~
  [`eval_expr _ (TypeBuiltin _ _ _ _) _ = _`] >- suspend "TypeBuiltin" >>
  suspend "Call"
QED

Resume eval_expr_nopop_current_memory_path[Name]:
  rpt strip_tac >>
  gvs[Once vyperInterpreterTheory.evaluate_def, bind_def, get_scopes_def,
      type_check_def, assert_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  rename1 `IS_SOME (lookup_scopes nm st.scopes)` >>
  Cases_on `lookup_scopes nm st.scopes` >> gvs[] >>
  drule_all scope_well_typed_lookup_scopes >> strip_tac >>
  simp[subscripts_type_def, evaluate_subscripts_def, read_memory_path_def]
QED


Resume eval_expr_nopop_current_memory_path[Struct]:
  rpt strip_tac >>
  rename1 `eval_expr cx (StructLit ann nsid fields) st = _` >>
  PairCases_on `nsid` >>
  gvs[Once vyperInterpreterTheory.evaluate_def, bind_def, return_def, AllCaseEqs()]
QED

Resume eval_expr_nopop_current_memory_path[TypeBuiltin]:
  rpt strip_tac >>
  gvs[Once vyperInterpreterTheory.evaluate_def, bind_def, ignore_bind_def,
      return_def, AllCaseEqs()]
QED

Resume eval_expr_nopop_current_memory_path[Flag]:
  rpt strip_tac >>
  rename1 `eval_expr cx (FlagMember ann nsid fld) st = _` >>
  PairCases_on `nsid` >>
  gvs[Once vyperInterpreterTheory.evaluate_def, lookup_flag_mem_def,
      bind_def, return_def, raise_def, lift_sum_def, lift_option_type_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()]
QED

Resume eval_expr_nopop_current_memory_path[Global]:
  rpt strip_tac >>
  rename1 `eval_expr cx (TopLevelName ann nsid) st = _` >>
  PairCases_on `nsid` >>
  gvs[Once vyperInterpreterTheory.evaluate_def, lookup_global_def,
      bind_def, return_def, raise_def, lift_sum_def, lift_option_type_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  rename1 `find_var_decl_by_name _ _ = SOME decl` >>
  Cases_on `decl` >>
  rename1 `find_var_decl_by_name _ _ = SOME (di, did)` >> Cases_on `di` >>
  gvs[bind_def, return_def, raise_def, vyperMiscTheory.option_CASE_rator,
      AllCaseEqs()]
QED

Resume eval_expr_nopop_current_memory_path[Attribute]:
  rpt strip_tac >>
  gvs[Once vyperInterpreterTheory.evaluate_def, bind_def, AllCaseEqs()] >>
  drule select_result_memory_place >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  `~expr_has_pop e` by simp[expr_has_pop_def] >>
  drule_all eval_expr_nopop_scopes >> strip_tac >>
  irule select_result_current_memory_path >>
  goal_assum (drule_at (Pat `select_result _ _ _ _ _ = _`)) >>
  simp[] >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume eval_expr_nopop_current_memory_path[Subscript]:
  rpt strip_tac >>
  gvs[Once vyperInterpreterTheory.evaluate_def, bind_def, AllCaseEqs()] >>
  drule select_result_memory_place >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  `~expr_has_pop e /\ ~expr_has_pop e'` by simp[expr_has_pop_def] >>
  imp_res_tac eval_expr_nopop_scopes >>
  drule read_result_state >> strip_tac >> gvs[] >>
  irule select_result_current_memory_path >>
  goal_assum (drule_at (Pat `select_result _ _ _ _ _ = _`)) >>
  simp[] >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume eval_expr_nopop_current_memory_path[If]:
  rpt strip_tac >>
  gvs[Once vyperInterpreterTheory.evaluate_def, bind_def, AllCaseEqs()] >>
  rename1 `conditional_result cx chosen mid = _` >>
  `chosen = PlaceR (MemoryPlace id path)` by
    (Cases_on `chosen` >>
     gvs[conditional_result_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
     rename1 `place_type_value cx pl mid = _` >> Cases_on `pl` >>
     gvs[COND_RATOR, bind_def, return_def, AllCaseEqs()]) >>
  drule conditional_result_state >> strip_tac >> gvs[] >>
  `~expr_has_pop e` by simp[expr_has_pop_def] >>
  drule_all eval_expr_nopop_scopes >> strip_tac >>
  gvs[switch_BoolV_def, bind_def, AllCaseEqs(), raise_def] >>
  drule read_result_state >> strip_tac >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >>
  first_x_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[]
QED

Resume eval_expr_nopop_current_memory_path[Call]:
  rpt strip_tac >>
  rename1 `eval_expr cx (Call ann target args kws) st = _` >>
  Cases_on `target` >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  all_tac >~ [`eval_expr _ (Call _ (IntCall _) _ _) _ = _`] >-
    suspend "IntCall" >~
  [`eval_ext_call _ _ _ _ _ _ _ = _`] >- suspend "ExtCall" >~
  [`eval_send _ _ _ _ = _`] >- suspend "Send" >~
  [`eval_raw_call _ _ _ _ _ _ _ = _`] >- suspend "RawCall" >>
  all_tac >~ [`eval_raw_call _ _ _ _ _ _ _ = _`] >-
    suspend "RawCalldata" >> suspend "Create"
QED

Resume eval_expr_nopop_current_memory_path[IntCall]:
  rename1 `eval_expr cx (Call ann (IntCall nsid) args kws) st = _` >>
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()]
QED

Resume eval_expr_nopop_current_memory_path[RawCall]:
  drule eval_raw_call_value >> simp[]
QED

Resume eval_expr_nopop_current_memory_path[RawCalldata]:
  drule eval_raw_call_value >> simp[]
QED

Resume eval_expr_nopop_current_memory_path[Send]:
  rename1 `eval_send cx has_gas vs mid = _` >>
  Cases_on `vs` >- gvs[eval_send_def, raise_def] >>
  rename1 `eval_send cx has_gas (to_v::rest) mid = _` >>
  Cases_on `rest` >>
  gvs[eval_send_def, bind_def, ignore_bind_def, return_def, raise_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  pairarg_tac >> gvs[bind_def, ignore_bind_def, return_def, AllCaseEqs()]
QED

Resume eval_expr_nopop_current_memory_path[ExtCall]:
  drule eval_ext_call_value >> simp[]
QED

Resume eval_expr_nopop_current_memory_path[Create]:
  qmatch_asmsub_rename_tac `eval_create cx kind _ _ _ _ _` >>
  Cases_on `kind` >> gvs[bind_def, AllCaseEqs()] >>
  drule eval_create_value >> simp[]
QED

Finalise eval_expr_nopop_current_memory_path

(* Immediate selections interpret sparse defaults using the syntax's type. *)
Theorem select_result_value:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  evaluate_subscripts tv v [sb] = INL w ==>
  select_result cx ty (Value v) sb s = (INL (Value w), s)
Proof
  simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
       return_def]
QED

Theorem select_result_value_error:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  evaluate_subscripts tv v [sb] = INR err ==>
  select_result cx ty (Value v) sb s = (INR (Error err), s)
Proof
  simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def]
QED

(* For a current local path the extension is read from the current entry,
   even when arbitrary historical snapshots were present initially. *)
Theorem select_result_current_memory:
  lookup_scopes id s.scopes = SOME entry /\
  subscripts_type entry.type path = SOME tv /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  evaluate_subscripts tv v [sb] = INL w ==>
  select_result cx ty (PlaceR (MemoryPlace id path)) sb s =
    (INL (PlaceR (MemoryPlace id (path ++ [sb]))), s) /\
  read_place cx (MemoryPlace id (path ++ [sb])) s = (INL w, s)
Proof
  rpt strip_tac >>
  `evaluate_subscripts entry.type entry.value (path ++ [sb]) = INL w` by
    (drule_all evaluate_subscripts_append >> simp[]) >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, get_scopes_def, bind_def, ignore_bind_def,
       lift_option_type_def, lift_sum_def, return_def,
       read_memory_path_def, extend_memory_place_def]
QED

Theorem select_result_current_memory_error:
  lookup_scopes id s.scopes = SOME entry /\
  subscripts_type entry.type path = SOME tv /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  evaluate_subscripts tv v [sb] = INR err ==>
  select_result cx ty (PlaceR (MemoryPlace id path)) sb s = (INR (Error err), s)
Proof
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, get_scopes_def, bind_def, ignore_bind_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def,
       read_memory_path_def]
QED

Theorem select_result_immutable:
  get_immutables cx src s = (INL imms, s) /\
  FLOOKUP imms id = SOME (itv, iv) /\
  subscripts_type itv path = SOME tv /\
  evaluate_subscripts itv iv path = INL v /\
  evaluate_subscripts tv v [sb] = INL w ==>
  select_result cx ty (PlaceR (ImmutablePlace src id path)) sb s =
    (INL (PlaceR (ImmutablePlace src id (path ++ [sb]))), s) /\
  read_place cx (ImmutablePlace src id (path ++ [sb])) s = (INL w, s)
Proof
  rpt strip_tac >>
  `evaluate_subscripts itv iv (path ++ [sb]) = INL w` by
    (drule_all evaluate_subscripts_append >> simp[]) >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, bind_def, ignore_bind_def,
       lift_option_type_def, lift_sum_def, return_def, extend_memory_place_def]
QED

Theorem select_result_immutable_error:
  get_immutables cx src s = (INL imms, s) /\
  FLOOKUP imms id = SOME (itv, iv) /\
  subscripts_type itv path = SOME tv /\
  evaluate_subscripts itv iv path = INL v /\
  evaluate_subscripts tv v [sb] = INR err ==>
  select_result cx ty (PlaceR (ImmutablePlace src id path)) sb s =
    (INR (Error err), s)
Proof
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, bind_def, ignore_bind_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def]
QED

(* Storage selection exposes the resolver's slot and leaf type. Reads and
   region/liveness follow the existing storage resolver boundaries. *)
Theorem select_result_storage_array:
  resolve_array_element cx tr slot (ArrayTV etv bd)
    [ValueSubscript (IntV i)] s = (INL (slot', tv, rest), s') ==>
  select_result cx ty (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
    (ValueSubscript (IntV i)) s =
      (INL (PlaceR (StoragePlace tr slot' tv)), s') /\ s' = s
Proof
  strip_tac >> drule resolve_array_element_state >> strip_tac >>
  simp[select_result_def, extend_place_def, extend_storage_place_def,
       bind_def, return_def]
QED

Theorem select_result_storage_array_error:
  resolve_array_element cx tr slot (ArrayTV etv bd)
    [ValueSubscript (IntV i)] s = (INR err, s') ==>
  select_result cx ty (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
    (ValueSubscript (IntV i)) s = (INR err, s') /\ s' = s
Proof
  strip_tac >> drule resolve_array_element_state >> strip_tac >>
  simp[select_result_def, extend_place_def, extend_storage_place_def,
       bind_def, return_def]
QED

(* The syntax-derived current-path witnesses survive intervening pop-free
   evaluation, including an internal call that restores the caller scopes. *)
Theorem eval_expr_nopop_current_memory_path_after:
  EVERY scope_well_typed s.scopes /\ ~expr_has_pop obj /\
  eval_expr cx obj s = (INL (PlaceR (MemoryPlace id path)), mid) /\
  ~expr_has_pop idx /\ eval_expr cx idx mid = (res, t) ==>
  ?entry tv v.
    lookup_scopes id t.scopes = SOME entry /\
    subscripts_type entry.type path = SOME tv /\
    well_formed_type_value tv /\ value_has_type tv v /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    read_memory_path entry path = INL v
Proof
  rpt strip_tac >>
  drule_all eval_expr_nopop_current_memory_path >> strip_tac >>
  drule_all eval_expr_nopop_scopes >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem evaluate_subscripts_array_oob:
  ~valid_index (ArrayTV etv bd) av i /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) ==>
  evaluate_subscripts (ArrayTV etv bd) (ArrayV av) [ValueSubscript (IntV i)] =
    INR (RuntimeError "evaluate_subscripts array_index")
Proof
  rpt strip_tac >>
  Cases_on `array_index (ArrayTV etv bd) av i` >-
    simp[evaluate_subscripts_def] >>
  drule array_index_bounds >> simp[]
QED
