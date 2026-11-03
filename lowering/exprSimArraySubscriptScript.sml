(* Source selection boundaries for array read simulation. *)
Theory exprSimArraySubscript
Ancestors
  compileEnv exprSim exprSimNoPop exprSimArrayIndex vyperPlaceResultTyping vyperState
  vyperTypeEnv vyperTypeInvariants exprSimHyps supportedExprTraverse exprSimAttribute
  vyperPlaceFrames vyperStatePreservation vyperInterpreter vyperArray exprSimLen exprSimPop

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

(* Restore the dynamic length word excluded by locals_kept, then frame the
   complete region rather than requiring a source-result/local-path link. *)
Theorem locals_kept_complete_regions:
  locals_kept cenv es s0 s1 /\
  (!n b sz. local_region cenv es.scopes s0 n b sz /\ dynarray_local cenv n ==>
    32 <= sz /\ mem_word_at b s1.vs_memory = mem_word_at b s0.vs_memory) ==>
  !n b sz. local_region cenv es.scopes s0 n b sz ==>
    mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory
Proof
  rpt strip_tac >>
  Cases_on `dynarray_local cenv n` >-
    (first_x_assum drule_all >> strip_tac >>
     `mem_bytes_at (b + 32) (sz - 32) s1.vs_memory =
      mem_bytes_at (b + 32) (sz - 32) s0.vs_memory` by
       (gvs[locals_kept_def] >> first_x_assum irule >>
        goal_assum (drule_at Any) >> simp[]) >>
     `sz = 32 + (sz - 32)` by decide_tac >>
     once_asm_rewrite_tac[] >>
     simp[valueEncodingProofsTheory.mem_bytes_at_split_padded,
          valueEncodingProofsTheory.mem_bytes_at_word]) >>
  gvs[locals_kept_def] >> first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem local_ptrs_rel_unchanged_scopes_headers:
  EVERY scope_well_typed es.scopes /\
  es'.scopes = es.scopes /\
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_rel func cenv es'.scopes s1 /\
  (!n q sz w. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) sz) /\
              lookup_var q s0 = SOME w ==> lookup_var q s1 = SOME w) /\
  (!n entry. lookup_scopes n es.scopes = SOME entry /\ dynarray_local cenv n ==>
    ?et bd. entry.type = ArrayTV et (Dynamic bd)) ==>
  !n b sz. local_region cenv es.scopes s0 n b sz /\ dynarray_local cenv n ==>
    32 <= sz /\ mem_word_at b s1.vs_memory = mem_word_at b s0.vs_memory
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[local_region_def] >>
  rename1 `lookup_scopes n es.scopes = SOME entry` >>
  `?et bd. entry.type = ArrayTV et (Dynamic bd)` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  `lookup_var p s1 = SOME w` by
    (first_x_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >> simp[]) >>
  fs[local_ptrs_rel_def] >>
  rpt (first_x_assum (drule_at (Pat `lookup_scopes _ _ = _`)) >> simp[]) >>
  rpt strip_tac >>
  drule_all scope_well_typed_lookup_scopes >> strip_tac >>
  Cases_on `entry.value` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  gvs[vyperTypingTheory.value_has_type_def,
      valueEncodingTheory.val_wf_def, valueEncodingTheory.type_memory_size_def,
      valueEncodingPropsTheory.val_in_memory_dynarray]
QED

(* Any occupied old allocation or complete local window keeps its subwindows. *)
Theorem expr_post_occupied_window:
  expr_post ctx func cenv cx e es sm sn s0 es' iv iop s1 /\
  (!n b sz. local_region cenv es.scopes s0 n b sz ==>
    mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  ((?aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b, sz) /\
               aid < sm.cs_next_id /\ b <= off /\ off + len <= b + sz /\
               (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
                 b + sz <= lb \/ lb + lsz <= b)) \/
   (?n b sz. local_region cenv es.scopes s0 n b sz /\
              b <= off /\ off + len <= b + sz) \/ len = 0) ==>
  mem_bytes_at off len s1.vs_memory = mem_bytes_at off len s0.vs_memory
Proof
  strip_tac
  >~ [`len = 0`] >- simp[valueEncodingTheory.mem_bytes_at_def]
  >~ [`FLOOKUP s0.vs_allocas aid = SOME (b, sz)`] >-
    (`mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory` by
       (fs[expr_post_def] >>
        qpat_x_assum `!aid off sz. FLOOKUP _ _ = _ /\ _ ==> _`
          (qspecl_then [`aid`, `b`, `sz`] mp_tac) >> simp[] >>
        disch_then irule >> rpt gen_tac >> strip_tac >>
        first_x_assum drule >> simp[]) >>
     drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
     strip_tac >> sym_tac >>
     qpat_x_assum `!off2 len2. _ /\ _ ==> _` irule >> simp[]) >>
  `mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory` by
    (qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` drule_all >> simp[]) >>
  drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
  strip_tac >> sym_tac >>
     qpat_x_assum `!off2 len2. _ /\ _ ==> _` irule >> simp[]
QED

Theorem expr_post_occupied_region_frame:
  expr_post ctx func cenv cx e es sm sn s0 es' iv iop s1 /\
  es'.scopes = es.scopes /\ local_ptrs_reserved cenv sm /\
  local_ptrs_rel func cenv es.scopes s0 /\ sm.cs_next_id <= sn.cs_next_id /\
  ((?aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b, sz) /\
               sa.cs_next_id <= aid /\ aid < sm.cs_next_id /\
               b <= off /\ off + len <= b + sz /\
               (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
                 b + sz <= lb \/ lb + lsz <= b)) \/
   (?n b sz. local_region cenv es.scopes s0 n b sz /\
              b <= off /\ off + len <= b + sz /\
              (dynarray_local cenv n /\ ~dynarray_type ty ==> b + 32 <= off)) \/
   len = 0) ==>
  ((?aid b sz. FLOOKUP s1.vs_allocas aid = SOME (b, sz) /\
               sa.cs_next_id <= aid /\ aid < sn.cs_next_id /\
               b <= off /\ off + len <= b + sz /\
               (!n lb lsz. local_region cenv es'.scopes s1 n lb lsz ==>
                 b + sz <= lb \/ lb + lsz <= b)) \/
   (?n b sz. local_region cenv es'.scopes s1 n b sz /\
              b <= off /\ off + len <= b + sz /\
              (dynarray_local cenv n /\ ~dynarray_type ty ==> b + 32 <= off)) \/
   len = 0)
Proof
  strip_tac
  >~ [`FLOOKUP s0.vs_allocas aid = SOME (b, sz)`] >-
    (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >>
     `FLOOKUP s1.vs_allocas aid = SOME (b, sz)` by
       (fs[expr_post_def] >> first_x_assum drule >> simp[]) >>
     simp[] >> rpt gen_tac >> strip_tac >>
     `local_region cenv es.scopes s0 n lb lsz` by
       (irule exprSimOpsTheory.local_region_frame >>
        conj_tac >- (qexists_tac `func` >> simp[]) >>
        qexistsl_tac [`sm`, `es.scopes`, `s1`] >> fs[expr_post_def]) >>
     first_x_assum drule >> simp[])
  >~ [`local_region cenv es.scopes s0 n b sz`] >-
    (disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[] >>
     irule exprSimOpsTheory.local_region_frame_fwd >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     fs[expr_post_def] >> simp[]) >>
  simp[]
QED

Theorem expr_val_at_expr_post_frame:
  expr_val_at cenv cx ty sa sm es v op s0 /\
  expr_post ctx func cenv cx e es sm sn s0 es' iv iop s1 /\
  es'.scopes = es.scopes /\ local_ptrs_reserved cenv sm /\
  local_ptrs_rel func cenv es.scopes s0 /\ sm.cs_next_id <= sn.cs_next_id /\
  (!w. eval_operand op s0 = SOME w ==> eval_operand op s1 = SOME w) ==>
  expr_val_at cenv cx ty sa sn es' v op s1
Proof
  strip_tac >> rewrite_tac[expr_val_at_def] >> rpt strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >>
  `eval_operand op s1 = SOME w` by (first_x_assum drule >> simp[]) >>
  simp[] >> drule expr_post_occupied_region_frame >> simp[] >>
  disch_then (qspecl_then [`ty`, `sa`, `w2n w`, `val_footprint tv v`] mp_tac) >>
  simp[] >> disch_then irule
  >~ [`FLOOKUP s0.vs_allocas aid = SOME (b, sz)`] >-
    (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
     first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]
QED

Theorem vv_at_located_nonword:
  ~is_word_type ty ==>
  (vv_at cenv cx ty sa sb es tv (LocatedValue t p) s <=>
   (p.ptr_location = LocMemory ==>
    !v. read_result cx tv es = (INL v, es) ==>
      expr_val_at cenv cx ty sa sb es v p.ptr_operand s))
Proof
  simp[vv_at_def, expr_val_at_def, GSYM AND_IMP_INTRO,
       RIGHT_FORALL_IMP_THM]
QED

Theorem vv_at_expr_post_frame:
  ~is_word_type ty /\ vv_at cenv cx ty sa sm es tv vv s0 /\
  expr_post ctx func cenv cx e es sm sn s0 es' iv iop s1 /\
  es'.scopes = es.scopes /\ local_ptrs_reserved cenv sm /\
  local_ptrs_rel func cenv es.scopes s0 /\ sm.cs_next_id <= sn.cs_next_id /\
  (!w. eval_operand (vv_operand vv) s0 = SOME w ==>
       eval_operand (vv_operand vv) s1 = SOME w) /\
  (!v. read_result cx tv es' = (INL v, es') <=>
       read_result cx tv es = (INL v, es)) ==>
  vv_at cenv cx ty sa sn es' tv vv s1
Proof
  Cases_on `vv` >-
    (rename1 `StackValue vt sop` >>
     simp[vv_at_def, contextTheory.vv_operand_def] >> rpt strip_tac >>
     qpat_x_assum `!v. read_result _ _ _ = _ ==> _` drule_all >> strip_tac >>
     drule_all expr_val_at_expr_post_frame >> simp[]) >>
  simp[vv_at_located_nonword, contextTheory.vv_operand_def] >>
  rpt strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_located_nonword] >> strip_tac >>
  drule_all expr_val_at_expr_post_frame >> simp[]
QED

Theorem expr_val_at_expr_post_bytes:
  expr_val_at cenv cx ty sa sm es v op s0 /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\ eval_operand op s0 = SOME w /\
  expr_post ctx func cenv cx e es sm sn s0 es' iv iop s1 /\
  (!n b sz. local_region cenv es.scopes s0 n b sz ==>
    mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory) ==>
  mem_bytes_at (w2n w) (val_footprint tvt v) s1.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tvt v) s0.vs_memory
Proof
  strip_tac >> qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >~ [`val_footprint tvt v = 0`] >- simp[valueEncodingTheory.mem_bytes_at_def] >>
  drule expr_post_occupied_window >> simp[] >>
  disch_then (qspecl_then [`w2n w`, `val_footprint tvt v`] mp_tac) >>
  simp[] >> disch_then irule >> (conj_tac >- first_assum ACCEPT_TAC)
  >~ [`FLOOKUP s0.vs_allocas aid = SOME (b, sz)`] >-
    (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
     first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]
QED

Theorem expr_val_rel_expr_post_nonword_frame:
  ~is_word_type ty /\ expr_val_rel cx ty v op s0 /\
  expr_val_at cenv cx ty sa sm es v op s0 /\
  expr_post ctx func cenv cx e es sm sn s0 es' iv iop s1 /\
  (!n b sz. local_region cenv es.scopes s0 n b sz ==>
    mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  (!w. eval_operand op s0 = SOME w ==> eval_operand op s1 = SOME w) ==>
  expr_val_rel cx ty v op s1
Proof
  strip_tac >> qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >>
  `eval_operand op s1 = SOME w` by (first_x_assum drule >> simp[]) >>
  simp[expr_val_rel_def] >> rpt strip_tac >>
  `val_wf tv v` by
    (qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_val_at_def]) >>
  `mem_bytes_at (w2n w) (val_footprint tv v) s1.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tv v) s0.vs_memory` by
    (drule_all expr_val_at_expr_post_bytes >> simp[]) >>
  irule val_in_memory_footprint_agree >> simp[] >>
  qexists_tac `s0.vs_memory` >> simp[EQ_SYM_EQ]
QED

Theorem vv_holds_expr_post_nonword_frame:
  ~is_word_type ty /\ vv_holds cenv cx ty tv vv es s0 /\
  vv_at cenv cx ty sa sm es tv vv s0 /\
  expr_post ctx func cenv cx e es sm sn s0 es' iv iop s1 /\
  (!n b sz. local_region cenv es.scopes s0 n b sz ==>
    mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  (!w. eval_operand (vv_operand vv) s0 = SOME w ==>
       eval_operand (vv_operand vv) s1 = SOME w) /\
  (!n q sz w. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) sz) /\
              lookup_var q s0 = SOME w ==> lookup_var q s1 = SOME w) /\
  (!v. read_result cx tv es' = (INL v, es') <=>
       read_result cx tv es = (INL v, es)) /\
  (!tr w. storage_holds cx tr ty tv w es ==> storage_holds cx tr ty tv w es') /\
  (!w. immutable_holds cenv cx ty tv w es ==> immutable_holds cenv cx ty tv w es') ==>
  vv_holds cenv cx ty tv vv es' s1
Proof
  Cases_on `vv` >-
    (rename1 `StackValue vt sop` >>
     simp[vv_holds_def, vv_at_def, contextTheory.vv_operand_def] >>
     strip_tac >> simp[] >>
     `expr_val_at cenv cx ty sa sm es v sop s0` by
       (first_x_assum drule >> simp[]) >>
     drule_all expr_val_rel_expr_post_nonword_frame >> simp[]) >>
  qmatch_goalsub_rename_tac `LocatedValue vt aptr` >>
  simp[vv_holds_def, contextTheory.vv_operand_def] >> strip_tac >>
  gvs[] >> Cases_on `aptr.ptr_location` >> gvs[]
  >~ [`val_in_memory`] >- suspend "memory"
  >> first_x_assum drule >> simp[]
QED

Resume vv_holds_expr_post_nonword_frame[memory]:
  conj_tac >-
    (qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_at_located_nonword] >> strip_tac >> rpt strip_tac >>
     `val_wf tvt v` by
       (qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[expr_val_at_def]) >>
     `mem_bytes_at (w2n w) (val_footprint tvt v) s1.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tvt v) s0.vs_memory` by
       (drule_all expr_val_at_expr_post_bytes >> simp[]) >>
     irule val_in_memory_footprint_agree >> simp[] >>
     qexists_tac `s0.vs_memory` >> simp[EQ_SYM_EQ]) >>
  rpt strip_tac >>
  qpat_x_assum `!id path. _ ==> local_place_at _ _ _ _ _ _ _` drule_all >>
  strip_tac >>
  drule_all exprSimAggregateChildrenTheory.local_place_at_vars_frame >> simp[]
QED
Finalise vv_holds_expr_post_nonword_frame

(* Environment consistency connects compile-time local types to scope entries. *)
Theorem expr_sim_inv_lookup_scope_type:
  expr_sim_inv cenv cx env es /\
  lookup_scopes n es.scopes = SOME entry ==>
  ?ty. cenv.ce_var_type n = SOME ty /\
       evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  strip_tac >>
  `env_scopes_consistent env cx es` by
    fs[expr_sim_inv_def, env_consistent_def] >>
  `IS_SOME (FLOOKUP env.var_types n)` by
    (fs[env_scopes_consistent_def] >> first_x_assum drule >> simp[]) >>
  Cases_on `FLOOKUP env.var_types n` >> gvs[] >>
  rename1 `FLOOKUP env.var_types n = SOME ty` >>
  qexists_tac `ty` >> conj_tac
  >- (fs[expr_sim_inv_def] >> first_x_assum drule >> simp[]) >>
  fs[env_scopes_consistent_def] >> first_x_assum drule_all >> simp[]
QED

Theorem expr_sim_inv_dynarray_scope_type:
  expr_sim_inv cenv cx env es /\
  lookup_scopes n es.scopes = SOME entry /\ dynarray_local cenv n ==>
  ?et bd. entry.type = ArrayTV et (Dynamic bd)
Proof
  strip_tac >> drule_all expr_sim_inv_lookup_scope_type >> strip_tac >>
  gvs[dynarray_local_def, dynarray_type_def] >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem expr_sim_inv_unchanged_scopes_complete_regions:
  expr_sim_inv cenv cx env es /\ es'.scopes = es.scopes /\
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_rel func cenv es'.scopes s1 /\
  locals_kept cenv es s0 s1 /\
  (!n q sz w. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) sz) /\
              lookup_var q s0 = SOME w ==> lookup_var q s1 = SOME w) ==>
  !n b sz. local_region cenv es.scopes s0 n b sz ==>
    mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule locals_kept_complete_regions >>
  goal_assum (drule_at Any) >> simp[] >>
  `EVERY scope_well_typed es.scopes` by
    fs[expr_sim_inv_def, state_well_typed_def] >>
  `!id entry. lookup_scopes id es.scopes = SOME entry /\ dynarray_local cenv id ==>
     ?et bd. entry.type = ArrayTV et (Dynamic bd)` by
    (rpt strip_tac >> drule_all expr_sim_inv_dynarray_scope_type >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  irule local_ptrs_rel_unchanged_scopes_headers >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexistsl_tac [`es'`, `func`] >> simp[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

(* Read-only observations of a captured result use only its corresponding
   source component; bookkeeping and the other locations may change. *)
Theorem read_result_source_components:
  (!id path. tv = PlaceR (MemoryPlace id path) ==> t.scopes = s.scopes) /\
  (!tr slot ty. tv = PlaceR (StoragePlace tr slot ty) ==>
     get_storage cx t tr = get_storage cx s tr) /\
  (!src id path. tv = PlaceR (ImmutablePlace src id path) ==>
     t.immutables = s.immutables) ==>
  (read_result cx tv t = (INL v, t) <=>
   read_result cx tv s = (INL v, s))
Proof
  Cases_on `tv` >> simp[read_result_def, return_def, raise_def] >>
  rename1 `read_place cx p` >> Cases_on `p` >>
  simp[read_place_def, vyperStorageBackendTheory.read_storage_slot_eq,
       get_scopes_def, get_immutables_def, get_address_immutables_def,
       bind_def, return_def, lift_option_type_def, lift_option_def,
       lift_sum_def, raise_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), return_def, raise_def]
  >~ [`lookup_scopes id s.scopes`] >-
    (Cases_on `lookup_scopes id s.scopes` >> simp[return_def, raise_def] >>
     rename1 `read_memory_path entry path` >>
     Cases_on `read_memory_path entry path` >> simp[return_def, raise_def]) >>
  Cases_on `ALOOKUP s.immutables cx.txn.target` >> simp[return_def, raise_def] >>
  rename1 `FLOOKUP (get_source_immutables src imms) id` >>
  Cases_on `FLOOKUP (get_source_immutables src imms) id` >>
  simp[return_def, raise_def] >>
  rename1 `evaluate_subscripts (FST pair) (SND pair) path` >>
  Cases_on `evaluate_subscripts (FST pair) (SND pair) path` >>
  simp[return_def, raise_def]
QED

Theorem storage_holds_source_frame:
  get_storage cx t tr = get_storage cx s tr /\
  (!v. read_result cx tv t = (INL v, t) <=>
       read_result cx tv s = (INL v, s)) /\
  storage_holds cx tr ty tv w s ==>
  storage_holds cx tr ty tv w t
Proof
  simp[storage_holds_def, vyperStorageBackendTheory.read_storage_slot_eq,
       AllCaseEqs()] >> metis_tac[]
QED

Theorem immutable_holds_source_frame:
  t.immutables = s.immutables /\
  (!v. read_result cx tv t = (INL v, t) <=>
       read_result cx tv s = (INL v, s)) /\
  immutable_holds cenv cx ty tv w s ==>
  immutable_holds cenv cx ty tv w t
Proof
  simp[immutable_holds_def] >> metis_tac[]
QED

(* The semantic load dispatch and the length-loader execution agree. *)
Theorem array_len_ok_ptr_load:
  eval_operand op ss = SOME w /\ (loc = LocCode ==> ~ctor) ==>
  array_len_ok T cnt (compile_ptr_load ctor imm loc) op ss
    (ptr_load_val ctor loc w ss)
Proof
  Cases_on `loc` >> simp[builtinPropsTheory.ptr_load_val_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[array_len_ok_MLOAD, array_len_ok_SLOAD, array_len_ok_TLOAD,
            array_len_ok_LocCode, array_len_ok_CALLDATALOAD]
QED

Theorem vv_holds_array_len_ok:
  stmt_state_rel ctx func cenv cx es ss /\
  vv_holds cenv cx t tv vv es ss /\ is_sized_type t /\
  evaluate_type (get_tenv cx) t = SOME tvt /\
  env.type_defs = get_tenv cx /\
  eval_result_typed (env,cx,es) tv (Type t) /\
  (!v. read_result cx tv es = (INL v,es) ==> value_has_type tvt v) /\
  (vv_location vv = SOME LocCode ==> ~cenv.ce_is_ctor) /\
  result_array_length cx tv es = (INL n,es) ==>
  array_len_ok T cnt
    (compile_ptr_load cenv.ce_is_ctor imm
      (case vv_location vv of SOME l => l | NONE => LocMemory))
    (vv_operand vv) ss (n2w n)
Proof
  strip_tac >> drule_all vv_holds_len_header >> strip_tac >>
  qpat_x_assum `ptr_load_val _ _ _ _ = _` (SUBST1_TAC o SYM) >>
  irule array_len_ok_ptr_load >> simp[] >>
  Cases_on `vv_location vv` >> gvs[]
QED

Theorem sub_layout_dynarray_elem:
  sub_layout itv iv k (ArrayTV et (Dynamic bound)) (ArrayV (DynArrayV vs)) /\
  LENGTH vs <= bound /\ j < LENGTH vs ==>
  sub_layout itv iv (k + 32 + j * type_memory_size et) et (EL j vs)
Proof
  strip_tac >>
  `SUC j <= bound` by decide_tac >>
  `SUC j * type_memory_size et <= bound * type_memory_size et` by
    simp[] >>
  qpat_x_assum `sub_layout _ _ _ _ _` mp_tac >>
  rewrite_tac[sub_layout_def, valueEncodingTheory.type_memory_size_def] >>
  strip_tac >> conj_tac
  >- (qpat_x_assum `SUC j * _ <= _` mp_tac >>
      pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  rpt strip_tac >> first_x_assum drule >>
  simp[valueEncodingPropsTheory.val_in_memory_dynarray] >> strip_tac >>
  drule_all exprSimAggregateEncodingTheory.elems_in_memory_EL >>
  simp[NoAsms, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem immutable_holds_dynarray_elem:
  immutable_holds cenv cx (ArrayT et (Dynamic bound)) tv w es /\
  read_result cx tv es = (INL (ArrayV (DynArrayV vs)),es) /\
  evaluate_type (get_tenv cx) et = SOME evt /\
  j < LENGTH vs /\
  read_result cx tv' es = (INL (EL j vs),es) ==>
  immutable_holds cenv cx et tv'
    (w + n2w (32 + j * type_memory_size evt)) es
Proof
  rw[immutable_holds_def] >>
  gvs[vyperValueTheory.evaluate_type_def, vyperTypingTheory.value_has_type_def] >>
  `value_has_type evt (EL j vs)` by
    (fs[vyperTypingTheory.all_have_type_EVERY, listTheory.EVERY_EL] >>
     first_x_assum drule >> simp[]) >>
  qexistsl_tac [`name`, `off`, `itv`, `iv`,
                `k + 32 + j * type_memory_size evt`] >>
  ASM_SIMP_TAC bool_ss [wordsTheory.word_add_n2w,
    AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  drule_all sub_layout_dynarray_elem >>
  simp[NoAsms, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem sub_layout_sarray_elem:
  sub_layout itv iv k (ArrayTV et (Fixed bound)) (ArrayV (SArrayV kvs)) /\
  j < bound ==>
  sub_layout itv iv (k + j * type_memory_size et) et
    (case ALOOKUP kvs j of NONE => default_value et | SOME v => v)
Proof
  strip_tac >>
  `SUC j * type_memory_size et <= bound * type_memory_size et` by simp[] >>
  qpat_x_assum `sub_layout _ _ _ _ _` mp_tac >>
  rewrite_tac[sub_layout_def, valueEncodingTheory.type_memory_size_def] >>
  strip_tac >> conj_tac
  >- (qpat_x_assum `SUC j * _ <= _` mp_tac >>
      pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  rpt strip_tac >> first_x_assum drule >>
  simp[valueEncodingPropsTheory.val_in_memory_sarray] >> strip_tac >>
  Cases_on `ALOOKUP kvs j`
  >- (simp[] >> first_x_assum drule_all >>
      simp[NoAsms]) >>
  simp[] >> drule_all valueEncodingProofsTheory.kvs_in_memory_lookup >>
  SIMP_TAC bool_ss [arithmeticTheory.ADD_ASSOC]
QED

Theorem immutable_holds_sarray_elem:
  immutable_holds cenv cx (ArrayT et (Fixed bound)) tv w es /\
  read_result cx tv es = (INL (ArrayV (SArrayV kvs)),es) /\
  evaluate_type (get_tenv cx) et = SOME evt /\
  j < bound /\
  read_result cx tv' es =
    (INL (case ALOOKUP kvs j of NONE => default_value evt | SOME v => v),es) ==>
  immutable_holds cenv cx et tv'
    (w + n2w (j * type_memory_size evt)) es
Proof
  rw[immutable_holds_def] >>
  gvs[vyperValueTheory.evaluate_type_def, vyperTypingTheory.value_has_type_def] >>
  `value_has_type evt
    (case ALOOKUP kvs j of NONE => default_value evt | SOME v => v)` by
    (Cases_on `ALOOKUP kvs j` >> simp[]
     >- metis_tac[vyperTypeDefaultsTheory.default_value_has_type] >>
     drule_all valueEncodingProofsTheory.sparse_has_type_lookup >> simp[]) >>
  qexistsl_tac [`name`, `off`, `itv`, `iv`,
                `k + j * type_memory_size evt`] >>
  ASM_SIMP_TAC bool_ss [wordsTheory.word_add_n2w,
    AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  drule_all sub_layout_sarray_elem >> simp[]
QED

Theorem local_place_at_array_elem:
  local_place_at cenv cx s id path (ArrayT et bd) w /\
  evaluate_type (get_tenv cx) et = SOME evt /\
  j < bound_length bd ==>
  local_place_at cenv cx s id (path ++ [ValueSubscript (IntV (&j))]) et
    (w + n2w ((case bd of Fixed n => 0 | Dynamic n => 32) +
               j * type_memory_size evt))
Proof
  rw[local_place_at_def] >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  drule_then (qspecl_then [`ValueSubscript (IntV (&j))`,
    `(case bd of Fixed n => 0 | Dynamic n => 32) + j * type_memory_size evt`,
    `evt`] mp_tac) mem_path_offset_snoc >>
  Cases_on `bd` >> gvs[vyperASTTheory.bound_length_def] >>
  simp[mem_step_offset_def] >> strip_tac >>
  simp[GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w]
QED

Theorem array_elem_slots_in_range:
  slots_in_range storage (w2n (w:bytes32)) (ArrayTV evt bd) /\
  j < (case bd of Fixed n => n
       | Dynamic n => w2n (read_slot storage (w2n w))) ==>
  slots_in_range storage
    (w2n (w + n2w ((case bd of Fixed n => 0 | Dynamic n => 1) +
                    j * type_slot_size evt))) evt
Proof
  strip_tac >>
  `slots_in_range storage
    (w2n w + ((case bd of Fixed n => 0 | Dynamic n => 1) +
               j * type_slot_size evt)) evt` by
    (Cases_on `bd` >>
     gvs[Once vyperLookupStorageTheory.slots_in_range_def,
         vyperLookupStorageTheory.array_slots_in_range_indexed] >>
     first_x_assum drule >>
     simp[arithmeticTheory.ADD_ASSOC]) >>
  `slots_in_range storage
     (w2n w + ((case bd of Fixed n => 0 | Dynamic n => 1) +
                j * type_slot_size evt)) evt =
   slots_in_range storage
     (w2n (w + n2w ((case bd of Fixed n => 0 | Dynamic n => 1) +
                    j * type_slot_size evt))) evt` by
    (irule (cj 1 vyperLookupStorageTheory.slots_in_range_offset_cong) >>
     Cases_on `w` >> simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w]) >>
  gvs[]
QED

Theorem stride_interval_index_unique[local]:
  !a i k sz q.
    a + i * sz <= q /\ q < a + i * sz + sz /\
    a + k * sz <= q /\ q < a + k * sz + sz ==> i = k
Proof
  rpt strip_tac >>
  Cases_on `i < k`
  >- (`SUC i * sz <= k * sz` by simp[] >>
      qpat_x_assum `SUC _ * _ <= _` mp_tac >>
      pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  Cases_on `k < i`
  >- (`SUC k * sz <= i * sz` by simp[] >>
      qpat_x_assum `SUC _ * _ <= _` mp_tac >>
      pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  decide_tac
QED

Theorem dead_bytes_array_elem:
  dead_bytes st a (ArrayTV evt bd) q b /\
  j < (case bd of Fixed n => n
       | Dynamic n => MIN n (w2n (lookup_storage (n2w a) st))) /\
  a + (case bd of Fixed n => 0 | Dynamic n => 1) +
    j * type_slot_size evt <= q /\
  q < a + (case bd of Fixed n => 0 | Dynamic n => 1) +
    j * type_slot_size evt + type_slot_size evt ==>
  dead_bytes st
    (a + (case bd of Fixed n => 0 | Dynamic n => 1) +
     j * type_slot_size evt) evt q b
Proof
  Cases_on `bd` >> simp[Once dead_bytes_def] >> rpt strip_tac
  >- (rename1 `i < n` >>
      drule (cj 1 accountsRelPropsTheory.dead_bytes_range) >> strip_tac >>
      `i = j` by (irule stride_interval_index_unique >>
                   qexistsl [`a`, `q`, `type_slot_size evt`] >> simp[]) >>
      gvs[]) >>
  rename1 `i < n` >>
  qpat_x_assum `if _ then _ else _` mp_tac >> IF_CASES_TAC >> strip_tac
  >- (drule (cj 1 accountsRelPropsTheory.dead_bytes_range) >> strip_tac >>
      `i = j` by (irule stride_interval_index_unique >>
                   qexistsl [`a + 1`, `q`, `type_slot_size evt`] >> simp[]) >>
      gvs[]) >>
  `i = j` by (irule stride_interval_index_unique >>
               qexistsl [`a + 1`, `q`, `type_slot_size evt`] >>
               fs[arithmeticTheory.RIGHT_ADD_DISTRIB]) >>
  gvs[]
QED

Theorem storage_read_live_array_elem:
  storage_read_live cx tr st w (ArrayTV evt bd) /\
  j < (case bd of Fixed n => n
       | Dynamic n => MIN n (w2n (lookup_storage w st))) ==>
  storage_read_live cx tr st
    (w + n2w ((case bd of Fixed n => 0 | Dynamic n => 1) +
              j * type_slot_size evt)) evt
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `storage_read_live cx tr st (w + n2w off) evt` >>
  `off + type_slot_size evt <= type_slot_size (ArrayTV evt bd)` by
    (Cases_on `bd` >> gvs[Abbr `off`, vyperValueTheory.type_slot_size_def] >>
     `SUC j * type_slot_size evt <= n * type_slot_size evt` by simp[] >>
     qpat_x_assum `SUC _ * _ <= _` mp_tac >>
     pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  Cases_on `type_slot_size evt = 0`
  >- (simp[storage_read_live_def] >> rpt strip_tac >>
      qspec_then `w + n2w off` mp_tac wordsTheory.w2n_lt >> decide_tac) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  qx_gen_tac `slot` >> qx_gen_tac `byte` >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `w2n w + off < dimword (:256)` by decide_tac >>
  `w2n (w + n2w off) = w2n w + off` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> strip_tac >>
  `w2n w <= slot /\ slot < w2n w + type_slot_size (ArrayTV evt bd)` by
    decide_tac >>
  `dead_bytes st (w2n w) (ArrayTV evt bd) slot byte` by
    (first_x_assum irule >> simp[]) >>
  drule dead_bytes_array_elem >> disch_then (qspec_then `j` mp_tac) >>
  SIMP_TAC bool_ss [Abbr `off`, wordsTheory.n2w_w2n,
    AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  disch_then irule >> simp[]
QED


Theorem array_select_val_wf:
  val_wf (ArrayTV evt bd) arr /\
  evaluate_subscripts (ArrayTV evt bd) arr
    [ValueSubscript (IntV (&j))] = INL v ==> val_wf evt v
Proof
  Cases_on `arr` >> simp[valueEncodingTheory.val_wf_def, evaluate_subscripts_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> Cases_on `bd` >>
  simp[valueEncodingTheory.val_wf_def, evaluate_subscripts_def,
       vyperValueOperationTheory.array_index_def, AllCaseEqs(),
       listTheory.oEL_THM] >> rpt strip_tac >> gvs[]
  >- (drule_all exprSimPopTheory.elems_val_wf_EL >> simp[]) >>
  rename1 `kvs_val_wf kvs evt n` >>
  Cases_on `ALOOKUP kvs j` >> gvs[]
  >- simp[valueEncodingProofsTheory.val_wf_default_value_proof] >>
  irule valueEncodingProofsTheory.kvs_val_wf_mem >>
  goal_assum (drule_at Any) >> drule alistTheory.ALOOKUP_MEM >>
  strip_tac >> qexists_tac `j` >> simp[]
QED
