(* Source selection boundaries for array read simulation. *)
Theory exprSimArraySubscript
Ancestors
  compileEnv exprLoweringProps exprOperandVar exprSim exprSimNoPop exprSimArrayIndex vyperPlaceResultTyping vyperState
  vyperTypeEnv vyperTypeInvariants exprSimHyps supportedExprTraverse supportedStmts exprSimAttribute
  vyperPlaceFrames vyperStatePreservation vyperInterpreter vyperArray exprSimLen exprSimPop
  exprOracleStorageInterfaces vyperImmutablesPreservation vyperCreateFrame vyperCallFrame vyperCallOutcomeFrame
  fragExec venomExecSemantics venomInst venomState rich_list emitHelper intCallReturn
  exprSimForeignImmutableFrame

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

Theorem select_result_immutable_success_path:
  select_result cx ty (PlaceR (ImmutablePlace md name path)) sb s =
    (INL out,t) ==>
  out = PlaceR (ImmutablePlace md name (path ++ [sb]))
Proof
  simp[select_result_def, extend_place_def, extend_memory_place_def,
       bind_def, ignore_bind_def, return_def, raise_def,
       lift_sum_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem select_result_immutable_origin:
  select_result cx ty pv sb s =
    (INL (PlaceR (ImmutablePlace md name path')),t) ==>
  ?path. pv = PlaceR (ImmutablePlace md name path) /\
         path' = path ++ [sb]
Proof
  Cases_on `pv` >> simp[select_result_def]
  >- simp[lift_option_type_def, bind_def, lift_sum_def,
          return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> drule extend_place_immutable_origin >> simp[]
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

Theorem sub_layout_representation_transport:
  sub_layout itv old k tvt v /\
  (!b mem. val_in_memory itv fresh b mem ==> val_in_memory itv old b mem) ==>
  sub_layout itv fresh k tvt v
Proof
  simp[sub_layout_def] >> metis_tac[]
QED

Theorem immutable_holds_representation_frame:
  immutable_holds cenv cx ty tv w s /\
  (!v. read_result cx tv s = (INL v,s) ==>
       read_result cx tv t = (INL v,t)) /\
  (!name off itv old.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP s.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms)
      name = SOME (itv,old) ==>
    ?fresh.
      FLOOKUP (case ALOOKUP t.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms)
        name = SOME (itv,fresh) /\
      (!b mem. val_in_memory itv fresh b mem ==> val_in_memory itv old b mem)) ==>
  immutable_holds cenv cx ty tv w t
Proof
  simp[immutable_holds_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`name`, `off`, `itv`, `fresh`, `k`, `tvt`, `v`] >> simp[] >>
  irule sub_layout_representation_transport >> goal_assum drule >> simp[]
QED

Theorem read_result_immutable_source_map:
  (case ALOOKUP t.immutables cx.txn.target of NONE => FEMPTY
     | SOME imms => get_source_immutables md imms) =
  (case ALOOKUP s.immutables cx.txn.target of NONE => FEMPTY
     | SOME imms => get_source_immutables md imms) ==>
  (read_result cx (PlaceR (ImmutablePlace md name path)) t = (INL v,t) <=>
   read_result cx (PlaceR (ImmutablePlace md name path)) s = (INL v,s))
Proof
  Cases_on `ALOOKUP t.immutables cx.txn.target` >>
  Cases_on `ALOOKUP s.immutables cx.txn.target` >>
  simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, bind_def, return_def,
       lift_option_type_def, lift_option_def, lift_sum_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[AllCaseEqs(), return_def, raise_def] >>
  rename1 `FLOOKUP (get_source_immutables md imms) name` >>
  Cases_on `FLOOKUP (get_source_immutables md imms) name` >>
  simp[return_def, raise_def] >>
  rename1 `evaluate_subscripts (FST tvv) (SND tvv) path` >>
  Cases_on `evaluate_subscripts (FST tvv) (SND tvv) path` >>
  simp[return_def, raise_def]
QED

Theorem expr_body_pre_foreign_immutable_read:
  expr_body_pre cenv cx env e s /\ ~expr_has_pop e /\
  eval_expr cx e s = (res,t) /\ md <> NONE ==>
  (read_result cx (PlaceR (ImmutablePlace md name path)) t = (INL v,t) <=>
   read_result cx (PlaceR (ImmutablePlace md name path)) s = (INL v,s))
Proof
  rpt strip_tac >> irule read_result_immutable_source_map >>
  drule_all expr_body_pre_foreign_immutable_frame >> simp[]
QED

Theorem immutable_holds_source_frame:
  (case ALOOKUP t.immutables cx.txn.target of NONE => FEMPTY
     | SOME imms => get_source_immutables cenv.ce_module imms) =
  (case ALOOKUP s.immutables cx.txn.target of NONE => FEMPTY
     | SOME imms => get_source_immutables cenv.ce_module imms) /\
  (!v. read_result cx tv t = (INL v, t) <=>
       read_result cx tv s = (INL v, s)) /\
  immutable_holds cenv cx ty tv w s ==>
  immutable_holds cenv cx ty tv w t
Proof
  simp[immutable_holds_def] >> metis_tac[]
QED

Theorem expr_body_pre_foreign_immutable_holds:
  expr_body_pre cenv cx env e s /\ ~expr_has_pop e /\
  eval_expr cx e s = (res,t) /\ cenv.ce_module <> NONE /\ md <> NONE /\
  immutable_holds cenv cx ty (PlaceR (ImmutablePlace md name path)) w s ==>
  immutable_holds cenv cx ty (PlaceR (ImmutablePlace md name path)) w t
Proof
  rpt strip_tac >> irule immutable_holds_source_frame >>
  goal_assum (drule_at Any) >>
  conj_tac
  >- (gen_tac >> drule_all expr_body_pre_foreign_immutable_read >> simp[]) >>
  qpat_x_assum `md <> NONE` kall_tac >>
  drule_all expr_body_pre_foreign_immutable_frame >> simp[]
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

Theorem decode_static_array_elem:
  !n stor off evt vs j.
    decode_static_array stor off evt n = SOME vs /\ j < n ==>
    decode_value stor (off + j * type_slot_size evt) evt = SOME (EL j vs)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[Once vyperStorageTheory.decode_value_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `j` >> gvs[] >>
  first_x_assum drule_all >>
  simp_tac bool_ss [arithmeticTheory.MULT_CLAUSES,
    AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem decode_dyn_array_elem:
  !n stor off evt vs j.
    decode_dyn_array stor off evt n = SOME vs /\ j < n ==>
    decode_value stor (off + j * type_slot_size evt) evt = SOME (EL j vs)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[Once vyperStorageTheory.decode_value_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `j` >> gvs[] >>
  first_x_assum drule_all >>
  simp_tac bool_ss [arithmeticTheory.MULT_CLAUSES,
    AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem read_storage_slot_array_elem:
  read_storage_slot cx tr w (ArrayTV evt bd) es = (INL arr,es') /\
  evaluate_subscripts (ArrayTV evt bd) arr
    [ValueSubscript (IntV (&j))] = INL v ==>
  read_storage_slot cx tr
    (w + n2w ((case bd of Fixed n => 0 | Dynamic n => 1) +
              j * type_slot_size evt)) evt es = (INL v,es')
Proof
  Cases_on `tr` >>
  simp[read_storage_slot_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def, bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `decode_value stor` >>
  Cases_on `bd` >>
  simp[Once vyperStorageTheory.decode_value_def, AllCaseEqs(),
       lift_option_def, raise_def, return_def] >>
  rpt strip_tac
  >>~- ([`decode_static_array stor (w2n w) evt n`],
     (Cases_on `decode_static_array stor (w2n w) evt n` >>
      gvs[raise_def, return_def] >>
      rename1 `decode_static_array stor (w2n w) evt n = SOME vs` >>
      drule vyperTypeStatePreservationTheory.decode_static_array_length >>
      strip_tac >>
      gvs[evaluate_subscripts_def, vyperValueOperationTheory.array_index_def,
          AllCaseEqs()] >>
      drule vyperValueTheory.enumerate_static_array_ALOOKUP >>
      disch_then (qspecl_then [`default_value evt`, `0`] mp_tac) >>
      simp[] >> strip_tac >>
      drule_all decode_static_array_elem >>
      strip_tac >>
      `decode_value stor (w2n (w + n2w (j * type_slot_size evt))) evt =
       decode_value stor (w2n w + j * type_slot_size evt) evt` by
        (irule (cj 1 exprSimAttributeFieldsTheory.decode_value_n2w) >>
         rewrite_tac[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n]) >>
      gvs[return_def])) >>
  Cases_on `w2n (read_slot stor (w2n w)) <= n` >>
  gvs[raise_def, return_def] >>
  Cases_on `decode_dyn_array stor (w2n w + 1) evt
    (MIN (w2n (read_slot stor (w2n w))) n)` >>
  gvs[raise_def, return_def] >>
  rename1 `decode_dyn_array stor (w2n w + 1) evt len = SOME vs` >>
  drule vyperTypeStatePreservationTheory.decode_dyn_array_length >>
  strip_tac >>
  gvs[evaluate_subscripts_def, vyperValueOperationTheory.array_index_def,
      listTheory.oEL_THM, AllCaseEqs()] >>
  drule_all decode_dyn_array_elem >> strip_tac >>
  `decode_value stor (w2n (w + n2w (j * type_slot_size evt + 1))) evt =
   decode_value stor (w2n w + 1 + j * type_slot_size evt) evt` by
    (irule (cj 1 exprSimAttributeFieldsTheory.decode_value_n2w) >>
     rewrite_tac[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
     simp_tac bool_ss [AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM]) >>
  simp[return_def]
QED

Theorem vv_at_memory_region:
  vv_at cenv cx t sa sb es tv vv s /\ ~is_word_type t /\
  read_result cx tv es = (INL v,es) /\
  evaluate_type (get_tenv cx) t = SOME tvt /\
  vv_loc vv = LocMemory /\ eval_operand (vv_operand vv) s = SOME w ==>
  val_wf tvt v /\
  ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
       sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
       b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
       (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
         b + sz <= lb \/ lb + lsz <= b)) \/
   (?n b sz. local_region cenv es.scopes s n b sz /\
       b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
       (dynarray_local cenv n /\ ~dynarray_type t ==> b + 32 <= w2n w)) \/
   val_footprint tvt v = 0)
Proof
  Cases_on `vv` >>
  simp[vv_at_def, exprSimAttributeTheory.vv_loc_def, contextTheory.vv_location_def,
       contextTheory.vv_operand_def, expr_val_at_def] >>
  strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem array_select_size_bound:
  val_wf (ArrayTV evt bd) arr /\
  evaluate_subscripts (ArrayTV evt bd) arr
    [ValueSubscript (IntV (&j))] = INL v ==>
  (case bd of Fixed n => 0 | Dynamic n => 32) +
    j * type_memory_size evt + type_memory_size evt <=
    val_footprint (ArrayTV evt bd) arr
Proof
  Cases_on `arr` >> simp[valueEncodingTheory.val_wf_def, evaluate_subscripts_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> Cases_on `bd` >>
  simp[valueEncodingTheory.val_wf_def, evaluate_subscripts_def,
       vyperValueOperationTheory.array_index_def, AllCaseEqs(),
       listTheory.oEL_THM, val_footprint_def,
       valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >> gvs[] >>
  `SUC j <= n` by decide_tac >>
  `SUC j * type_memory_size evt <= n * type_memory_size evt` by
    (irule arithmeticTheory.LESS_MONO_MULT >> simp[]) >>
  qpat_x_assum `SUC j * _ <= _` mp_tac >>
  simp_tac bool_ss [arithmeticTheory.MULT_CLAUSES] >> decide_tac
QED

Theorem array_select_footprint_bound:
  val_wf (ArrayTV evt bd) arr /\
  evaluate_subscripts (ArrayTV evt bd) arr
    [ValueSubscript (IntV (&j))] = INL v ==>
  (case bd of Fixed n => 0 | Dynamic n => 32) +
    j * type_memory_size evt + val_footprint evt v <=
    val_footprint (ArrayTV evt bd) arr
Proof
  strip_tac >>
  `val_wf evt v` by (drule_all array_select_val_wf >> simp[]) >>
  drule_all array_select_size_bound >>
  drule_all val_footprint_le >> decide_tac
QED

Theorem val_in_memory_array_elem:
  val_wf (ArrayTV evt bd) arr /\
  val_in_memory (ArrayTV evt bd) arr a mem /\
  evaluate_subscripts (ArrayTV evt bd) arr
    [ValueSubscript (IntV (&j))] = INL v ==>
  val_in_memory evt v
    (a + ((case bd of Fixed cap => 0 | Dynamic cap => 32) +
          j * type_memory_size evt)) mem
Proof
  Cases_on `arr` >> simp[valueEncodingTheory.val_wf_def, evaluate_subscripts_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> Cases_on `bd` >>
  simp[valueEncodingTheory.val_wf_def, evaluate_subscripts_def,
       vyperValueOperationTheory.array_index_def, AllCaseEqs(),
       listTheory.oEL_THM, valueEncodingPropsTheory.val_in_memory_dynarray,
       valueEncodingPropsTheory.val_in_memory_sarray] >>
  rpt strip_tac >> gvs[]
  >- (drule_all exprSimAggregateEncodingTheory.elems_in_memory_EL >>
      simp[NoAsms, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  drule_all valueEncodingProofsTheory.kvs_in_memory_lookup >> simp[]
QED

Theorem array_elem_ptr_w2n:
  stmt_state_rel ctx func cenv cx es q /\
  vv_at cenv cx (ArrayT et bd) sa sn es tv bvv q /\
  read_result cx tv es = (INL arr,es) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV evt bd) /\
  evaluate_subscripts (ArrayTV evt bd) arr [ValueSubscript (IntV (&j))] = INL v /\
  vv_loc bvv = LocMemory /\ eval_operand (vv_operand bvv) q = SOME w ==>
  w2n (w + n2w ((case bd of Fixed cap => 0 | Dynamic cap => 32) +
      j * type_memory_size evt)) = w2n w +
      ((case bd of Fixed cap => 0 | Dynamic cap => 32) + j * type_memory_size evt)
Proof
  strip_tac >>
  `~is_word_type (ArrayT et bd)` by simp[is_word_type_def] >>
  drule exprSimAttributeTheory.stmt_state_rel_region_lt >> strip_tac >>
  drule_all vv_at_memory_region >> strip_tac >>
  drule_all array_select_footprint_bound >> strip_tac >>
  irule exprSimAttributeTheory.field_ptr_w2n >>
  qexistsl [`val_footprint evt v`, `val_footprint (ArrayTV evt bd) arr`] >>
  conj_tac >- decide_tac >>
  metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]
QED

Theorem array_vv_at_elem:
  stmt_state_rel ctx func cenv cx es q /\
  vv_at cenv cx (ArrayT et bd) sa sn es tv bvv q /\
  read_result cx tv es = (INL arr,es) /\
  read_result cx tv' es = (INL v,es) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV evt bd) /\
  evaluate_subscripts (ArrayTV evt bd) arr [ValueSubscript (IntV (&j))] = INL v /\
  eval_operand (vv_operand bvv) q = SOME w /\
  eval_operand dst q = SOME (w + n2w
    ((case bd of Fixed cap => 0 | Dynamic cap => 32) + j * type_memory_size evt)) ==>
  vv_at cenv cx et sa sn es tv'
    (LocatedValue et (mk_ptr dst (vv_loc bvv))) q
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) et = SOME evt` by
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  simp[vv_at_def, contextTheory.mk_ptr_def] >> strip_tac >>
  `~is_word_type (ArrayT et bd)` by simp[is_word_type_def] >>
  drule_all array_elem_ptr_w2n >>
  simp_tac bool_ss [Once arithmeticTheory.ADD_COMM] >> strip_tac >>
  drule_all vv_at_memory_region >> strip_tac >>
  `val_wf evt v` by (drule_all array_select_val_wf >> simp[]) >>
  drule_all array_select_footprint_bound >> strip_tac >>
  simp[] >>
  all_tac
  >~ [`FLOOKUP q.vs_allocas aid = SOME (b,sz)`]
  >- (disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC)
  >~ [`local_region cenv es.scopes q n b sz`]
  >- (disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >> simp[] >>
      Cases_on `bd` >> gvs[dynarray_type_def] >> strip_tac >>
      gvs[] >> decide_tac) >>
  disj2_tac >> disj2_tac >> decide_tac
QED

Theorem array_element_encoding_typing_probe[local]:
  val_wf (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
    (ArrayV (SArrayV [(0,NoneV)])) /\
  val_in_memory (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
    (ArrayV (SArrayV [(0,NoneV)])) 0 (REPLICATE 32 (1w:8 word)) /\
  evaluate_subscripts (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
    (ArrayV (SArrayV [(0,NoneV)])) [ValueSubscript (IntV 0)] = INL NoneV /\
  mem_word_at 0 (REPLICATE 32 (1w:8 word)) <>
    typed_val_to_w256 (BaseTV (UintT 256)) NoneV
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> rpt strip_tac >> gvs[]
QED


Theorem array_vv_holds_elem:
  stmt_state_rel ctx func cenv cx es q /\
  vv_holds cenv cx (ArrayT et bd) tv bvv es q /\
  vv_at cenv cx (ArrayT et bd) sa sn es tv bvv q /\
  read_result cx tv es = (INL arr,es) /\
  read_result cx tv' es = (INL v,es) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV evt bd) /\
  value_has_type evt v /\
  evaluate_subscripts (ArrayTV evt bd) arr [ValueSubscript (IntV (&j))] = INL v /\
  j < bound_length bd /\
  eval_operand (vv_operand bvv) q = SOME w /\
  eval_operand dst q = SOME (w + n2w
    (if is_slot_addressed (vv_loc bvv) then
       (case bd of Fixed cap => 0 | Dynamic cap => 1) + j * type_slot_size evt
     else (case bd of Fixed cap => 0 | Dynamic cap => 32) + j * type_memory_size evt)) /\
  (!id path. tv' = PlaceR (MemoryPlace id path) ==>
     ?p0. tv = PlaceR (MemoryPlace id p0) /\
       path = p0 ++ [ValueSubscript (IntV (&j))]) ==>
  vv_holds cenv cx et tv'
    (LocatedValue et (mk_ptr dst (vv_loc bvv))) es q
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) et = SOME evt` by
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `vv_loc bvv = LocMemory`
  >- (gvs[compileEnvTheory.is_slot_addressed_def] >>
      drule_all array_elem_ptr_w2n >> strip_tac >>
      `~is_word_type (ArrayT et bd)` by simp[is_word_type_def] >>
      drule_all vv_at_memory_region >> disch_then (assume_tac o CONJUNCT1) >>
      Cases_on `bvv` >>
      gvs[vv_holds_def, expr_val_rel_def, is_word_type_def,
          exprSimAttributeTheory.vv_loc_def, contextTheory.vv_operand_def,
          contextTheory.vv_location_def] >>
      `val_in_memory evt v (w2n w +
        ((case bd of Fixed cap => 0 | Dynamic cap => 32) + j * type_memory_size evt))
        q.vs_memory` by
        (irule val_in_memory_array_elem >> goal_assum (drule_at Any) >> simp[]) >>
      gvs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
      simp[contextTheory.mk_ptr_def, vv_holds_def] >>
      rpt conj_tac >> rpt strip_tac >>
      all_tac
      >>~- ([`mem_word_at _ _ = _`], drule_all val_in_memory_word_type >> simp[]) >>
      rpt strip_tac >>
      qpat_x_assum `!id path. tv' = _ ==> _` drule >> strip_tac >> gvs[] >>
      drule_all local_place_at_array_elem >> simp[]) >>
  Cases_on `bvv` >>
  gvs[exprSimAttributeTheory.vv_loc_def, contextTheory.vv_location_def,
      contextTheory.vv_operand_def] >>
  Cases_on `p.ptr_location` >>
  gvs[vv_holds_def, contextTheory.mk_ptr_def,
      compileEnvTheory.is_slot_addressed_def] >>
  all_tac
  >~ [`immutable_holds cenv cx et tv' _ es`]
  >- (`value_has_type (ArrayTV evt bd) arr` by gvs[immutable_holds_def] >>
      Cases_on `arr` >>
      gvs[evaluate_subscripts_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> Cases_on `bd` >>
      gvs[evaluate_subscripts_def, vyperValueOperationTheory.array_index_def,
          vyperTypingTheory.value_has_type_def,
          listTheory.oEL_THM, AllCaseEqs()]
      >- (drule_all immutable_holds_dynarray_elem >> simp[]) >>
      rename1 `read_result cx tv es = (INL (ArrayV (SArrayV kvs)),es)` >>
      rename1 `immutable_holds cenv cx (ArrayT et (Fixed cap)) tv w es` >>
      irule immutable_holds_sarray_elem >> simp[] >> qexistsl [`cap`, `kvs`, `tv`] >> simp[]) >>
  gvs[storage_holds_def] >>
  drule_all read_storage_slot_array_elem >> strip_tac >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  qmatch_goalsub_abbrev_tac `slots_in_range stor` >>
  `j < (case bd of Fixed cap => cap
        | Dynamic cap => MIN cap (w2n (lookup_storage w stor)))` by
    (Cases_on `bd` >- gvs[vyperASTTheory.bound_length_def] >>
     qpat_x_assum `read_storage_slot _ _ w _ _ = _` mp_tac >>
     simp[vyperStorageBackendTheory.read_storage_slot_eq, Abbr `stor`] >>
     simp[Once vyperStorageTheory.decode_value_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `decode_value _ _ (ArrayTV _ _) = _` mp_tac >>
     simp[Once vyperStorageTheory.decode_value_def, AllCaseEqs()] >>
     strip_tac >> gvs[] >>
     drule vyperTypeStatePreservationTheory.decode_dyn_array_length >> strip_tac >>
     gvs[evaluate_subscripts_def, vyperValueOperationTheory.array_index_def,
         listTheory.oEL_THM, AllCaseEqs(), vyperStorageTheory.read_slot_def] >>
     simp[Abbr `stor`]) >>
  gvs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  (conj_tac
  >- (once_rewrite_tac[arithmeticTheory.ADD_COMM] >> irule array_elem_slots_in_range >> simp[vyperStorageTheory.read_slot_def] >>
      Cases_on `bd` >> gvs[] >> decide_tac) >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule storage_read_live_array_elem >> simp[])
QED

Theorem array_vv_post:
  vv_post ctx func cenv cx obj es sa sn s0 es1 tv bvv q /\
  expr_type obj = ArrayT et bd /\
  read_result cx tv es1 = (INL arr,es1) /\
  read_result cx tv' es1 = (INL v,es1) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV evt bd) /\
  value_has_type evt v /\
  evaluate_subscripts (ArrayTV evt bd) arr [ValueSubscript (IntV (&j))] = INL v /\
  j < bound_length bd /\
  eval_operand (vv_operand bvv) q = SOME w /\
  eval_operand dst q = SOME (w + n2w
    (if is_slot_addressed (vv_loc bvv) then
       (case bd of Fixed cap => 0 | Dynamic cap => 1) + j * type_slot_size evt
     else (case bd of Fixed cap => 0 | Dynamic cap => 32) + j * type_memory_size evt)) /\
  (!id path. tv' = PlaceR (MemoryPlace id path) ==>
     ?p0. tv = PlaceR (MemoryPlace id p0) /\
       path = p0 ++ [ValueSubscript (IntV (&j))]) ==>
  vv_post ctx func cenv cx (Subscript et obj idx) es sa sn s0 es1 tv'
    (LocatedValue et (mk_ptr dst (vv_loc bvv))) q
Proof
  strip_tac >>
  gvs[vv_post_def, vyperASTTheory.expr_type_def] >>
  conj_tac
  >- (drule_all (SRULE[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
                    array_vv_holds_elem) >> simp[]) >>
  conj_tac
  >- (Cases_on `vv_loc bvv = LocMemory`
      >- (gvs[compileEnvTheory.is_slot_addressed_def] >>
          drule_all (SRULE[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
                       array_vv_at_elem) >> simp[]) >>
      simp[vv_at_def, contextTheory.mk_ptr_def]) >>
  first_assum ACCEPT_TAC
QED

Theorem eval_mutual_noeffect_storage[local]:
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:value list). T) /\
  (!cx e. ~expr_has_effect e ==> !s res t tr.
    eval_expr cx e s = (res,t) ==> get_storage cx t tr = get_storage cx s tr) /\
  (!cx es. ~supported_exprs_exists expr_effect_root es ==> !s res t tr.
    eval_exprs cx es s = (res,t) ==> get_storage cx t tr = get_storage cx s tr) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T) /\
  (!(cx:evaluation_context) (es:expr list). T)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def]
  >~ [`eval_expr _ (Name _ _) _ = _`]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()])
  >~ [`eval_expr _ (TopLevelName _ _) _ = _`]
  >- (rpt strip_tac >> gvs[Once evaluate_def] >> drule lookup_global_state >> simp[])
  >~ [`eval_expr _ (FlagMember _ _ _) _ = _`]
  >- (rpt strip_tac >> gvs[Once evaluate_def] >> drule lookup_flag_mem_state >> simp[])
  >~ [`eval_expr _ (Literal _ _) _ = _`]
  >- simp[Once evaluate_def, return_def]
  >~ [`eval_expr _ (IfExp _ _ _ _) _ = _`]
  >- suspend "IfExp"
  >~ [`eval_expr _ (StructLit _ _ _) _ = _`]
  >- suspend "StructLit"
  >~ [`eval_expr _ (Subscript _ _ _) _ = _`]
  >- suspend "Subscript"
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`]
  >- suspend "Attribute"
  >~ [`eval_expr _ (Builtin _ _ _) _ = _`]
  >- suspend "Builtin"
  >~ [`eval_expr _ (TypeBuiltin _ _ _ _) _ = _`]
  >- suspend "TypeBuiltin"
  >~ [`eval_exprs _ [] _ = _`]
  >- simp[Once evaluate_def, return_def] >>
  suspend "Cons"
QED

Resume eval_mutual_noeffect_storage[IfExp]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def,
      switch_BoolV_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac conditional_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED
Resume eval_mutual_noeffect_storage[StructLit]:
  simp[supported_fields_exists_every, supported_exprs_exists_every,
       listTheory.EXISTS_MAP] >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED
Resume eval_mutual_noeffect_storage[Subscript]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED
Resume eval_mutual_noeffect_storage[Attribute]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Resume eval_mutual_noeffect_storage[Builtin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (Cases_on `bt = Len` >> rpt gen_tac >> strip_tac >>
      Cases_on `bt = Env MsgGas` >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> imp_res_tac result_array_length_state >>
      imp_res_tac next_gas_reading_state >>
      imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >> gvs[] >>
      gvs[vyperStorageBackendTheory.get_storage_def,
          type_check_def, assert_def, return_def,
          supported_exprs_exists_every, listTheory.EXISTS_MEM,
          vyperContextTheory.builtin_args_length_ok_def] >>
      all_tac
      >>~- ([`LENGTH es = 1`], Cases_on `es` >> gvs[] >> metis_tac[]) >>
      Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  simp[Once evaluate_def, type_check_def, assert_def, bind_def,
       ignore_bind_def, raise_def]
QED
Resume eval_mutual_noeffect_storage[TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `type_builtin_args_length_ok tb (LENGTH es)` >>
  rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED
Resume eval_mutual_noeffect_storage[Cons]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> gvs[] >>
  qpat_x_assum `!s res t tr. eval_expr _ _ _ = _ ==> _` drule >>
  disch_then (qspec_then `tr` assume_tac) >>
  qpat_x_assum `!s0 tv t0 s1 v t1. _ /\ _ ==> _` drule_all >>
  strip_tac >> simp[]
QED
Finalise eval_mutual_noeffect_storage

Theorem eval_expr_noeffect_storage:
  ~expr_has_effect e /\ eval_expr cx e s = (res,t) ==>
  get_storage cx t tr = get_storage cx s tr
Proof
  strip_tac >>
  drule (cj 5 eval_mutual_noeffect_storage) >>
  disch_then drule >> simp[]
QED

Theorem eval_expr_noeffect_storage_read:
  ~expr_has_effect e /\ eval_expr cx e s = (res,t) ==>
  read_storage_slot cx tr w tvt t =
    (case read_storage_slot cx tr w tvt s of (r,_) => (r,t))
Proof
  strip_tac >> drule_all eval_expr_noeffect_storage >> strip_tac >>
  simp[vyperStorageBackendTheory.read_storage_slot_eq] >>
  Cases_on `decode_value (get_storage cx s tr) (w2n w) tvt` >> simp[]
QED

Theorem eval_expr_noeffect_storage_place_read:
  ~expr_has_effect e /\ eval_expr cx e s = (res,t) ==>
  read_result cx (PlaceR (StoragePlace tr w tvt)) t =
    (case read_result cx (PlaceR (StoragePlace tr w tvt)) s of (r,_) => (r,t))
Proof
  strip_tac >> simp[read_result_def, read_place_def] >>
  irule eval_expr_noeffect_storage_read >> goal_assum (drule_at Any) >> simp[]
QED

Theorem eval_expr_noeffect_storage_holds:
  ~expr_has_effect e /\ eval_expr cx e s = (res,t) /\
  storage_holds cx tr ty (PlaceR (StoragePlace tr' slot tvt)) w s ==>
  storage_holds cx tr ty (PlaceR (StoragePlace tr' slot tvt)) w t
Proof
  strip_tac >>
  `!tr. get_storage cx t tr = get_storage cx s tr` by
    (gen_tac >> drule_all eval_expr_noeffect_storage >> simp[]) >>
  gvs[storage_holds_def, read_result_def, read_place_def,
      vyperStorageBackendTheory.read_storage_slot_eq, AllCaseEqs()]
QED

(* Compiler metadata and operand frames between two expression fragments. *)
Theorem compile_expr_local_ptrs_reserved:
  compile_expr cenv ty e sa = (vv, sb) /\
  local_ptrs_reserved cenv sa ==>
  local_ptrs_reserved cenv sb
Proof
  strip_tac >> drule (cj 1 compile_expr_grows) >> strip_tac >>
  irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]
QED

Theorem lower_value_local_ptrs_reserved:
  lower_value compile_expr cenv ty e sa = (op, sb) /\
  local_ptrs_reserved cenv sa ==>
  local_ptrs_reserved cenv sb
Proof
  strip_tac >> drule (cj 2 compile_expr_grows) >> strip_tac >>
  irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]
QED

Theorem expr_post_cenv_ptr_vars:
  local_ptrs_reserved cenv sa /\
  expr_post ctx func cenv cx e es sa sb s0 es' v op s1 ==>
  !n q sz w. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) sz) /\
             lookup_var q s0 = SOME w ==> lookup_var q s1 = SOME w
Proof
  simp[expr_post_def, local_ptrs_reserved_def] >> rpt strip_tac >>
  `not_fresh_at sa q` by metis_tac[] >>
  first_x_assum irule >> simp[]
QED

Theorem compile_expr_operand_expr_post_frame:
  compile_expr cenv ty obj sa = (bvv, sm) /\
  local_ptrs_reserved cenv sa /\
  ((!l. vv_operand bvv <> Label l) \/ s1.vs_labels = s0.vs_labels) /\
  expr_post ctx func cenv cx idx es sm sn s0 es' v op s1 ==>
  !w. eval_operand (vv_operand bvv) s0 = SOME w ==>
      eval_operand (vv_operand bvv) s1 = SOME w
Proof
  strip_tac >>
  `!x. vv_operand bvv = Var x ==> not_fresh_at sm x` by
    (metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var]) >>
  rpt strip_tac >> Cases_on `vv_operand bvv` >>
  gvs[venomStateTheory.eval_operand_def] >>
  fs[expr_post_def] >> first_x_assum irule >> metis_tac[]
QED

(* Sparse/default representations differ, but give the same observation. *)
Theorem sparse_default_code_observation_probe[local]:
  !b mem.
    val_in_memory (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
      (ArrayV (SArrayV [])) b mem =
    val_in_memory (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
      (ArrayV (SArrayV [(0,IntV 0)])) b mem
Proof
  simp[valueEncodingTheory.val_in_memory_def,
       vyperValueTheory.default_value_def] 
QED

Theorem sparse_default_code_layout_probe[local]:
  !k tvt v.
    sub_layout (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
      (ArrayV (SArrayV [])) k tvt v =
    sub_layout (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
      (ArrayV (SArrayV [(0,IntV 0)])) k tvt v
Proof
  simp[sub_layout_def, sparse_default_code_observation_probe]
QED

Theorem dynamic_sparse_code_observation_probe[local]:
  !b mem.
    val_in_memory
      (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (Dynamic 1))
      (ArrayV (DynArrayV [ArrayV (SArrayV [])])) b mem =
    val_in_memory
      (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (Dynamic 1))
      (ArrayV (DynArrayV [ArrayV (SArrayV [(0,IntV 0)])])) b mem
Proof
  simp[Once valueEncodingTheory.val_in_memory_def] >>
  simp[valueEncodingTheory.val_in_memory_def,
       vyperValueTheory.default_value_def]
QED

(* Successful typed reads do not identify the existential layout's path. *)
Theorem captured_read_provenance_probe[local]:
  sub_layout (ArrayTV (BaseTV BoolT) (Fixed 1))
    (ArrayV (SArrayV [(0,BoolV F)])) 0 (BaseTV BoolT) (BoolV F) /\
  value_has_type (BaseTV BoolT) (BoolV T) /\
  evaluate_subscripts (ArrayTV (BaseTV BoolT) (Fixed 1))
    (ArrayV (SArrayV [(0,BoolV T)])) [ValueSubscript (IntV 0)] =
      INL (BoolV T) /\
  ~sub_layout (ArrayTV (BaseTV BoolT) (Fixed 1))
    (ArrayV (SArrayV [(0,BoolV F)])) 0 (BaseTV BoolT) (BoolV T)
Proof
  conj_tac
  >- simp[sub_layout_def, valueEncodingTheory.val_in_memory_def,
          valueEncodingTheory.type_memory_size_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  simp[sub_layout_def, valueEncodingTheory.type_memory_size_def] >>
  qexistsl [`0`, `REPLICATE 32 (0w:8 word)`] >>
  simp[valueEncodingTheory.val_in_memory_def,
       vyperValueTheory.default_value_def] >> EVAL_TAC >> simp[]
QED

Theorem immutable_root_read:
  !cx es md name tvt v.
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
               NONE => FEMPTY | SOME imms => get_source_immutables md imms)
      name = SOME (tvt,v) ==>
    read_result cx (PlaceR (ImmutablePlace md name [])) es = (INL v, es)
Proof
  rpt strip_tac >>
  simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, bind_def, return_def,
       lift_option_type_def, lift_option_def, lift_sum_def,
       evaluate_subscripts_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  gvs[return_def, finite_mapTheory.FLOOKUP_EMPTY]
QED

Theorem immutable_holds_root:
  !cenv cx ty es name off tvt v.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
               NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms)
      name = SOME (tvt,v) /\
    evaluate_type (get_tenv cx) ty = SOME tvt /\
    value_has_type tvt v /\
    off + type_memory_size tvt < dimword (:256) ==>
    immutable_holds cenv cx ty
      (PlaceR (ImmutablePlace cenv.ce_module name [])) (n2w off) es
Proof
  rpt strip_tac >> simp[immutable_holds_def] >>
  qexistsl [`name`, `off`, `tvt`, `v`, `0`, `v`] >>
  `off < dimword (:256)` by decide_tac >>
  simp[sub_layout_def, immutable_root_read]
QED

(* A captured immutable root reads the replacement, not its old snapshot. *)
Theorem immutable_root_replacement_read_probe[local]:
  !cx es.
    read_result cx (PlaceR (ImmutablePlace NONE "a" []))
      (es with immutables :=
        [(cx.txn.target, [(NONE,
          FEMPTY |+ ("a", (ArrayTV (BaseTV (UintT 256)) (Fixed 1),
            ArrayV (SArrayV [(0,IntV 1)]))))])]) =
    (INL (ArrayV (SArrayV [(0,IntV 1)])),
      es with immutables :=
        [(cx.txn.target, [(NONE,
          FEMPTY |+ ("a", (ArrayTV (BaseTV (UintT 256)) (Fixed 1),
            ArrayV (SArrayV [(0,IntV 1)]))))])])
Proof
  simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, get_source_immutables_def,
       bind_def, return_def, lift_option_type_def, lift_option_def,
       lift_sum_def, evaluate_subscripts_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Reconstruct the root's current layout using the new value. *)
Theorem immutable_root_replacement_holds_probe[local]:
  !cenv cx es off.
    cenv.ce_module = NONE /\
    FLOOKUP cenv.ce_module_vars (NONE,"a") = SOME (ImmutableLoc off) /\
    off + 32 < dimword (:256) ==>
    immutable_holds cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 1))
      (PlaceR (ImmutablePlace NONE "a" [])) (n2w off)
      (es with immutables :=
        [(cx.txn.target, [(NONE,
          FEMPTY |+ ("a", (ArrayTV (BaseTV (UintT 256)) (Fixed 1),
            ArrayV (SArrayV [(0,IntV 1)]))))])])
Proof
  rpt strip_tac >>
  qpat_assum `cenv.ce_module = NONE` (fn th => once_rewrite_tac[GSYM th]) >>
  irule immutable_holds_root >>
  conj_tac >- simp[] >>
  qexistsl [`ArrayTV (BaseTV (UintT 256)) (Fixed 1)`,
            `ArrayV (SArrayV [(0,IntV 1)])`] >>
  simp[get_source_immutables_def, finite_mapTheory.FLOOKUP_UPDATE,
       valueEncodingTheory.type_memory_size_def, vyperValueTheory.evaluate_type_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem immutable_mutation_call_probe[local]:
  !cx es body.
    body =
      [Assign (BaseTarget (TopLevelNameTarget (NONE,"a")))
         (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 1))
           (MakeArray (SOME (BaseT (UintT 256))) (Fixed 1))
           [Literal (BaseT (UintT 256)) (IntL 1)]);
       Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))] /\
    ~MEM (NONE,"f") cx.stk /\
    get_module_code cx NONE = SOME
      [VariableDecl Private Immutable "a"
         (ArrayT (BaseT (UintT 256)) (Fixed 1)) NONE;
       FunctionDecl Internal Nonpayable F F "f" [] []
         (BaseT (UintT 256)) body] ==>
    eval_expr cx (Call (BaseT (UintT 256)) (IntCall (NONE,"f")) [] NONE)
      (es with immutables :=
        [(cx.txn.target, [(NONE,
          FEMPTY |+ ("a", (ArrayTV (BaseTV (UintT 256)) (Fixed 1),
            ArrayV (SArrayV [(0,IntV 0)]))))])]) =
    (INL (Value (IntV 0)),
      es with immutables :=
        [(cx.txn.target, [(NONE,
          FEMPTY |+ ("a", (ArrayTV (BaseTV (UintT 256)) (Fixed 1),
            ArrayV (SArrayV [(0,IntV 1)]))))])])
Proof
  rpt strip_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_module_code``, ``get_tenv``]) >>
  simp[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_module_code``, ``get_tenv``]) >>
  fs[vyperContextTheory.get_module_code_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_module_code``, ``get_tenv``]) >>
  simp[] >> EVAL_TAC >> simp[]
QED

Theorem immutable_mutation_body_supported_probe[local]:
  !body.
    body =
      [Assign (BaseTarget (TopLevelNameTarget (NONE,"a")))
         (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 1))
           (MakeArray (SOME (BaseT (UintT 256))) (Fixed 1))
           [Literal (BaseT (UintT 256)) (IntL 1)]);
       Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))] ==>
    supported_stmts
      [VariableDecl Private Immutable "a"
         (ArrayT (BaseT (UintT 256)) (Fixed 1)) NONE;
       FunctionDecl Internal Nonpayable F F "f" [] []
         (BaseT (UintT 256)) body] [] body
Proof
  rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem nested_immutable_array_offset_probe[local]:
  mem_path_offset
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (Dynamic 1))
    [ValueSubscript (IntV 0)] =
    SOME (32, ArrayTV (BaseTV (UintT 256)) (Fixed 1))
Proof
  simp[mem_path_offset_def, mem_step_offset_def,
       valueEncodingTheory.type_memory_size_def]
QED

Theorem compile_nested_immutable_array_probe[local]:
  !cenv ty st off.
    FLOOKUP cenv.ce_module_vars (NONE,"a") = SOME (ImmutableLoc off) /\
    cenv.ce_hashmap_info (NONE,"a") = NONE ==>
    compile_expr cenv ty
      (Subscript (ArrayT (BaseT (UintT 256)) (Fixed 1))
        (TopLevelName
          (ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Dynamic 1))
          (NONE,"a"))
        (Literal (BaseT (UintT 256)) (IntL 0))) st =
    (do
       p <- compile_array_subscript (Lit (n2w off)) (Lit 0w) T 0 32 32 F
         (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode);
       comp_return (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 1))
          (mk_ptr p LocCode))
     od) st
Proof
  rpt strip_tac >>
  simp[Once (CONJUNCT1 exprLoweringTheory.compile_expr_raw_def),
       exprLoweringTheory.compile_expr_body_def,
       exprLoweringTheory.compile_subscript_def, vyperASTTheory.expr_size_def,
       vyperASTTheory.expr_type_def, exprLoweringTheory.place_type_def] >>
  simp[exprCallBoundsTheory.expr_child_callback_def,
       vyperASTTheory.expr_size_def, exprLoweringTheory.lower_value_def] >>
  simp[Once (CONJUNCT1 exprLoweringTheory.compile_expr_raw_def),
       exprLoweringTheory.compile_expr_body_def,
       exprLoweringTheory.compile_literal_vv_def,
       comp_bind_def, comp_return_def] >>
  simp[contextTheory.vv_location_def, contextTheory.vv_operand_def,
       contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def,
       compileEnvTheory.word_scale_def, compileEnvTheory.elem_size_in_location_def,
       compileEnvTheory.is_slot_addressed_def, compileEnvTheory.is_signed_type_def,
       compileEnvTheory.type_memory_bytes_def] >>
  simp[Once (CONJUNCT1 exprLoweringTheory.compile_expr_raw_def),
       exprLoweringTheory.compile_expr_body_def,
       exprLoweringTheory.compile_literal_vv_def,
       exprLoweringTheory.unwrap_value_def] >>
  simp[comp_return_def, vyperASTTheory.expr_type_def,
       exprLoweringTheory.unwrap_value_def, integer_wordTheory.i2w_def]
QED

(* Code-spine audit (compile_expr_body and both dispatcher bodies):
   TopLevelName/ImmutableLoc creates LocCode. Subscript and ordinary Attribute
   propagate the object's location; Pop propagates its target's location.
   Name always uses LocMemory (ce_allocas or ce_mem_locs). Literals return
   StackValue or a freshly allocated memory buffer. FlagMember is StackValue;
   StructLit uses base_ptr of a fresh buffer. IfExp's non-code result is proved
   in exprSimIfExpTheory.compile_expr_ifexp_not_code.
   All compile_call branches wrap results as StackValue or LocMemory/base_ptr;
   callbacks for arguments cannot supply the returned location. The builtin
   dispatcher similarly uses as_stack_val, as_ptr_val LocMemory, or base_ptr;
   MethodId's literal branch calls compile_literal_vv. The type-builtin
   dispatcher returns StackValue or LocMemory/base_ptr, including ABI paths.
   Thus no dispatcher callback's returned location escapes as a code pointer.
   This is an audit, not a general compiler provenance/execution theorem.

   The nested offset above is geometric, independent of the root value.
   Reconstructing immutable_holds at a later source state additionally needs
   read_result cx captured_place es = (INL v, es), where v has the selected
   type and sub_layout itv fresh_root 32 selected_type v. In this example that
   requires the fresh dynamic root to have element 0. A fresh empty root has
   the same type/geometry but no readable captured path. Neither compilation
   equations nor frag_exec's continuation inclusion establish that premise.
*)

Theorem nested_immutable_mutation_call_probe[local]:
  !cx es body.
    body =
      [Assign (BaseTarget (TopLevelNameTarget (NONE,"a")))
         (Builtin (ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Dynamic 1))
           (MakeArray (SOME (ArrayT (BaseT (UintT 256)) (Fixed 1))) (Dynamic 1)) []);
       Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))] /\
    ~MEM (NONE,"f") cx.stk /\
    get_module_code cx NONE = SOME
      [VariableDecl Private Immutable "a"
         (ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Dynamic 1)) NONE;
       FunctionDecl Internal Nonpayable F F "f" [] []
         (BaseT (UintT 256)) body] ==>
    eval_expr cx (Call (BaseT (UintT 256)) (IntCall (NONE,"f")) [] NONE)
      (es with immutables :=
        [(cx.txn.target, [(NONE,
          FEMPTY |+ ("a", (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (Dynamic 1),
            ArrayV (DynArrayV [ArrayV (SArrayV [(0,IntV 0)])]))))])]) =
    (INL (Value (IntV 0)),
      es with immutables :=
        [(cx.txn.target, [(NONE,
          FEMPTY |+ ("a", (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (Dynamic 1),
            ArrayV (DynArrayV []))))])])
Proof
  rpt strip_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_module_code``, ``get_tenv``]) >>
  simp[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_module_code``, ``get_tenv``]) >>
  fs[vyperContextTheory.get_module_code_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_module_code``, ``get_tenv``]) >>
  simp[] >> EVAL_TAC >> simp[]
QED

Theorem nested_immutable_mutation_body_unsupported_probe[local]:
  !body.
    body =
      [Assign (BaseTarget (TopLevelNameTarget (NONE,"a")))
         (Builtin (ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Dynamic 1))
           (MakeArray (SOME (ArrayT (BaseT (UintT 256)) (Fixed 1))) (Dynamic 1)) []);
       Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))] ==>
    ~supported_stmts
      [VariableDecl Private Immutable "a"
         (ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Dynamic 1)) NONE;
       FunctionDecl Internal Nonpayable F F "f" [] []
         (BaseT (UintT 256)) body] [] body
Proof
  gen_tac >> disch_then SUBST1_TAC >> EVAL_TAC
QED


(* Nested array immutables are rejected by the supported-value boundary,
   even though the evaluator itself permits the replacement. *)
Theorem nested_immutable_type_unsupported_probe[local]:
  !tops.
    ~supported_value_type tops
      (ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Dynamic 1))
Proof
  gen_tac >> EVAL_TAC
QED


Theorem immutable_dynamic_root_reconstruction_probe[local]:
  !cenv cx es off.
    cenv.ce_module = NONE /\
    FLOOKUP cenv.ce_module_vars (NONE,"a") = SOME (ImmutableLoc off) /\
    off + 64 < dimword (:256) ==>
    immutable_holds cenv cx (ArrayT (BaseT (UintT 256)) (Dynamic 1))
      (PlaceR (ImmutablePlace NONE "a" [])) (n2w off)
      (es with immutables :=
        [(cx.txn.target, [(NONE,
          FEMPTY |+ ("a", (ArrayTV (BaseTV (UintT 256)) (Dynamic 1),
            ArrayV (DynArrayV []))))])])
Proof
  rpt strip_tac >>
  qpat_assum `cenv.ce_module = NONE` (fn th => once_rewrite_tac[GSYM th]) >>
  irule immutable_holds_root >>
  conj_tac >- simp[] >>
  qexistsl [`ArrayTV (BaseTV (UintT 256)) (Dynamic 1)`,
            `ArrayV (DynArrayV [])`] >>
  simp[get_source_immutables_def, finite_mapTheory.FLOOKUP_UPDATE,
       valueEncodingTheory.type_memory_size_def,
       vyperValueTheory.evaluate_type_def] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def]
QED

Theorem supported_immutable_array_element_not_array:
  !tops et bd inner ib.
    supported_value_type tops (ArrayT et bd) ==>
    et <> ArrayT inner ib
Proof
  rpt gen_tac >> Cases_on `bd` >>
  simp[supportedTypesTheory.supported_value_array_depth] >>
  rpt strip_tac >> gvs[supportedTypesTheory.supported_word_type_def]
QED

Theorem supported_immutable_tuple_element_not_array:
  !tops ts et inner ib.
    supported_value_type tops (TupleT ts) /\ MEM et ts ==>
    et <> ArrayT inner ib
Proof
  rpt strip_tac >>
  gvs[supportedTypesTheory.supported_value_tuple_depth,
      listTheory.EVERY_MEM] >>
  first_x_assum drule >>
  simp[supportedTypesTheory.supported_scalar_type_def,
       supportedTypesTheory.supported_word_type_def,
       supportedTypesTheory.supported_string_type_def]
QED

Theorem supported_immutable_struct_field_not_array:
  !tops ns fields name et inner ib.
    supported_value_type tops (StructT ns) /\
    supported_struct_fields tops ns = SOME fields /\
    MEM (name,et) fields ==>
    et <> ArrayT inner ib
Proof
  rpt strip_tac >>
  gvs[supportedTypesTheory.supported_value_type_def,
      supportedTypesTheory.supported_scalar_type_def,
      supportedTypesTheory.supported_word_type_def,
      supportedTypesTheory.supported_string_type_def,
      listTheory.EVERY_MEM] >>
  first_x_assum drule >>
  simp[supportedTypesTheory.supported_word_type_def]
QED

Theorem compile_immutable_root_shape:
  !cenv ty ann md name off st.
    FLOOKUP cenv.ce_module_vars (md,name) = SOME (ImmutableLoc off) ==>
    compile_expr cenv ty (TopLevelName ann (md,name)) st =
      (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode), st)
Proof
  rpt strip_tac >>
  simp[Once (CONJUNCT1 exprLoweringTheory.compile_expr_raw_def),
       exprLoweringTheory.compile_expr_body_def, vyperASTTheory.expr_type_def]
QED

Theorem eval_immutable_root:
  !cx es ann md name ts tvt v.
    get_module_code cx md = SOME ts /\
    find_var_decl_by_name name ts = NONE /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
               NONE => FEMPTY | SOME imms => get_source_immutables md imms)
      name = SOME (tvt,v) ==>
    eval_expr cx (TopLevelName ann (md,name)) es =
      (INL (PlaceR (ImmutablePlace md name [])), es)
Proof
  rpt strip_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def, lookup_global_def,
       get_immutables_def, get_address_immutables_def,
       bind_def, return_def, lift_option_type_def, lift_option_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  gvs[return_def, finite_mapTheory.FLOOKUP_EMPTY]
QED

(* C1.4.12 consumer-interface ledger (not an asserted theorem):

   Proposed remaining provenance interface:
     expr_body_pre cenv cx env obj es /\
     expr_type obj = ArrayT et bd /\ ~expr_has_pop obj /\
     eval_expr cx obj es = (INL tv, em) /\
     compile_expr cenv ty obj sa = (bvv, sm) /\
     vv_location bvv = SOME LocCode
       ==> ?name off.
         tv = PlaceR (ImmutablePlace cenv.ce_module name []) /\
         vv_operand bvv = Lit (n2w off) /\
         FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
           SOME (ImmutableLoc off).

   This interface is still UNPROVED and may require a conditional supported
   program premise or a split on int_calls_expr idx. expr_body_pre does NOT
   globally require supported_expr obj: supported_program tops is provided
   only for members of int_calls_expr. Thus the three inversion facts above
   cannot by themselves exclude all proper selected code subobjects at the
   use site. With a call in idx, extract the supported module via its body
   precondition; without calls a source immutable frame may be the relevant
   route. Neither route is currently a formal provenance theorem.

   Checked root branches: compile_immutable_root_shape fixes operand and
   compiler offset; eval_immutable_root fixes source result and unchanged
   source state from actual module-code/declaration/lookup premises. They do
   not derive those premises from expr_body_pre. In particular ce_module
   agreement and the source-name/compiler-name correspondence need proof.

   Branch obligations still missing for the proposed general interface:
   Subscript/Attribute propagate location but require typing plus supported
   declaration inversion to exclude array-valued proper components; Pop is
   excluded by syntax. IfExp has a checked non-code-location theorem. Name,
   literals, StructLit, FlagMember, Call, builtin and type-builtin dispatch
   have the audited output wrappers, but no general non-code theorem for
   all these branches was found. No broad compiler induction is claimed.

   Endpoint reconstruction ledger after the root facts are available:
   - eval_expr_immutable_metadata_frame and immutable_metadata_frame_lookup
     preserve lookup existence/type at the index endpoint, not its value;
   - expr_body_pre_eval_result supplies the endpoint semantic invariants;
     the typed immutable-lookup consequence must give value_has_type there;
   - evaluate_type uses the same cx, so its root type equation is unchanged;
   - compiler module-vars/offset and off+type_memory_size bounds are static;
   - immutable_holds_root consumes precisely these current facts. No old/new
     read equality is needed in this branch. vv_at/operand-frame integration
     is separate and remains open; no frozen theorem proof follows yet.
*)

(* A call-free expression may still pop an immutable: no-pop is essential. *)
Theorem callfree_immutable_pop_mutates_probe[local]:
  !cx s.
    s.immutables =
      [(cx.txn.target, [(NONE, FEMPTY |+
        ("a", (ArrayTV (BaseTV (UintT 256)) (Dynamic 1),
               ArrayV (DynArrayV [IntV 7]))))])] ==>
    ?v t. pop_place cx (ImmutablePlace NONE "a" []) s = (INL v,t) /\
          t.immutables <> s.immutables
Proof
  rpt strip_tac >>
  simp[pop_place_def, get_immutables_def, get_address_immutables_def,
       bind_def, return_def, lift_option_type_def, lift_option_def,
       lift_sum_def, set_immutable_def] >>
  EVAL_TAC >>
  gvs[raise_def, return_def] >>
  EVAL_TAC >>
  strip_tac >>
  pop_assum (mp_tac o Q.AP_TERM `\fm. FLOOKUP fm "a"`) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem eval_mutual_callfree_nopop_immutables[local]:
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:value list). T) /\
  (!cx e. int_calls_expr e = [] /\ ~expr_has_pop e ==> !s res t.
    eval_expr cx e s = (res,t) ==> t.immutables = s.immutables) /\
  (!cx es. EVERY (\e. int_calls_expr e = [] /\ ~expr_has_pop e) es ==> !s res t.
    eval_exprs cx es s = (res,t) ==> t.immutables = s.immutables) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T) /\
  (!cx es. EVERY (\e. int_calls_expr e = [] /\ ~expr_has_pop e) es ==> !s res t.
    eval_expr_results cx es s = (res,t) ==> t.immutables = s.immutables)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[vyperTypeCallGraphTheory.int_calls_expr_def, expr_has_pop_def, supported_expr_exists_def,
       expr_pop_root_def, int_calls_exprs_empty_every,
       int_calls_named_exprs_empty_every, supported_exprs_exists_every,
       supported_fields_exists_every, listTheory.EVERY_CONJ,
       listTheory.EVERY_MAP, combinTheory.o_DEF]
  >~ [`eval_expr _ (Name _ _) _ = _`]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()])
  >~ [`eval_expr _ (TopLevelName _ _) _ = _`]
  >- (rpt strip_tac >> gvs[Once evaluate_def] >> drule lookup_global_immutables >> simp[])
  >~ [`eval_expr _ (FlagMember _ _ _) _ = _`]
  >- (rpt strip_tac >> gvs[Once evaluate_def] >> drule lookup_flag_mem_state >> simp[])
  >~ [`eval_expr _ (Literal _ _) _ = _`]
  >- simp[Once evaluate_def, return_def]
  >~ [`eval_expr _ (IfExp _ _ _ _) _ = _`]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def,
          switch_BoolV_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac read_result_state >> imp_res_tac conditional_result_state >> gvs[] >>
      gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[])
  >~ [`eval_expr _ (StructLit _ _ _) _ = _`]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      imp_res_tac lift_sum_state >> gvs[] >> metis_tac[])
  >~ [`eval_expr _ (Subscript _ _ _) _ = _`]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac read_result_state >> imp_res_tac select_result_state >>
      gvs[] >> metis_tac[])
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac select_result_state >> gvs[] >> metis_tac[])
  >~ [`eval_expr _ (Builtin _ _ _) _ = _`] >- suspend "Builtin"
  >~ [`eval_expr _ (TypeBuiltin _ _ _ _) _ = _`] >- suspend "TypeBuiltin"
  >~ [`eval_expr _ (Call _ (Send _) _ _) _ = _`] >- suspend "Send"
  >~ [`eval_expr _ (Call _ (ExtCall _ _ _ _) _ _) _ = _`] >- suspend "ExtCall"
  >~ [`eval_expr _ (Call _ (RawCallTarget _) _ _) _ = _`] >- suspend "RawCall"
  >~ [`eval_expr _ (Call _ (RawCallCalldataTarget _) _ _) _ = _`] >- suspend "RawCalldata"
  >~ [`eval_expr _ (Call _ RawLog _ _) _ = _`] >- suspend "RawLog"
  >~ [`eval_expr _ (Call _ RawRevert _ _) _ = _`] >- suspend "RawRevert"
  >~ [`eval_expr _ (Call _ SelfDestructTarget _ _) _ = _`] >- suspend "SelfDestruct"
  >~ [`eval_expr _ (Call _ (CreateTarget _ _ _) _ _) _ = _`] >- suspend "Create"
  >~ [`eval_exprs _ [] _ = _`] >- simp[Once evaluate_def, return_def]
  >~ [`eval_exprs _ (_::_) _ = _`] >- suspend "Cons"
  >~ [`eval_expr_results _ [] _ = _`] >- simp[Once evaluate_def, return_def] >>
  suspend "ResultsCons"
QED

Resume eval_mutual_callfree_nopop_immutables[Builtin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (Cases_on `bt = Len` >> rpt gen_tac >> strip_tac >>
      Cases_on `bt = Env MsgGas` >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> imp_res_tac result_array_length_state >>
      imp_res_tac next_gas_reading_state >>
      imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >> gvs[] >>
      gvs[type_check_def, assert_def, return_def,
          vyperContextTheory.builtin_args_length_ok_def] >>
      all_tac
      >>~- ([`LENGTH es = 1`], Cases_on `es` >> gvs[] >> metis_tac[])) >>
  simp[Once evaluate_def, type_check_def, assert_def, bind_def,
       ignore_bind_def, raise_def]
QED
Resume eval_mutual_callfree_nopop_immutables[TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `type_builtin_args_length_ok tb (LENGTH es)` >>
  rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED
Resume eval_mutual_callfree_nopop_immutables[Send]:
  rpt gen_tac >> strip_tac >>
  Cases_on `LENGTH es = if has_gas then 3 else 2` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), type_check_def, assert_def, return_def] >>
  imp_res_tac eval_send_preserves_non_accounts >> gvs[] >> metis_tac[]
QED
Resume eval_mutual_callfree_nopop_immutables[ExtCall]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> imp_res_tac eval_ext_call_preserves_non_accounts >>
  imp_res_tac read_results_state >> gvs[] >>
  `!n. EVERY (\e. int_calls_expr e = []) (TAKE n es)` by
    simp[rich_listTheory.EVERY_TAKE] >>
  `!n. EVERY (\e. int_calls_expr e = []) (DROP n es)` by
    simp[rich_listTheory.EVERY_DROP] >>
  `!n m. EVERY (\e. int_calls_expr e = []) (TAKE n (DROP m es))` by
    simp[rich_listTheory.EVERY_TAKE] >>
  `!n. EVERY (\e. ~supported_expr_exists expr_pop_root e) (TAKE n es)` by
    simp[rich_listTheory.EVERY_TAKE] >>
  `!n. EVERY (\e. ~supported_expr_exists expr_pop_root e) (DROP n es)` by
    simp[rich_listTheory.EVERY_DROP] >>
  `!n m. EVERY (\e. ~supported_expr_exists expr_pop_root e) (TAKE n (DROP m es))` by
    simp[rich_listTheory.EVERY_TAKE] >>
  gvs[] >>
  rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!a b c. _` drule_all >> strip_tac) >>
  metis_tac[]
QED
Resume eval_mutual_callfree_nopop_immutables[RawCall]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
       return_def, raise_def, type_check_def, assert_def,
       lift_option_type_def, vyperMiscTheory.option_CASE_rator] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[]
QED
Resume eval_mutual_callfree_nopop_immutables[RawCalldata]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
       return_def, raise_def, type_check_def, assert_def,
       lift_option_type_def, vyperMiscTheory.option_CASE_rator] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[]
QED
Resume eval_mutual_callfree_nopop_immutables[RawLog]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
       return_def, raise_def, check_def, type_check_def, assert_def,
       lift_option_def, lift_option_type_def, push_log_def, vyperMiscTheory.option_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >> metis_tac[]
QED
Resume eval_mutual_callfree_nopop_immutables[RawRevert]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
      return_def, raise_def, check_def, type_check_def, assert_def] >> metis_tac[]
QED
Resume eval_mutual_callfree_nopop_immutables[SelfDestruct]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
       return_def, raise_def, check_def, type_check_def, assert_def,
       lift_option_def, lift_option_type_def, get_accounts_def,
       vyperMiscTheory.option_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac transfer_value_immutables >> gvs[] >> metis_tac[]
QED
Resume eval_mutual_callfree_nopop_immutables[Create]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `!n. EVERY (\e. int_calls_expr e = []) (TAKE n es)` by
    simp[rich_listTheory.EVERY_TAKE] >>
  `!n. EVERY (\e. int_calls_expr e = []) (DROP n es)` by
    simp[rich_listTheory.EVERY_DROP] >>
  `!n m. EVERY (\e. int_calls_expr e = []) (TAKE n (DROP m es))` by
    simp[rich_listTheory.EVERY_TAKE] >>
  `!n m. EVERY (\e. int_calls_expr e = []) (DROP n (DROP m es))` by
    simp[rich_listTheory.EVERY_DROP] >>
  `!n. EVERY (\e. ~supported_expr_exists expr_pop_root e) (TAKE n es)` by
    simp[rich_listTheory.EVERY_TAKE] >>
  `!n. EVERY (\e. ~supported_expr_exists expr_pop_root e) (DROP n es)` by
    simp[rich_listTheory.EVERY_DROP] >>
  `!n m. EVERY (\e. ~supported_expr_exists expr_pop_root e) (TAKE n (DROP m es))` by
    simp[rich_listTheory.EVERY_TAKE] >>
  `!n m. EVERY (\e. ~supported_expr_exists expr_pop_root e) (DROP n (DROP m es))` by
    simp[rich_listTheory.EVERY_DROP] >>
  Cases_on `kind` >> gvs[] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac check_create_blueprint_result_state >> gvs[] >>
  imp_res_tac read_results_state >> gvs[] >>
  imp_res_tac eval_create_preserves_scopes_immutables >> gvs[] >>
  rpt (qpat_x_assum `!s prefix t s1 code_size t1. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!s prefix t s1 results t1 s2 args t2. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!s prefix t. _` drule_all >> strip_tac) >>
  metis_tac[]
QED
Resume eval_mutual_callfree_nopop_immutables[Cons]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED
Resume eval_mutual_callfree_nopop_immutables[ResultsCons]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  metis_tac[]
QED
Finalise eval_mutual_callfree_nopop_immutables

Theorem eval_expr_callfree_nopop_immutables:
  int_calls_expr e = [] /\ ~expr_has_pop e /\
  eval_expr cx e s = (res,t) ==> t.immutables = s.immutables
Proof
  strip_tac >> drule_all (cj 5 eval_mutual_callfree_nopop_immutables) >> simp[]
QED

Theorem eval_exprs_callfree_nopop_immutables:
  int_calls_exprs es = [] /\ EVERY (\e. ~expr_has_pop e) es /\
  eval_exprs cx es s = (res,t) ==> t.immutables = s.immutables
Proof
  strip_tac >> irule (cj 6 eval_mutual_callfree_nopop_immutables) >>
  goal_assum (drule_at Any) >>
  gvs[listTheory.EVERY_CONJ, int_calls_exprs_empty_every]
QED

Theorem read_result_immutable_callfree_nopop:
  int_calls_expr e = [] /\ ~expr_has_pop e /\
  eval_expr cx e s = (res,t) ==>
  (read_result cx (PlaceR (ImmutablePlace md name path)) t = (INL v,t) <=>
   read_result cx (PlaceR (ImmutablePlace md name path)) s = (INL v,s))
Proof
  strip_tac >> drule_all eval_expr_callfree_nopop_immutables >> strip_tac >>
  irule read_result_source_components >> simp[]
QED

Theorem immutable_holds_callfree_nopop:
  int_calls_expr e = [] /\ ~expr_has_pop e /\
  eval_expr cx e s = (res,t) /\
  immutable_holds cenv cx ty (PlaceR (ImmutablePlace md name path)) w s ==>
  immutable_holds cenv cx ty (PlaceR (ImmutablePlace md name path)) w t
Proof
  strip_tac >>
  drule_all eval_expr_callfree_nopop_immutables >> strip_tac >>
  irule immutable_holds_source_frame >> simp[] >>
  metis_tac[read_result_immutable_callfree_nopop]
QED

Theorem vv_holds_code_immutable_callfree_nopop:
  int_calls_expr e = [] /\ ~expr_has_pop e /\
  eval_expr cx e s = (res,t) /\
  vv_location vv = SOME LocCode /\
  vv_holds cenv cx ty (PlaceR (ImmutablePlace md name path)) vv s q /\
  (!w. eval_operand (vv_operand vv) q = SOME w ==>
       eval_operand (vv_operand vv) q' = SOME w) ==>
  vv_holds cenv cx ty (PlaceR (ImmutablePlace md name path)) vv t q'
Proof
  Cases_on `vv` >> simp[contextTheory.vv_location_def] >>
  rpt strip_tac >> rename1 `pp.ptr_location = LocCode` >>
  gvs[vv_holds_def, contextTheory.vv_operand_def] >>
  drule_all immutable_holds_callfree_nopop >> simp[]
QED

Theorem vv_at_code:
  vv_location vv = SOME LocCode ==> vv_at cenv cx ty sa sb t tv vv q
Proof
  Cases_on `vv` >> simp[contextTheory.vv_location_def, vv_at_def]
QED

(* C1.4.13 use-site ledger:
   The empty-int_calls_expr branch now has checked immutable-table and
   captured ImmutablePlace read/holds preservation, including proper paths.
   Both exclusions matter: no internal calls alone permits ImmutablePlace
   Pop (the checked primitive probe above). The frozen no-pop hypothesis
   yields ~expr_has_pop idx by expr_has_pop_def and supported_expr_exists_def.
   The call-free premise is supplied by the branch split, and successful
   index evaluation by the source Subscript equation. Operand preservation
   is supplied by compile_expr_operand_expr_post_frame after index simulation.
   vv_at_code needs only the known location. No supported_program or root
   restriction is used in these boundaries.

   Remaining interface: vv_holds_code_immutable_callfree_nopop requires the
   captured source result to be an ImmutablePlace. Neither vv_location nor
   vv_holds alone establishes that shape; code representations can describe
   reads of other result forms. General compiler/source result provenance
   is still unproved. No storage-read frame across external calls is claimed.
   The nonempty-internal-call route and task-level endpoint composition
   remain gated; the C1.4.12 proposed root-only implication is NOT proved.
*)

(* The proposed origin proof cannot extract module-variable correspondence
   from the body precondition: that precondition ignores this table. *)
Theorem expr_body_pre_global_module_vars_frame:
  expr_body_pre (cenv with ce_module_vars := vars) cx env
    (TopLevelName ann nsid) es <=>
  expr_body_pre cenv cx env (TopLevelName ann nsid) es
Proof
  simp[expr_body_pre_def, expr_sim_inv_def,
       allocLimitsTheory.alloc_limits_expr_def,
       placeTypingPropsTheory.place_map_tables_agree_on_defined_def]
QED

Theorem expr_body_pre_global_module_frame:
  expr_body_pre (cenv with ce_module := md) cx env
    (TopLevelName ann nsid) es <=>
  expr_body_pre cenv cx env (TopLevelName ann nsid) es
Proof
  simp[expr_body_pre_def, expr_sim_inv_def,
       allocLimitsTheory.alloc_limits_expr_def,
       placeTypingPropsTheory.place_map_tables_agree_on_defined_def]
QED

Theorem eval_global_no_decl_immutable:
  find_var_decl_by_name name ts = NONE /\
  get_module_code cx md = SOME ts /\
  eval_expr cx (TopLevelName ann (md,name)) es = (INL tv,em) ==>
  tv = PlaceR (ImmutablePlace md name []) /\ em = es
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, lookup_global_def,
      get_immutables_def, get_address_immutables_def,
      bind_def, return_def, lift_option_type_def, lift_option_def,
      raise_def, vyperMiscTheory.option_CASE_rator, AllCaseEqs()]
QED

(* Unlike expr_body_pre alone, the environment relations of state_rel rule
   out a successful storage lookup compiled as an immutable pointer. *)
Theorem related_global_code_result_origin:
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  FLOOKUP cenv.ce_module_vars (md,name) = SOME (ImmutableLoc off) /\
  eval_expr cx (TopLevelName ann (md,name)) s = (INL res,t) ==>
  res = PlaceR (ImmutablePlace md name []) /\ t = s
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, lookup_global_def,
      bind_def, return_def, lift_option_type_def, raise_def,
      get_immutables_def, get_address_immutables_def, lift_option_def,
      vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
      var_decl_info_CASE_rator, AllCaseEqs()]
  >~ [`StorageVarDecl`]
  >- (drule_all exprSimLeavesTheory.toplevel_storage_ce_vars >>
      Cases_on `tr` >> simp[]) >>
  rename1 `HashMapVarDecl tr kt vt` >> Cases_on `tr` >>
  gvs[storage_vars_rel_def, transient_vars_rel_def]
  >~ [`lookup_var_slot_from_layout cx T md id`]
  >- (qpat_x_assum `!src ts name d id slot_num. _ /\ _ /\ var_decl_transient d /\ _ ==> _`
        (drule_then mp_tac) >> simp[var_decl_transient_def] >>
        goal_assum (drule_at Any) >>
        goal_assum (drule_at Any) >> simp[var_decl_transient_def]) >>
  qpat_x_assum `!src ts name d id slot_num. _ /\ _ /\ ~var_decl_transient d /\ _ ==> _`
    (drule_then mp_tac) >> simp[var_decl_transient_def] >>
        goal_assum (drule_at Any) >>
        goal_assum (drule_at Any) >> simp[var_decl_transient_def]
QED

Theorem related_global_code_place_origin:
  !cenv cx ann md name off s p t.
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    FLOOKUP cenv.ce_module_vars (md,name) = SOME (ImmutableLoc off) /\
    eval_expr cx (TopLevelName ann (md,name)) s = (INL (PlaceR p),t) ==>
    p = ImmutablePlace md name [] /\ t = s
Proof
  rpt strip_tac >> drule_all related_global_code_result_origin >> simp[]
QED

Theorem select_result_value_or_immutable:
  ((?v. pv = Value v) \/
   (?md name path. pv = PlaceR (ImmutablePlace md name path))) /\
  select_result cx ty pv sb s = (INL res,t) ==>
  (?v. res = Value v) \/
  (?md name path. res = PlaceR (ImmutablePlace md name path))
Proof
  strip_tac
  >- (gvs[select_result_def, bind_def, return_def, raise_def,
          lift_sum_def, AllCaseEqs()]) >>
  gvs[] >> drule select_result_immutable_success_path >> simp[] >> metis_tac[]
QED

Theorem compile_attribute_code_origin:
  vv_location (FST (compile_attribute cfn cenv rt ty obj fld sc)) = SOME LocCode ==>
  vv_location (FST (cfn cenv ty obj sc)) = SOME LocCode
Proof
  Cases_on `cfn cenv ty obj sc` >>
  rename1 `cfn cenv ty obj sc = (vv,sm)` >>
  simp[exprLoweringTheory.compile_attribute_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >>
  Cases_on `vv_location vv` >>
  simp[contextTheory.vv_location_def, contextTheory.mk_ptr_def]
QED

Theorem compile_subscript_code_origin:
  vv_location (FST (compile_subscript cfn cenv rt ty obj idx sc)) = SOME LocCode ==>
  vv_location (FST (cfn cenv ty obj sc)) = SOME LocCode
Proof
  Cases_on `cfn cenv ty obj sc` >>
  rename1 `cfn cenv ty obj sc = (vv,sm)` >>
  Cases_on `place_type cenv obj`
  >~ [`ValPT bt`]
  >- (Cases_on `bt` >> Cases_on `vv_location vv` >>
      simp[exprLoweringTheory.compile_subscript_def,
           comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[contextTheory.vv_location_def, contextTheory.mk_ptr_def]) >>
  Cases_on `vv_location vv` >>
  simp[exprLoweringTheory.compile_subscript_def,
       comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[comp_bind_def, comp_return_def,
      contextTheory.vv_location_def, contextTheory.mk_ptr_def]
QED

Theorem compile_expr_code_result_origin:
  !e cenv cx ty sc s res t.
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    ~expr_has_pop e /\
    vv_location (FST (compile_expr cenv ty e sc)) = SOME LocCode /\
    eval_expr cx e s = (INL res,t) ==>
    (?v. res = Value v) \/
    (?md name path. res = PlaceR (ImmutablePlace md name path))
Proof
  ho_match_mp_tac (vyperASTTheory.expr_induction |> Q.SPEC `P` |>
    Q.SPEC `\x. T` |> SIMP_RULE (srw_ss()) []) >>
  rpt conj_tac >> rpt gen_tac >>
  simp[expr_has_pop_def, supported_expr_exists_def, expr_pop_root_def] >>
  all_tac >~ [`eval_expr _ (Name _ _) _ = _`] >- suspend "Name" >~
  [`eval_expr _ (TopLevelName _ _) _ = _`] >- suspend "Global" >~
  [`eval_expr _ (FlagMember _ _ _) _ = _`] >- suspend "Flag" >~
  [`eval_expr _ (IfExp _ _ _ _) _ = _`] >- suspend "If" >~
  [`eval_expr _ (Literal _ _) _ = _`] >-
    (rpt strip_tac >> drule eval_expr_literal_value >> metis_tac[]) >~
  [`eval_expr _ (StructLit _ _ _) _ = _`] >- suspend "Struct" >~
  [`eval_expr _ (Subscript _ _ _) _ = _`] >- suspend "Subscript" >~
  [`eval_expr _ (Attribute _ _ _) _ = _`] >- suspend "Attribute" >~
  [`eval_expr _ (Builtin _ _ _) _ = _`] >-
    (rpt strip_tac >> drule eval_expr_builtin_value >> metis_tac[]) >~
  [`eval_expr _ (TypeBuiltin _ _ _ _) _ = _`] >- suspend "TypeBuiltin" >>
  suspend "Call"
QED

Resume compile_expr_code_result_origin[Name]:
  rename1 `Name ann nm` >>
  Cases_on `FLOOKUP cenv.ce_vars nm` >>
  simp[Once exprLoweringTheory.compile_expr_def,
       exprLoweringTheory.compile_name_vv_def, comp_return_def,
       comp_bind_def, comp_ignore_bind_def,
       contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[contextTheory.vv_location_def] >>
  rename1 `FLOOKUP cenv.ce_vars nm = SOME vl` >> Cases_on `vl` >>
  simp[comp_return_def, comp_bind_def,
       contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[contextTheory.vv_location_def]
QED

Resume compile_expr_code_result_origin[If]:
  simp[exprSimIfExpTheory.compile_expr_ifexp_not_code]
QED

Resume compile_expr_code_result_origin[Struct]:
  rpt strip_tac >>
  rename1 `eval_expr cx (StructLit ann nsid fields) st = _` >>
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()]
QED

Resume compile_expr_code_result_origin[TypeBuiltin]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
QED

Resume compile_expr_code_result_origin[Flag]:
  rpt strip_tac >>
  rename1 `eval_expr cx (FlagMember ann nsid fld) st = _` >>
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, lookup_flag_mem_def,
      bind_def, return_def, raise_def, lift_sum_def, lift_option_type_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()]
QED

Resume compile_expr_code_result_origin[Global]:
  rename1 `TopLevelName ann nsid` >> PairCases_on `nsid` >>
  Cases_on `FLOOKUP cenv.ce_module_vars (nsid0,nsid1)` >>
  simp[Once exprLoweringTheory.compile_expr_def,
       contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[contextTheory.vv_location_def] >>
  rename1 `FLOOKUP cenv.ce_module_vars _ = SOME vl` >> Cases_on `vl` >>
  simp[contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[contextTheory.vv_location_def] >>
  rpt strip_tac >> drule_all related_global_code_result_origin >>
  strip_tac >> gvs[]
QED
Resume compile_expr_code_result_origin[Attribute]:
  rpt strip_tac >>
  qpat_x_assum `vv_location _ = SOME LocCode` mp_tac >>
  simp[Once exprLoweringTheory.compile_expr_def] >>
  strip_tac >> drule_then assume_tac compile_attribute_code_origin >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >>
  irule select_result_value_or_immutable >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume compile_expr_code_result_origin[Subscript]:
  rpt strip_tac >>
  qpat_x_assum `vv_location _ = SOME LocCode` mp_tac >>
  simp[Once exprLoweringTheory.compile_expr_def] >>
  strip_tac >> drule_then assume_tac compile_subscript_code_origin >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >>
  irule select_result_value_or_immutable >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume compile_expr_code_result_origin[Call]:
  rpt strip_tac >>
  rename1 `eval_expr cx (Call ann target args kws) st = _` >>
  Cases_on `target` >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()]
  >~ [`eval_expr _ (Call _ (IntCall _) _ _) _ = _`]
  >- suspend "IntCall"
  >~ [`eval_ext_call _ _ _ _ _ _ _ = _`]
  >- (drule eval_ext_call_value >> metis_tac[])
  >~ [`eval_send _ _ _ _ = _`]
  >- suspend "Send"
  >~ [`eval_raw_call _ _ _ _ _ _ _ = _`]
  >- (drule eval_raw_call_value >> metis_tac[])
  >~ [`eval_raw_call _ _ _ _ _ _ _ = _`]
  >- (drule eval_raw_call_value >> metis_tac[]) >>
  suspend "Create"
QED
Resume compile_expr_code_result_origin[IntCall]:
  rename1 `eval_expr cx (Call ann (IntCall nsid) args kws) st = _` >>
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()]
QED

Resume compile_expr_code_result_origin[Send]:
  rename1 `eval_send cx has_gas vs mid = _` >>
  Cases_on `vs` >- gvs[eval_send_def, raise_def] >>
  rename1 `eval_send cx has_gas (to_v::rest) mid = _` >>
  Cases_on `rest` >>
  gvs[eval_send_def, bind_def, ignore_bind_def, return_def, raise_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  pairarg_tac >> gvs[bind_def, ignore_bind_def, return_def, AllCaseEqs()]
QED

Resume compile_expr_code_result_origin[Create]:
  qmatch_asmsub_rename_tac `eval_create cx kind _ _ _ _ _` >>
  Cases_on `kind` >> gvs[bind_def, AllCaseEqs()] >>
  drule eval_create_value >> metis_tac[]
QED
Finalise compile_expr_code_result_origin

Theorem compile_expr_code_place_origin:
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  ~expr_has_pop e /\
  vv_location (FST (compile_expr cenv ty e sc)) = SOME LocCode /\
  eval_expr cx e s = (INL (PlaceR p),t) ==>
  ?md name path. p = ImmutablePlace md name path
Proof
  rpt strip_tac >> drule_all compile_expr_code_result_origin >> simp[]
QED

(* Conditional separation: the body precondition permits a compiler table
   override even when the successful source name denotes storage. This
   does not assert existence of a full frozen-theorem counterexample. *)
Theorem body_pre_global_code_storage_separation[local]:
  expr_body_pre cenv cx env (TopLevelName ann (md,name)) es /\
  eval_expr cx (TopLevelName ann (md,name)) es =
    (INL (PlaceR (StoragePlace tr slot tvt)), em) ==>
  !off ty st.
    expr_body_pre
      (cenv with ce_module_vars := FEMPTY |+ ((md,name), ImmutableLoc off))
      cx env (TopLevelName ann (md,name)) es /\
    compile_expr
      (cenv with ce_module_vars := FEMPTY |+ ((md,name), ImmutableLoc off))
      ty (TopLevelName ann (md,name)) st =
      (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode),st) /\
    PlaceR (StoragePlace tr slot tvt) <> PlaceR (ImmutablePlace md name [])
Proof
  rpt strip_tac >> simp[expr_body_pre_global_module_vars_frame] >>
  simp[compile_immutable_root_shape, finite_mapTheory.FLOOKUP_UPDATE] >> gvs[]
QED

(* C1.4.14 origin check: the proposed expr_body_pre-only implication has
   NOT been proved. The missing implication is
     expr_body_pre cenv cx env (TopLevelName ann (md,name)) es /\
     FLOOKUP cenv.ce_module_vars (md,name) = SOME (ImmutableLoc off)
       ==> ?ts. get_module_code cx md = SOME ts /\
                find_var_decl_by_name name ts = NONE.
   expr_sim_inv relates local types, flags, struct fields and hashmap
   dispatch; it has no ce_module_vars/source-declaration correspondence.
   The two checked precondition frame lemmas show that this table and
   ce_module can be changed freely for TopLevelName. The checked conditional
   separation shows that whenever the source successfully denotes storage,
   the same precondition permits replacing the compiler entry by ImmutableLoc.
   It does not assert that a complete state satisfying that antecedent was
   constructed, nor that the frozen task's operand simulation premise holds.
   eval_global_no_decl_immutable checks the source constructor boundary once
   actual module-code and no-storage-declaration facts have been established.
   md = cenv.ce_module is likewise NOT derived (ce_module is unconstrained).
   A later provenance argument must use more than expr_body_pre; in
   particular the frozen operand simulation premise has not been used here.
*)

(* A zero-code replay reconstructs the representation relationally, not at
   the original target state. Source replay is an explicit premise. *)
Theorem expr_vv_case_zero_code_replay:
  expr_vv_case nocalls ctx func cenv cx obj /\
  expr_body_pre cenv cx env obj t /\
  (nocalls ==> int_calls_expr obj = []) /\
  compile_expr cenv ty obj sc = (vv,sc) /\
  eval_expr cx obj t = (INL tv,t) /\
  expr_vv_res_ok (INL tv) /\
  fn_has_code sc sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc ==>
  frag_exec ctx sc sc
    (\s. s = q /\ stmt_state_rel ctx func cenv cx t s)
    (vv_post ctx func cenv cx obj t sc sc q t tv vv)
    (expr_exit (INL tv))
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_vv_case _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_case_def]) >>
  disch_then (qspecl_then [`env`,`ty`,`t`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sc`,`sc`,`vv`,`INL tv`,`t`,`q`] mp_tac) >>
  simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem expr_vv_case_zero_code_replay_operand:
  expr_vv_case nocalls ctx func cenv cx obj /\
  expr_body_pre cenv cx env obj t /\
  (nocalls ==> int_calls_expr obj = []) /\
  compile_expr cenv ty obj sc = (vv,sc) /\
  eval_expr cx obj t = (INL tv,t) /\ expr_vv_res_ok (INL tv) /\
  fn_has_code sc sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\
  (!x. op = Var x ==> not_fresh_at sc x) /\
  (!l. op <> Label l) /\ eval_operand op q = SOME iw ==>
  frag_exec ctx sc sc
    (\s. s = q /\ stmt_state_rel ctx func cenv cx t s)
    (\s. vv_post ctx func cenv cx obj t sc sc q t tv vv s /\
         eval_operand op s = SOME iw)
    (expr_exit (INL tv))
Proof
  strip_tac >> drule_all expr_vv_case_zero_code_replay >>
  disch_then (qspec_then `q` assume_tac) >>
  irule fragExecTheory.frag_exec_conseq >> first_assum (irule_at Any) >>
  simp[] >> rpt strip_tac >>
  Cases_on `op` >> gvs[venomStateTheory.eval_operand_def, vv_post_def] >>
  first_x_assum irule >> metis_tac[]
QED

(* Root specialization and a residual-fragment composition test. The
   continuation can be compile_array_subscript_ok/oob once its premises
   have been obtained; no target-state equality is used. *)
Theorem immutable_root_replay_then[local]:
  expr_vv_case nocalls ctx func cenv cx (TopLevelName ann (md,name)) /\
  expr_body_pre cenv cx env (TopLevelName ann (md,name)) t /\
  FLOOKUP cenv.ce_module_vars (md,name) = SOME (ImmutableLoc off) /\
  eval_expr cx (TopLevelName ann (md,name)) t = (INL tv,t) /\
  expr_vv_res_ok (INL tv) /\
  fn_has_code sc sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\
  (!x. op = Var x ==> not_fresh_at sc x) /\
  (!l. op <> Label l) /\ eval_operand op q = SOME iw /\
  cs_extends sc sd /\
  (!s. vv_post ctx func cenv cx (TopLevelName ann (md,name)) t sc sc q t tv
          (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) s /\
       eval_operand op s = SOME iw ==>
       frag_exec ctx sc sd (\r. r = s) Q (expr_exit (INL tv))) ==>
  frag_exec ctx sc sd
    (\s. s = q /\ stmt_state_rel ctx func cenv cx t s)
    Q (expr_exit (INL tv))
Proof
  strip_tac >>
  `compile_expr cenv (expr_type (TopLevelName ann (md,name)))
     (TopLevelName ann (md,name)) sc =
     (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode),sc)` by
    (irule compile_immutable_root_shape >> simp[]) >>
  `nocalls ==> int_calls_expr (TopLevelName ann (md,name)) = []` by
    simp[vyperTypeCallGraphTheory.int_calls_expr_def] >>
  drule_all expr_vv_case_zero_code_replay_operand >>
  disch_then (mp_then Any irule fragExecTheory.frag_exec_then) >>
  simp[compileEnvTheory.cs_extends_refl]
QED

(* C1.4.15 bounded replay result:
   - expr_vv_case_zero_code_replay applies the frozen universal operand
     premise at any new source endpoint satisfying its body precondition.
   - The saved-operand variant preserves a non-label operand already below
     sc's freshness frontier. immutable_root_replay_then checks zero-code
     root specialization and relational composition with a residual fragment.
   - Source replay eval_expr cx obj t = (INL tv,t), expr_body_pre at t,
     expr_vv_res_ok, fn_has_code sc sc func, local_ptrs_reserved, and saved
     operand freshness remain explicit hypotheses. In particular this does
     not derive replay of a captured result from LocCode. A root with source
     storage may replay its place even though the compiler says code; no
     ImmutablePlace provenance is needed by these conditional boundaries.
   - Proper Subscript/Attribute code paths are not zero-code in general.
     Neither same-result source replay nor their code erasure is proved.
     The continuation probe tests the frag_exec interface only: it does not
     discharge array_len_ok or the other array-operation premises.
   No endpoint equality or theorem falsehood is asserted here.
*)

(* Supported immutable writes have only scalar proper descendants. *)
Theorem supported_scalar_evaluate_type_base:
  !ty tenv tv.
    supported_scalar_type ty /\ evaluate_type tenv ty = SOME tv ==>
    ?bt. tv = BaseTV bt
Proof
  Cases_on `ty` >> simp[supportedTypesTheory.supported_scalar_type_def,
    supportedTypesTheory.supported_word_type_def,
    supportedTypesTheory.supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem subscripts_type_base_not_array:
  !path bt et bd. subscripts_type (BaseTV bt) path <> SOME (ArrayTV et bd)
Proof
  Cases_on `path` >> simp[subscripts_type_def] >> rpt gen_tac >>
  rename1 `subscript_type (BaseTV bt) sb` >>
  Cases_on `sb` >> simp[subscript_type_def] >>
  rename1 `ValueSubscript v` >> Cases_on `v` >> simp[subscript_type_def]
QED

Theorem supported_scalars_evaluate_types_base:
  !ts tenv tvs.
    EVERY supported_scalar_type ts /\ evaluate_types tenv ts [] = SOME tvs ==>
    EVERY (\tv. ?bt. tv = BaseTV bt) tvs
Proof
  simp[vyperValueTheory.evaluate_types_OPT_MMAP] >>
  rpt strip_tac >>
  gvs[vyperMiscTheory.OPT_MMAP_SOME_IFF] >>
  simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >> rpt strip_tac >>
  `IS_SOME (evaluate_type tenv x)` by
    (gvs[listTheory.EVERY_MEM, listTheory.MEM_MAP] >> metis_tac[]) >>
  irule supported_scalar_evaluate_type_base >>
  qexistsl [`tenv`, `x`] >> Cases_on `evaluate_type tenv x` >>
  gvs[listTheory.EVERY_MEM]
QED

Theorem subscripts_type_flat_not_array:
  !tv sb path et bd.
    (!child. subscript_type tv sb = SOME child ==> ?bt. child = BaseTV bt) ==>
    subscripts_type tv (sb::path) <> SOME (ArrayTV et bd)
Proof
  rpt strip_tac >>
  gvs[subscripts_type_def, AllCaseEqs(), subscripts_type_base_not_array]
QED

Theorem supported_value_type_proper_array_path:
  !tops ty tv path et bd.
    supported_value_type tops ty /\
    evaluate_type (type_env tops) ty = SOME tv /\ path <> [] ==>
    subscripts_type tv path <> SOME (ArrayTV et bd)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `path` >> gvs[] >>
  irule subscripts_type_flat_not_array >>
  rename1 `subscript_type tv sb` >> rpt strip_tac >>
  Cases_on `ty` >>
  gvs[supportedTypesTheory.supported_value_type_def,
      supportedTypesTheory.supported_scalar_type_def,
      supportedTypesTheory.supported_word_type_def,
      supportedTypesTheory.supported_string_type_def]
  >>~- ([`evaluate_type _ (BaseT bt) = SOME tv`],
    Cases_on `bt` >> gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
    Cases_on `sb` >> gvs[subscript_type_def] >>
    rename1 `ValueSubscript v` >> Cases_on `v` >> gvs[subscript_type_def])
  >~ [`evaluate_type _ (TupleT ts) = SOME tv`] >-
    (gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     drule_all supported_scalars_evaluate_types_base >> strip_tac >>
     Cases_on `sb` >> gvs[subscript_type_def] >>
     rename1 `ValueSubscript v` >> Cases_on `v` >>
     gvs[subscript_type_def, AllCaseEqs(), listTheory.EVERY_EL])
  >~ [`evaluate_type _ (ArrayT elem bound) = SOME tv`] >-
    (Cases_on `bound` >> gvs[] >>
     `supported_scalar_type elem` by
       simp[supportedTypesTheory.supported_scalar_type_def] >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     drule_all supported_scalar_evaluate_type_base >> strip_tac >> gvs[] >>
     Cases_on `sb` >> gvs[subscript_type_def] >>
     rename1 `ValueSubscript v` >> Cases_on `v` >>
     gvs[subscript_type_def, AllCaseEqs()]) >>
  rename1 `supported_struct_fields tops ns` >>
  Cases_on `supported_struct_fields tops ns` >> gvs[] >>
  rename1 `supported_struct_fields tops ns = SOME fields` >>
  drule retAbiPlanPropsTheory.supported_struct_fields_type_env >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `EVERY supported_scalar_type (MAP SND fields)` by
    (gvs[listTheory.EVERY_MAP, listTheory.EVERY_MEM,
         supportedTypesTheory.supported_scalar_type_def] >> metis_tac[]) >>
  drule_all supported_scalars_evaluate_types_base >> strip_tac >>
  Cases_on `sb`
  >- (rename1 `ValueSubscript v` >> Cases_on `v` >> gvs[subscript_type_def]) >>
  gvs[subscript_type_def] >>
  `LENGTH tvs = LENGTH fields` by
    (gvs[vyperValueTheory.evaluate_types_OPT_MMAP,
         vyperMiscTheory.OPT_MMAP_SOME_IFF]) >>
  drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  gvs[listTheory.MEM_ZIP, listTheory.EVERY_EL] >> metis_tac[]
QED

(* A frame for the captured entry is not a frame for its layout witness. *)
Theorem immutable_selected_entry_frame_obstruction[local]:
  !cenv cx es.
    cenv.ce_module = NONE /\
    cenv.ce_module_vars = FEMPTY |+ ((NONE,"b"),ImmutableLoc 0) ==>
    let av = ArrayV (SArrayV []);
        aty = ArrayTV (BaseTV BoolT) (Fixed 1);
        am = (ArrayTV aty (Fixed 1),ArrayV (SArrayV [(0,av)]));
        s = es with immutables := [(cx.txn.target,[(NONE,
          FEMPTY |+ ("a",am) |+ ("b",(aty,av)))])];
        t = es with immutables := [(cx.txn.target,[(NONE,
          FEMPTY |+ ("a",am) |+
            ("b",(aty,ArrayV (SArrayV [(0,BoolV T)]))))])];
        p = PlaceR (ImmutablePlace NONE "a" [ValueSubscript (IntV 0)])
    in
      FLOOKUP (get_source_immutables NONE
        (THE (ALOOKUP s.immutables cx.txn.target))) "a" =
      FLOOKUP (get_source_immutables NONE
        (THE (ALOOKUP t.immutables cx.txn.target))) "a" /\
      [ValueSubscript (IntV 0)] <> [] /\
      read_result cx p s = (INL av,s) /\
      read_result cx p t = (INL av,t) /\
      immutable_holds cenv cx (ArrayT (BaseT BoolT) (Fixed 1)) p 0w s /\
      ~immutable_holds cenv cx (ArrayT (BaseT BoolT) (Fixed 1)) p 0w t
Proof
  rpt strip_tac >> simp[LET_THM] >>
  simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, get_source_immutables_def,
       bind_def, return_def, lift_option_type_def, lift_option_def,
       lift_sum_def, evaluate_subscripts_def, subscript_type_def,
       finite_mapTheory.FLOOKUP_UPDATE, vyperValueOperationTheory.array_index_def] >>
  simp[return_def] >>
  simp[immutable_holds_def, get_source_immutables_def,
       finite_mapTheory.FLOOKUP_UPDATE, vyperValueTheory.evaluate_type_def,
       valueEncodingTheory.type_memory_size_def] >>
  simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, get_source_immutables_def,
       bind_def, return_def, lift_option_type_def, lift_option_def,
       lift_sum_def, evaluate_subscripts_def, subscript_type_def,
       finite_mapTheory.FLOOKUP_UPDATE, vyperValueOperationTheory.array_index_def,
       vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def] >>
  conj_tac
  >- (qexists `0` >>
      simp[sub_layout_def] >> EVAL_TAC) >>
  simp[sub_layout_def, valueEncodingTheory.type_memory_size_def,
       vyperTypingTheory.value_has_type_def] >>
  rpt strip_tac >> Cases_on `k = 0` >> simp[] >>
  qexistsl [`0`, `REPLICATE 31 (0w:8 word) ++ [1w]`] >>
  simp[valueEncodingTheory.val_in_memory_def,
       vyperValueTheory.default_value_def] >> EVAL_TAC >>
  simp[wordsTheory.word_0_n2w, wordsTheory.w2n_n2w]
QED

(* Runtime endpoint relations do not preserve the type of a layout witness. *)
Theorem immutable_retyped_endpoint_probe[local]:
  !ce cx0 es vs fn ctx0.
    let cenv = ce with <| ce_module := NONE; ce_is_ctor := F;
          ce_vars := FEMPTY;
          ce_module_vars := FEMPTY |+ ((NONE,"b"),ImmutableLoc 0) |>;
        cx = cx0 with sources := [];
        func = fn with fn_blocks := [];
        ctx = ctx0 with ctx_functions := [func];
        av = ArrayV (SArrayV []);
        aty = ArrayTV (BaseTV BoolT) (Fixed 1);
        am = (ArrayTV aty (Fixed 1),ArrayV (SArrayV [(0,av)]));
        s = es with <| scopes := []; pending_deletions := [];
          accounts := vs.vs_accounts; tStorage := vs.vs_transient;
          logs := []; outcomes := SOME vs.vs_outcomes; requests := [];
          immutables := [(cx.txn.target,[(NONE,
            FEMPTY |+ ("a",am) |+ ("b",(aty,av)))])] |>;
        t = s with immutables := [(cx.txn.target,[(NONE,
            FEMPTY |+ ("a",am) |+ ("b",(NoneTV,NoneV)))])];
        ss = vs with <| vs_allocas := FEMPTY; vs_alloca_next := 0;
          vs_logs := []; vs_requests := []; vs_data_section := REPLICATE 32 0w;
          vs_call_ctx := vs.vs_call_ctx with <|
            cc_caller := cx.txn.sender; cc_address := cx.txn.target;
            cc_callvalue := n2w cx.txn.value; cc_calldata := cx.txn.calldata;
            cc_static := F |>;
          vs_tx_ctx := vs.vs_tx_ctx with <|
            tc_origin := cx.txn.origin; tc_gasprice := n2w cx.txn.gas_price;
            tc_chainid := n2w cx.txn.chain_id; tc_blobhashes := cx.txn.blob_hashes |>;
          vs_block_ctx := vs.vs_block_ctx with <|
            bc_coinbase := cx.txn.coinbase; bc_timestamp := n2w cx.txn.time_stamp;
            bc_number := n2w cx.txn.block_number;
            bc_prevrandao := n2w cx.txn.prev_randao;
            bc_gaslimit := n2w cx.txn.gas_limit; bc_basefee := n2w cx.txn.base_fee;
            bc_blobbasefee := n2w cx.txn.blob_base_fee |> |>;
        p = PlaceR (ImmutablePlace NONE "a" [ValueSubscript (IntV 0)])
    in
      stmt_state_rel ctx func cenv cx s ss /\
      stmt_state_rel ctx func cenv cx t ss /\
      ~cenv.ce_is_ctor /\
      read_result cx p s = (INL av,s) /\
      read_result cx p t = (INL av,t) /\
      immutable_holds cenv cx (ArrayT (BaseT BoolT) (Fixed 1)) p 0w s /\
      ~immutable_holds cenv cx (ArrayT (BaseT BoolT) (Fixed 1)) p 0w t
Proof
  rpt gen_tac >> simp[LET_THM] >>
  conj_tac >- suspend "relations" >>
  conj_tac >- suspend "relations" >>
  simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, get_source_immutables_def,
       bind_def, return_def, lift_option_type_def, lift_option_def,
       lift_sum_def, evaluate_subscripts_def, subscript_type_def,
       finite_mapTheory.FLOOKUP_UPDATE, vyperValueOperationTheory.array_index_def] >>
  simp[return_def, immutable_holds_def, get_source_immutables_def,
       finite_mapTheory.FLOOKUP_UPDATE, vyperValueTheory.evaluate_type_def,
       valueEncodingTheory.type_memory_size_def] >>
  simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, get_source_immutables_def,
       bind_def, return_def, lift_option_type_def, lift_option_def,
       lift_sum_def, evaluate_subscripts_def, subscript_type_def,
       finite_mapTheory.FLOOKUP_UPDATE, vyperValueOperationTheory.array_index_def,
       vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def] >>
  conj_tac
  >- (qexists `0` >> simp[sub_layout_def] >> EVAL_TAC) >>
  simp[sub_layout_def, valueEncodingTheory.type_memory_size_def]
QED

Resume immutable_retyped_endpoint_probe[relations]:
  markerLib.RESUME_TAC >> (
  `!a b. ~TC (fn_directly_calls (ctx0 with ctx_functions := [fn with fn_blocks := []])) a b` by
    (simp[Once relationTheory.TC_CASES1, fcgDefsTheory.fn_directly_calls_def,
      venomInstTheory.lookup_function_def, listTheory.FIND_thm,
      venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def]) >>
  simp[stmt_state_rel_def, state_rel_def, immutable_alloca_sep_def,
    local_ptrs_rel_def, lookup_scopes_def, local_region_def,
    venomStateTheory.lookup_var_def, storage_rel_def, transient_rel_def,
    accounts_rel_def, accounts_agree_def, transient_agree_def,
    logs_rel_def, call_ctx_rel_def,
    venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def,
    vfmStateTheory.lookup_account_def,
    storage_agree_def] >>
  simp[storage_vars_rel_def, transient_vars_rel_def,
    vyperContextTheory.get_module_code_def, finite_mapTheory.FLOOKUP_UPDATE,
    venomMemDefsTheory.alloca_inv_def, venomInstTheory.fn_insts_def,
    venomInstTheory.fn_insts_blocks_def] >>
  conj_tac >- suspend "immutable_rel" >>
  simp[alloca_room_def, pending_alloca_size_def, unit_alloca_frame_def,
    venomInstTheory.lookup_function_def, venomInstTheory.fn_insts_def,
    venomInstTheory.fn_insts_blocks_def] >>
  simp[venomMemDefsTheory.allocas_non_overlapping_def,
    venomMemDefsTheory.alloca_next_valid_def, listTheory.FIND_thm])
QED

Resume immutable_retyped_endpoint_probe[immutable_rel]:
  markerLib.RESUME_TAC >>
  simp[immutables_rel_def, get_source_immutables_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC >>
  simp[wordsTheory.word_0_n2w, wordsTheory.w2n_n2w]
QED

Finalise immutable_retyped_endpoint_probe

(* A return observer changes only the function used inside frag_exec, not the
   fixed function indexing the source/target relation. *)
Definition fragment_return_observer_def:
  fragment_return_observer fn sb =
    fn with fn_blocks :=
      <| bb_label := sb.cs_current_bb;
         bb_instructions := sb.cs_current_insts ++
           [mk_inst sb.cs_next_id RET [Lit 0w] []] |> :: fn.fn_blocks
End

Theorem fragment_return_observer_has_code:
  fn_has_code sa sb fn /\
  (!bb. MEM bb (emitted_blocks sa sb) ==>
        bb.bb_label <> sb.cs_current_bb) ==>
  fn_has_code sa sb (fragment_return_observer fn sb)
Proof
  simp[fn_has_code_def, fragment_return_observer_def,
       lookup_block_def, listTheory.FIND_thm, IS_PREFIX_APPEND]
QED

Theorem fragment_return_observer_at_end:
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  run_from 0 ctx (fragment_return_observer fn sb) s =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |> s
Proof
  rpt strip_tac >>
  simp[run_from_def, fragment_return_observer_def, lookup_block_def,
       listTheory.FIND_thm, Once exec_block_def, get_instruction_def,
       listTheory.EL_APPEND_EQN, step_inst_non_invoke, mk_inst_def,
       Once step_inst_base_def, eval_operands_def, eval_operand_def]
QED

Theorem frag_exec_return_observer_witness:
  frag_exec ctx sa sb (\s. s = s0 /\ P s) Q (\r. F) /\
  fn_has_code sa sb fn /\
  (!bb. MEM bb (emitted_blocks sa sb) ==>
        bb.bb_label <> sb.cs_current_bb) /\
  P s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s1. Q s1 /\ s1.vs_data_section = s0.vs_data_section
Proof
  rpt strip_tac >>
  `fn_has_code sa sb (fragment_return_observer fn sb)` by
    (irule fragment_return_observer_has_code >> simp[]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `fragment_return_observer fn sb` mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `Q s1` >>
  `run_from 0 ctx (fragment_return_observer fn sb) s1 =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |> s1` by
    (irule fragment_return_observer_at_end >> simp[]) >>
  qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  drule run_from_intret_data_section >> strip_tac >>
  qexists `s1` >> simp[]
QED

Theorem expr_sim_return_observer_witness:
  expr_sim ctx func cenv cx ty idx es /\
  lower_value compile_expr cenv ty idx sa = (op,sb) /\
  (do result <- eval_expr cx idx; read_result cx result od) es = (INL v,t) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!bb. MEM bb (emitted_blocks sa sb) ==>
        bb.bb_label <> sb.cs_current_bb) /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s1. expr_post ctx func cenv cx idx es sa sb s0 t v op s1 /\
       s1.vs_data_section = s0.vs_data_section
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_def, expr_res_ok_def] >>
  disch_then drule_all >>
  disch_then (qspec_then `s0` mp_tac) >>
  simp[] >> strip_tac >>
  `expr_exit (INL v) = (\r. F)` by simp[FUN_EQ_THM] >>
  gvs[] >> drule_all frag_exec_return_observer_witness >> simp[]
QED

(* A concrete non-well-formed initial label: the IfExp exit is also the
   initial block label.  This tests a containment inference, not simulation. *)
Definition observer_collision_start_def:
  observer_collision_start =
    <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
       cs_current_bb := "@exit_2"; cs_current_insts := [];
       cs_blocks := []; cs_data_sections := [] |>
End

Definition observer_collision_index_def:
  observer_collision_index =
    IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL T))
      (Literal (BaseT (UintT 256)) (IntL 0))
      (Literal (BaseT (UintT 256)) (IntL 1))
End

Theorem observer_collision_compile[local]:
  lower_value compile_expr cenv (BaseT (UintT 256)) observer_collision_index
    observer_collision_start =
  (Var "%0",
    <| cs_next_var := 1; cs_next_label := 3; cs_next_id := 5;
       cs_current_bb := "@exit_2"; cs_current_insts := [];
       cs_blocks :=
         [<| bb_label := "@else_1"; bb_instructions :=
             [mk_inst 3 ASSIGN [Lit 1w] ["%0"];
              mk_inst 4 JMP [Label "@exit_2"] []] |>;
          <| bb_label := "@then_0"; bb_instructions :=
             [mk_inst 1 ASSIGN [Lit 0w] ["%0"];
              mk_inst 2 JMP [Label "@exit_2"] []] |>;
          <| bb_label := "@exit_2"; bb_instructions :=
             [mk_inst 0 JNZ [Lit 1w; Label "@then_0"; Label "@else_1"] []] |>];
       cs_data_sections := [] |>)
Proof
  EVAL_TAC >> simp[]
QED

Theorem observer_collision_containment_probe:
  let (op,sb) = lower_value compile_expr cenv (BaseT (UintT 256))
                 observer_collision_index observer_collision_start in
    fn_has_code observer_collision_start sb (fn with fn_blocks := sb.cs_blocks) /\
    fn_inst_ids_distinct (fn with fn_blocks := sb.cs_blocks) /\
    ?bb. MEM bb (emitted_blocks observer_collision_start sb) /\
         bb.bb_label = sb.cs_current_bb
Proof
  simp[observer_collision_compile] >>
  conj_tac
  >- (simp[fn_has_code_def, emitted_blocks_def, observer_collision_start_def,
           lookup_block_def, listTheory.FIND_thm] >>
      rpt strip_tac >> gvs[]) >>
  conj_tac >- EVAL_TAC >>
  simp[emitted_blocks_def, observer_collision_start_def] >>
  qexists `<| bb_label := "@exit_2"; bb_instructions :=
    [mk_inst 0 JNZ [Lit 1w; Label "@then_0"; Label "@else_1"] []] |>` >>
  simp[]
QED

(* The actual unsigned static-array suffix adds instructions at the colliding
   exit label.  Whole-fragment containment therefore excludes this fixture. *)
Definition observer_collision_array_end_def:
  observer_collision_array_end cenv =
    let (op,sb) = lower_value compile_expr cenv (BaseT (UintT 256))
                   observer_collision_index observer_collision_start in
    SND (compile_array_subscript (Lit 0w) op F 2 32 32 F
           (\p. emit_op MLOAD [p]) sb)
End

Theorem observer_collision_array_end_fields[local]:
  (observer_collision_array_end cenv).cs_blocks =
    (SND (lower_value compile_expr cenv (BaseT (UintT 256))
       observer_collision_index observer_collision_start)).cs_blocks /\
  (observer_collision_array_end cenv).cs_current_bb = "@exit_2" /\
  HD (observer_collision_array_end cenv).cs_current_insts =
    mk_inst 5 LT [Var "%0"; Lit 2w] ["%1"] /\
  (observer_collision_array_end cenv).cs_current_insts <> []
Proof
  EVAL_TAC >> simp[]
QED

Theorem observer_collision_array_containment_impossible:
  ~fn_has_code observer_collision_start (observer_collision_array_end cenv) fn
Proof
  rewrite_tac[fn_has_code_def] >> strip_tac >>
  qpat_x_assum `!bb. _` (qspec_then
    `<| bb_label := "@exit_2"; bb_instructions :=
      [mk_inst 0 JNZ [Lit 1w; Label "@then_0"; Label "@else_1"] []] |>` mp_tac) >>
  simp[emitted_blocks_def, observer_collision_start_def,
       observer_collision_array_end_fields, observer_collision_compile] >>
  strip_tac >> gvs[observer_collision_array_end_fields] >>
  qpat_x_assum `_ ≼ _` mp_tac >>
  simp[listTheory.isPREFIX_CONSR, observer_collision_array_end_fields] >>
  strip_tac >>
  `HD (observer_collision_array_end cenv).cs_current_insts =
   mk_inst 0 JNZ [Lit 1w; Label "@then_0"; Label "@else_1"] []` by simp[] >>
  gvs[observer_collision_array_end_fields, mk_inst_def]
QED

Definition observer_prefilled_start_def:
  observer_prefilled_start cenv = observer_collision_start with
    cs_current_insts := (observer_collision_array_end cenv).cs_current_insts
End

Definition observer_prefilled_index_end_def:
  observer_prefilled_index_end cenv =
    SND (lower_value compile_expr cenv (BaseT (UintT 256))
           observer_collision_index (observer_prefilled_start cenv))
End

Definition observer_prefilled_array_end_def:
  observer_prefilled_array_end cenv =
    SND (compile_array_subscript (Lit 0w) (Var "%0") F 2 32 32 F
      (\p. emit_op MLOAD [p]) (observer_prefilled_index_end cenv))
End

Theorem observer_prefilled_fields[local]:
  FST (lower_value compile_expr cenv (BaseT (UintT 256))
       observer_collision_index (observer_prefilled_start cenv)) = Var "%0" /\
  (observer_prefilled_index_end cenv).cs_current_insts = [] /\
  (observer_prefilled_index_end cenv).cs_current_bb = "@exit_2" /\
  (observer_prefilled_array_end cenv).cs_current_bb = "@exit_2" /\
  (observer_prefilled_array_end cenv).cs_current_insts =
    (observer_collision_array_end cenv).cs_current_insts /\
  (observer_prefilled_array_end cenv).cs_blocks =
    (observer_prefilled_index_end cenv).cs_blocks /\
  (observer_prefilled_index_end cenv).cs_blocks =
    [<| bb_label := "@else_1"; bb_instructions :=
        [mk_inst 3 ASSIGN [Lit 1w] ["%0"];
         mk_inst 4 JMP [Label "@exit_2"] []] |>;
     <| bb_label := "@then_0"; bb_instructions :=
        [mk_inst 1 ASSIGN [Lit 0w] ["%0"];
         mk_inst 2 JMP [Label "@exit_2"] []] |>;
     <| bb_label := "@exit_2"; bb_instructions :=
        (observer_collision_array_end cenv).cs_current_insts ++
        [mk_inst 0 JNZ [Lit 1w; Label "@then_0"; Label "@else_1"] []] |>]
Proof
  EVAL_TAC >> simp[]
QED

Theorem observer_prefilled_containment_probe:
  fn_has_code (observer_prefilled_start cenv)
    (observer_prefilled_array_end cenv)
    (fn with fn_blocks := (observer_prefilled_array_end cenv).cs_blocks) /\
  fn_inst_ids_distinct
    (fn with fn_blocks := (observer_prefilled_array_end cenv).cs_blocks) /\
  ?bb. MEM bb (emitted_blocks (observer_prefilled_start cenv)
                   (observer_prefilled_index_end cenv)) /\
       bb.bb_label = (observer_prefilled_index_end cenv).cs_current_bb
Proof
  conj_tac
  >- (simp[fn_has_code_def, emitted_blocks_def, observer_prefilled_fields,
           observer_prefilled_start_def, observer_collision_start_def,
           lookup_block_def, listTheory.FIND_thm] >>
      rpt strip_tac >> gvs[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  simp[emitted_blocks_def, observer_prefilled_fields,
       observer_prefilled_start_def, observer_collision_start_def] >>
  qexists `<| bb_label := "@exit_2"; bb_instructions :=
    (observer_collision_array_end cenv).cs_current_insts ++
    [mk_inst 0 JNZ [Lit 1w; Label "@then_0"; Label "@else_1"] []] |>` >>
  simp[]
QED

Theorem observer_prefilled_return_observer_not_contained:
  ~fn_has_code (observer_prefilled_start cenv) (observer_prefilled_index_end cenv)
    (fragment_return_observer
      (fn with fn_blocks := (observer_prefilled_array_end cenv).cs_blocks)
      (observer_prefilled_index_end cenv))
Proof
  rewrite_tac[fn_has_code_def] >> strip_tac >>
  qpat_x_assum `!bb. _` (qspec_then
    `<| bb_label := "@exit_2"; bb_instructions :=
       (observer_collision_array_end cenv).cs_current_insts ++
       [mk_inst 0 JNZ [Lit 1w; Label "@then_0"; Label "@else_1"] []] |>` mp_tac) >>
  simp[emitted_blocks_def, observer_prefilled_fields,
       observer_prefilled_start_def, observer_collision_start_def,
       fragment_return_observer_def, lookup_block_def, listTheory.FIND_thm,
       observer_collision_array_end_fields] >>
  strip_tac >>
  `HD ((observer_collision_array_end cenv).cs_current_insts ++
       [mk_inst 0 JNZ [Lit 1w; Label "@then_0"; Label "@else_1"] []]) =
    mk_inst (observer_prefilled_index_end cenv).cs_next_id RET [Lit 0w] []`
    by simp[] >>
  Cases_on `(observer_collision_array_end cenv).cs_current_insts` >>
  gvs[observer_collision_array_end_fields, mk_inst_def]
QED

Definition observer_sanitized_start_def:
  observer_sanitized_start = observer_collision_start with cs_current_bb := "@fresh"
End

Definition observer_sanitized_index_end_def:
  observer_sanitized_index_end cenv =
    SND (lower_value compile_expr cenv (BaseT (UintT 256))
      observer_collision_index observer_sanitized_start)
End

Theorem observer_sanitized_fresh_block[local]:
  MEM <| bb_label := "@fresh"; bb_instructions :=
       [mk_inst 0 JNZ [Lit 1w; Label "@then_0"; Label "@else_1"] []] |>
    (emitted_blocks observer_sanitized_start (observer_sanitized_index_end cenv))
Proof
  EVAL_TAC >> simp[]
QED

Theorem observer_sanitized_fixed_function_missing_label:
  lookup_block "@fresh" (observer_prefilled_array_end cenv).cs_blocks = NONE
Proof
  simp[observer_prefilled_fields, lookup_block_def, listTheory.FIND_thm]
QED

Theorem observer_sanitized_fixed_function_not_contained:
  ~fn_has_code observer_sanitized_start (observer_sanitized_index_end cenv)
    (fn with fn_blocks := (observer_prefilled_array_end cenv).cs_blocks)
Proof
  rewrite_tac[fn_has_code_def] >> strip_tac >>
  qpat_x_assum `!bb. _` (qspec_then
    `<| bb_label := "@fresh"; bb_instructions :=
       [mk_inst 0 JNZ [Lit 1w; Label "@then_0"; Label "@else_1"] []] |>` mp_tac) >>
  simp[observer_sanitized_fresh_block,
       observer_sanitized_fixed_function_missing_label]
QED

(* A call in the proposed nested immutable mutation candidate requires a
   supported main module. Its immutable declaration already violates that
   requirement, independently of the choice of Boolean representation values
   or of any fixed-function operand simulation contract. *)
Theorem expr_body_pre_called_nested_immutable_rejected:
  expr_body_pre cenv cx env e es /\
  MEM (NONE,callee) (int_calls_expr e) /\
  get_module_code cx NONE = SOME tops /\
  MEM (VariableDecl Private Immutable name
    (ArrayT (ArrayT et ib) bd) NONE) tops ==> F
Proof
  strip_tac >>
  fs[expr_body_pre_def, listTheory.EVERY_MEM] >>
  qpat_x_assum `!c. MEM c _ ==> _` drule >> simp[] >>
  strip_tac >> gvs[] >>
  drule_all supportedProgramTheory.supported_program_declaration >>
  simp[supportedDeclsTheory.supported_declaration_header_def,
       supportedProgramTheory.supported_declaration_body_def] >>
  strip_tac >> drule supported_immutable_array_element_not_array >> simp[]
QED

(* Completeness, not merely the soundness clauses for global lookup, ties a
   declared immutable to its semantic type. This rules out changing a flat
   declaration's runtime type to a nested array in a consistent environment. *)
Theorem env_consistent_declared_immutable_type:
  env_consistent env cx es /\
  get_module_code cx src = SOME tops /\
  MEM (VariableDecl vis Immutable name ty init) tops /\
  FLOOKUP (get_source_immutables src
    (case ALOOKUP es.immutables cx.txn.target of
       SOME imms => imms | NONE => [])) name = SOME (tv,v) ==>
  evaluate_type (get_tenv cx) ty = SOME tv
Proof
  strip_tac >>
  fs[vyperTypeInvariantsTheory.env_consistent_def,
     vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `FLOOKUP env.bare_globals (src,name) = SOME ty` by
    (fs[vyperTypeInvariantsTheory.bare_globals_complete_def] >>
     qpat_x_assum `!src ts vis mut id ty init. _` drule >>
     disch_then drule >> simp[]) >>
  fs[vyperTypeInvariantsTheory.env_immutables_consistent_def] >>
  first_x_assum drule_all >> simp[]
QED

(* sub_layout is an encoding implication, not a typed structural path.
   An empty fixed array observes no bytes, even strictly inside a flat root. *)
Theorem sub_layout_empty_fixed_array:
  k <= type_memory_size itv ==>
  sub_layout itv iv k (ArrayTV et (Fixed 0)) (ArrayV (SArrayV []))
Proof
  simp[sub_layout_def, valueEncodingTheory.type_memory_size_def,
       valueEncodingTheory.val_in_memory_def]
QED

(* An empty fragment can be observed without changing the function indexing
   the simulation relation. The observer immediately returns its whole state. *)
Theorem frag_exec_empty_post:
  frag_exec ctx sc sc (\s. s = s0 /\ P s) Q (\r. F) /\
  fn_has_code sc sc fn /\ P s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sc.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  Q s0
Proof
  rpt strip_tac >>
  `fn_has_code sc sc (fragment_return_observer fn sc)` by
    (irule fragment_return_observer_has_code >>
     simp[emitted_blocks_def]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `fragment_return_observer fn sc` mp_tac) >>
  simp[] >> strip_tac >>
  imp_res_tac fragment_return_observer_at_end >>
  qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `run_from _ _ _ s0 = _` mp_tac >>
  simp[run_from_def, fragment_return_observer_def, lookup_block_def,
       listTheory.FIND_thm, Once exec_block_def, get_instruction_def,
       listTheory.EL_APPEND_EQN, step_inst_non_invoke, mk_inst_def,
       Once step_inst_base_def, eval_operands_def, eval_operand_def] >>
  strip_tac >> gvs[]
QED

Theorem expr_vv_case_empty_code_necessary:
  expr_vv_case F ctx func cenv cx e /\
  expr_body_pre cenv cx env e es /\
  compile_expr cenv ty e sc =
    (LocatedValue (expr_type e) (mk_ptr (Lit w) LocCode), sc) /\
  eval_expr cx e es = (INL tv,es) /\
  expr_vv_res_ok (INL tv) /\
  fn_has_code sc sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ stmt_state_rel ctx func cenv cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sc.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  immutable_holds cenv cx (expr_type e) tv w es
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_vv_case _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_case_def] >>
  disch_then (qspecl_then [`env`, `ty`, `es`] mp_tac) >>
  simp[expr_vv_sim_def] >>
  disch_then drule_all >>
  disch_then (qspec_then `s0` mp_tac) >>
  simp[] >> strip_tac >>
  `expr_exit (INL tv) = (\r. F)` by simp[FUN_EQ_THM] >>
  gvs[] >> drule_all frag_exec_empty_post >>
  simp[vv_post_def, vv_holds_def, eval_operand_def, contextTheory.mk_ptr_def]
QED

Theorem expr_vv_case_global_code_necessary:
  expr_vv_case F ctx func cenv cx (TopLevelName ann (md,name)) /\
  expr_body_pre cenv cx env (TopLevelName ann (md,name)) es /\
  FLOOKUP cenv.ce_module_vars (md,name) = SOME (ImmutableLoc off) /\
  eval_expr cx (TopLevelName ann (md,name)) es =
    (INL (PlaceR (ImmutablePlace md name [])),es) /\
  fn_has_code sc sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ stmt_state_rel ctx func cenv cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sc.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  immutable_holds cenv cx ann (PlaceR (ImmutablePlace md name [])) (n2w off) es
Proof
  rpt strip_tac >>
  irule (expr_vv_case_empty_code_necessary |>
    Q.INST [`e` |-> `TopLevelName ann (md,name)`] |>
    SRULE [vyperASTTheory.expr_type_def]) >>
  simp[expr_vv_res_ok_def] >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qexistsl [`ctx`, `env`, `func`, `md`, `name`, `NoneT`] >>
  simp[Once exprLoweringTheory.compile_expr_def, vyperASTTheory.expr_type_def,
       contextTheory.mk_ptr_def, expr_vv_res_ok_def]
QED

(* Nonempty uint256 singleton layouts distinguish unequal encoded words. *)
Theorem sub_layout_singleton_uint256_separation:
  val_to_w256 (IntV x) <> val_to_w256 (IntV y) ==>
  ~sub_layout (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
       (ArrayV (SArrayV [(0,IntV y)])) k
       (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
       (ArrayV (SArrayV [(0,IntV x)]))
Proof
  rpt strip_tac >>
  gvs[sub_layout_def, valueEncodingTheory.type_memory_size_def] >>
  `k = 0` by decide_tac >> gvs[] >>
  qpat_x_assum `!b mem. _` (qspecl_then
    [`0`, `(mstore 0 (val_to_w256 (IntV y)) ARB).vs_memory`] mp_tac) >>
  simp[valueEncodingPropsTheory.val_in_memory_sarray,
       valueEncodingTheory.val_in_memory_def,
       valueEncodingPropsTheory.mstore_mem_word_at_same,
       alistTheory.ALOOKUP_def]
QED

Theorem immutable_holds_singleton_uint256_separation:
  val_to_w256 (IntV x) <> val_to_w256 (IntV y) /\
  (!nm off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) ==>
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
               NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms)
      nm = SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 1),
                 ArrayV (SArrayV [(0,IntV y)]))) /\
  read_result cx tv es = (INL (ArrayV (SArrayV [(0,IntV x)])),es) ==>
  ~immutable_holds cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 1)) tv w es
Proof
  rpt strip_tac >>
  gvs[immutable_holds_def, vyperValueTheory.evaluate_type_def] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule_all sub_layout_singleton_uint256_separation >>
  disch_then (qspec_then `k` mp_tac) >> simp[]
QED

(* Conditional full-contract separation. Applicability of the source/target
   fixture is explicit: no satisfiability of expr_body_pre or stmt_state_rel
   is asserted here. In particular this is not a counterexample to the task. *)
Theorem expr_vv_case_global_singleton_uint256_separation:
  md <> cenv.ce_module /\
  expr_body_pre cenv cx env
    (TopLevelName (ArrayT (BaseT (UintT 256)) (Fixed 1)) (md,name)) es /\
  FLOOKUP cenv.ce_module_vars (md,name) = SOME (ImmutableLoc 0) /\
  eval_expr cx (TopLevelName (ArrayT (BaseT (UintT 256)) (Fixed 1)) (md,name)) es =
    (INL (PlaceR (ImmutablePlace md name [])),es) /\
  read_result cx (PlaceR (ImmutablePlace md name [])) es =
    (INL (ArrayV (SArrayV [(0,IntV x)])),es) /\
  val_to_w256 (IntV x) <> val_to_w256 (IntV y) /\
  (!nm off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) ==>
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
               NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms)
      nm = SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 1),
                 ArrayV (SArrayV [(0,IntV y)]))) /\
  fn_has_code sc sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ stmt_state_rel ctx func cenv cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sc.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ~expr_vv_case F ctx func cenv cx
    (TopLevelName (ArrayT (BaseT (UintT 256)) (Fixed 1)) (md,name))
Proof
  rpt strip_tac >>
  drule_all expr_vv_case_global_code_necessary >> strip_tac >>
  drule_all immutable_holds_singleton_uint256_separation >> simp[] >>
  qexists `0w` >> simp[]
QED

Theorem compile_expr_code_empty_path_root:
  !e cenv cx ty sc vv sc' es md nm t.
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  ~expr_has_pop e /\ compile_expr cenv ty e sc = (vv,sc') /\
  vv_location vv = SOME LocCode /\
  eval_expr cx e es = (INL (PlaceR (ImmutablePlace md nm [])),t) ==>
  ?ann off. e = TopLevelName ann (md,nm) /\
    FLOOKUP cenv.ce_module_vars (md,nm) = SOME (ImmutableLoc off) /\
    vv = LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode) /\
    sc' = sc /\ t = es
Proof
  Cases >> rpt gen_tac >> strip_tac >>
  all_tac >~ [`compile_expr _ _ (Name _ _) _ = _`] >- suspend "Name" >~
  [`compile_expr _ _ (TopLevelName _ _) _ = _`] >- suspend "Global" >~
  [`compile_expr _ _ (FlagMember _ _ _) _ = _`] >- suspend "Flag" >~
  [`compile_expr _ _ (IfExp _ _ _ _) _ = _`] >- suspend "If" >~
  [`compile_expr _ _ (Literal _ _) _ = _`] >- suspend "Literal" >~
  [`compile_expr _ _ (StructLit _ _ _) _ = _`] >- suspend "Struct" >~
  [`compile_expr _ _ (Subscript _ _ _) _ = _`] >- suspend "Subscript" >~
  [`compile_expr _ _ (Attribute _ _ _) _ = _`] >- suspend "Attribute" >~
  [`compile_expr _ _ (Builtin _ _ _) _ = _`] >- suspend "Builtin" >~
  [`compile_expr _ _ (TypeBuiltin _ _ _ _) _ = _`] >- suspend "TypeBuiltin" >~
  [`compile_expr _ _ (Pop _ _) _ = _`] >- suspend "Pop" >>
  suspend "Call"
QED

Resume compile_expr_code_empty_path_root[Name]:
  rename1 `Name ann name` >>
  Cases_on `FLOOKUP cenv.ce_vars name` >>
  gvs[Once exprLoweringTheory.compile_expr_def,
       exprLoweringTheory.compile_name_vv_def, comp_return_def,
       comp_bind_def, comp_ignore_bind_def,
       contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[contextTheory.vv_location_def] >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME vl` >> Cases_on `vl` >>
  gvs[comp_return_def, comp_bind_def,
       contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[contextTheory.vv_location_def]
QED

Resume compile_expr_code_empty_path_root[Global]:
  rename1 `TopLevelName ann nsid` >> PairCases_on `nsid` >>
  Cases_on `FLOOKUP cenv.ce_module_vars (nsid0,nsid1)` >>
  gvs[Once exprLoweringTheory.compile_expr_def,
       contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[contextTheory.vv_location_def] >>
  rename1 `FLOOKUP cenv.ce_module_vars _ = SOME vl` >> Cases_on `vl` >>
  gvs[contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[contextTheory.vv_location_def] >>
  drule_all related_global_code_result_origin >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def]
QED

Resume compile_expr_code_empty_path_root[Flag]:
  gvs[Once exprLoweringTheory.compile_expr_def, contextTheory.vv_location_def]
QED
Resume compile_expr_code_empty_path_root[If]:
  gvs[] >> metis_tac[exprSimIfExpTheory.compile_expr_ifexp_not_code, pairTheory.FST]
QED
Resume compile_expr_code_empty_path_root[Literal]:
  drule eval_expr_literal_value >> simp[]
QED
Resume compile_expr_code_empty_path_root[Struct]:
  rename1 `StructLit ann nsid fields` >> PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()]
QED
Resume compile_expr_code_empty_path_root[Subscript]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  drule select_result_immutable_origin >> simp[]
QED
Resume compile_expr_code_empty_path_root[Attribute]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  drule select_result_immutable_origin >> simp[]
QED
Resume compile_expr_code_empty_path_root[Builtin]:
  drule eval_expr_builtin_value >> simp[]
QED
Resume compile_expr_code_empty_path_root[TypeBuiltin]:
  gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
QED
Resume compile_expr_code_empty_path_root[Pop]:
  gvs[expr_has_pop_def, supported_expr_exists_def, expr_pop_root_def]
QED
Resume compile_expr_code_empty_path_root[Call]:
  rename1 `eval_expr cx (Call ann target args kws) st = _` >>
  Cases_on `target` >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()]
  >~ [`eval_expr _ (Call _ (IntCall _) _ _) _ = _`]
  >- (rename1 `Call ann (IntCall nsid) args kws` >>
      PairCases_on `nsid` >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
          AllCaseEqs()])
  >~ [`eval_ext_call _ _ _ _ _ _ _ = _`]
  >- (drule eval_ext_call_value >> simp[])
  >~ [`eval_send _ _ _ _ = _`]
  >- (rename1 `eval_send cx has_gas vs mid = _` >>
      Cases_on `vs` >- gvs[eval_send_def, raise_def] >>
      rename1 `eval_send cx has_gas (to_v::rest) mid = _` >>
      Cases_on `rest` >>
      gvs[eval_send_def, bind_def, ignore_bind_def, return_def, raise_def,
          vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
      pairarg_tac >> gvs[bind_def, ignore_bind_def, return_def, AllCaseEqs()])
  >~ [`eval_raw_call _ _ _ _ _ _ _ = _`]
  >- (drule eval_raw_call_value >> simp[])
  >~ [`eval_raw_call _ _ _ _ _ _ _ = _`]
  >- (drule eval_raw_call_value >> simp[]) >>
  qmatch_asmsub_rename_tac `eval_create cx kind _ _ _ _ _` >>
  Cases_on `kind` >> gvs[bind_def, AllCaseEqs()] >>
  drule eval_create_value >> simp[]
QED
Finalise compile_expr_code_empty_path_root

(* Rebuild a current-module root at a later state from its own declaration,
   not from an unrelated existential immutable_holds witness. No frame for
   the later lookup or value is asserted by this theorem. *)
Theorem compile_expr_code_empty_path_root_holds:
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  ~expr_has_pop e /\ compile_expr cenv ty e sc = (vv,sc') /\
  vv_location vv = SOME LocCode /\
  eval_expr cx e es =
    (INL (PlaceR (ImmutablePlace cenv.ce_module nm [])),t) /\
  FLOOKUP (case ALOOKUP later.immutables cx.txn.target of
             NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms)
    nm = SOME (tvt,v) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
  value_has_type tvt v /\
  (!off. FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) ==>
         off + type_memory_size tvt < dimword (:256)) ==>
  vv_holds cenv cx (expr_type e)
    (PlaceR (ImmutablePlace cenv.ce_module nm [])) vv later s
Proof
  rpt strip_tac >> drule_all compile_expr_code_empty_path_root >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def, vv_holds_def,
      contextTheory.mk_ptr_def, eval_operand_def] >>
  irule immutable_holds_root >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem flat_runtime_type_array_path:
  ((?b. rt = BaseTV b) \/
   (?b cap. rt = ArrayTV (BaseTV b) cap) \/
   (?ts. rt = TupleTV ts /\ EVERY (\t. ?b. t = BaseTV b) ts) \/
   (?fs. rt = StructTV fs /\ EVERY (\kv. ?b. SND kv = BaseTV b) fs)) /\
  subscripts_type rt path = SOME (ArrayTV et bd) ==>
  path = []
Proof
  rpt gen_tac >> strip_tac >> Cases_on `path` >> simp[] >>
  rename1 `subscripts_type rt (sb::rest)` >>
  `!child. subscript_type rt sb = SOME child ==> ?b. child = BaseTV b` by
    (rpt strip_tac >> gvs[] >>
     Cases_on `sb` >> gvs[subscript_type_def]
     >~ [`subscript_type _ (ValueSubscript v) = _`]
     >- (Cases_on `v` >> gvs[subscript_type_def, AllCaseEqs(), listTheory.EVERY_EL]) >>
     drule alistTheory.ALOOKUP_MEM >> strip_tac >>
     gvs[listTheory.EVERY_MEM] >>
     first_x_assum drule >> simp[]) >>
  drule_all subscripts_type_flat_not_array >> simp[] >>
  qexistsl [`rest`, `et`, `bd`] >> gvs[]
QED

Theorem flat_immutable_runtime_array_path:
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
             NONE => FEMPTY | SOME imms => get_source_immutables md imms)
    nm = SOME (rt,v) /\
  ((?b. rt = BaseTV b) \/
   (?b cap. rt = ArrayTV (BaseTV b) cap) \/
   (?ts. rt = TupleTV ts /\ EVERY (\t. ?b. t = BaseTV b) ts) \/
   (?fs. rt = StructTV fs /\ EVERY (\kv. ?b. SND kv = BaseTV b) fs)) /\
  runtime_place_typed cx es (ImmutablePlace md nm path) (ArrayTV et bd) ==>
  path = []
Proof
  rpt gen_tac >> disch_tac >>
  `subscripts_type rt path = SOME (ArrayTV et bd)` by
    (Cases_on `ALOOKUP es.immutables cx.txn.target` >>
     gvs[vyperTypeInvariantsTheory.runtime_place_typed_def,
         place_type_value_def, get_immutables_def, get_address_immutables_def,
         bind_def, return_def, raise_def, lift_option_type_def,
         lift_option_def, vyperMiscTheory.option_CASE_rator] >>
     gvs[AllCaseEqs(), return_def, raise_def]) >>
  irule flat_runtime_type_array_path >> goal_assum (drule_at Any) >>
  gvs[]
QED
