Theory vyperEvalExprPreservesScopesDom
Ancestors
  list pair sum vyperMisc vyperContext vyperState vyperCreate vyperCreateFrame vyperInterpreter vyperLookup
  vyperScopePreservation vyperStatePreservation vyperPlaceFrames vyperCallFrame vyperCallOutcomeFrame
  vyperCallOutcome[ignore_grammar]

Theorem Send_outcome_preserves_locals:
  (do
    (rq,outcome) <- take_call_outcome target [] (SOME amount);
    check outcome.co_success "send failed";
    adopt_call_outcome rq outcome;
    return (Value NoneV)
  od) st = (res,st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables
Proof
  strip_tac >>
  drule_all (Send_outcome_transport |> Q.INST
    [`R` |-> `\s t. t.scopes = s.scopes /\ t.immutables = s.immutables`]
    |> SRULE []) >> simp[]
QED

(* Operational evidence and typing validity are deliberately independent. *)
Definition entry_pop_step_def:
  entry_pop_step entry popPath entry' <=>
  ?arr p shortened current' history.
    read_memory_path entry popPath = INL arr /\
    popped_value arr = INL p /\ pop_element arr = INL shortened /\
    ((?live. evaluate_subscripts entry.type entry.value popPath = INL live /\
         assign_subscripts entry.type entry.value popPath (Replace shortened) =
           INL current' /\ history = entry.popped) \/
     (?err. evaluate_subscripts entry.type entry.value popPath = INR err /\
         current' = entry.value /\
         replace_popped entry.type popPath shortened entry.popped = SOME history)) /\
    entry' = entry with <|value := current';
      popped := record_pop popPath arr p history|>
End

Theorem entry_pop_step_metadata:
  entry_pop_step entry path entry' ==>
  entry'.type = entry.type /\ entry'.assignable = entry.assignable
Proof
  simp[entry_pop_step_def] >> rpt strip_tac >> gvs[]
QED

Definition scope_pop_step_def:
  scope_pop_step sc (id,(source,path)) sc' <=>
    ?pre frame rest next.
      find_containing_scope id sc = SOME (pre,frame,source,rest) /\
      entry_pop_step source path next /\
      sc' = pre ++ ((frame |+ (id,next)) :: rest)
End

Definition scope_pop_trace_def:
  (scope_pop_trace sc [] final <=> final = sc) /\
  (scope_pop_trace sc (ev::events) final <=>
    ?middle. scope_pop_step sc ev middle /\
      scope_pop_trace middle events final)
End

Theorem scope_pop_trace_append:
  !xs sc ys final.
    scope_pop_trace sc (xs ++ ys) final <=>
    ?middle. scope_pop_trace sc xs middle /\ scope_pop_trace middle ys final
Proof
  Induct >> simp[scope_pop_trace_def] >> metis_tac[]
QED

Theorem pop_memory_scope_trace_events:
  pop_place cx (MemoryPlace id path) st = (res,st') ==>
  ?events. scope_pop_trace st.scopes events st'.scopes /\
    (events = [] \/
     ?pre frame source rest.
       find_containing_scope id st.scopes = SOME (pre,frame,source,rest) /\
       events = [(id,(source,path))] /\
       ?arr. read_memory_path source path = INL arr)
Proof
  Cases_on `st'.scopes = st.scopes`
  >- (strip_tac >> qexists_tac `[]` >> simp[scope_pop_trace_def]) >>
  simp[pop_place_def, bind_def, get_scopes_def, lift_option_type_def] >>
  Cases_on `find_containing_scope id st.scopes` >>
  simp[return_def, raise_def] >- (strip_tac >> gvs[] >>
    simp[scope_pop_trace_def]) >>
  PairCases_on `x` >>
  simp[type_check_def, assert_def, check_def, bind_def, ignore_bind_def,
       lift_sum_def, lift_option_type_def, return_def, raise_def,
       set_scopes_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[vyperMiscTheory.sum_CASE_rator, vyperMiscTheory.option_CASE_rator,
      AllCaseEqs(), return_def, raise_def, bind_def, set_scopes_def] >>
  qexists_tac `[(id,(x2,path))]` >>
  simp[scope_pop_trace_def, scope_pop_step_def, entry_pop_step_def] >>
  metis_tac[]
QED

Theorem pop_memory_scope_trace:
  pop_place cx (MemoryPlace id path) st = (res,st') ==>
  ?events. scope_pop_trace st.scopes events st'.scopes
Proof
  metis_tac[pop_memory_scope_trace_events]
QED

Definition scope_pop_effect_def:
  scope_pop_effect f <=>
    !st res st'. f st = (res,st') ==>
      ?events. scope_pop_trace st.scopes events st'.scopes
End

Theorem scope_pop_effect_identity:
  (!st res st'. f st = (res,st') ==> st'.scopes = st.scopes) ==>
  scope_pop_effect f
Proof
  simp[scope_pop_effect_def] >> rpt strip_tac >>
  qexists_tac `[]` >> simp[scope_pop_trace_def] >> metis_tac[]
QED

Theorem scope_pop_effect_bind:
  scope_pop_effect f /\ (!v. scope_pop_effect (g v)) ==>
  scope_pop_effect (bind f g)
Proof
  simp[scope_pop_effect_def, bind_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  TRY (goal_assum (drule_at Any) >> NO_TAC) >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `events' ++ events` >>
  irule (iffRL scope_pop_trace_append) >> metis_tac[]
QED

Theorem pop_nonmemory_scopes:
  (!id path. p <> MemoryPlace id path) /\
  pop_place cx p st = (res,st') ==> st'.scopes = st.scopes
Proof
  Cases_on `p`
  >- metis_tac[vyperScopePreservationTheory.pop_storage_place_scopes_immutables]
  >- simp[] >>
  simp[pop_place_def, bind_def, ignore_bind_def,
       get_immutables_def, get_address_immutables_def,
       get_accounts_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rpt strip_tac >>
  gvs[vyperMiscTheory.sum_CASE_rator, vyperMiscTheory.option_CASE_rator,
      AllCaseEqs(), return_def, raise_def] >>
  metis_tac[set_immutable_scopes]
QED

Theorem pop_place_scope_effect:
  scope_pop_effect (pop_place cx p)
Proof
  Cases_on `p`
  >- (irule scope_pop_effect_identity >> rpt strip_tac >>
      irule pop_nonmemory_scopes >> goal_assum (drule_at Any) >> simp[])
  >- (simp[scope_pop_effect_def] >> metis_tac[pop_memory_scope_trace]) >>
  irule scope_pop_effect_identity >> rpt strip_tac >>
  irule pop_nonmemory_scopes >> goal_assum (drule_at Any) >> simp[]
QED

Theorem scope_pop_effect_return[simp]:
  scope_pop_effect (return v)
Proof
  irule scope_pop_effect_identity >> simp[return_def]
QED

Theorem scope_pop_effect_raise[simp]:
  scope_pop_effect (raise e)
Proof
  irule scope_pop_effect_identity >> simp[raise_def]
QED

Theorem scope_pop_effect_lift_sum[simp]:
  scope_pop_effect (lift_sum v)
Proof
  irule scope_pop_effect_identity >> Cases_on `v` >>
  simp[lift_sum_def, return_def, raise_def]
QED

Theorem scope_pop_effect_lift_option[simp]:
  scope_pop_effect (lift_option v msg)
Proof
  irule scope_pop_effect_identity >> Cases_on `v` >>
  simp[lift_option_def, return_def, raise_def]
QED

Theorem scope_pop_effect_lift_option_type[simp]:
  scope_pop_effect (lift_option_type v msg)
Proof
  irule scope_pop_effect_identity >> Cases_on `v` >>
  simp[lift_option_type_def, return_def, raise_def]
QED

Theorem scope_pop_effect_cond:
  scope_pop_effect (if b then f else g) <=>
    if b then scope_pop_effect f else scope_pop_effect g
Proof
  Cases_on `b` >> simp[]
QED

Theorem scope_pop_effect_primitives[simp]:
  scope_pop_effect (check b msg) /\
  scope_pop_effect (type_check b msg) /\
  scope_pop_effect (lift_sum_runtime sv) /\
  scope_pop_effect (read_result cx tv) /\
  scope_pop_effect get_scopes /\
  scope_pop_effect get_accounts /\
  scope_pop_effect get_transient_storage /\
  scope_pop_effect (lookup_global cx src id) /\
  scope_pop_effect (read_storage_slot cx transient slot tyv) /\
  scope_pop_effect (transfer_value sender dest amount) /\
  scope_pop_effect (lookup_flag_mem cx (src,id) mid) /\
  scope_pop_effect (append_logs logs) /\
  scope_pop_effect (update_accounts ua) /\
  scope_pop_effect (update_transient ut)
Proof
  rpt conj_tac >> irule scope_pop_effect_identity >>
  rpt strip_tac >>
  FIRST (map (fn th => drule th >> simp[])
    [check_scopes, type_check_scopes, lift_sum_runtime_scopes,
     read_result_state, get_scopes_scopes, get_accounts_scopes,
     get_transient_storage_scopes, lookup_global_scopes,
     read_storage_slot_scopes, transfer_value_scopes,
     lookup_flag_mem_scopes, append_logs_scopes, update_accounts_scopes,
     update_transient_scopes])
QED

Theorem scope_pop_effect_bind_guarded:
  scope_pop_effect f /\
  (!st v middle. f st = (INL v,middle) ==> scope_pop_effect (g v)) ==>
  scope_pop_effect (bind f g)
Proof
  simp[scope_pop_effect_def, bind_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[scope_pop_trace_append]
QED

Theorem eval_name_scope_effect[local]:
  scope_pop_effect (eval_expr cx (Name ty id))
Proof
  rewrite_tac[Once evaluate_def] >>
  irule scope_pop_effect_bind >> simp[] >> gen_tac >>
  rewrite_tac[ignore_bind_def] >> irule scope_pop_effect_bind >> simp[]
QED

Theorem eval_toplevel_scope_effect[local]:
  scope_pop_effect (eval_expr cx (TopLevelName ty (src,id)))
Proof
  simp[Once evaluate_def]
QED

Theorem eval_flag_scope_effect[local]:
  scope_pop_effect (eval_expr cx (FlagMember ty nsid mid))
Proof
  Cases_on `nsid` >> simp[Once evaluate_def]
QED

Theorem eval_literal_scope_effect[local]:
  scope_pop_effect (eval_expr cx (Literal ty lit))
Proof
  simp[Once evaluate_def]
QED

Theorem eval_structlit_scope_effect[local]:
  (!ks. ks = MAP FST kes ==> scope_pop_effect (eval_exprs cx (MAP SND kes))) ==>
  scope_pop_effect (eval_expr cx (StructLit ty (src,id) kes))
Proof
  strip_tac >> first_x_assum (qspec_then `MAP FST kes` mp_tac) >>
  simp[] >> strip_tac >> simp[Once evaluate_def, LET_THM] >>
  irule scope_pop_effect_bind >> simp[]
QED

Theorem scope_pop_effect_switch:
  scope_pop_effect f /\ scope_pop_effect g ==>
  scope_pop_effect (switch_BoolV cx tv f g)
Proof
  strip_tac >> rewrite_tac[switch_BoolV_def] >>
  irule scope_pop_effect_bind >> simp[] >>
  gen_tac >> simp[scope_pop_effect_cond]
QED

Theorem eval_pop_scope_effect[local]:
  scope_pop_effect (eval_target_place cx bt) ==>
  scope_pop_effect (eval_expr cx (Pop ty bt))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  irule scope_pop_effect_bind >> simp[pop_place_scope_effect]
QED

Theorem scope_pop_effect_place_primitives[simp]:
  scope_pop_effect (lookup_global cx src id) /\
  scope_pop_effect (get_place pv) /\
  scope_pop_effect (extend_place cx pv sb) /\
  scope_pop_effect (read_place cx p) /\
  scope_pop_effect (place_type_value cx p)
Proof
  rpt conj_tac >> irule scope_pop_effect_identity >> rpt strip_tac >>
  FIRST (map (fn th => drule th >> simp[])
    [lookup_global_state, get_place_state, extend_place_state, read_place_state, place_type_value_state])
QED

Theorem scope_pop_effect_selection[simp]:
  scope_pop_effect (select_result cx ty res sb)
Proof
  Cases_on `res` >> simp[select_result_def] >>
  irule scope_pop_effect_bind >> simp[] >> gen_tac >>
  irule scope_pop_effect_bind >> simp[]
QED

Theorem scope_pop_effect_conditional[simp]:
  scope_pop_effect (conditional_result cx res)
Proof
  Cases_on `res` >> simp[conditional_result_def] >>
  irule scope_pop_effect_bind >> simp[] >> gen_tac >>
  simp[scope_pop_effect_cond] >> disj2_tac >>
  irule scope_pop_effect_bind >> simp[]
QED

Theorem eval_attribute_scope_effect[local]:
  scope_pop_effect (eval_expr cx e) ==>
  scope_pop_effect (eval_expr cx (Attribute ty e id))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  irule scope_pop_effect_bind >> simp[]
QED

Theorem eval_ifexp_scope_effect[local]:
  (!st tv middle. eval_expr cx e st = (INL tv,middle) ==>
    scope_pop_effect (eval_expr cx e1)) /\
  (!st tv middle. eval_expr cx e st = (INL tv,middle) ==>
    scope_pop_effect (eval_expr cx e2)) /\
  scope_pop_effect (eval_expr cx e) ==>
  scope_pop_effect (eval_expr cx (IfExp ty e e1 e2))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  irule scope_pop_effect_bind_guarded >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule scope_pop_effect_bind >> simp[scope_pop_effect_conditional] >>
  irule scope_pop_effect_switch >>
  conj_tac >> first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem eval_exprs_empty_scope_effect[local]:
  scope_pop_effect (eval_exprs cx [])
Proof
  simp[Once evaluate_def]
QED

Theorem scope_pop_effect_saved_region:
  (!prev st res st'. st.scopes = prev /\ f prev st = (res,st') ==>
    st'.scopes = prev) ==>
  scope_pop_effect (bind get_scopes f)
Proof
  strip_tac >> irule scope_pop_effect_identity >>
  simp[bind_def, get_scopes_def, return_def] >> metis_tac[]
QED

Theorem eval_exprs_cons_scope_effect[local]:
  (!st tv middle st1 v middle1.
    eval_expr cx e st = (INL tv,middle) /\
    read_result cx tv st1 = (INL v,middle1) ==>
    scope_pop_effect (eval_exprs cx es)) /\
  scope_pop_effect (eval_expr cx e) ==>
  scope_pop_effect (eval_exprs cx (e::es))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac
  >- (first_x_assum irule >> metis_tac[]) >> simp[]
QED

Theorem eval_name_place_scope_effect[local]:
  scope_pop_effect (eval_base_place cx (NameTarget id))
Proof
  rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[] >>
  gen_tac >> rewrite_tac[ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_toplevel_place_scope_effect[local]:
  scope_pop_effect (eval_base_place cx (TopLevelNameTarget (src,id)))
Proof
  simp[Once evaluate_def]
QED

Theorem eval_attribute_base_place_scope_effect[local]:
  scope_pop_effect (eval_base_place cx bt) ==>
  scope_pop_effect (eval_base_place cx (AttributeTarget bt id))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_target_place_scope_effect[local]:
  scope_pop_effect (eval_base_place cx bt) ==>
  scope_pop_effect (eval_target_place cx bt)
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_subscript_base_place_scope_effect[local]:
  (!st pv middle. eval_base_place cx bt st = (INL pv,middle) ==>
    scope_pop_effect (eval_expr cx e)) /\
  scope_pop_effect (eval_base_place cx bt) ==>
  scope_pop_effect (eval_base_place cx (SubscriptTarget bt e))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac
  >- (first_x_assum irule >> goal_assum (drule_at Any)) >>
  gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem scope_pop_effect_array_primitives[simp]:
  scope_pop_effect (result_array_length cx tv) /\
  scope_pop_effect next_gas_reading /\
  scope_pop_effect (precompile_call_success bt) /\
  scope_pop_effect (eval_raw_call cx flags target calldata amount gas)
Proof
  rpt conj_tac >> irule scope_pop_effect_identity >> rpt strip_tac >>
  FIRST (map (fn th => drule th >> rw[] >> simp[])
    [result_array_length_state, next_gas_reading_state,
     precompile_call_success_state,
     eval_raw_call_preserves_non_accounts])
QED

Theorem eval_subscript_scope_effect[local]:
  (!st tv middle. eval_expr cx e1 st = (INL tv,middle) ==>
    scope_pop_effect (eval_expr cx e2)) /\
  scope_pop_effect (eval_expr cx e1) ==>
  scope_pop_effect (eval_expr cx (Subscript ty e1 e2))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac
  >- (first_x_assum irule >> goal_assum (drule_at Any)) >>
  gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_builtin_scope_effect[local]:
  (!st x middle.
    type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" st = (INL x,middle) /\
    bt <> Len /\ bt <> Env MsgGas /\ code_slice_source bt es = NONE ==>
    scope_pop_effect (eval_exprs cx es)) /\
  (!st x middle code_ty addr.
    type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" st = (INL x,middle) /\
    bt <> Len /\ bt <> Env MsgGas /\ code_slice_source bt es = SOME (code_ty,addr) ==>
    scope_pop_effect (eval_exprs cx (TL es))) /\
  (!st x middle code_ty addr st1 tail_vs st2.
    type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" st = (INL x,middle) /\
    bt <> Len /\ bt <> Env MsgGas /\ code_slice_source bt es = SOME (code_ty,addr) /\
    eval_exprs cx (TL es) st1 = (INL tail_vs,st2) ==>
    scope_pop_effect (eval_exprs cx [addr])) /\
  (!st x middle.
    type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" st = (INL x,middle) /\
    bt = Len ==> scope_pop_effect (eval_expr cx (HD es))) ==>
  scope_pop_effect (eval_expr cx (Builtin ty bt es))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac
  >- (Cases_on `bt = Len` >> simp[]
      >- (ho_match_mp_tac scope_pop_effect_bind >> conj_tac
          >- (first_x_assum irule >> metis_tac[]) >>
          gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[]) >>
      Cases_on `bt = Env MsgGas` >> simp[] >>
      Cases_on `bt = Bop In \/ bt = Bop NotIn` >> simp[]
      >- (ho_match_mp_tac scope_pop_effect_bind >> conj_tac
          >- (first_x_assum irule >> gvs[] >> metis_tac[]) >>
          gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[] >>
          ho_match_mp_tac scope_pop_effect_bind >> simp[]) >>
      ho_match_mp_tac scope_pop_effect_bind >> conj_tac
      >- (Cases_on `code_slice_source bt es` >> simp[]
          >- (first_x_assum irule >> metis_tac[]) >>
          rename1 `SOME p` >> PairCases_on `p` >> simp[] >>
          ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac
          >- (first_x_assum irule >> metis_tac[]) >>
          rpt gen_tac >> strip_tac >>
          ho_match_mp_tac scope_pop_effect_bind >> conj_tac
          >- (first_x_assum irule >> metis_tac[]) >>
          gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >>
          gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[]) >>
      gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >>
      gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >>
      gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[]) >> simp[]
QED

Theorem eval_typebuiltin_scope_effect[local]:
  (!st x middle.
    type_check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args" st = (INL x,middle)
    ==> scope_pop_effect (eval_exprs cx es)) ==>
  scope_pop_effect (eval_expr cx (TypeBuiltin ty tb typ es))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac
  >- (first_x_assum irule >> goal_assum (drule_at Any)) >>
  gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem scope_pop_effect_log_create[simp]:
  scope_pop_effect (push_log log) /\
  scope_pop_effect (eval_create cx kind has_salt rof tys vs code_size)
Proof
  conj_tac >> irule scope_pop_effect_identity >> rpt strip_tac >>
  FIRST (map (fn th => drule th >> simp[])
    [push_log_scopes, vyperCreateFrameTheory.eval_create_preserves_scopes_immutables])
QED

Theorem scope_pop_effect_check_not_static[simp]:
  scope_pop_effect (check_not_static cx)
Proof
  simp[check_not_static_def]
QED

Theorem eval_raw_call_scope_effect[local]:
  scope_pop_effect (eval_exprs cx es) ==>
  scope_pop_effect (eval_expr cx (Call ty (RawCallTarget flags) es drv))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  rewrite_tac[ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_raw_calldata_scope_effect[local]:
  scope_pop_effect (eval_exprs cx es) ==>
  scope_pop_effect (eval_expr cx (Call ty (RawCallCalldataTarget flags) es drv))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  rewrite_tac[ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_raw_revert_scope_effect[local]:
  scope_pop_effect (eval_exprs cx es) ==>
  scope_pop_effect (eval_expr cx (Call ty RawRevert es drv))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_selfdestruct_scope_effect[local]:
  scope_pop_effect (eval_exprs cx es) ==>
  scope_pop_effect (eval_expr cx (Call ty SelfDestructTarget es drv))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  simp[LET_THM] >> ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem eval_raw_log_scope_effect[local]:
  scope_pop_effect (eval_exprs cx es) ==>
  scope_pop_effect (eval_expr cx (Call ty RawLog es drv))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >> gen_tac >>
  simp[LET_THM] >> ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac scope_pop_effect_bind >> simp[]
QED

Theorem scope_pop_effect_frame:
  state_rel_frame (\st st'. st'.scopes = st.scopes) f ==>
  scope_pop_effect f
Proof
  simp[state_rel_frame_def] >> strip_tac >>
  irule scope_pop_effect_identity >> rpt strip_tac >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[]
QED

Theorem scope_pop_effect_read[simp]:
  scope_pop_effect (\st. return (g st) st)
Proof
  irule scope_pop_effect_identity >> simp[return_def]
QED

Theorem scope_pop_effect_outcome_primitives[simp]:
  scope_pop_effect (vyperCallOutcome$take_call_outcome target calldata value_opt) /\
  scope_pop_effect (vyperCallOutcome$adopt_call_outcome rq co)
Proof
  conj_tac
  >- (irule scope_pop_effect_frame >> irule state_rel_frame_locals_take >> simp[]) >>
  irule scope_pop_effect_identity >>
  simp[vyperCallOutcomeTheory.adopt_call_outcome_equation, return_def] >>
  gen_tac >> IF_CASES_TAC >>
  Cases_on `co.co_success` >> Cases_on `rq.cr_kind = MessageCall` >> simp[]
QED

Theorem scope_pop_effect_call_helpers[simp]:
  scope_pop_effect (eval_send cx has_gas vs) /\
  scope_pop_effect (eval_ext_call cx static skip_check sig opts vs) /\
  scope_pop_effect (check_create_blueprint has_salt vs)
Proof
  rpt conj_tac >> irule scope_pop_effect_identity >> rpt strip_tac >>
  FIRST (map (fn th => drule th >> simp[])
    [eval_send_preserves_non_accounts, eval_ext_call_preserves_non_accounts,
     vyperCreateFrameTheory.check_create_blueprint_result_state])
QED

Theorem eval_send_scope_effect[local]:
  (!st x middle.
    type_check (LENGTH es = if has_gas then 3 else 2) "Send args" st = (INL x,middle) ==>
    scope_pop_effect (eval_exprs cx es)) ==>
  scope_pop_effect (eval_expr cx (Call ty (Send has_gas) es drv))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac
  >- (first_x_assum irule >> goal_assum (drule_at Any)) >> simp[]
QED

(* Consume a guarded recursive IH only at an isolated effect leaf.  Facts are
   normalized once; no traversal or simplification of the quantified guard. *)
fun POP_EFFECT_GUARD_TAC (asl,w) =
  let
    val normalize = SIMP_RULE bool_ss [oneTheory.one, ignore_bind_def]
    val facts = List.concat (map (CONJUNCTS o normalize o ASSUME) asl)
    val atoms = List.filter (not o is_forall o concl) facts
    val eqs = List.filter (fn th => is_eq (concl th) andalso
      is_var (lhs (concl th))) atoms
    val facts = facts @ map (SIMP_RULE bool_ss eqs) atoms
    fun discharge th =
      if is_imp (snd (strip_forall (concl th))) then
        discharge (tryfind (MATCH_MP th) facts)
      else th
    fun close ih goal =
      if can (match_term (snd (strip_imp (snd (strip_forall (concl ih)))))) w then
        ACCEPT_TAC (discharge (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] ih)) goal
      else NO_TAC goal
  in
    FIRST (map close facts) (asl,w)
  end;

val POP_EFFECT_BIND_STEP = FIRST [
  POP_EFFECT_GUARD_TAC,
  (simp[] >> NO_TAC),
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac,
  gen_tac, strip_tac];

Theorem finally_conditional_lock_scopes:
  finally f (do pop_function prev;
    if guard then
      case slot of NONE => return ()
      | SOME s => release_nonreentrant_lock addr s
    else return () od) st = (res,st') ==> st'.scopes = prev
Proof
  `!st res st'. (if guard then
      case slot of NONE => return ()
      | SOME s => release_nonreentrant_lock addr s
    else return ()) st = (res,st') ==> st'.scopes = st.scopes` by
    (Cases_on `guard` >> Cases_on `slot` >> simp[return_def] >>
     metis_tac[release_nonreentrant_lock_scopes]) >>
  metis_tac[finally_pop_function_then_scopes]
QED

Theorem read_results_scope_pop_effect[local,simp]:
  scope_pop_effect (read_results cx results)
Proof
  irule scope_pop_effect_identity >> rpt strip_tac >>
  drule read_results_state >> simp[]
QED

Theorem eval_expr_results_empty_scope_effect[local]:
  scope_pop_effect (eval_expr_results cx [])
Proof
  simp[Once evaluate_def]
QED

Theorem eval_expr_results_scope_effect[local]:
  scope_pop_effect (eval_expr cx e) /\
  (!st pv middle. eval_expr cx e st = (INL pv,middle) ==>
    scope_pop_effect (eval_expr_results cx es)) ==>
  scope_pop_effect (eval_expr_results cx (e::es))
Proof
  strip_tac >> rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind >> conj_tac
  >- (first_x_assum irule >> goal_assum (drule_at Any)) >> simp[]
QED

Theorem eval_mutual_scope_pop_effect_results[local]:
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:value list). T) /\
  (!cx e. scope_pop_effect (eval_expr cx e)) /\
  (!cx es. scope_pop_effect (eval_exprs cx es)) /\
  (!cx bt. scope_pop_effect (eval_base_place cx bt)) /\
  (!cx bt. scope_pop_effect (eval_target_place cx bt)) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T) /\
  (!cx es. scope_pop_effect (eval_expr_results cx es))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >~
  [`scope_pop_effect (eval_expr _ (Call _ (ExtCall _ _ _ _) _ _))`] >-
    suspend "ExtCall" >~
  [`scope_pop_effect (eval_expr _ (Call _ (CreateTarget kind has_salt rof kw_order) _ _))`] >-
    suspend "Create" >~
  [`scope_pop_effect (eval_expr _ (Call _ (IntCall _) _ _))`] >-
    suspend "IntCall" >~
  [`scope_pop_effect (eval_expr _ (Builtin _ _ _))`] >-
    suspend "Builtin" >>
  FIRST ((simp[] >> NO_TAC) :: map (fn th => FIRST
    [MATCH_ACCEPT_TAC (GEN_ALL th),
     match_mp_tac (GEN_ALL th) >> rpt conj_tac >> first_assum ACCEPT_TAC] >> NO_TAC)
    [eval_name_scope_effect, eval_toplevel_scope_effect, eval_flag_scope_effect,
     eval_literal_scope_effect, eval_structlit_scope_effect,
     eval_pop_scope_effect, eval_attribute_scope_effect, eval_ifexp_scope_effect,
     eval_exprs_empty_scope_effect, eval_exprs_cons_scope_effect,
     eval_expr_results_empty_scope_effect, eval_expr_results_scope_effect,
     eval_name_place_scope_effect, eval_toplevel_place_scope_effect,
     eval_attribute_base_place_scope_effect, eval_target_place_scope_effect,
     eval_subscript_base_place_scope_effect, eval_subscript_scope_effect,
     eval_typebuiltin_scope_effect,
     eval_raw_call_scope_effect, eval_raw_calldata_scope_effect,
      eval_raw_revert_scope_effect,
     eval_selfdestruct_scope_effect, eval_raw_log_scope_effect, eval_send_scope_effect])
QED

Resume eval_mutual_scope_pop_effect_results[ExtCall]:
  rewrite_tac[Once evaluate_def] >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  rpt POP_EFFECT_BIND_STEP
QED

Resume eval_mutual_scope_pop_effect_results[Builtin]:
  irule eval_builtin_scope_effect >>
  Cases_on `bt = Bop In \/ bt = Bop NotIn` >> gvs[] >> metis_tac[]
QED

Resume eval_mutual_scope_pop_effect_results[Create]:
  Cases_on `kind` >> Cases_on `has_salt` >> gvs[] >>
  `TAKE (LENGTH es - 2) (DROP 2 es) = DROP 2 es` by
    metis_tac[LENGTH_DROP, TAKE_LENGTH_ID] >>
  pop_assum (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `DROP (LENGTH es - 2) (DROP 2 es) = []` by
    metis_tac[LENGTH_DROP, DROP_LENGTH_NIL] >>
  pop_assum (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  simp_tac (srw_ss()) [Once evaluate_def] >>
  rpt POP_EFFECT_BIND_STEP >>
  simp_tac (srw_ss()) [LET_THM, LENGTH_DROP, GSYM arithmeticTheory.SUB_PLUS] >>
  rpt POP_EFFECT_BIND_STEP
QED

Resume eval_mutual_scope_pop_effect_results[IntCall]:
  rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  ntac 3 (ho_match_mp_tac scope_pop_effect_bind_guarded >>
          conj_tac >- simp[] >> rpt gen_tac >> strip_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac scope_pop_effect_bind_guarded >> conj_tac >- POP_EFFECT_GUARD_TAC >>
  rpt gen_tac >> strip_tac >>
  simp[LET_THM] >>
  ho_match_mp_tac scope_pop_effect_saved_region >>
  map_every qx_gen_tac [`prev`,`st0`,`res`,`st1`] >> strip_tac >>
  rpt (qpat_x_assum `!a. _` kall_tac) >>
  gvs[bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac finally_set_scopes >>
  imp_res_tac read_results_state >>
  imp_res_tac lift_option_type_scopes >>
  imp_res_tac (SRULE[ignore_bind_def] finally_conditional_lock_scopes) >>
  gvs[] >>
  gvs[push_function_def, return_def, AllCaseEqs()] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  gvs[raise_def, return_def] >>
  Cases_on `FST (SND tup)` >> gvs[return_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
  qpat_x_assum `ignore_bind _ _ _ = _` mp_tac >>
  simp[ignore_bind_def, bind_def, check_def, assert_def, return_def,
       raise_def, COND_RATOR, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac acquire_nonreentrant_lock_scopes >> gvs[]
QED

Finalise eval_mutual_scope_pop_effect_results

Theorem eval_mutual_scope_pop_effect:
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:value list). T) /\
  (!cx e. scope_pop_effect (eval_expr cx e)) /\
  (!cx es. scope_pop_effect (eval_exprs cx es)) /\
  (!cx bt. scope_pop_effect (eval_base_place cx bt)) /\
  (!cx bt. scope_pop_effect (eval_target_place cx bt)) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T)
Proof
  metis_tac[eval_mutual_scope_pop_effect_results]
QED

Theorem eval_expr_results_scope_pop_effect:
  scope_pop_effect (eval_expr_results cx es)
Proof
  metis_tac[eval_mutual_scope_pop_effect_results]
QED

(* A pop trace only rewrites existing entries, so every frame keeps its
   domain and every entry its type and assignability. *)
Theorem scope_pop_step_frames[local]:
  scope_pop_step sc ev sc' ==>
  LIST_REL (\f f'. FDOM f' = FDOM f /\
    !id e. FLOOKUP f id = SOME e ==>
      ?e'. FLOOKUP f' id = SOME e' /\
        e'.type = e.type /\ e'.assignable = e.assignable) sc sc'
Proof
  PairCases_on `ev` >> rw[scope_pop_step_def] >>
  drule vyperLookupTheory.find_containing_scope_structure >> strip_tac >>
  gvs[] >> irule LIST_REL_APPEND_suff >> simp[EVERY2_refl] >>
  drule entry_pop_step_metadata >>
  rw[finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[finite_mapTheory.FLOOKUP_DEF, pred_setTheory.ABSORPTION_RWT] >> rw[]
QED

Theorem scope_pop_trace_frames:
  !events sc final. scope_pop_trace sc events final ==>
  LIST_REL (\f f'. FDOM f' = FDOM f /\
    !id e. FLOOKUP f id = SOME e ==>
      ?e'. FLOOKUP f' id = SOME e' /\
        e'.type = e.type /\ e'.assignable = e.assignable) sc final
Proof
  Induct >> rw[scope_pop_trace_def] >- simp[EVERY2_refl] >>
  drule scope_pop_step_frames >> first_x_assum drule >>
  qmatch_goalsub_abbrev_tac `LIST_REL R middle final` >>
  `!x y z. R x y /\ R y z ==> R x z` by
    (simp[Abbr`R`] >> rw[] >> first_x_assum drule >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  metis_tac[EVERY2_trans]
QED

Theorem scope_pop_trace_scopes_dom:
  scope_pop_trace sc events final ==> MAP FDOM sc = MAP FDOM final
Proof
  strip_tac >> drule scope_pop_trace_frames >>
  rw[MAP_EQ_EVERY2, LIST_REL_EL_EQN]
QED

Theorem scope_pop_effect_scopes_dom[local]:
  f st = (res,st') ==> scope_pop_effect f ==>
  MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rw[scope_pop_effect_def] >> first_x_assum drule >> strip_tac >>
  drule scope_pop_trace_scopes_dom >> simp[]
QED

(* ========================================================================
   Main theorems (exported)
   ======================================================================== *)

Theorem eval_expr_preserves_scopes_dom:
  ∀e cx st res st'.
    eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> drule scope_pop_effect_scopes_dom >>
  simp[eval_mutual_scope_pop_effect_results]
QED


Theorem eval_expr_preserves_var_in_scope:
  ∀cx st st' n e res.
    eval_expr cx e st = (res, st') ⇒
    (var_in_scope st n ⇔ var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_expr_preserves_scopes_dom]
QED

Theorem eval_expr_preserves_scopes_len:
  ∀e cx st res st'.
    eval_expr cx e st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_expr_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED

Theorem eval_base_place_preserves_scopes_dom:
  ∀cx bt st res st'. eval_base_place cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> drule scope_pop_effect_scopes_dom >>
  simp[eval_mutual_scope_pop_effect_results, eval_expr_results_scope_pop_effect]
QED

Theorem eval_base_place_preserves_var_in_scope:
  ∀cx st st' n bt res.
    eval_base_place cx bt st = (res, st') ⇒
    (var_in_scope st n ⇔ var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_base_place_preserves_scopes_dom]
QED

Theorem eval_base_place_preserves_scopes_len:
  ∀bt cx st res st'.
    eval_base_place cx bt st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_base_place_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED

Theorem eval_exprs_preserves_scopes_dom:
  ∀es cx st res st'.
    eval_exprs cx es st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> drule scope_pop_effect_scopes_dom >>
  simp[eval_mutual_scope_pop_effect_results, eval_expr_results_scope_pop_effect]
QED

Theorem eval_expr_results_preserves_scopes_dom:
  eval_expr_results cx es st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> drule scope_pop_effect_scopes_dom >>
  simp[eval_mutual_scope_pop_effect_results, eval_expr_results_scope_pop_effect]
QED

Theorem eval_exprs_preserves_var_in_scope:
  ∀cx st st' n es res.
    eval_exprs cx es st = (res, st') ⇒
    (var_in_scope st n ⇔ var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_exprs_preserves_scopes_dom]
QED

Theorem eval_exprs_preserves_scopes_len:
  ∀es cx st res st'.
    eval_exprs cx es st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_exprs_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED

Theorem eval_target_place_preserves_scopes_dom:
  !cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> drule scope_pop_effect_scopes_dom >>
  simp[eval_mutual_scope_pop_effect_results, eval_expr_results_scope_pop_effect]
QED

Theorem eval_target_place_preserves_var_in_scope:
  !cx bt st res st' n. eval_target_place cx bt st = (res,st') ==>
    (var_in_scope st n <=> var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_target_place_preserves_scopes_dom]
QED

Theorem eval_target_place_preserves_scopes_len:
  !cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_target_place_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED
