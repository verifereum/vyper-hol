(* Pointwise immutable-cell frames, including constructor execution. *)
Theory vyperProtectedImmutableFrame
Ancestors
  list pair option finite_map alist vyperState vyperContext
  vyperInterpreter vyperBareGlobalName vyperPlaceFrames
  vyperScopePreservation vyperImmutablesPreservation
  vyperRuntimeWriteSafety vyperMachineFrame
  vyperStoragePlaceProvenance vyperCallOutcomeFrame vyperAST
  vyperTypeSystem vyperMisc vyperEvalFrame vyperStatePreservation
  vyperCreateFrame vyperLookupStorage
Libs evalWalkLib

Theorem set_immutable_other_cell:
  set_immutable cx src id tv v st = (res,st') /\
  (src <> sid \/ id <> nm) ==>
  lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm
Proof
  simp[set_immutable_def, bind_def, get_address_immutables_def,
       lift_option_type_def, set_address_immutables_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> gvs[] >>
  simp[lookup_immutable_def, set_source_immutables_def,
       get_source_immutables_def, ALOOKUP_ADELKEY, FLOOKUP_UPDATE] >>
  Cases_on `src = sid` >> gvs[FLOOKUP_UPDATE]
QED

Theorem write_immutable_place_other_cell:
  write_place cx (ImmutablePlace src id path) v st = (res,st') /\
  (src <> sid \/ id <> nm) ==>
  lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm
Proof
  simp[write_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> gvs[] >>
  metis_tac[set_immutable_other_cell]
QED

Theorem pop_immutable_place_other_cell:
  pop_place cx (ImmutablePlace src id path) st = (res,st') /\
  (src <> sid \/ id <> nm) ==>
  lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm
Proof
  simp[pop_place_def, bind_def, ignore_bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> gvs[] >>
  metis_tac[set_immutable_other_cell]
QED

Theorem write_place_protected_cell:
  write_place cx pl v st = (res,st') /\
  (!src id path. pl = ImmutablePlace src id path ==> ~protected src id) ==>
  !sid nm. protected sid nm ==>
  lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm
Proof
  Cases_on `pl` >> rpt strip_tac
  >- (drule write_storage_place_immutables >>
      simp[lookup_immutable_def])
  >- (drule write_memory_place_immutables >>
      simp[lookup_immutable_def]) >>
  irule write_immutable_place_other_cell >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem pop_place_protected_cell:
  pop_place cx pl st = (res,st') /\
  (!src id path. pl = ImmutablePlace src id path ==> ~protected src id) ==>
  !sid nm. protected sid nm ==>
  lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm
Proof
  Cases_on `pl` >> rpt strip_tac
  >- (drule pop_storage_place_scopes_immutables >>
      simp[lookup_immutable_def])
  >- (rename1 `pop_place cx (MemoryPlace id path) st = _` >>
      mp_tac machine_frame_pop_memory_place >>
      simp[state_rel_frame_def] >>
      disch_then (qspec_then `st` mp_tac) >>
      simp[machine_frame_def, lookup_immutable_def]) >>
  irule pop_immutable_place_other_cell >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem lookup_global_immutable_root:
  lookup_global cx src id st =
    (INL (PlaceR (ImmutablePlace sid nm path)),st') ==>
  sid = src /\ nm = id /\ path = []
Proof
  simp[lookup_global_def, bind_def, ignore_bind_def, lift_option_type_def,
       get_immutables_def, get_address_immutables_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, lift_option_type_def,
           record_storage_event_def, return_def, raise_def]) >>
  rpt strip_tac >> gvs[bind_def, ignore_bind_def, record_storage_event_def,
                       return_def, raise_def]
QED

Theorem extend_place_immutable_root:
  extend_place cx operand sb st =
    (INL (PlaceR (ImmutablePlace sid nm path)),st') ==>
  ?pre. operand = PlaceR (ImmutablePlace sid nm pre) /\ path = pre ++ [sb]
Proof
  Cases_on `operand`
  >- (simp[extend_place_def, raise_def])
  >- (rename1 `PlaceR pl` >> Cases_on `pl`
      >- (simp[extend_place_def, bind_def, return_def, raise_def] >>
          rpt strip_tac >> gvs[AllCaseEqs()] >>
          drule extend_storage_place_subregion >> strip_tac >> gvs[]) >>
      simp[extend_place_def, bind_def, ignore_bind_def, lift_sum_def,
           return_def, raise_def, extend_memory_place_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
      rpt strip_tac >> gvs[]) >>
  Cases_on `sb` >>
  simp[extend_place_def, bind_def, lift_option_type_def,
       record_storage_event_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> gvs[bind_def, ignore_bind_def, record_storage_event_def,
                       return_def, raise_def]
QED

Theorem eval_name_target_memory_root:
  eval_base_place cx (NameTarget id) st = (INL operand,st') ==>
  operand = PlaceR (MemoryPlace id [])
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, check_def, return_def, raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

(* Stack changes select a caller but do not change the immutable address. *)
Theorem lookup_immutable_stk[simp]:
  lookup_immutable (cx with stk := stk) st sid nm =
  lookup_immutable cx st sid nm
Proof
  simp[lookup_immutable_def]
QED

(* A frame is address-local: internal calls may change the stack, never txn. *)
val protected_relation = ``\(s:evaluation_state) (t:evaluation_state).
  !sid nm. protected sid nm ==>
    lookup_immutable cx t sid nm = lookup_immutable cx s sid nm``;
val protected_frame_net =
  let
    val leaves = [machine_frame_primitives, machine_frame_read_result,
      machine_frame_read_results, machine_frame_reads, machine_frame_select_result,
      machine_frame_extend_place, machine_frame_get_place, machine_frame_read_place,
      machine_frame_place_type_value, machine_frame_new_variable,
      machine_frame_next_gas_reading, machine_frame_precompile_call_success,
      machine_frame_handlers, machine_frame_push_function,
      machine_frame_pop_function, machine_frame_unchanged_reads,
      machine_frame_array_iterator_results]
    fun leaf th = (subst [``machine_frame`` |-> protected_relation] (concl th),
      irule state_rel_frame_machine >> conj_tac
      >- simp[machine_frame_def, lookup_immutable_def] >> MATCH_ACCEPT_TAC th)
  in evalWalkLib.walk_net
    (map SPEC_ALL [state_rel_frame_bind_guarded, state_rel_frame_try,
      state_rel_frame_finally, state_rel_frame_finally_unless_halt])
    ((``!s t u. ^protected_relation s t /\ ^protected_relation t u ==>
         ^protected_relation s u``, metis_tac[]) ::
     map leaf (List.concat (map (CONJUNCTS o SPEC_ALL) leaves))) end;
val protected_frame_result = BETA_RULE
  (ISPEC protected_relation (Q.GEN `R` state_rel_frame_result));
val PROTECTED_GUARDS =
  qpat_assum `!sid fn ts mut nr args ds rt body.
    get_module_code cx sid = SOME ts /\ _ ==> _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [EQT_INTRO th]) >> assume_tac th);
val PROTECTED_IH =
  PROTECTED_GUARDS >>
  RULE_ASSUM_TAC (REWRITE_RULE [GSYM protected_frame_result]) >>
  evalWalkLib.IH_TAC {stop = K false, normalise = SIMP_RULE bool_ss
    [oneTheory.one, ignore_bind_def, FST, SND, pair_case_thm, UNCURRY,
     lock_if_nr_def, unlock_if_nr_def, lookup_immutable_stk, get_module_code_stk]};
val PROTECTED_FORWARD_IH =
  RULE_ASSUM_TAC (REWRITE_RULE [GSYM protected_frame_result]) >>
  evalWalkLib.FORWARD_IH_TAC {normalise = SIMP_RULE (srw_ss())
    [oneTheory.one, FST, SND, lock_if_nr_def, is_view_mut_def, ignore_bind_def,
     lookup_immutable_stk, get_module_code_stk, lookup_immutable_def]};
val PROTECTED_STEP = evalWalkLib.STEP
  {net = protected_frame_net, at = RAND_CONV,
   unfolds = [switch_BoolV_def, ignore_bind_def],
   intros = [CONV_TAC (HO_REWR_CONV FORALL_PROD), gen_tac, strip_tac,
     conj_tac, CONV_TAC (RAND_CONV ETA_CONV)],
   fallbacks = [PROTECTED_IH, evalWalkLib.NORMALISE_IH_TAC PROTECTED_IH,
     first_assum (fn th => irule th >> rpt conj_tac >>
       first_assum MATCH_ACCEPT_TAC)]};
val PROTECTED_CASE = evalWalkLib.EVAL_CASE all_tac PROTECTED_STEP;

Theorem protected_writes_frame_mutual:
  (!sid nm. R sid nm ==> ~protected sid nm) ==>
  (!cx s.
    (!sid fn ts mut nr args dflts ret body.
      get_module_code cx sid = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) body) /\
    stmt_writes_ok (runtime_write_root R) s ==>
    !st res st'. eval_stmt cx s st = (res,st') ==>
      !sid nm. protected sid nm ==> lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  (!cx ss.
    (!sid fn ts mut nr args dflts ret body.
      get_module_code cx sid = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) body) /\
    stmts_writes_ok (runtime_write_root R) ss ==>
    !st res st'. eval_stmts cx ss st = (res,st') ==>
      !sid nm. protected sid nm ==> lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  (!cx it.
    (!sid fn ts mut nr args dflts ret body.
      get_module_code cx sid = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) body) /\
    (case it of Array e => expr_writes_ok (runtime_write_root R) e
      | Range x y => expr_writes_ok (runtime_write_root R) x /\ expr_writes_ok (runtime_write_root R) y) ==>
    !st res st'. eval_iterator cx it st = (res,st') ==>
      !sid nm. protected sid nm ==> lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  (!cx tyv nm body vs.
    (!sid fn ts mut nr args dflts ret body.
      get_module_code cx sid = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) body) /\
    stmts_writes_ok (runtime_write_root R) body ==>
    !st res st'. eval_for cx tyv nm body vs st = (res,st') ==>
      !sid nm. protected sid nm ==> lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  (!cx e.
    (!sid fn ts mut nr args dflts ret body.
      get_module_code cx sid = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) body) /\
    expr_writes_ok (runtime_write_root R) e ==>
    !st res st'. eval_expr cx e st = (res,st') ==>
      !sid nm. protected sid nm ==> lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  (!cx es.
    (!sid fn ts mut nr args dflts ret body.
      get_module_code cx sid = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) body) /\
    EVERY (expr_writes_ok (runtime_write_root R)) es ==>
    !st res st'. eval_exprs cx es st = (res,st') ==>
      !sid nm. protected sid nm ==> lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  (!cx t.
    (!sid fn ts mut nr args dflts ret body.
      get_module_code cx sid = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) body) /\
    runtime_write_root R t /\ target_writes_ok (runtime_write_root R) t ==>
    !st res st'. eval_base_place cx t st = (res,st') ==>
      (!sid nm. protected sid nm ==> lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
      (!sid nm path. res = INL (PlaceR (ImmutablePlace sid nm path)) ==> ~protected sid nm)) /\
  (!cx t.
    (!sid fn ts mut nr args dflts ret body.
      get_module_code cx sid = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) body) /\
    runtime_write_root R t /\ target_writes_ok (runtime_write_root R) t ==>
    !st res st'. eval_target_place cx t st = (res,st') ==>
      (!sid nm. protected sid nm ==> lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
      (!sid nm path. res = INL (ImmutablePlace sid nm path) ==> ~protected sid nm)) /\
  (!cx g v.
    (!sid fn ts mut nr args dflts ret body.
      get_module_code cx sid = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) body) /\
    atarget_writes_ok (runtime_write_root R) g ==>
    !st res st'. assign_tuple_targets cx g v st = (res,st') ==>
      !sid nm. protected sid nm ==> lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  (!cx gs vs.
    (!sid fn ts mut nr args dflts ret body.
      get_module_code cx sid = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) body) /\
    EVERY (atarget_writes_ok (runtime_write_root R)) gs ==>
    !st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==>
      !sid nm. protected sid nm ==> lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  (!cx es.
    (!sid fn ts mut nr args dflts ret body.
      get_module_code cx sid = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) body) /\
    EVERY (expr_writes_ok (runtime_write_root R)) es ==>
    !st res st'. eval_expr_results cx es st = (res,st') ==>
      !sid nm. protected sid nm ==> lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm)
Proof
  disch_tac >> ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`eval_base_place cx (TopLevelNameTarget _)`]
  >- (simp[runtime_write_root_def] >> strip_tac >> rpt gen_tac >>
      simp[Once evaluate_def] >> strip_tac >> conj_tac
      >- metis_tac[lookup_global_immutables, lookup_immutable_def] >>
      rpt strip_tac >> gvs[] >> drule lookup_global_immutable_root >>
      rpt strip_tac >> gvs[] >> metis_tac[])
  >~ [`eval_base_place cx (NameTarget _)`]
  >- (simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
           type_check_def, assert_def, check_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >> gvs[])
  >~ [`eval_base_place cx (AttributeTarget _ _)`]
  >- (strip_tac >> simp[runtime_write_root_def, expr_writes_ok_def] >>
      strip_tac >> fs[] >> rpt gen_tac >> simp[Once evaluate_def] >>
      Cases_on `eval_base_place cx t st` >>
      rename1 `eval_base_place cx t st = (answer,mid)` >>
      first_x_assum drule >> disch_then drule >> strip_tac >>
      Cases_on `answer` >> simp[bind_def, raise_def] >> rpt strip_tac >> gvs[]
      >- metis_tac[machine_frame_extend_place, state_rel_frame_result,
                   machine_frame_def, lookup_immutable_def] >>
      metis_tac[extend_place_immutable_root, machine_frame_extend_place,
        state_rel_frame_result, machine_frame_def, lookup_immutable_def])
  >~ [`eval_base_place cx (SubscriptTarget _ _)`]
  >- suspend "subscript_target"
  >> PURE_REWRITE_TAC[GSYM protected_frame_result,
       stmt_writes_ok_def, expr_writes_ok_def, atarget_writes_ok_def,
       runtime_write_root_def, EVERY_DEF] >> rpt strip_tac
  >~ [`eval_stmt cx Pass`]
  >- (simp[protected_frame_result, Once evaluate_def, return_def])
  >~ [`eval_stmt cx Continue`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx Break`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (Return NONE)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (Return (SOME _))`]
  >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (Raise RaiseBare)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (Raise RaiseUnreachable)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (Raise (RaiseReason _))`] >- (fs[] >> PROTECTED_CASE)
  >~ [`eval_stmt cx (Assert _ AssertBare)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (Assert _ AssertUnreachable)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (Assert _ (AssertReason _))`]
  >- (fs[] >> PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmts cx []`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmts cx (_::_)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_exprs cx []`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_exprs cx (_::_)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_expr_results cx []`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_expr_results cx (_::_)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_expr cx (Literal _ _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_expr cx (Name _ _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_expr cx (TopLevelName _ _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_expr cx (FlagMember _ _ _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_expr cx (IfExp _ _ _ _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_expr cx (Subscript _ _ _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_expr cx (Attribute _ _ _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (Expr _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (AnnAssign _ _ _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (If _ _ _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (Raise (RaiseCustomError _))`]
  >- (fs[] >> PROTECTED_CASE >> first_x_assum irule >>
      simp[] >> drule order_custom_error_args_perm >>
      metis_tac[sortingTheory.PERM_EVERY])
  >~ [`eval_stmt cx (Assert _ (AssertCustomError _))`]
  >- (fs[] >> PROTECTED_CASE >> first_x_assum irule >>
      simp[] >> drule order_custom_error_args_perm >>
      metis_tac[sortingTheory.PERM_EVERY])
  >~ [`eval_iterator cx (Array _)`] >- (fs[] >> PROTECTED_CASE >> metis_tac[])
  >~ [`eval_iterator cx (Range _ _)`] >- (fs[] >> PROTECTED_CASE >> metis_tac[])
  >~ [`eval_for cx _ _ _ []`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_for cx _ _ _ (_::_)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (For _ _ _ _ _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_expr cx (StructLit _ _ _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (Assign (TupleTarget _) _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`assign_tuple_targets cx (TupleTarget _) _`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`assign_tuple_target_list cx [] []`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`assign_tuple_target_list cx (_::_) (_::_)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`assign_tuple_target_list cx _ _`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (Log _ _)`]
  >- (PROTECTED_CASE >> simp[protected_frame_result] >>
      metis_tac[push_log_immutables, lookup_immutable_def])
  >~ [`eval_expr cx (TypeBuiltin _ _ _ _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_expr cx (Builtin _ _ _)`]
  >- (PROTECTED_CASE
      >- (gvs[type_check_def, assert_def, check_def, return_def, raise_def] >>
          Cases_on `es` >> fs[builtin_args_length_ok_def] >> metis_tac[]) >> metis_tac[])
  >~ [`eval_expr cx (Call _ (Send _) _ _)`]
  >- (PROTECTED_CASE >- metis_tac[] >> simp[protected_frame_result] >>
      metis_tac[eval_send_preserves_non_accounts, lookup_immutable_def])
  >~ [`eval_expr cx (Call _ (ExtCall _ _ _ _) _ _)`]
  >- (PROTECTED_CASE
      >- metis_tac[rich_listTheory.EVERY_TAKE]
      >- metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]
      >- metis_tac[rich_listTheory.EVERY_DROP] >>
      simp[protected_frame_result] >>
      metis_tac[eval_ext_call_preserves_non_accounts, lookup_immutable_def])
  >~ [`eval_expr cx (Call _ (RawCallTarget _) _ _)`]
  >- (PROTECTED_CASE >- metis_tac[] >> simp[protected_frame_result] >>
      metis_tac[eval_raw_call_preserves_non_accounts, lookup_immutable_def])
  >~ [`eval_expr cx (Call _ (RawCallCalldataTarget _) _ _)`]
  >- (PROTECTED_CASE >- metis_tac[] >> simp[protected_frame_result] >>
      metis_tac[eval_raw_call_preserves_non_accounts, lookup_immutable_def])
  >~ [`eval_expr cx (Call _ RawRevert _ _)`] >- (PROTECTED_CASE >> metis_tac[])
  >~ [`eval_stmt cx (Assign (BaseTarget _) _)`]
  >- (PROTECTED_CASE
      >- (simp[protected_frame_result] >>
          qpat_x_assum `!s pv t s2 v t2. _` drule >>
          disch_then drule >> simp[] >> metis_tac[]) >>
      qpat_x_assum `!s pv t s2 v t2. _` drule >>
      disch_then drule >> simp[] >> strip_tac >>
      qpat_x_assum `!st res st'. _` drule >>
      disch_then drule >> strip_tac >>
      simp[protected_frame_result] >> rpt strip_tac >>
      drule write_place_protected_cell >>
      disch_then (qspec_then `protected` mp_tac) >> simp[] >> metis_tac[])
  >~ [`eval_stmt cx (AugAssign _ _ _ _)`]
  >- (PROTECTED_GUARDS >> fs[] >> PROTECTED_CASE
      >- (simp[protected_frame_result] >> metis_tac[]) >>
      simp[protected_frame_result] >> rpt strip_tac >>
      drule write_place_protected_cell >>
      disch_then (qspec_then `protected` mp_tac) >> simp[] >> metis_tac[])
  >~ [`assign_tuple_targets cx (BaseTarget _) _`]
  >- (PROTECTED_GUARDS >> fs[] >> PROTECTED_CASE
      >- (simp[protected_frame_result] >> metis_tac[]) >>
      simp[protected_frame_result] >> rpt strip_tac >>
      drule write_place_protected_cell >>
      disch_then (qspec_then `protected` mp_tac) >> simp[] >> metis_tac[])
  >~ [`eval_expr cx (Pop _ _)`]
  >- (PROTECTED_GUARDS >> fs[] >> PROTECTED_CASE
      >- (simp[protected_frame_result] >> metis_tac[]) >>
      simp[protected_frame_result] >> rpt strip_tac >>
      drule pop_place_protected_cell >>
      disch_then (qspec_then `protected` mp_tac) >> simp[] >> metis_tac[])
  >~ [`eval_stmt cx (Append _ _)`]
  >- (PROTECTED_GUARDS >> fs[] >> PROTECTED_CASE
      >- (simp[protected_frame_result] >> metis_tac[]) >>
      qmatch_goalsub_rename_tac `append_place cx pl value` >>
      Cases_on `pl` >> fs[]
      >- (simp[protected_frame_result] >>
          metis_tac[append_storage_place_scopes_immutables, lookup_immutable_def]) >>
      simp[append_place_def] >> rpt PROTECTED_STEP >>
      simp[protected_frame_result] >> rpt strip_tac
      >- (drule write_memory_place_immutables >> simp[lookup_immutable_def]) >>
      qpat_x_assum `!st res st'. eval_target_place _ _ _ = _ ==> _` drule >>
      strip_tac >> irule write_immutable_place_other_cell >>
      goal_assum (drule_at Any) >> metis_tac[])
  >~ [`eval_expr cx (Call _ SelfDestructTarget _ _)`]
  >- (PROTECTED_CASE >- metis_tac[]
      >- (simp[protected_frame_result] >>
          metis_tac[transfer_value_immutables, lookup_immutable_def])
      >- simp[protected_frame_result, update_accounts_def, return_def,
              lookup_immutable_def] >>
      simp[protected_frame_result, update_pending_deletions_def, return_def,
           lookup_immutable_def])
  >~ [`eval_expr cx (Call _ (CreateTarget _ _ _ _) _ _)`]
  >- (PROTECTED_CASE
      >>~- ([`state_rel_frame _ (eval_create _ _ _ _ _ _ _)`],
        simp[protected_frame_result] >>
        metis_tac[eval_create_preserves_scopes_immutables, lookup_immutable_def]) >>
      metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP])
  >~ [`eval_expr cx (Call _ RawLog _ _)`]
  >- (simp_tac bool_ss [Once evaluate_def] >>
      MATCH_MP_TAC state_rel_frame_bind_guarded >> conj_tac
      >- simp[] >> conj_tac >- metis_tac[] >> rpt gen_tac >> strip_tac >>
      simp[protected_frame_result, bind_def, ignore_bind_def, type_check_def,
           assert_def, check_def, return_def, raise_def, lift_option_type_def,
           lift_option_def, check_not_static_def, push_log_def, AllCaseEqs()] >>
      rpt strip_tac >>
      Cases_on `dest_ArrayV (HD v)` >> gvs[return_def, raise_def] >>
      Cases_on `dest_BytesV (EL 1 v)` >> gvs[return_def, raise_def] >>
      simp[lookup_immutable_def])
  >~ [`eval_expr cx (Call _ (IntCall _) _ _)`] >- suspend "internal_call"
  >>~- ([`eval_target_place cx t st = (res,st')`],
    PROTECTED_GUARDS >> fs[] >>
    qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
    simp_tac bool_ss [Once evaluate_def] >>
    Cases_on `eval_base_place cx t st` >>
    rename1 `eval_base_place cx t st = (answer,mid)` >>
    first_x_assum drule >> strip_tac >>
    Cases_on `answer` >>
    simp[bind_def, raise_def, get_place_def, return_def, AllCaseEqs()] >>
    rpt strip_tac >> gvs[] >>
    rename1 `get_place operand mid = _` >> Cases_on `operand` >>
    gvs[get_place_def, return_def, raise_def])
  >~ [`assign_tuple_target_list cx (_::_) []`] >- (PROTECTED_CASE >> metis_tac[])
QED

Resume protected_writes_frame_mutual[subscript_target]:
  strip_tac >> simp[runtime_write_root_def, expr_writes_ok_def] >>
  strip_tac >> PROTECTED_GUARDS >> fs[] >> rpt gen_tac >>
  simp[Once evaluate_def] >>
  Cases_on `eval_base_place cx t st` >>
  rename1 `eval_base_place cx t st = (answer,mid)` >>
  qpat_x_assum `!st res st'. eval_base_place _ _ _ = _ ==> _` drule >>
  strip_tac >> Cases_on `answer` >> simp[bind_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!s pv t. _` drule >> strip_tac >>
  Cases_on `eval_expr cx e mid` >>
  rename1 `eval_expr cx e mid = (ea,emid)` >>
  qpat_x_assum `!st res st' sid nm. eval_expr _ _ _ = _ /\ _ ==> _` drule >>
  strip_tac >> Cases_on `ea` >> gvs[] >>
  rename1 `eval_expr cx e mid = (INL expr_value,emid)` >>
  Cases_on `read_result cx expr_value emid` >>
  rename1 `read_result cx _ emid = (ra,rmid)` >>
  `!sid nm. lookup_immutable cx rmid sid nm = lookup_immutable cx emid sid nm` by
    metis_tac[machine_frame_read_result, state_rel_frame_result,
              machine_frame_def, lookup_immutable_def] >>
  Cases_on `ra` >> gvs[]
  >~ [`lookup_immutable cx st' sid nm = _`]
  >- metis_tac[machine_frame_extend_place, state_rel_frame_result,
               machine_frame_def, lookup_immutable_def] >>
  drule extend_place_immutable_root >> strip_tac >> metis_tac[]
QED

Resume protected_writes_frame_mutual[internal_call]:
  simp_tac bool_ss [Once evaluate_def] >>
  PROTECTED_STEP >> PROTECTED_STEP >> PROTECTED_STEP >>
  PROTECTED_STEP >> PROTECTED_STEP >>
  ntac 5 PROTECTED_STEP >> ntac 5 PROTECTED_STEP >>
  ntac 5 PROTECTED_STEP >> ntac 5 PROTECTED_STEP >>
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [LET_THM, FST, SND] >>
  rename1 `INL (imut,inr,iargs,idflts,iretty,ibody)` >>
  qmatch_asmsub_rename_tac `lookup_callable_function cx.in_deploy fn ts` >>
  `get_module_code cx src_id_opt = SOME ts` by
    (qpat_x_assum `lift_option_type (get_module_code _ _) _ _ = _` mp_tac >>
     Cases_on `get_module_code cx src_id_opt` >>
     simp[lift_option_type_def, return_def, raise_def]) >>
  `lookup_callable_function cx.in_deploy fn ts = SOME (imut,inr,iargs,idflts,iretty,ibody)` by
    (qpat_x_assum `lift_option_type (lookup_callable_function _ _ _) _ _ = _` mp_tac >>
     Cases_on `lookup_callable_function cx.in_deploy fn ts` >>
     simp[lift_option_type_def, return_def, raise_def]) >>
  `EVERY (expr_writes_ok (runtime_write_root R)) idflts /\
   stmts_writes_ok (runtime_write_root R) ibody` by
    (qpat_x_assum `!sid fn ts mut nr args ds rt body. get_module_code _ _ = _ /\ _ ==> _`
       (drule_then drule) >> simp[]) >>
  PROTECTED_GUARDS >>
  ntac 5 PROTECTED_STEP >>
  strip_tac >> PROTECTED_STEP >>
  PROTECTED_STEP >- metis_tac[]
  >- (fs[] >> metisTools.METIS_TAC []) >>
  ntac 5 PROTECTED_STEP >> ntac 5 PROTECTED_STEP >>
  ntac 5 PROTECTED_STEP >> ntac 3 PROTECTED_STEP
  >- (strip_tac >>
      `!sid func ts mut nr args ds rt body.
         get_module_code (cx with stk updated_by CONS (src_id_opt,fn)) sid = SOME ts /\
         lookup_callable_function (cx with stk updated_by CONS (src_id_opt,fn)).in_deploy func ts =
           SOME (mut,nr,args,ds,rt,body) ==>
         EVERY (expr_writes_ok (runtime_write_root R)) ds /\
         stmts_writes_ok (runtime_write_root R) body` by
        (qpat_x_assum `!sid fn ts mut nr args ds rt body. get_module_code cx sid = _ /\ _ ==> _`
           mp_tac >> simp[get_module_code_def]) >>
      fs[] >>
      qpat_assum `!sid func ts mut nr args ds rt body. get_module_code (cx with stk updated_by _) sid = _ /\ _ ==> _`
        (fn th => RULE_ASSUM_TAC (REWRITE_RULE [EQT_INTRO th])) >>
      `EVERY (expr_writes_ok (runtime_write_root R))
         (DROP (LENGTH idflts - (LENGTH iargs - LENGTH es)) idflts)` by
        metis_tac[rich_listTheory.EVERY_DROP] >>
      fs[lookup_immutable_def] >> PROTECTED_FORWARD_IH) >>
  ntac 5 PROTECTED_STEP >> ntac 5 PROTECTED_STEP >>
  ntac 5 PROTECTED_STEP >> ntac 3 PROTECTED_STEP >>
  simp_tac bool_ss [lock_if_nr_def, unlock_if_nr_def] >>
  PROTECTED_STEP
  >- metis_tac[]
  >- (POP_ASSUM_LIST (K all_tac) >>
      rewrite_tac[protected_frame_result] >> rpt gen_tac >> strip_tac >>
      Cases_on `inr` >> Cases_on `cx.nonreentrant_slot` >>
      gvs[return_def, raise_def] >>
      rename1 `acquire_nonreentrant_lock _ slot _` >>
      Cases_on `acquire_nonreentrant_lock cx.txn.target slot
        (is_view_mut imut \/ cx.txn.is_static) st` >>
      drule acquire_nonreentrant_lock_immutables >>
      Cases_on `imut = View \/ imut = Pure` >>
      gvs[is_view_mut_def, ignore_bind_def, bind_def, check_not_static_def,
          type_check_def, assert_def, check_def, return_def, raise_def,
          AllCaseEqs()] >>
      strip_tac >> simp[lookup_immutable_def]) >>
  ntac 4 PROTECTED_STEP >>
  simp_tac bool_ss [BETA_THM] >> ntac 4 PROTECTED_STEP >>
  strip_tac >>
  qmatch_asmsub_rename_tac `push_function (src_id_opt,fn) env cx ps = (INL cxf,pt)` >>
  `cxf = cx with stk updated_by CONS (src_id_opt,fn)` by
    (qpat_x_assum `push_function _ _ _ _ = _` mp_tac >>
     simp[push_function_def, return_def]) >>
  fs[] >>
  `!sid func ts mut nr args ds rt body.
     get_module_code cxf sid = SOME ts /\
     lookup_callable_function cxf.in_deploy func ts = SOME (mut,nr,args,ds,rt,body) ==>
     EVERY (expr_writes_ok (runtime_write_root R)) ds /\
     stmts_writes_ok (runtime_write_root R) body` by
    (qpat_x_assum `cxf = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `!sid fn ts mut nr args ds rt body. get_module_code cx sid = _ /\ _ ==> _`
       mp_tac >> simp[get_module_code_def]) >>
  `state_rel_frame (\s t. !sid nm. protected sid nm ==>
      lookup_immutable cxf t sid nm = lookup_immutable cxf s sid nm)
     (eval_stmts cxf ibody)` by
    (qpat_x_assum `cxf = _` SUBST_ALL_TAC >>
     simp_tac (srw_ss()) [lookup_immutable_stk, lookup_immutable_def] >>
     PROTECTED_FORWARD_IH) >>
  qpat_x_assum `cxf = _` SUBST_ALL_TAC >>
  qpat_x_assum `state_rel_frame _ (eval_stmts _ _)`
    (fn th => POP_ASSUM_LIST (K all_tac) >>
      assume_tac (REWRITE_RULE [lookup_immutable_stk] th)) >>
  rpt (CHANGED_TAC PROTECTED_STEP)
  >- gvs[lookup_immutable_def] >>
  simp[protected_frame_result] >>
  rpt gen_tac >> strip_tac >>
  drule release_nonreentrant_lock_immutables >>
  simp[lookup_immutable_def]
QED

Finalise protected_writes_frame_mutual
