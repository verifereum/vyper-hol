Theory bodyLoopImmutableFrame
Ancestors
  alist list relation vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperTypeContract vyperTypeSystem vyperStorageAccessFrame
  vyperTypeCallGraphSoundness vyperAST vyperState vyperInterpreter
  vyperBareGlobalName vyperImmutablesPreservation vyperStoragePlaceProvenance
  vyperContext vyperCallOutcomeFrame vyperEvalFrame vyperMachineFrame
  vyperScopePreservation vyperCreateFrame vyperLookupStorage vyperMisc
  whitelistForIterImmFrame bodyStorageCases rich_list
Libs evalWalkLib

(* A loop's initial calls generate a set closed under callable bodies and
   defaults. The checker guards each member of this set against writes. *)
Theorem loop_calls_reachable_writes:
  EVERY (callee_writes_ok mods p) calls ==>
  ?reached.
    EVERY reached calls /\
    !sid fn ts deploy mut nr args dflts ret body.
      reached (sid,fn) /\
      ALOOKUP mods sid = SOME ts /\
      lookup_callable_function deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (callee_write_ok p)) dflts /\
      stmts_writes_ok (callee_write_ok p) body /\
      EVERY reached (function_int_calls dflts body)
Proof
  strip_tac >>
  qexists_tac
    `\callee. ?origin. MEM origin calls /\
      (origin = callee \/
       TC (call_edge_rel (contract_call_edges mods)) origin callee)` >>
  conj_tac >- (simp[EVERY_MEM] >> metis_tac[]) >>
  rpt gen_tac >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `origin` (CONJUNCTS_THEN assume_tac)) STRIP_ASSUME_TAC) >>
  rename1 `lookup_callable_function deploy fn ts =
             SOME (mut,nr,args,dflts,ret,bod)` >>
  Cases_on `dflts = [] /\ bod = []`
  >- gvs[stmt_writes_ok_def, function_int_calls_def, int_calls_expr_def,
         int_calls_stmt_def] >>
  `?vis mut' nr' raw args' ret'.
     MEM (FunctionDecl vis mut' nr' raw fn args' dflts ret' bod) ts` by
    metis_tac[lookup_callable_function_SOME_decompose] >>
  strip_tac >>
  drule ALOOKUP_MEM >> strip_tac >>
  `EVERY (expr_writes_ok (callee_write_ok p)) dflts /\
   stmts_writes_ok (callee_write_ok p) bod` by
    (qpat_x_assum `EVERY _ calls` mp_tac >>
     simp[EVERY_MEM] >> disch_then drule >>
     simp[callee_writes_ok_def, EVERY_MEM, pairTheory.FORALL_PROD] >>
     disch_then (drule_at Any) >> disch_then (drule_at Any) >>
     simp[contract_reachable_TC] >> metis_tac[]) >>
  simp[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM ((sid,fn),callee) (contract_call_edges mods)` by
    (irule contract_call_edges_function >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  metis_tac[TC_SUBSET, TC_TRANSITIVE, transitive_def, call_edge_rel_def]
QED

Theorem extend_immutable_array_field_error[local]:
  lookup_immutable cx st src name = SOME (ArrayTV elem bound,ArrayV av) ==>
  ?err. extend_place cx (PlaceR (ImmutablePlace src name []))
          (AttrSubscript fld) st = (INR err,st)
Proof
  simp[lookup_immutable_def, extend_place_def, read_place_def,
       place_type_value_def, get_immutables_def, get_address_immutables_def,
       bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def, subscripts_type_def, evaluate_subscripts_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> simp[] >>
  strip_tac >> simp[return_def, raise_def, subscripts_type_def,
                    evaluate_subscripts_def]
QED

Theorem eval_base_place_immutable_array_access[local]:
  !target cx st st' src name path elem bound av.
    lookup_immutable cx st src name = SOME (ArrayTV elem bound,ArrayV av) /\
    eval_base_place cx target st =
      (INL (PlaceR (ImmutablePlace src name path)),st') ==>
    !pending. place_access target pending = (TopLevelNameTarget (src,name),[]) \/
      (target = TopLevelNameTarget (src,name) /\ path = [])
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> rpt strip_tac
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
         type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`]
  >- (rename1 `eval_base_place cx (TopLevelNameTarget nsid) st = _` >>
      PairCases_on `nsid` >> gvs[Once evaluate_def] >>
      metis_tac[lookup_global_immutable_root]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  drule extend_place_immutable_root >> strip_tac >> gvs[] >>
  rename1 `eval_base_place cx inner st = _` >>
  first_x_assum (qspec_then `inner` mp_tac) >> simp[] >> strip_tac >>
  simp[place_access_def] >>
  first_x_assum (qspecl_then [`cx`,`st`] mp_tac) >>
  disch_then drule_all >> strip_tac
  >~ [`place_access inner [] = _`]
  >- (first_x_assum (qspec_then `[]` strip_assume_tac) >>
      gvs[place_access_def]) >>
  gvs[place_access_def] >>
  qmatch_asmsub_rename_tac
    `extend_place cx (PlaceR (ImmutablePlace src name child)) (AttrSubscript fld) mid` >>
  first_x_assum (qspec_then `fld::pending` strip_assume_tac) >> gvs[] >>
  gvs[Once evaluate_def] >>
  drule lookup_global_immutables >> strip_tac >>
  `?err. extend_place cx (PlaceR (ImmutablePlace src name []))
           (AttrSubscript fld) mid = (INR err,mid)` by
    (irule extend_immutable_array_field_error >>
     qexistsl [`av`,`bound`,`elem`] >> gvs[lookup_immutable_def]) >>
  gvs[]
QED

Theorem immutable_array_guarded_target:
  lookup_immutable cx st src name = SOME (ArrayTV elem bound,ArrayV av) /\
  callee_write_ok (TopLevelNameTarget (src,name)) target /\
  eval_target_place cx target st = (INL pl,st') ==>
  !path. pl <> ImmutablePlace src name path
Proof
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, get_place_def,
                      return_def, raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule_all eval_base_place_immutable_array_access >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  gvs[callee_write_ok_def, place_contains_def, place_access_def]
QED

(* A relation on observations of the immutable store, not a frame on
   the whole store. It need only preserve the observation when it holds. *)
val array_cell = ``\(st:evaluation_state). obs st.immutables : bool``;
val array_relation = rhs (concl (DEPTH_CONV BETA_CONV
  ``\s t. ^array_cell s ==> ^array_cell t``));
val array_frame_result = BETA_RULE
  (ISPEC array_relation (Q.GEN `R` state_rel_frame_result));
val array_guard = ``callee_write_ok p``;
val array_mutations = ``\(addr:address). !cx target s pl t.
    cx.txn.target = addr /\ ^array_guard target /\
    eval_target_place cx target s = (INL pl,t) /\
    ^array_cell s /\ ^array_cell t ==>
    (!v. state_rel_frame ^array_relation (write_place cx pl v)) /\
    (!v. state_rel_frame ^array_relation (append_place cx pl v)) /\
    state_rel_frame ^array_relation (pop_place cx pl)``;

Theorem guarded_array_target_bind[local]:
  state_rel_frame ^array_relation (eval_target_place cx target) /\
  (!s pl t. eval_target_place cx target s = (INL pl,t) /\
            ^array_cell s /\ ^array_cell t ==>
            state_rel_frame ^array_relation (next pl)) ==>
  state_rel_frame ^array_relation (bind (eval_target_place cx target) next)
Proof
  simp[array_frame_result, bind_def] >> rpt strip_tac >>
  Cases_on `eval_target_place cx target st` >>
  rename1 `eval_target_place cx target st = (answer,mid)` >>
  Cases_on `answer` >> gvs[] >>
  qpat_assum `!st res st'. eval_target_place cx target st = _ ==> _`
    (drule_then drule) >> strip_tac
  >- (qpat_x_assum `!s pl t. eval_target_place _ _ _ = _ /\ _ ==> _`
        drule >> simp[] >> disch_then (drule_all_then ACCEPT_TAC)) >>
  first_assum ACCEPT_TAC
QED

val array_net =
  let
    val leaves = [machine_frame_primitives, machine_frame_read_result,
      machine_frame_read_results, machine_frame_reads, machine_frame_select_result,
      machine_frame_extend_place, machine_frame_get_place, machine_frame_read_place,
      machine_frame_place_type_value, machine_frame_new_variable,
      machine_frame_next_gas_reading, machine_frame_precompile_call_success,
      machine_frame_handlers, machine_frame_push_function,
      machine_frame_pop_function, machine_frame_unchanged_reads,
      machine_frame_array_iterator_results]
    fun leaf th = (subst [``machine_frame`` |-> array_relation] (concl th),
      irule state_rel_frame_machine >> conj_tac
      >- simp[machine_frame_def] >> MATCH_ACCEPT_TAC th)
  in evalWalkLib.walk_net
    (map SPEC_ALL [state_rel_frame_bind_guarded, state_rel_frame_try,
      state_rel_frame_finally, state_rel_frame_finally_unless_halt])
    (map leaf (List.concat (map (CONJUNCTS o SPEC_ALL) leaves))) end;

Theorem array_code_stk[local]:
  get_module_code (cx with stk updated_by f) = get_module_code cx
Proof
  simp[FUN_EQ_THM, get_module_code_def]
QED

val array_context_simps = [array_code_stk, oneTheory.one,
  ignore_bind_def, FST, SND, pair_case_thm, UNCURRY];
val array_induction_hypothesis =
  evalWalkLib.IH_TAC {stop = K false,
    normalise = SIMP_RULE bool_ss array_context_simps};
val array_syntax = [int_calls_expr_def, int_calls_stmt_def, int_calls_iterator_def,
  int_calls_assert_reason_def, int_calls_raise_reason_def, int_calls_atarget_def,
  stmt_writes_ok_def, expr_writes_ok_def, atarget_writes_ok_def,
  GSYM vyperTypeEvalProofsTheory.int_calls_exprs_MAP_SND,
  EVERY_APPEND, EVERY_DEF, SF ETA_ss];
val ARRAY_TRANSITIVITY =
  qmatch_goalsub_abbrev_tac `!s t u. P s t /\ P t u ==> P s u` >>
  simp[Abbr `P`];
val ARRAY_TARGET =
  conj_tac >- array_induction_hypothesis >>
  BETA_TAC >> rpt strip_tac >>
  qpat_assum `!cx target s pl t. _ /\ _ /\ eval_target_place cx target s = _ /\ _ ==> _`
    (drule_at_then (Pat `eval_target_place _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac;
val ARRAY_STEP = IF (MATCH_MP_TAC guarded_array_target_bind) ARRAY_TARGET
  (evalWalkLib.STEP
    {net = array_net, at = RAND_CONV,
     unfolds = [switch_BoolV_def, ignore_bind_def, check_not_static_def,
       vyperCreateTheory.eval_create_operands_def],
     intros = [ARRAY_TRANSITIVITY, CONV_TAC (HO_REWR_CONV FORALL_PROD),
       gen_tac, strip_tac, conj_tac, CONV_TAC (RAND_CONV ETA_CONV)],
     fallbacks = [array_induction_hypothesis,
       evalWalkLib.NORMALISE_IH_TAC array_induction_hypothesis]});
val ARRAY_CASE = evalWalkLib.EVAL_CASE all_tac ARRAY_STEP;
val ARRAY_ATOMIC_FRAME = simp_tac (srw_ss()) [array_frame_result,
  return_def, raise_def, push_log_def, update_accounts_def,
  update_pending_deletions_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[eval_ext_call_preserves_non_accounts, eval_raw_call_preserves_non_accounts,
    eval_send_preserves_non_accounts, eval_create_preserves_scopes_immutables,
    vyperStatePreservationTheory.transfer_value_immutables];
val ARRAY_CUSTOM = ARRAY_CASE >>
  qmatch_goalsub_rename_tac `eval_exprs cx ordered` >>
  drule order_custom_error_args_perm >> strip_tac >>
  `EVERY reached (int_calls_exprs ordered)` by
    (simp[body_exprs_main_calls_every] >>
     qpat_x_assum `EVERY reached (int_calls_exprs (custom_error_exprs _))` mp_tac >>
     simp[body_exprs_main_calls_every] >> metis_tac[sortingTheory.PERM_EVERY]) >>
  `EVERY (expr_writes_ok ^array_guard) ordered` by metis_tac[sortingTheory.PERM_EVERY] >>
  array_induction_hypothesis;
val ARRAY_CASE_SIMPLE = ARRAY_CASE >>
  (first_assum ACCEPT_TAC ORELSE simp[array_frame_result, return_def, raise_def]);
fun ARRAY_EXPR_CHUNK (g as (_,w)) =
  case strip_comb (rand w) of
    (head,[_,chunk]) =>
      if aconv head ``eval_exprs`` then
        (`EVERY reached (int_calls_exprs ^chunk) /\
          EVERY (expr_writes_ok ^array_guard) ^chunk` by
           (fs[body_exprs_main_calls_every] >> conj_tac >>
            rpt (FIRST [irule EVERY_TAKE, irule EVERY_DROP]) >> first_assum ACCEPT_TAC) >>
         array_induction_hypothesis) g
      else ARRAY_ATOMIC_FRAME g
  | _ => ARRAY_ATOMIC_FRAME g;

val array_code = ``\cx. get_module_code cx = ALOOKUP mods /\
                        cx.in_deploy = deploy /\ cx.txn.target = addr``;
val array_iterator_writes = ``\it. case it of
    Array e => expr_writes_ok ^array_guard e
  | Range lo hi => expr_writes_ok ^array_guard lo /\ expr_writes_ok ^array_guard hi``;

Theorem reached_callable_guards[local]:
  (!sid func ts mut nr args dflts ret bod.
    reached (sid,func) /\ ALOOKUP mods sid = SOME ts /\
    lookup_callable_function deploy func ts = SOME (mut,nr,args,dflts,ret,bod) ==>
    EVERY (expr_writes_ok ^array_guard) dflts /\
    stmts_writes_ok ^array_guard bod /\ EVERY reached (function_int_calls dflts bod)) /\
  ^array_code cx /\ reached (sid,func) /\
  lift_option_type (get_module_code cx sid) msg s = (INL ts,t) /\
  lift_option_type (lookup_callable_function cx.in_deploy func ts) msg' s' =
    (INL (mut,nr,args,dflts,ret,bod),t') ==>
  EVERY (expr_writes_ok ^array_guard) dflts /\ stmts_writes_ok ^array_guard bod /\
  EVERY reached (int_calls_exprs dflts) /\ EVERY reached (int_calls_stmts bod)
Proof
  simp[vyperTypeEvalProofsTheory.lift_option_type_INL_eq,
       function_int_calls_def, EVERY_APPEND] >> rpt strip_tac >>
  qpat_x_assum `get_module_code cx sid = SOME ts` mp_tac >>
  qpat_x_assum `lookup_callable_function cx.in_deploy _ _ = _` mp_tac >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!sid func ts mut nr args dflts ret bod. _`
    (drule_all_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

(* The induction covers calls reached from the iterator body. Each reached
   callee supplies the guard and the call closure for its defaults and body. *)
Theorem reachable_guarded_immutable_frame[local]:
  (!sid func ts mut nr args dflts ret bod.
    reached (sid,func) /\ ALOOKUP mods sid = SOME ts /\
    lookup_callable_function deploy func ts = SOME (mut,nr,args,dflts,ret,bod) ==>
    EVERY (expr_writes_ok ^array_guard) dflts /\
    stmts_writes_ok ^array_guard bod /\ EVERY reached (function_int_calls dflts bod)) /\
  ^array_mutations addr ==>
  (!cx s. ^array_code cx /\ EVERY reached (int_calls_stmt s) /\
          stmt_writes_ok ^array_guard s ==>
     state_rel_frame ^array_relation (eval_stmt cx s)) /\
  (!cx ss. ^array_code cx /\ EVERY reached (int_calls_stmts ss) /\
           stmts_writes_ok ^array_guard ss ==>
     state_rel_frame ^array_relation (eval_stmts cx ss)) /\
  (!cx it. ^array_code cx /\ EVERY reached (int_calls_iterator it) /\
           ^array_iterator_writes it ==>
     state_rel_frame ^array_relation (eval_iterator cx it)) /\
  (!cx tyv nm bod vs. ^array_code cx /\ EVERY reached (int_calls_stmts bod) /\
                     stmts_writes_ok ^array_guard bod ==>
     state_rel_frame ^array_relation (eval_for cx tyv nm bod vs)) /\
  (!cx e. ^array_code cx /\ EVERY reached (int_calls_expr e) /\
          expr_writes_ok ^array_guard e ==>
     state_rel_frame ^array_relation (eval_expr cx e)) /\
  (!cx es. ^array_code cx /\ EVERY reached (int_calls_exprs es) /\
           EVERY (expr_writes_ok ^array_guard) es ==>
     state_rel_frame ^array_relation (eval_exprs cx es)) /\
  (!cx t. ^array_code cx /\ EVERY reached (int_calls_target t) /\
          target_writes_ok ^array_guard t ==>
     state_rel_frame ^array_relation (eval_base_place cx t)) /\
  (!cx t. ^array_code cx /\ EVERY reached (int_calls_target t) /\
          target_writes_ok ^array_guard t ==>
     state_rel_frame ^array_relation (eval_target_place cx t)) /\
  (!cx g v. ^array_code cx /\ EVERY reached (int_calls_atarget g) /\
            atarget_writes_ok ^array_guard g ==>
     state_rel_frame ^array_relation (assign_tuple_targets cx g v)) /\
  (!cx gs vs. ^array_code cx /\ EVERY reached (int_calls_atargets gs) /\
              EVERY (atarget_writes_ok ^array_guard) gs ==>
     state_rel_frame ^array_relation (assign_tuple_target_list cx gs vs))
Proof
  BETA_TAC >> strip_tac >> ho_match_mp_tac evaluate_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp_tac (srw_ss()) array_syntax >> rpt strip_tac >>
  all_tac
  >~ [`eval_expr _ (Call _ (IntCall _) _ _)`] >- suspend "intcall"
  >~ [`eval_expr _ (Builtin _ _ _)`] >- suspend "builtin"
  >~ [`eval_expr _ (Call _ (CreateTarget _ _ _ _) _ _)`] >- suspend "create"
  >~ [`eval_expr _ (Call _ RawLog _ _)`] >- suspend "rawlog"
  >~ [`eval_stmt _ (Raise (RaiseCustomError _))`] >- ARRAY_CUSTOM
  >~ [`eval_stmt _ (Assert _ (AssertCustomError _))`] >- ARRAY_CUSTOM
  >~ [`eval_expr _ (StructLit _ _ _)`] >- (fs[SF ETA_ss] >> ARRAY_CASE_SIMPLE)
  >~ [`eval_expr _ (TypeBuiltin _ _ _ _)`] >- (fs[SF ETA_ss] >> ARRAY_CASE_SIMPLE)
  >~ [`eval_stmt _ (Log _ _)`] >- (ARRAY_CASE >> ARRAY_ATOMIC_FRAME)
  >~ [`eval_expr _ (Call _ (Send _) _ _)`] >- (ARRAY_CASE >> ARRAY_ATOMIC_FRAME)
  >~ [`eval_expr _ (Call _ (ExtCall _ _ _ _) _ _)`]
  >- (ARRAY_CASE >> ARRAY_EXPR_CHUNK)
  >~ [`eval_expr _ (Call _ (RawCallTarget _) _ _)`]
  >- (ARRAY_CASE >> ARRAY_ATOMIC_FRAME)
  >~ [`eval_expr _ (Call _ (RawCallCalldataTarget _) _ _)`]
  >- (ARRAY_CASE >> ARRAY_ATOMIC_FRAME)
  >~ [`eval_expr _ (Call _ SelfDestructTarget _ _)`]
  >- (ARRAY_CASE >> ARRAY_ATOMIC_FRAME) >>
  ARRAY_CASE_SIMPLE
QED

Resume reachable_guarded_immutable_frame[builtin]:
  ARRAY_CASE
  >- (gvs[type_check_def, assert_def, check_def, return_def, raise_def] >>
      Cases_on `es` >> gvs[builtin_args_length_ok_def, int_calls_expr_def,
                            EVERY_APPEND]) >>
  gvs[type_check_def, assert_def, check_def, return_def, raise_def,
      code_slice_source_SOME, expr_writes_ok_def, int_calls_expr_def, EVERY_APPEND,
      DISJ_IMP_THM, FORALL_AND_THM, AllCaseEqs()] >>
  array_induction_hypothesis
QED

Resume reachable_guarded_immutable_frame[create]:
  ARRAY_CASE >>
  all_tac >>~- ([`state_rel_frame _ (eval_create _ _ _ _ _ _ _)`],
    ARRAY_ATOMIC_FRAME) >>
  rename1 `state_rel_frame _ (eval_exprs cx (create_operand_order kind has_salt es))` >>
  `EVERY reached (int_calls_exprs (create_operand_order kind has_salt es)) /\
   EVERY (expr_writes_ok ^array_guard) (create_operand_order kind has_salt es)` by
    (simp[body_exprs_main_calls_every] >>
     fs[body_exprs_main_calls_every] >>
     Cases_on `kind` >> Cases_on `es` >>
     gvs[vyperCreateTheory.create_operand_order_def, EVERY_TAKE, EVERY_DROP] >>
     rename1 `EVERY _ rest` >> Cases_on `rest` >>
     gvs[vyperCreateTheory.create_operand_order_def, EVERY_TAKE, EVERY_DROP]) >>
  array_induction_hypothesis
QED

Resume reachable_guarded_immutable_frame[rawlog]:
  simp_tac bool_ss [Once evaluate_def] >>
  MATCH_MP_TAC state_rel_frame_bind_guarded >> conj_tac >- ARRAY_TRANSITIVITY >>
  conj_tac >- array_induction_hypothesis >>
  rpt gen_tac >> strip_tac >>
  simp[array_frame_result, bind_def, ignore_bind_def, type_check_def,
       assert_def, check_def, return_def, raise_def, lift_option_type_def,
       check_not_static_def, push_log_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `dest_ArrayV (HD v)` >> gvs[return_def, raise_def] >>
  Cases_on `dest_BytesV (EL 1 v)` >> gvs[return_def, raise_def] >>
  fs[]
QED

Resume reachable_guarded_immutable_frame[intcall]:
  simp_tac bool_ss [Once evaluate_def] >>
  ntac 25 ARRAY_STEP >> rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [LET_THM, FST, SND] >>
  rename1 `INL (imut,inr,iargs,idflts,iretty,ibody)` >>
  drule_all_then strip_assume_tac (BETA_RULE reached_callable_guards) >>
  `!n. EVERY (expr_writes_ok ^array_guard) (DROP n idflts) /\
       EVERY reached (int_calls_exprs (DROP n idflts))` by
    simp[EVERY_DROP, int_calls_exprs_DROP_EVERY] >>
  ntac 5 ARRAY_STEP >>
  strip_tac >> ARRAY_STEP >>
  ARRAY_STEP >- ARRAY_TRANSITIVITY
  >- (gvs[type_check_def, assert_def, return_def, raise_def] >>
      array_induction_hypothesis) >>
  ntac 18 ARRAY_STEP
  >- (rpt strip_tac >>
      gvs[array_code_stk,vyperTypeEvalProofsTheory.lift_option_type_INL_eq,
          type_check_def,assert_def,return_def,raise_def] >>
      evalWalkLib.FORWARD_IH_TAC
        {normalise = SIMP_RULE (srw_ss()) array_context_simps}) >>
  rpt (CHANGED_TAC ARRAY_STEP) >>
  simp_tac bool_ss [lock_if_nr_def, unlock_if_nr_def]
  >- (POP_ASSUM_LIST (K all_tac) >>
      rewrite_tac[array_frame_result] >> rpt gen_tac >> strip_tac >>
      Cases_on `inr` >> Cases_on `cx.nonreentrant_slot` >>
      gvs[return_def, raise_def] >>
      rename1 `acquire_nonreentrant_lock _ slot _` >>
      Cases_on `acquire_nonreentrant_lock cx.txn.target slot
        (is_view_mut imut \/ cx.txn.is_static) st` >>
      drule vyperStatePreservationTheory.acquire_nonreentrant_lock_immutables >>
      Cases_on `imut = View \/ imut = Pure` >>
      gvs[is_view_mut_def, ignore_bind_def, bind_def, check_not_static_def,
          type_check_def, assert_def, check_def, return_def, raise_def,
          AllCaseEqs()] >>
      strip_tac >> simp[])
  >~ [`state_rel_frame _ (eval_stmts _ _)`]
  >- (qmatch_asmsub_rename_tac `push_function (sid,func) env cx ps = (INL cxf,pt)` >>
      `cxf = cx with stk updated_by CONS (sid,func)` by
        (qpat_x_assum `push_function _ _ _ _ = _` mp_tac >> simp[push_function_def, return_def]) >>
      gvs[array_code_stk] >>
      evalWalkLib.FORWARD_IH_TAC
        {normalise = SIMP_RULE (srw_ss()) array_context_simps}) >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[array_frame_result] >> rpt gen_tac >> strip_tac >>
  Cases_on `inr /\ imut <> View /\ imut <> Pure` >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
  drule vyperStatePreservationTheory.release_nonreentrant_lock_immutables >>
  simp[]
QED

Finalise reachable_guarded_immutable_frame[local]

Theorem callee_write_ok_global[local]:
  FST (place_access p []) = TopLevelNameTarget nid ==>
  callee_write_ok p = (\w. ~place_contains w p)
Proof
  simp[FUN_EQ_THM, callee_write_ok_def] >> strip_tac >> gen_tac >>
  Cases_on `FST (place_access w [])` >> simp[place_contains_def]
QED

Theorem loop_iterator_place_in_expr_places[local]:
  !e p. loop_iterator_place e = SOME p ==> MEM p (expr_places e)
Proof
  measureInduct_on `expr_size e` >>
  Cases_on `e` >> simp[loop_iterator_place_def,expr_places_def,AllCaseEqs(),MEM_MAP] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

Theorem guarded_immutable_body_observation[local]:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  loop_iterator_place e = SOME p /\
  FST (place_access p []) = TopLevelNameTarget nid /\
  iterator_unmodified (Array e) ss /\
  stmt_loop_calls_ok [(NONE,tops)] (For id et (Array e) bound ss) /\
  ^array_mutations cx.txn.target /\ ^array_cell st /\
  eval_stmts cx ss st = (res,st') ==>
  ^array_cell st'
Proof
  BETA_TAC >>
  simp[iterator_unmodified_def, stmt_loop_calls_ok_def] >> rpt strip_tac >>
  qpat_x_assum `case loop_iterator_place e of NONE => T | SOME _ => _` mp_tac >>
  simp[] >> strip_tac >> drule loop_calls_reachable_writes >> strip_tac >>
  `stmts_writes_ok (callee_write_ok p) ss` by
    (drule callee_write_ok_global >> disch_then SUBST1_TAC >>
     fs[EVERY_MEM] >> metis_tac[loop_iterator_place_in_expr_places]) >>
  `state_rel_frame ^array_relation (eval_stmts cx ss)` by
    (irule (cj 2 reachable_guarded_immutable_frame) >>
     qexistsl [`cx.txn.target`,`cx.in_deploy`,`[(NONE,tops)]`,`p`,`reached`] >>
     simp[FUN_EQ_THM,get_module_code_def] >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     qpat_assum `!sid fn ts deploy mut nr args dflts ret body. _`
       (drule_at_then (Pat `lookup_callable_function _ _ _ = _`) mp_tac) >>
     simp[]) >>
  drule_all state_rel_frame_at >> simp[]
QED

val selected_cell = ``\s. ?v. lookup_immutable cx s src name = SOME (root_ty,v) /\
                          evaluate_subscripts root_ty v path = INL selected``;
val selected_relation = rhs (concl (DEPTH_CONV BETA_CONV
  ``\s t. ^selected_cell s ==> ^selected_cell t``));

(* The guarded mutation rule sees the target's actual success. Its frame is
   transported to the eventual mutation, even across RHS evaluation. *)
Theorem for_selected_immutable_body_frame_from_guard:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  loop_iterator_place e = SOME p /\
  FST (place_access p []) = TopLevelNameTarget (src,name) /\
  iterator_unmodified (Array e) ss /\
  stmt_loop_calls_ok [(NONE,tops)] (For id et (Array e) bound ss) /\
  (!cx' target s pl t.
      cx'.txn.target = cx.txn.target /\ callee_write_ok p target /\
      eval_target_place cx' target s = (INL pl,t) /\
      (?v. lookup_immutable cx s src name = SOME (root_ty,v) /\
           evaluate_subscripts root_ty v path = INL selected) /\
      (?v. lookup_immutable cx t src name = SOME (root_ty,v) /\
           evaluate_subscripts root_ty v path = INL selected) ==>
      (!v. state_rel_frame ^selected_relation (write_place cx' pl v)) /\
      (!v. state_rel_frame ^selected_relation (append_place cx' pl v)) /\
      state_rel_frame ^selected_relation (pop_place cx' pl)) /\
  (?v. lookup_immutable cx st src name = SOME (root_ty,v) /\
       evaluate_subscripts root_ty v path = INL selected) /\
  eval_stmts cx ss st = (res,st') ==>
  ?v. lookup_immutable cx st' src name = SOME (root_ty,v) /\
      evaluate_subscripts root_ty v path = INL selected
Proof
  mp_tac (Q.INST [`obs` |-> `\imm. ^selected_cell (st with immutables := imm)`,
                  `nid` |-> `(src,name)`] guarded_immutable_body_observation) >>
  simp[lookup_immutable_def]
QED

(* The original whole-array frame is a specialization at the action's
   address. Only mutations of other places are permitted by its guard. *)
val array_cell =
  ``\cx st. lookup_immutable cx st src name = SOME (ArrayTV elem bound,ArrayV av)``;
val array_relation = rhs (concl (DEPTH_CONV BETA_CONV
  ``\s t. ^array_cell cx s ==> ^array_cell cx t``));
val array_guard = ``callee_write_ok (TopLevelNameTarget (src,name))``;
val array_code = ``\cx. get_module_code cx = ALOOKUP mods /\ cx.in_deploy = deploy``;
val array_iterator_writes = ``\it. case it of
    Array e => expr_writes_ok ^array_guard e
  | Range lo hi => expr_writes_ok ^array_guard lo /\ expr_writes_ok ^array_guard hi``;

Theorem lookup_immutable_replace_store[local]:
  lookup_immutable cx (s with immutables := t.immutables) src name =
  lookup_immutable cx t src name
Proof
  simp[lookup_immutable_def]
QED

Theorem guarded_whole_array_mutations[local]:
  !cx' target s pl t.
    cx'.txn.target = cx.txn.target /\ ^array_guard target /\
    eval_target_place cx' target s = (INL pl,t) /\
    ^array_cell cx s /\ ^array_cell cx t ==>
    (!v. state_rel_frame ^array_relation (write_place cx' pl v)) /\
    (!v. state_rel_frame ^array_relation (append_place cx' pl v)) /\
    state_rel_frame ^array_relation (pop_place cx' pl)
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  `!s. lookup_immutable cx s src name = lookup_immutable cx' s src name` by
    simp[lookup_immutable_def] >>
  fs[] >> drule_all immutable_array_guarded_target >> strip_tac >>
  `!src' name' path. pl = ImmutablePlace src' name' path ==>
     (src',name') <> (src,name)` by metis_tac[pairTheory.PAIR_EQ] >>
  simp[state_rel_frame_result] >> rpt strip_tac >>
  imp_res_tac lookup_immutable_write_other >>
  imp_res_tac append_guarded_immutable_frame >>
  imp_res_tac pop_place_immutable_other >> gvs[]
QED

Theorem reachable_immutable_array_frame[local]:
  (!sid func ts mut nr args dflts ret bod.
    reached (sid,func) /\ ALOOKUP mods sid = SOME ts /\
    lookup_callable_function deploy func ts = SOME (mut,nr,args,dflts,ret,bod) ==>
    EVERY (expr_writes_ok ^array_guard) dflts /\
    stmts_writes_ok ^array_guard bod /\ EVERY reached (function_int_calls dflts bod)) ==>
  (!cx s. ^array_code cx /\ EVERY reached (int_calls_stmt s) /\
          stmt_writes_ok ^array_guard s ==>
     state_rel_frame ^array_relation (eval_stmt cx s)) /\
  (!cx ss. ^array_code cx /\ EVERY reached (int_calls_stmts ss) /\
           stmts_writes_ok ^array_guard ss ==>
     state_rel_frame ^array_relation (eval_stmts cx ss)) /\
  (!cx it. ^array_code cx /\ EVERY reached (int_calls_iterator it) /\
           ^array_iterator_writes it ==>
     state_rel_frame ^array_relation (eval_iterator cx it)) /\
  (!cx tyv nm bod vs. ^array_code cx /\ EVERY reached (int_calls_stmts bod) /\
                     stmts_writes_ok ^array_guard bod ==>
     state_rel_frame ^array_relation (eval_for cx tyv nm bod vs)) /\
  (!cx e. ^array_code cx /\ EVERY reached (int_calls_expr e) /\
          expr_writes_ok ^array_guard e ==>
     state_rel_frame ^array_relation (eval_expr cx e)) /\
  (!cx es. ^array_code cx /\ EVERY reached (int_calls_exprs es) /\
           EVERY (expr_writes_ok ^array_guard) es ==>
     state_rel_frame ^array_relation (eval_exprs cx es)) /\
  (!cx t. ^array_code cx /\ EVERY reached (int_calls_target t) /\
          target_writes_ok ^array_guard t ==>
     state_rel_frame ^array_relation (eval_base_place cx t)) /\
  (!cx t. ^array_code cx /\ EVERY reached (int_calls_target t) /\
          target_writes_ok ^array_guard t ==>
     state_rel_frame ^array_relation (eval_target_place cx t)) /\
  (!cx g v. ^array_code cx /\ EVERY reached (int_calls_atarget g) /\
            atarget_writes_ok ^array_guard g ==>
     state_rel_frame ^array_relation (assign_tuple_targets cx g v)) /\
  (!cx gs vs. ^array_code cx /\ EVERY reached (int_calls_atargets gs) /\
              EVERY (atarget_writes_ok ^array_guard) gs ==>
     state_rel_frame ^array_relation (assign_tuple_target_list cx gs vs))
Proof
  suspend "specialize"
QED

Resume reachable_immutable_array_frame[specialize]:
  BETA_TAC >> strip_tac >> rpt conj_tac >> qx_gen_tac `cx` >>
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`p` |-> `TopLevelNameTarget (src,name)`,
                  `addr` |-> `cx.txn.target`,
                  `obs` |-> `\imm. ^array_cell cx (ARB with immutables := imm)`]
                reachable_guarded_immutable_frame) >>
  simp[lookup_immutable_replace_store] >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
                MATCH_ACCEPT_TAC (BETA_RULE guarded_whole_array_mutations))) >>
  strip_tac >> first_assum irule >> simp[]
QED

Finalise reachable_immutable_array_frame

Theorem for_bare_immutable_array_body_observation:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  iterator_unmodified (Array (TopLevelName (ArrayT et bd) (src,name))) ss /\
  stmt_loop_calls_ok [(NONE,tops)]
    (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) bound ss) /\
  lookup_immutable cx st src name = SOME (ArrayTV elem arrbound,ArrayV av) /\
  eval_stmts cx ss st = (res,st') ==>
  lookup_immutable cx st' src name = lookup_immutable cx st src name
Proof
  simp[iterator_unmodified_def, expr_places_def, stmt_loop_calls_ok_def,
       loop_iterator_place_def] >> rpt strip_tac >>
  drule loop_calls_reachable_writes >> strip_tac >>
  `callee_write_ok (TopLevelNameTarget (src,name)) =
   (\w. ~place_contains w (TopLevelNameTarget (src,name)))` by
    (irule callee_write_ok_global >> simp[place_access_def]) >>
  `!sid fn ts mut nr args dflts ret body.
     reached (sid,fn) /\ ALOOKUP [(NONE,tops)] sid = SOME ts /\
     lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
     EVERY (expr_writes_ok ^array_guard) dflts /\
     stmts_writes_ok ^array_guard body /\ EVERY reached (function_int_calls dflts body)` by
    (rpt gen_tac >>
     qpat_assum `!sid fn ts deploy mut nr args dflts ret body. _`
       (MATCH_ACCEPT_TAC o SPEC_ALL)) >>
  `state_rel_frame
    (\s t. lookup_immutable cx s src name = SOME (ArrayTV elem arrbound,ArrayV av) ==>
            lookup_immutable cx t src name = SOME (ArrayTV elem arrbound,ArrayV av))
    (eval_stmts cx ss)` by
    (drule_then (irule o cj 2) reachable_immutable_array_frame >>
     simp[FUN_EQ_THM, get_module_code_def]) >>
  drule_all state_rel_frame_at >> simp[]
QED
