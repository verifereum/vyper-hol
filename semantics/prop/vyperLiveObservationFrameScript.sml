(* An immutable-store observation survives evaluation of guarded syntax
   whose internal calls stay within a closed set of keys. *)
Theory vyperLiveObservationFrame
Ancestors
  list rich_list pair sorting vyperAST vyperState vyperContext vyperMisc
  vyperInterpreter vyperTypeSystem vyperTypeCallGraph vyperTypeEvalProofs
  vyperReadOnlyEval vyperCallOutcomeFrame vyperMachineFrame vyperEvalFrame
  vyperImmutablesPreservation vyperCreateFrame vyperStatePreservation
  vyperGuardedTargetBind
Libs evalWalkLib

val cell = ``\(st:evaluation_state). obs st.immutables : bool``;
val observation = rhs (concl (DEPTH_CONV BETA_CONV
  ``\s t. ^cell s ==> ^cell t``));
val observation_result = BETA_RULE
  (ISPEC observation (Q.GEN `R` state_rel_frame_result));
val code = ``\cx. get_module_code cx = M /\
                  cx.in_deploy = deploy /\ cx.txn.target = addr``;
val iterator_writes = ``\it. case it of
    Array e => expr_writes_ok G e
  | Range lo hi => expr_writes_ok G lo /\ expr_writes_ok G hi``;
val mutations = ``\(addr:address). !cx target s pl t.
    cx.txn.target = addr /\ G target /\
    eval_target_place cx target s = (INL pl,t) /\ ^cell s /\ ^cell t ==>
    (!v. state_rel_frame ^observation (write_place cx pl v)) /\
    (!v. state_rel_frame ^observation (append_place cx pl v)) /\
    state_rel_frame ^observation (pop_place cx pl)``;
val live_callables = ``
  !sid fn ts mut nr args ds rt b.
    P (sid,fn) /\ M sid = SOME ts /\
    lookup_callable_function deploy fn ts = SOME (mut,nr,args,ds,rt,b) ==>
    EVERY (expr_writes_ok G) ds /\ stmts_writes_ok G b /\
    EVERY P (function_int_calls ds b)``;

val every_calls_exprs = SIMP_CONV (srw_ss())
  [int_calls_exprs_FLAT_MAP, EVERY_FLAT, EVERY_MAP]
  ``EVERY P (int_calls_exprs es)``;

val observation_target_bind = BETA_RULE
  (INST [``P : evaluation_state -> bool`` |-> cell]
    state_rel_frame_eval_target_bind);

Theorem live_callable_guards[local]:
  ^live_callables /\ ^code cx /\ P (sid,fn) /\
  lift_option_type (get_module_code cx sid) msg s = (INL ts,t) /\
  lift_option_type (lookup_callable_function cx.in_deploy fn ts) msg' s' =
    (INL (mut,nr,args,ds,rt,b),t') ==>
  EVERY (expr_writes_ok G) ds /\ stmts_writes_ok G b /\
  EVERY P (int_calls_exprs ds) /\ EVERY P (int_calls_stmts b)
Proof
  simp[lift_option_type_INL_eq, function_int_calls_def, EVERY_APPEND] >>
  rpt strip_tac >>
  qpat_x_assum `get_module_code cx sid = SOME ts` mp_tac >>
  qpat_x_assum `lookup_callable_function cx.in_deploy _ _ = _` mp_tac >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!sid fn ts mut nr args ds rt b. _`
    (drule_all_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

val live_module_code_stk =
  PURE_REWRITE_RULE [GSYM FUN_EQ_THM] get_module_code_stk_irrelevant;

val observation_net =
  let
    val leaves = [machine_frame_primitives, machine_frame_read_result,
      machine_frame_read_results, machine_frame_reads, machine_frame_select_result,
      machine_frame_extend_place, machine_frame_get_place, machine_frame_read_place,
      machine_frame_place_type_value, machine_frame_new_variable,
      machine_frame_next_gas_reading, machine_frame_precompile_call_success,
      machine_frame_handlers, machine_frame_push_function,
      machine_frame_pop_function, machine_frame_unchanged_reads,
      machine_frame_array_iterator_results]
    fun leaf th = (subst [``machine_frame`` |-> observation] (concl th),
      irule state_rel_frame_machine >> conj_tac
      >- simp[machine_frame_def] >> MATCH_ACCEPT_TAC th)
  in evalWalkLib.walk_net
    (map SPEC_ALL [state_rel_frame_bind_guarded, state_rel_frame_try,
      state_rel_frame_finally, state_rel_frame_finally_unless_halt])
    (map leaf (List.concat (map (CONJUNCTS o SPEC_ALL) leaves))) end;

val live_context_simps = [live_module_code_stk, oneTheory.one,
  ignore_bind_def, FST, SND, pair_case_thm, UNCURRY];
val LIVE_IH = evalWalkLib.IH_TAC {stop = K false,
  normalise = SIMP_RULE bool_ss live_context_simps};
val LIVE_FORWARD_IH = evalWalkLib.FORWARD_IH_TAC
  {normalise = SIMP_RULE (srw_ss()) live_context_simps};
val live_syntax = [int_calls_expr_def, int_calls_stmt_def, int_calls_iterator_def,
  int_calls_assert_reason_def, int_calls_raise_reason_def, int_calls_atarget_def,
  stmt_writes_ok_def, expr_writes_ok_def, atarget_writes_ok_def,
  GSYM int_calls_exprs_MAP_SND, EVERY_APPEND, EVERY_DEF, SF ETA_ss];
val LIVE_TRANSITIVITY =
  qmatch_goalsub_abbrev_tac `!s t u. R s t /\ R t u ==> R s u` >>
  simp[Abbr `R`];
val LIVE_TARGET =
  conj_tac >- LIVE_IH >> BETA_TAC >> rpt strip_tac >>
  qpat_assum `!cx target s pl t. _ /\ _ /\ eval_target_place cx target s = _ /\ _ ==> _`
    (drule_at_then (Pat `eval_target_place _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac;
val LIVE_STEP = IF (MATCH_MP_TAC observation_target_bind) LIVE_TARGET
  (evalWalkLib.STEP
    {net = observation_net, at = RAND_CONV,
     unfolds = [switch_BoolV_def, ignore_bind_def, check_not_static_def,
       vyperCreateTheory.eval_create_operands_def],
     intros = [LIVE_TRANSITIVITY, CONV_TAC (HO_REWR_CONV FORALL_PROD),
       gen_tac, strip_tac, conj_tac, CONV_TAC (RAND_CONV ETA_CONV)],
     fallbacks = [LIVE_IH, evalWalkLib.NORMALISE_IH_TAC LIVE_IH]});
val LIVE_CASE = evalWalkLib.EVAL_CASE all_tac LIVE_STEP;
val LIVE_ATOMIC = simp_tac (srw_ss()) [observation_result,
  return_def, raise_def, push_log_def, update_accounts_def,
  update_pending_deletions_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[eval_ext_call_preserves_non_accounts, eval_raw_call_preserves_non_accounts,
    eval_send_preserves_non_accounts, eval_create_preserves_scopes_immutables,
    transfer_value_immutables];
val LIVE_CUSTOM = LIVE_CASE >>
  qmatch_goalsub_rename_tac `eval_exprs cx ordered` >>
  drule order_custom_error_args_perm >> strip_tac >>
  `EVERY P (int_calls_exprs ordered)` by
    (simp[every_calls_exprs] >>
     qpat_x_assum `EVERY P (int_calls_exprs (custom_error_exprs _))` mp_tac >>
     simp[every_calls_exprs] >> metis_tac[PERM_EVERY]) >>
  `EVERY (expr_writes_ok G) ordered` by metis_tac[PERM_EVERY] >> LIVE_IH;
val LIVE_SIMPLE = LIVE_CASE >>
  (first_assum ACCEPT_TAC ORELSE simp[observation_result, return_def, raise_def]);
fun LIVE_EXPR_CHUNK (g as (_,w)) =
  case strip_comb (rand w) of
    (head,[_,chunk]) =>
      if aconv head ``eval_exprs`` then
        (`EVERY P (int_calls_exprs ^chunk) /\ EVERY (expr_writes_ok G) ^chunk` by
           (fs[every_calls_exprs] >> conj_tac >>
            rpt (FIRST [irule EVERY_TAKE, irule EVERY_DROP]) >> first_assum ACCEPT_TAC) >>
         LIVE_IH) g
      else LIVE_ATOMIC g
  | _ => LIVE_ATOMIC g;

Theorem live_guarded_observation_mutual[local]:
  ^live_callables /\ ^mutations addr ==>
  (!cx s. ^code cx /\ EVERY P (int_calls_stmt s) /\ stmt_writes_ok G s ==>
     state_rel_frame ^observation (eval_stmt cx s)) /\
  (!cx ss. ^code cx /\ EVERY P (int_calls_stmts ss) /\ stmts_writes_ok G ss ==>
     state_rel_frame ^observation (eval_stmts cx ss)) /\
  (!cx it. ^code cx /\ EVERY P (int_calls_iterator it) /\ ^iterator_writes it ==>
     state_rel_frame ^observation (eval_iterator cx it)) /\
  (!cx tyv nm bod vs. ^code cx /\ EVERY P (int_calls_stmts bod) /\
                     stmts_writes_ok G bod ==>
     state_rel_frame ^observation (eval_for cx tyv nm bod vs)) /\
  (!cx e. ^code cx /\ EVERY P (int_calls_expr e) /\ expr_writes_ok G e ==>
     state_rel_frame ^observation (eval_expr cx e)) /\
  (!cx es. ^code cx /\ EVERY P (int_calls_exprs es) /\ EVERY (expr_writes_ok G) es ==>
     state_rel_frame ^observation (eval_exprs cx es)) /\
  (!cx t. ^code cx /\ EVERY P (int_calls_target t) /\ target_writes_ok G t ==>
     state_rel_frame ^observation (eval_base_place cx t)) /\
  (!cx t. ^code cx /\ EVERY P (int_calls_target t) /\ target_writes_ok G t ==>
     state_rel_frame ^observation (eval_target_place cx t)) /\
  (!cx g v. ^code cx /\ EVERY P (int_calls_atarget g) /\ atarget_writes_ok G g ==>
     state_rel_frame ^observation (assign_tuple_targets cx g v)) /\
  (!cx gs vs. ^code cx /\ EVERY P (int_calls_atargets gs) /\
              EVERY (atarget_writes_ok G) gs ==>
     state_rel_frame ^observation (assign_tuple_target_list cx gs vs))
Proof
  BETA_TAC >> strip_tac >> ho_match_mp_tac evaluate_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp_tac (srw_ss()) live_syntax >> rpt strip_tac >>
  all_tac
  >~ [`eval_expr _ (Call _ (IntCall _) _ _)`] >- suspend "intcall"
  >~ [`eval_expr _ (Builtin _ _ _)`] >- suspend "builtin"
  >~ [`eval_expr _ (Call _ (CreateTarget _ _ _ _) _ _)`] >- suspend "create"
  >~ [`eval_expr _ (Call _ RawLog _ _)`] >- suspend "rawlog"
  >~ [`eval_stmt _ (Raise (RaiseCustomError _))`] >- LIVE_CUSTOM
  >~ [`eval_stmt _ (Assert _ (AssertCustomError _))`] >- LIVE_CUSTOM
  >~ [`eval_expr _ (StructLit _ _ _)`] >- (fs[SF ETA_ss] >> LIVE_SIMPLE)
  >~ [`eval_expr _ (TypeBuiltin _ _ _ _)`] >- (fs[SF ETA_ss] >> LIVE_SIMPLE)
  >~ [`eval_stmt _ (Log _ _)`] >- (LIVE_CASE >> LIVE_ATOMIC)
  >~ [`eval_expr _ (Call _ (Send _) _ _)`] >- (LIVE_CASE >> LIVE_ATOMIC)
  >~ [`eval_expr _ (Call _ (ExtCall _ _ _ _) _ _)`] >- (LIVE_CASE >> LIVE_EXPR_CHUNK)
  >~ [`eval_expr _ (Call _ (RawCallTarget _) _ _)`] >- (LIVE_CASE >> LIVE_ATOMIC)
  >~ [`eval_expr _ (Call _ (RawCallCalldataTarget _) _ _)`] >- (LIVE_CASE >> LIVE_ATOMIC)
  >~ [`eval_expr _ (Call _ SelfDestructTarget _ _)`] >- (LIVE_CASE >> LIVE_ATOMIC) >>
  LIVE_SIMPLE
QED

Resume live_guarded_observation_mutual[builtin]:
  LIVE_CASE
  >- (gvs[type_check_def, assert_def, check_def, return_def, raise_def] >>
      Cases_on `es` >> gvs[builtin_args_length_ok_def, int_calls_expr_def,
                            EVERY_APPEND]) >>
  gvs[type_check_def, assert_def, check_def, return_def, raise_def,
      code_slice_source_SOME, expr_writes_ok_def, int_calls_expr_def, EVERY_APPEND,
      DISJ_IMP_THM, FORALL_AND_THM, AllCaseEqs()] >> LIVE_IH
QED

Resume live_guarded_observation_mutual[create]:
  LIVE_CASE >>
  all_tac >>~- ([`state_rel_frame _ (eval_create _ _ _ _ _ _ _)`], LIVE_ATOMIC) >>
  rename1 `state_rel_frame _ (eval_exprs cx (create_operand_order kind has_salt es))` >>
  `EVERY P (int_calls_exprs (create_operand_order kind has_salt es)) /\
   EVERY (expr_writes_ok G) (create_operand_order kind has_salt es)` by
    (simp[every_calls_exprs] >> fs[every_calls_exprs] >>
     Cases_on `kind` >> Cases_on `es` >>
     gvs[vyperCreateTheory.create_operand_order_def, EVERY_TAKE, EVERY_DROP] >>
     rename1 `EVERY _ rest` >> Cases_on `rest` >>
     gvs[vyperCreateTheory.create_operand_order_def, EVERY_TAKE, EVERY_DROP]) >>
  LIVE_IH
QED

Resume live_guarded_observation_mutual[rawlog]:
  simp_tac bool_ss [Once evaluate_def] >>
  MATCH_MP_TAC state_rel_frame_bind_guarded >> conj_tac >- LIVE_TRANSITIVITY >>
  conj_tac >- LIVE_IH >> rpt gen_tac >> strip_tac >>
  simp[observation_result, bind_def, ignore_bind_def, type_check_def,
       assert_def, check_def, return_def, raise_def, lift_option_type_def,
       check_not_static_def, push_log_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `dest_ArrayV (HD v)` >> gvs[return_def, raise_def] >>
  Cases_on `dest_BytesV (EL 1 v)` >> gvs[return_def, raise_def] >> fs[]
QED

Resume live_guarded_observation_mutual[intcall]:
  simp_tac bool_ss [Once evaluate_def] >>
  ntac 25 LIVE_STEP >> rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [LET_THM, FST, SND] >>
  rename1 `INL (imut,inr,iargs,idflts,iretty,ibody)` >>
  drule_all_then strip_assume_tac (BETA_RULE live_callable_guards) >>
  `!n. EVERY (expr_writes_ok G) (DROP n idflts) /\
       EVERY P (int_calls_exprs (DROP n idflts))` by
    fs[every_calls_exprs, EVERY_DROP] >>
  ntac 5 LIVE_STEP >> strip_tac >> LIVE_STEP >>
  LIVE_STEP >- LIVE_TRANSITIVITY
  >- (gvs[type_check_def, assert_def, return_def, raise_def] >> LIVE_IH) >>
  ntac 18 LIVE_STEP
  >- (rpt strip_tac >>
      gvs[live_module_code_stk, lift_option_type_INL_eq,
          type_check_def, assert_def, return_def, raise_def] >> LIVE_FORWARD_IH) >>
  rpt (CHANGED_TAC LIVE_STEP) >>
  simp_tac bool_ss [lock_if_nr_def, unlock_if_nr_def]
  >- (POP_ASSUM_LIST (K all_tac) >>
      rewrite_tac[observation_result] >> rpt gen_tac >> strip_tac >>
      Cases_on `inr` >> Cases_on `cx.nonreentrant_slot` >>
      gvs[return_def, raise_def] >>
      rename1 `acquire_nonreentrant_lock _ slot _` >>
      Cases_on `acquire_nonreentrant_lock cx.txn.target slot
        (is_view_mut imut \/ cx.txn.is_static) st` >>
      drule acquire_nonreentrant_lock_immutables >>
      Cases_on `imut = View \/ imut = Pure` >>
      gvs[is_view_mut_def, ignore_bind_def, bind_def, check_not_static_def,
          type_check_def, assert_def, check_def, return_def, raise_def,
          AllCaseEqs()] >> strip_tac >> simp[])
  >~ [`state_rel_frame _ (eval_stmts _ _)`]
  >- (qmatch_asmsub_rename_tac `push_function (sid,fn) env cx ps = (INL cxf,pt)` >>
      `cxf = cx with stk updated_by CONS (sid,fn)` by
        (qpat_x_assum `push_function _ _ _ _ = _` mp_tac >> simp[push_function_def, return_def]) >>
      gvs[live_module_code_stk] >> LIVE_FORWARD_IH) >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[observation_result] >> rpt gen_tac >> strip_tac >>
  Cases_on `inr /\ imut <> View /\ imut <> Pure` >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
  drule release_nonreentrant_lock_immutables >> simp[]
QED

Finalise live_guarded_observation_mutual[local]

Theorem live_guarded_list_observation_frames:
  ^live_callables /\ ^mutations addr ==>
  (!cx es. ^code cx /\ EVERY P (int_calls_exprs es) /\ EVERY (expr_writes_ok G) es ==>
     state_rel_frame ^observation (eval_exprs cx es)) /\
  (!cx ss. ^code cx /\ EVERY P (int_calls_stmts ss) /\ stmts_writes_ok G ss ==>
     state_rel_frame ^observation (eval_stmts cx ss))
Proof
  BETA_TAC >> strip_tac >>
  mp_tac (BETA_RULE live_guarded_observation_mutual) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> conj_tac >> first_assum ACCEPT_TAC
QED
