Theory vyperLogPreservation

Ancestors
  pair option sum vyperMisc vyperCall vyperStatePreservation vyperCallFrame vyperCallOutcomeFrame
  vyperState[ignore_grammar] vyperInterpreter[ignore_grammar] vyperCallOutcome[ignore_grammar] vyperCallOutcomeProps[ignore_grammar]
  vyperCreate vyperCreateFrame vyperTypeExternalDefaults vyperPlaceFrames
  vyperMachineFrame vyperEvalFrame

(* Keep existing free statement-list variables when importing oracle grammar. *)
val _ = hide "body";

Definition log_extends_def:
  log_extends (st:evaluation_state) (st':evaluation_state) <=>
    isPREFIX st.logs st'.logs
End

Theorem log_extends_refl:
  log_extends st st
Proof
  simp[log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem log_extends_trans:
  log_extends st st1 /\ log_extends st1 st2 ==> log_extends st st2
Proof
  simp[log_extends_def] >> metis_tac[rich_listTheory.IS_PREFIX_TRANS]
QED

Theorem log_extends_eq_logs:
  st.logs = st'.logs ==> log_extends st st'
Proof
  simp[log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem log_extends_append:
  log_extends st (st with logs := st.logs ++ events)
Proof
  simp[log_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem push_log_log_extends[local]:
  push_log ev st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> gvs[push_log_logs] >> simp[log_extends_append]
QED

Theorem set_scopes_logs[local]:
  set_scopes env st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  gvs[vyperStateTheory.set_scopes_def, vyperStateTheory.return_def]
QED

Theorem set_address_immutables_logs[local]:
  set_address_immutables cx imms st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  gvs[vyperStateTheory.set_address_immutables_def,
      vyperStateTheory.return_def]
QED

Theorem set_storage_backend_logs[local]:
  set_storage_backend cx is_transient storage st = (res,st') ==>
    st'.logs = st.logs
Proof
  Cases_on `is_transient` >> rpt strip_tac >>
  gvs[vyperStateTheory.set_storage_backend_def, vyperStateTheory.bind_def,
      vyperStateTheory.update_transient_def,
      vyperStateTheory.update_accounts_def,
      vyperStateTheory.get_accounts_def, vyperStateTheory.return_def,
      AllCaseEqs()]
QED

Theorem write_storage_slot_logs[local]:
  write_storage_slot cx is_transient slot tv v st = (res,st') ==>
    st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.write_storage_slot_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  imp_res_tac set_storage_backend_logs >> gvs[]
QED

Theorem set_immutable_logs[local]:
  set_immutable cx src n tv v st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `set_immutable _ _ _ _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.set_immutable_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_address_immutables_state >> gvs[] >>
  imp_res_tac set_address_immutables_logs >> gvs[]
QED

Theorem append_place_logs[local]:
  append_place cx p v st = (res,st') ==> st'.logs = st.logs
Proof
  Cases_on `p` >- (
    rename1 `StoragePlace tr slot tv` >>
    Cases_on `tv` >> simp[vyperStateTheory.append_place_def] >>
    TRY (rename1 `ArrayTV et bound` >> Cases_on `bound`) >>
    simp[vyperStateTheory.append_place_def] >>
    gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
        vyperStateTheory.check_def, vyperStateTheory.assert_def,
        vyperStateTheory.return_def, vyperStateTheory.raise_def,
        AllCaseEqs()] >> rpt strip_tac >>
    imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
    imp_res_tac place_type_value_state >> imp_res_tac read_place_state >>
    imp_res_tac lift_sum_state >> imp_res_tac write_place_logs >>
    imp_res_tac write_storage_slot_logs >> gvs[]) >>
  simp[vyperStateTheory.append_place_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac place_type_value_state >> imp_res_tac read_place_state >>
  imp_res_tac lift_sum_state >> imp_res_tac write_place_logs >> gvs[]
QED

Theorem pop_place_logs[local]:
  pop_place cx p st = (res,st') ==> st'.logs = st.logs
Proof
  Cases_on `p` >- (
    rename1 `StoragePlace tr slot tv` >>
    Cases_on `tv` >> simp[vyperStateTheory.pop_place_def] >>
    TRY (rename1 `ArrayTV et bound` >> Cases_on `bound`) >>
    simp[vyperStateTheory.pop_place_def, vyperStateTheory.bind_def,
         vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
         vyperStateTheory.assert_def, vyperStateTheory.return_def,
         vyperStateTheory.raise_def, AllCaseEqs()] >> rpt strip_tac >>
    imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
    imp_res_tac write_storage_slot_logs >> gvs[]) >>
  simp[vyperStateTheory.pop_place_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.get_scopes_def,
       vyperStateTheory.type_check_def, vyperStateTheory.check_def,
       vyperStateTheory.assert_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, UNCURRY, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac lift_option_type_state >> imp_res_tac lift_sum_state >>
  imp_res_tac get_immutables_state >>
  imp_res_tac set_scopes_logs >> imp_res_tac set_immutable_logs >> gvs[]
QED

Theorem transfer_value_logs[local]:
  transfer_value fromAddr toAddr amount st = (res,st') ==>
  st'.logs = st.logs
Proof

  strip_tac >> drule concrete_send_step_locals >> simp[]
QED

Theorem eval_send_log_extends:
  eval_send cx has_gas vs st = (res,st') ==> log_extends st st'
Proof
  Cases_on `vs` >- simp[eval_send_def, raise_def, log_extends_refl] >>
  Cases_on `t` >- simp[eval_send_def, raise_def, log_extends_refl] >>
  simp[eval_send_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def,
       get_transient_storage_def, lift_option_def, lift_option_type_def,
       check_def, update_accounts_def, update_transient_def, append_logs_def,
       vyperCallOutcomeTheory.take_call_outcome_def,
       vyperCallOutcomeTheory.adopt_call_outcome_equation, LET_THM, UNCURRY,
       COND_RATOR, option_CASE_rator, prod_CASE_rator, sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >> imp_res_tac frame_call_value_state >>
  gvs[log_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

(* Compositional proof control for the actual activated call clause. *)
Definition log_monad_def:
  log_monad f <=> !s r t. f s = (r,t) ==> log_extends s t
End

Theorem log_monad_bind_guarded[local]:
  log_monad f /\
  (!s v t. f s = (INL v,t) ==> log_monad (g v)) ==>
  log_monad (vyperState$bind f g)
Proof
  simp[log_monad_def, vyperStateTheory.bind_def] >> rpt strip_tac >>
  Cases_on `f s` >> Cases_on `q` >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all log_extends_trans >> simp[]
QED

Theorem log_monad_primitives[local]:
  log_monad (return v) /\ log_monad (\s. return (g s) s) /\
  log_monad (raise e) /\
  log_monad (type_check b msg) /\ log_monad (check b msg) /\
  log_monad (lift_option opt msg) /\ log_monad (lift_option_type opt msg) /\
  log_monad (lift_sum_runtime rs) /\ log_monad get_accounts /\
  log_monad get_transient_storage /\ log_monad (update_accounts upd) /\
  log_monad (update_transient upd_t) /\ log_monad (append_logs logs) /\
  log_monad (adopt_call_outcome rq co)
Proof
  simp[log_monad_def, vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vyperStateTheory.check_def, vyperStateTheory.type_check_def,
       vyperStateTheory.assert_def, vyperStateTheory.lift_option_def,
       vyperStateTheory.lift_option_type_def, vyperStateTheory.lift_sum_runtime_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_accounts_def, vyperStateTheory.update_transient_def,
       append_logs_def, adopt_call_outcome_equation] >>
  rpt strip_tac >> rpt CASE_TAC >>
  gvs[option_CASE_rator, sum_CASE_rator, AllCaseEqs(),
      vyperStateTheory.return_def, vyperStateTheory.raise_def,
      log_extends_def, rich_listTheory.IS_PREFIX_APPEND,
      rich_listTheory.IS_PREFIX_REFL]
QED

Theorem log_monad_take[local]:
  log_monad (take_call_outcome target calldata value_opt)
Proof
  simp[log_monad_def] >> rpt strip_tac >>
  drule take_call_outcome_frame >>
  simp[evaluation_state_component_equality, log_extends_def,
       rich_listTheory.IS_PREFIX_REFL]
QED

Theorem log_monad_frame_call_value[local]:
  log_monad (frame_call_value cx value_opt)
Proof
  simp[log_monad_def] >> rpt strip_tac >>
  drule frame_call_value_state >> simp[log_extends_refl]
QED

(* Index primitive leaves once; never traverse their continuations or the
   large guarded IHs just to recognise a primitive computation. *)
val EXTCALL_LOG_MONAD_LEAF_TAC =
  let
    val structural = Net.insert
      (concl log_monad_bind_guarded |> dest_imp |> snd,
       MATCH_MP_TAC log_monad_bind_guarded >> conj_tac) Net.empty
    val leaves = List.foldl (fn (th,net) =>
      Net.insert (concl th, MATCH_ACCEPT_TAC th) net) structural
      (log_monad_take :: log_monad_frame_call_value ::
       CONJUNCTS log_monad_primitives)
  in
    fn (asl,w) => FIRST (Net.match w leaves) (asl,w)
  end;

(* Reduce exposed applications only, not continuation arguments. *)
val extcall_log_head_conv =
  let
    val reduce = FIRST_CONV
      [BETA_CONV, REWR_CONV pair_case_thm, REWR_CONV UNCURRY]
    fun head tm = (reduce ORELSEC RATOR_CONV head) tm
  in head end;

(* Preserve CASE_TAC branch order without its broad datatype rewrite set.
   Only fresh branch facts, never guarded IHs, become rewrite rules. *)
fun EXTCALL_LOG_MONAD_CASE_TAC (g as (old,_)) =
  let
    fun simplify (asl,w) =
      let
        val fresh = List.filter (fn a => not (is_forall a) andalso
          not (List.exists (aconv a) old)) asl
        val rules = map ASSUME fresh
      in
        simp_tac bool_ss
          (optionTheory.option_CLAUSES :: pair_case_thm :: UNCURRY :: rules) >>
        RULE_ASSUM_TAC (fn th =>
          if is_forall (concl th) then th else REWRITE_RULE rules th) >>
        MAP_EVERY assume_tac rules
      end (asl,w)
  in
    (BasicProvers.PURE_CASE_TAC >> simplify) g
  end;

val EXTCALL_LOG_MONAD_STEP_TAC =
  FIRST [
    first_assum ACCEPT_TAC,
    EXTCALL_LOG_MONAD_LEAF_TAC,
    CONV_TAC (HO_REWR_CONV FORALL_PROD),
    CONV_TAC (RAND_CONV extcall_log_head_conv),
    gen_tac, strip_tac, conj_tac,
    CONV_TAC (RAND_CONV (REWR_CONV vyperStateTheory.ignore_bind_def)),
    CONV_TAC (RAND_CONV ETA_CONV),
    CHANGED_TAC (fn (asl,w) =>
      simp_tac bool_ss (pair_case_thm :: UNCURRY ::
        List.map ASSUME (List.filter is_eq asl)) (asl,w)),
    EXTCALL_LOG_MONAD_CASE_TAC];

val EXTCALL_LOG_MONAD_TAC = rpt EXTCALL_LOG_MONAD_STEP_TAC;

Theorem eval_ext_call_log_monad[local]:
  log_monad (eval_ext_call cx static skip_check sig opts vs)
Proof
  PairCases_on `sig` >> Cases_on `vs` >>
  simp_tac bool_ss [eval_ext_call_def, eval_ext_call_effects_def, LET_THM] >>
  EXTCALL_LOG_MONAD_TAC
QED

Theorem eval_ext_call_log_extends:
  eval_ext_call cx static skip_check sig opts vs st = (res,st') ==>
  log_extends st st'
Proof
  mp_tac (REWRITE_RULE [log_monad_def] eval_ext_call_log_monad) >> simp[]
QED

Theorem eval_raw_call_log_extends:
  eval_raw_call cx flags target_addr calldata amount gas st = (res,st') ==>
  log_extends st st'
Proof
  simp[eval_raw_call_def, check_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def,
       get_transient_storage_def, lift_option_def, update_accounts_def,
       update_transient_def, append_logs_def,
       vyperCallOutcomeTheory.take_call_outcome_def,
       vyperCallOutcomeTheory.adopt_call_outcome_equation, LET_THM, UNCURRY,
       COND_RATOR, option_CASE_rator, prod_CASE_rator, sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >> imp_res_tac frame_call_value_state >>
  gvs[log_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem acquire_nonreentrant_lock_logs[local]:
  acquire_nonreentrant_lock addr slot is_view st = (res,st') ==>
  st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.acquire_nonreentrant_lock_def,
       vyperStateTheory.bind_def, vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_transient_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `lookup_storage (n2w slot)
              (vfmExecution$lookup_transient_storage addr st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  gvs[vyperStateTheory.update_transient_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def]
QED

Theorem release_nonreentrant_lock_logs[local]:
  release_nonreentrant_lock addr slot st = (res,st') ==>
  st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `release_nonreentrant_lock _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.release_nonreentrant_lock_def,
       vyperStateTheory.bind_def, vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_transient_def, vyperStateTheory.return_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem entry_lock_action_logs[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => do
         acquire_nonreentrant_lock cx.txn.target slot
           (is_view \/ cx.txn.is_static);
         if is_view then return () else check_not_static cx
       od
   else return ()) st = (res,st') ==>
  st'.logs = st.logs
Proof
  Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def,
       COND_RATOR, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac acquire_nonreentrant_lock_logs >> gvs[]
QED

Theorem log_extends_eval_frame[local]:
  (!s t u. log_extends s t /\ log_extends t u ==> log_extends s u) /\
  (!s t. machine_frame s t ==> log_extends s t) /\
  (!cx p v. state_rel_frame log_extends (write_place cx p v)) /\
  (!cx p v. state_rel_frame log_extends (append_place cx p v)) /\
  (!cx p. state_rel_frame log_extends (pop_place cx p)) /\
  (!ev. state_rel_frame log_extends (push_log ev)) /\
  (!a b n. state_rel_frame log_extends (transfer_value a b n)) /\
  (!cx g vs. state_rel_frame log_extends (eval_send cx g vs)) /\
  (!cx st sk sig opts vs.
     state_rel_frame log_extends (eval_ext_call cx st sk sig opts vs)) /\
  (!cx fl a d m g. state_rel_frame log_extends (eval_raw_call cx fl a d m g)) /\
  (!cx k h r ts vs cs.
     state_rel_frame log_extends (eval_create cx k h r ts vs cs)) /\
  (!a n v. state_rel_frame log_extends (acquire_nonreentrant_lock a n v)) /\
  (!a n. state_rel_frame log_extends (release_nonreentrant_lock a n))
Proof
  rewrite_tac[state_rel_frame_result] >> rpt conj_tac >> rpt gen_tac
  >- metis_tac[log_extends_trans]
  >- simp[machine_frame_def, log_extends_eq_logs]
  >- metis_tac[write_place_logs, log_extends_eq_logs]
  >- metis_tac[append_place_logs, log_extends_eq_logs]
  >- metis_tac[pop_place_logs, log_extends_eq_logs]
  >- metis_tac[push_log_log_extends]
  >- metis_tac[transfer_value_logs, log_extends_eq_logs]
  >- metis_tac[eval_send_log_extends]
  >- metis_tac[eval_ext_call_log_extends]
  >- metis_tac[eval_raw_call_log_extends]
  >- metis_tac[eval_create_logs_extend, log_extends_def]
  >- metis_tac[acquire_nonreentrant_lock_logs, log_extends_eq_logs] >>
  metis_tac[release_nonreentrant_lock_logs, log_extends_eq_logs]
QED

Theorem eval_mutual_log_extends =
  REWRITE_RULE [state_rel_frame_result]
    (MATCH_MP eval_state_rel_frame log_extends_eval_frame);

Theorem eval_expr_results_log_extends:
  eval_expr_results cx es st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED

Theorem eval_stmt_log_extends:
  !cx s st res st'.
    eval_stmt cx s st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED

Theorem eval_expr_log_extends:
  !cx e st res st'.
    eval_expr cx e st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED

Theorem eval_exprs_log_extends:
  !cx es st res st'.
    eval_exprs cx es st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED

Theorem eval_stmts_log_extends:
  !cx ss st res st'.
    eval_stmts cx ss st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED

Definition machine_log_extends_def:
  machine_log_extends (am:abstract_machine) (am':abstract_machine) <=>
    isPREFIX am.logs am'.logs
End

Theorem machine_log_extends_refl:
  machine_log_extends am am
Proof
  simp[machine_log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem machine_log_extends_trans:
  machine_log_extends am am1 /\ machine_log_extends am1 am2 ==>
  machine_log_extends am am2
Proof
  simp[machine_log_extends_def] >>
  metis_tac[rich_listTheory.IS_PREFIX_TRANS]
QED

Theorem machine_log_extends_eq_logs:
  am.logs = am'.logs ==> machine_log_extends am am'
Proof
  simp[machine_log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem abstract_machine_from_state_logs[simp]:
  (abstract_machine_from_state srcs exps layouts st).logs = st.logs
Proof
  simp[vyperInterpreterTheory.abstract_machine_from_state_def]
QED

Theorem merge_constants_logs[local]:
  (merge_constants addr src_id_opt cenv am).logs = am.logs
Proof
  simp[vyperInterpreterTheory.merge_constants_def]
QED

Theorem evaluate_all_constants_logs:
  evaluate_all_constants cx am addr mods = SOME am' ==> am'.logs = am.logs
Proof
  simp[vyperInterpreterTheory.evaluate_all_constants_def] >>
  qid_spec_tac `am` >>
  qspec_tac (`constants_order mods`, `mods`) >> Induct >-
    simp[vyperInterpreterTheory.evaluate_module_constants_def] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[vyperInterpreterTheory.evaluate_module_constants_def, AllCaseEqs()] >>
  rpt strip_tac >>
  first_x_assum drule >>
  simp[merge_constants_logs]
QED

Theorem send_call_value_logs[local]:
  send_call_value mut cx st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `send_call_value _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.send_call_value_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `cx.txn.value = 0` >> Cases_on `mut = Payable` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.check_def, vyperStateTheory.assert_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  imp_res_tac transfer_value_logs >> gvs[]
QED

Theorem external_unlock_action_logs[local]:
  (if nr /\ mut <> View /\ mut <> Pure then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st = (res,st') ==>
  st'.logs = st.logs
Proof
  Cases_on `nr` >> Cases_on `mut = View` >> Cases_on `mut = Pure` >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[vyperStateTheory.return_def] >>
  metis_tac[release_nonreentrant_lock_logs]
QED

Theorem eval_external_defaults_log_extends[local]:
  eval_external_defaults cx es st = (res,st') ==> log_extends st st'
Proof
  simp[vyperInterpreterTheory.eval_external_defaults_run] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  simp[] >> strip_tac >> gvs[] >>
  drule eval_exprs_log_extends >> simp[log_extends_def]
QED

Theorem call_body_pipeline_log_extends[local]:
  (do lock_action; eval_stmts cx body od) st = (res,st') ==>
  (!s0 r s1. lock_action s0 = (r,s1) ==> s1.logs = s0.logs) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `(do lock_action; eval_stmts _ _ od) _ = _` mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac eval_stmts_log_extends >>
  metis_tac[log_extends_eq_logs, log_extends_trans]
QED

Theorem call_external_function_success_log_extends:
  call_external_function orc gobs am cx nr mut ts all_mods args dflts vals body ret =
    (INL v,am',rqs) ==>
  machine_log_extends am am'
Proof
  strip_tac >> drule call_external_function_success_phases >> strip_tac >>
  drule call_body_pipeline_log_extends >>
  (impl_tac >- (rpt strip_tac >> imp_res_tac entry_lock_action_logs)) >>
  strip_tac >>
  drule eval_external_defaults_log_extends >> strip_tac >>
  imp_res_tac send_call_value_logs >>
  imp_res_tac external_unlock_action_logs >>
  `am_c.logs = am.logs` by
    (Cases_on `cx.in_deploy` >> gvs[] >>
     imp_res_tac evaluate_all_constants_logs >> gvs[]) >>
  gvs[machine_log_extends_def, log_extends_def,
      vyperInterpreterTheory.initial_state_def,
      vyperInterpreterTheory.abstract_machine_from_state_def] >>
  drule external_unlock_action_logs >> strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  gvs[] >> metis_tac[rich_listTheory.IS_PREFIX_TRANS]
QED

Theorem call_external_success_log_extends:
  call_external orc gobs am tx = (INL v,am',rqs) ==> machine_log_extends am am'
Proof
  rpt strip_tac >>
  qpat_x_assum `call_external _ _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.call_external_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac call_external_function_success_log_extends >>
  gvs[machine_log_extends_def, vyperInterpreterTheory.finalize_pending_deletions_def]
QED

Theorem call_external_function_error_logs_rollback:
  call_external_function orc gobs am cx nr mut ts all_mods args dflts vals body ret =
    (INR e,am',rqs) ==>
  am'.logs = am.logs
Proof
  strip_tac >> imp_res_tac call_external_function_error_rollback >> gvs[]
QED

Theorem call_external_error_logs_rollback:
  call_external orc gobs am tx = (INR e,am',rqs) ==> am'.logs = am.logs
Proof
  strip_tac >> imp_res_tac call_external_error_rollback >> gvs[]
QED

Theorem call_external_log_extends:
  call_external orc gobs am tx = (res,am',rqs) ==> machine_log_extends am am'
Proof
  Cases_on `res` >> strip_tac >-
    (imp_res_tac call_external_success_log_extends) >>
  imp_res_tac call_external_error_logs_rollback >>
  simp[machine_log_extends_eq_logs]
QED

Theorem call_external_transaction_log_extends_empty:
  call_external_transaction orc gobs am tx = (res,am',rqs) ==>
  isPREFIX [] am'.logs
Proof
  simp[]
QED

Theorem call_external_transaction_success_fresh:
  call_external_transaction orc gobs am tx = (INL v,am',rqs) ==>
  call_external orc gobs (clear_machine_logs am) tx = (INL v,am',rqs) /\
  machine_log_extends (clear_machine_logs am) am'
Proof
  simp[vyperInterpreterTheory.call_external_transaction_def] >>
  metis_tac[call_external_log_extends]
QED

(* Integration audit: all log preservation exports must be kernel closed. *)
val () = List.app (fn (name,th) =>
  let val (oracles,_) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Log preservation oracle debt: " ^ name)
  end) (DB.thms "vyperLogPreservation");

Theorem log_extends_outcome_rules[local]:
  (!s. log_extends s s) /\
  (!s t u. log_extends s t /\ log_extends t u ==> log_extends s u) /\
  (!s os rqs. log_extends s (s with <|outcomes := os; requests := rqs|>)) /\
  (!s accounts transient logs pending. log_extends s
     (s with <|accounts := accounts; tStorage := transient;
               logs := s.logs ++ logs; pending_deletions := pending|>))
Proof
  rpt conj_tac
  >- simp[log_extends_refl]
  >- metis_tac[log_extends_trans]
  >- simp[log_extends_def, rich_listTheory.IS_PREFIX_REFL] >>
  simp[log_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem log_extends_final_frame:
  log_extends st mid /\ isPREFIX mid.logs st'.logs ==>
  log_extends st st'
Proof
  simp[log_extends_def] >> metis_tac[rich_listTheory.IS_PREFIX_TRANS]
QED

Theorem Send_outcome_log_extends:
  (do
    (rq,outcome) <- take_call_outcome target [] (SOME amount);
    check outcome.co_success "send failed";
    adopt_call_outcome rq outcome;
    return (Value NoneV)
  od) st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> strip_assume_tac log_extends_outcome_rules >>
  drule_all (Send_outcome_transport |> Q.INST [`R` |-> `log_extends`]) >> simp[]
QED

Theorem ExtCall_outcome_log_extends:
  (!bs s res t. k bs s = (res,t) ==> log_extends s t) /\
  (do
    accounts <- get_accounts;
    (if ret_type = NoneT then
       check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success "ExtCall reverted";
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = (res,st') ==> log_extends st st'
Proof
  rpt strip_tac >> strip_assume_tac log_extends_outcome_rules >>
  drule_all (ExtCall_outcome_transport |> Q.INST [`R` |-> `log_extends`]) >> simp[]
QED
