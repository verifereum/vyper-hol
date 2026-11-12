(*
 * The source side of the selected external call, and the guarded body's
 * code, as S1 (loweringRuntimeCorrect) and the counted body runs
 * (loweringPtrBodyRun, loweringMemBodyRun) use them.
 *
 * TOP-LEVEL:
 *   call_external_selected_body, call_external_selected_body_gas -- the
 *     source runs the selected body, at any gas observations
 *   send_call_value_with_scopes, send_call_value_with_gas_obs -- moving
 *     the value ignores scopes and gas observations
 *   type_stmts_none_valued_return -- a body typed at NoneT has no valued
 *     return
 *   guarded_body_code, guarded_body_stmts_env -- the guarded body's code
 *)

Theory externalCallSelected
Ancestors
  vyperState vyperContext vyperInterpreter vyperTypeSystem
  vyperTypeSelectedEntrySoundness e2eDefs supportedStmts
  compileEnv compileVyper stmtLowering stmtLoweringMono moduleLowering
  fragExec loweringPosts stmtSimProps bodySim stmtsEnvRetTy

val _ = Parse.hide "body";

(* send_call_value reads and writes only accounts, so it runs the same
   under any scopes. *)
Theorem send_call_value_with_scopes:
  !mut cx s r s'.
    send_call_value mut cx s = (r, s') ==>
    s'.scopes = s.scopes /\
    !sc. send_call_value mut cx (s with scopes := sc) =
         (r, s' with scopes := sc)
Proof
  rw[send_call_value_def, transfer_value_def, vyperStateTheory.bind_def,
     vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
     vyperStateTheory.assert_def, vyperStateTheory.return_def,
     vyperStateTheory.raise_def, vyperStateTheory.get_accounts_def,
     vyperStateTheory.update_accounts_def] >>
  gvs[AllCaseEqs()]
QED

(* Likewise under any gas observations. *)
Theorem send_call_value_with_gas_obs:
  !mut cx s r s'.
    send_call_value mut cx s = (r, s') ==>
    s'.gas_obs = s.gas_obs /\
    !gs. send_call_value mut cx (s with gas_obs := gs) =
         (r, s' with gas_obs := gs)
Proof
  rw[send_call_value_def, transfer_value_def, vyperStateTheory.bind_def,
     vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
     vyperStateTheory.assert_def, vyperStateTheory.return_def,
     vyperStateTheory.raise_def, vyperStateTheory.get_accounts_def,
     vyperStateTheory.update_accounts_def] >>
  gvs[AllCaseEqs()]
QED

(* call_external_body sets the scopes before it reads them. *)
Theorem call_external_body_scopes[local]:
  !am cx nr mut tenv s sc env body ret.
    call_external_body am cx nr mut tenv (s with scopes := sc) env body ret =
    call_external_body am cx nr mut tenv s env body ret
Proof
  simp[call_external_body_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.set_scopes_def]
QED

(* The call valid_vyper_call selects, at gas observations gobs, sends the
   call value and then runs call_external_body from the bound arguments,
   with pending deletions finalised on success and on halt.  es0 is the state after
   the value moved, as external_entry_reaches_body starts the body from
   it; the body starts from es0 with the call's observations. *)
Theorem call_external_selected_body_gas:
  !tops am tx ret mut args fbody env orc gobs es0.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INL (), es0) ==>
    call_external orc gobs am tx =
      case call_external_body am
             (initial_evaluation_context am.sources am.layouts tx NONE)
             F mut (type_env tops) (es0 with gas_obs := gobs) env fbody ret of
        (INL v, am', rqs) => (INL v, finalize_pending_deletions am', rqs)
      | (INR HaltException, am', rqs) =>
          (INR HaltException, finalize_pending_deletions am', rqs)
      | failure => failure
Proof
  rw[source_deployment_rel_def] >>
  `type_env_all_modules [(NONE, tops)] = type_env tops` by
    simp[type_env_all_modules_def, type_env_def] >>
  simp[call_external_def, find_function_module_def,
       lookup_exported_function_def, get_self_code_def, get_module_code_def,
       initial_evaluation_context_def] >>
  qmatch_goalsub_abbrev_tac `call_external_function orc gobs am cx` >>
  qabbrev_tac `es1 = (es0 with gas_obs := gobs) with scopes := [FEMPTY]` >>
  `send_call_value mut cx
     (initial_state am [FEMPTY] with
        <| outcomes := orc; requests := []; gas_obs := gobs |>) =
   (INL (), es1)` by
    (qpat_x_assum `send_call_value _ _ _ = _` mp_tac >>
     simp[Abbr `cx`, initial_evaluation_context_def] >> strip_tac >>
     drule send_call_value_with_gas_obs >> strip_tac >>
     pop_assum (qspec_then `gobs` assume_tac) >>
     drule send_call_value_with_scopes >> strip_tac >>
     pop_assum (qspec_then `[FEMPTY]` mp_tac) >>
     simp[Abbr `es1`, initial_state_def]) >>
  `eval_external_defaults cx [] es1 = (INL [], es1)` by
    simp[Abbr `es1`, eval_external_defaults_def, evaluate_def,
         vyperStateTheory.bind_def,
         vyperStateTheory.ignore_bind_def, vyperStateTheory.get_scopes_def,
         vyperStateTheory.set_scopes_def, vyperStateTheory.finally_def,
         vyperStateTheory.return_def] >>
  `call_external_function orc gobs am cx F mut tops [(NONE, tops)] args []
     tx.args fbody ret =
   call_external_body am cx F mut (type_env tops) es1 env fbody ret` by
    (qpat_assum `_ = type_env tops` (SUBST1_TAC o SYM) >>
     irule call_external_function_body >> gvs[Abbr `cx`]) >>
  gvs[Abbr `es1`, call_external_body_scopes]
QED

(* call_external_selected_body_gas without gas observations. *)
Theorem call_external_selected_body:
  !tops am tx ret mut args fbody env orc es0.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INL (), es0) ==>
    call_external orc [] am tx =
      case call_external_body am
             (initial_evaluation_context am.sources am.layouts tx NONE)
             F mut (type_env tops) es0 env fbody ret of
        (INL v, am', rqs) => (INL v, finalize_pending_deletions am', rqs)
      | (INR HaltException, am', rqs) =>
          (INR HaltException, finalize_pending_deletions am', rqs)
      | failure => failure
Proof
  rpt strip_tac >>
  drule_all call_external_selected_body_gas >>
  disch_then (qspec_then `[]` SUBST1_TAC) >>
  `es0 with gas_obs := [] = es0` suffices_by simp[] >>
  drule (cj 1 send_call_value_with_gas_obs) >>
  simp[initial_state_def, vyperStateTheory.evaluation_state_component_equality]
QED

(* type_stmt rejects Return (SOME e) at NoneT. *)
Theorem type_stmt_none_valued_return[local]:
  (!env ret_ty s.
     ret_ty = NoneT /\ IS_SOME (type_stmt env ret_ty s) ==>
     ~stmt_valued_return s) /\
  (!env ret_ty ss.
     ret_ty = NoneT /\ IS_SOME (type_stmts env ret_ty ss) ==>
     ~stmts_valued_return ss)
Proof
  ho_match_mp_tac type_stmt_ind >>
  rw[type_stmt_def, stmt_valued_return_def] >>
  gvs[optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >> metis_tac[]
QED

(* A body typed at NoneT has no valued return. *)
Theorem type_stmts_none_valued_return:
  !env ss env'.
    type_stmts env NoneT ss = SOME env' ==> ~stmts_valued_return ss
Proof
  metis_tac[type_stmt_none_valued_return, optionTheory.IS_SOME_DEF]
QED

(* The guarded body's code from sa: the body's statements to sb, then (if
   the block is still open) the end, to st'. *)
Theorem guarded_body_code:
  !cenv nkey ut iv fbody rt sa st'.
    compile_guarded_body cenv F nkey ut iv fbody rt sa = ((), st') ==>
    ?sb. compile_stmts cenv NoLoop
           (case rt of SOME t => t | NONE => BaseT BoolT) fbody sa =
           ((), sb) /\
         cs_extends sa sb /\ cs_extends sb st'
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_guarded_body_def, comp_bind_def, comp_ignore_bind_def,
       comp_get_def, comp_return_def] >>
  Cases_on `compile_stmts cenv NoLoop
              (case rt of SOME t => t | NONE => BaseT BoolT) fbody sa` >>
  rename1 `_ = (u, sb)` >> Cases_on `u` >> simp[] >>
  `cs_extends sa sb` by
    (qspecl_then [`cenv`, `NoLoop`,
                  `case rt of SOME t => t | NONE => BaseT BoolT`, `fbody`]
       mp_tac (cj 2 compile_stmt_cs_mono) >>
     simp[cs_mono_def] >> disch_then drule >> simp[]) >>
  rw[] >>
  gvs[comp_return_def, comp_ignore_bind_def, comp_bind_def,
      cs_extends_refl] >>
  Cases_on `rt` >> gvs[] >>
  drule (SIMP_RULE std_ss [cs_appends_def] (cj 1 cs_appends_emit_helpers)) >>
  simp[]
QED

(* The body's code at the typing's return type: body_stmts_sim compiles at
   the return type the typing checks the body against, while
   compile_guarded_body compiles a function without a return type at
   BaseT BoolT. *)
Theorem guarded_body_stmts_env:
  !tops bindings ctx cx cenv fbody ret rt env_t env' sa sb.
    supported_stmts tops bindings fbody /\ body_inv tops ctx cenv cx /\
    rt = (if ret = NoneT then NONE else SOME ret) /\
    type_stmts env_t ret fbody = SOME env' /\
    compile_stmts cenv NoLoop
      (case rt of SOME t => t | NONE => BaseT BoolT) fbody sa = ((), sb) ==>
    ?cenv'. stmts_env cenv NoLoop ret fbody sa = (cenv', sb)
Proof
  rpt strip_tac >> qpat_x_assum `rt = _` SUBST_ALL_TAC >>
  `stmts_env cenv NoLoop ret fbody sa =
   stmts_env cenv NoLoop
     (case (if ret = NoneT then NONE else SOME ret) of
        SOME t => t | NONE => BaseT BoolT) fbody sa` by
    (Cases_on `ret = NoneT` >> gvs[] >>
     drule type_stmts_none_valued_return >> strip_tac >>
     drule_all stmts_env_ret_ty >>
     disch_then (qspecl_then [`NoLoop`, `NoneT`, `BaseT BoolT`]
                   SUBST1_TAC) >> simp[]) >>
  gvs[compile_stmts_env] >>
  Cases_on `stmts_env cenv NoLoop
              (case (if ret = NoneT then NONE else SOME ret) of
                 SOME t => t | NONE => BaseT BoolT) fbody sa` >>
  gvs[]
QED
