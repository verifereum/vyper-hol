(*
 * S1, lower_vyper_runtime_unit_correct, composed from its three pieces
 * (#642)
 *
 * The source runs the external function valid_vyper_call selects: it
 * binds the arguments, moves the call value (send_call_value) and runs the
 * body; call_external_body then turns the body's outcome into the call's
 * result.  The lowered code runs the same three steps:
 *   - the entry (#639): from the initial state, run_context reaches the
 *     start of the selected function's guarded body in a state related
 *     by stmt_state_rel to the source state where the body starts, or,
 *     when the source cannot move the value, ends in a matching abort;
 *   - the body (#636-#638): bodySimMain's body_stmts_sim, in the
 *     external function's frame;
 *   - the halt (#640): a return statement exits as the frame's RetQ
 *     accepts (external_frame_ret_ok, from the return sequences of
 *     vyperLoweringCorrect), and falling off the end of a function
 *     without a return type stops (external_fallthrough_result_rel_any).
 *
 * The pieces still to prove are stated as the composition uses them, each
 * in its own theory.
 *
 * TOP-LEVEL:
 *   lower_vyper_runtime_unit_correct -- S1
 *   external_fallthrough_result_rel_any -- the fall-through halt, with
 *     state_rel at any compile env
 *   call_external_selected_body, call_external_selected_body_gas -- the
 *     source runs the selected body, at any gas observations
 *   type_stmts_none_valued_return -- a body typed at NoneT has no valued
 *     return
 *
 * The pieces S1 rests on, one per theory:
 *   externalBodySourceOk: external_body_source_ok -- the source side
 *     (typing soundness)
 *   externalEntryValueRevert: external_entry_value_revert and
 *   externalEntryReachesBody: external_entry_reaches_body -- the entry
 *     bridge (#639)
 *   externalBodyFrame: external_body_frame -- the body judgment's
 *     premises at the body's start (#637)
 *   externalFrameRetOk: external_frame_ret_ok -- the frame's returns
 *     (#640)
 *   stmtsEnvRetTy: stmts_env_ret_ty -- a supported body without a valued
 *     return compiles the same at every return type
 *
 * The body judgment is counted: its source run reads the gas observations
 * that the target path's GAS reads produce (gas_explicit), so S1's source
 * call takes those observations (source_unit_execution_correct).
 *)

Theory loweringRuntimeCorrect
Ancestors
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list pair fragExec  bodySim bodySimMain loweringHalt stmtLoweringMono  exprLoweringProps
  compileEnv compileVyper moduleLowering stmtLowering
  e2eDefs supportedProgram vyperLoweringCorrect rawReturnHeader bodyAbiDecodeTarget
  vyperTypeSelectedEntrySoundness vyperTypeSystem
  vyperInterpreter vyperState vyperContext
  venomState venomExecSemantics venomWf
  gasContext gasSummary gasOutcome gasExemptCert fragGasPath fragGasMode
  externalBodySourceOk externalEntryValueRevert externalEntryReachesBody externalBodyFrame externalFrameRetOk stmtsEnvRetTy

val _ = Parse.hide "body";

(* ===== The source side (#639) ===== *)

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
   with pending deletions finalised on success.  es0 is the state after
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
      | failure => failure
Proof
  rpt strip_tac >>
  drule_all call_external_selected_body_gas >>
  disch_then (qspec_then `[]` SUBST1_TAC) >>
  `es0 with gas_obs := [] = es0` suffices_by simp[] >>
  drule (cj 1 send_call_value_with_gas_obs) >>
  simp[initial_state_def, vyperStateTheory.evaluation_state_component_equality]
QED
(* ADMITTED (typing soundness): the body of a checked external function
   ends in an outcome the statement judgment speaks of (no type error, no
   break or continue outside a loop), and it falls off its end only when
   the function has no return type (the type checker's
   stmts_no_fallthrough).  Most of it should follow from
   checked_selected_entry_no_static_error and
   callable_body_typing_from_env_consistent. *)

(* ===== The entry (#639) ===== *)



(* ===== The body's frame (#637) ===== *)


(* ===== The frame's returns (#640) ===== *)



(* ===== The fall-through halt (#640) ===== *)

(* external_fallthrough_result_rel with state_rel at any compile env cenv'
   rather than the guarded body's: the body simulation ends at the compile
   env after the body's declarations. *)
Theorem external_fallthrough_result_rel_any:
  !ctx cenv cenv' nkey ut iv stmts st x st' sb func cx es tops tx srcs exps
     layouts Q.
    ~lookup_raw_return_or_F (NONE : num option) tx.function_name External tops /\
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_guarded_body cenv F nkey ut iv stmts NONE st = (x, st') /\
    compile_stmts cenv NoLoop (BaseT BoolT) stmts st = ((), sb) /\
    ~block_is_terminated sb ==>
    frag_exec ctx sb st'
      (\s. state_rel func cenv' cx es s)
      Q
      (external_call_result_rel tops NoneT tx
         (INL NoneV, finalize_pending_deletions
                       (abstract_machine_from_state srcs exps layouts es),
          es.requests))
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `cenv`, `F`, `nkey`, `ut`, `iv`, `stmts`, `st`, `x`,
               `st'`, `st`, `sb`] mp_tac compile_guarded_body_stop_unlock_frag >>
  simp[comp_return_def] >> disch_then irule >> rpt strip_tac >>
  qspecl_then [`func`, `cenv'`, `cx`, `es`, `es`, `s`, `ss`, `F`, `nkey`,
               `iv`, `tops`, `tx`, `srcs`, `exps`, `layouts`] mp_tac
    external_halt_success_unlock >>
  impl_tac >- gvs[vyperStateTheory.return_def] >>
  strip_tac >> gvs[external_call_result_rel_def, tx_return_bytes_def, return_bytes_def,
                  abstract_machine_from_state_def]
QED

(* ===== The return type of a body without a valued return ===== *)


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

(* ===== The source's result ===== *)

(* call_external_body without a lock, from es0 in the bound scope, where
   the body ran to es'. *)
Theorem call_external_body_run[local]:
  !am cx mut tenv env fbody ret es0 res es'.
    es0.scopes = [env] /\
    eval_stmts cx fbody es0 = (res, es') ==>
    (res = INL () ==>
     call_external_body am cx F mut tenv es0 env fbody ret =
       (INL NoneV,
        abstract_machine_from_state am.sources am.exports am.layouts es',
        es'.requests)) /\
    (!v. res = INR (ReturnException v) ==>
     call_external_body am cx F mut tenv es0 env fbody ret =
       case evaluate_type tenv ret of
         NONE => (INR (Error (TypeError "eval ret")), am, es'.requests)
       | SOME tv =>
           case safe_cast tv v of
             NONE => (INR (Error (TypeError "ext cast ret")), am,
                      es'.requests)
           | SOME v' =>
               (INL v',
                abstract_machine_from_state am.sources am.exports am.layouts
                  es', es'.requests)) /\
    (!e. res = INR e /\ (!v. e <> ReturnException v) ==>
     call_external_body am cx F mut tenv es0 env fbody ret =
       (INR e, am, es'.requests))
Proof
  rpt gen_tac >> strip_tac >>
  `es0 with scopes := [env] = es0` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[call_external_body_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.set_scopes_def] >>
  rpt strip_tac >> gvs[]
  >- (BasicProvers.EVERY_CASE_TAC >> gvs[])
  >> Cases_on `e` >> gvs[]
QED

(* ===== The body's run ===== *)

Theorem call_external_body_gas_suffix[local]:
  es0.scopes = [env] /\
  (!tail. eval_stmts cx fbody (es0 with gas_obs := gs ++ tail) =
    (res, es' with gas_obs := tail)) ==>
  !tail.
    call_external_body am cx F mut tenv
      (es0 with gas_obs := gs ++ tail) env fbody ret =
    call_external_body am cx F mut tenv
      (es0 with gas_obs := gs) env fbody ret
Proof
  strip_tac >>
  qpat_x_assum `!tail. eval_stmts _ _ _ = _`
    (fn th => assume_tac th >> assume_tac (SIMP_RULE list_ss [] (Q.SPEC `[]` th))) >>
  `!readings. (es0 with gas_obs := readings) with scopes := [env] =
     es0 with gas_obs := readings` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[call_external_body_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.set_scopes_def, abstract_machine_from_state_gas_obs]
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

(* A body outcome other than a return exits as external_call_result_rel
   asks of the call's failure, given that a RevertData exit reverts. *)
Theorem expr_exit_external_result[local]:
  !e r tops ret tx am rqs.
    expr_exit (INR e : unit + exception) r /\
    (!d a t. e = Error (RevertData d) /\ r = Abort a t ==> a = Revert_abort) ==>
    external_call_result_rel tops ret tx (INR e, am, rqs) r
Proof
  rpt strip_tac >>
  Cases_on `r` >> gvs[expr_exit_def] >>
  Cases_on `e` >> gvs[expr_exit_def] >>
  TRY (rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  gvs[external_call_result_rel_def]
QED

(* ===== S1 ===== *)

(* S1 when the value moves and the body starts. *)
Theorem lower_vyper_runtime_unit_body[local]:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  rpt strip_tac >>
  drule_all external_entry_reaches_body >> strip_tac >>
  drule_all external_body_frame >> strip_tac >>
  drule_all external_frame_ret_ok >>
  disch_then (qspec_then `func` assume_tac) >>
  drule_all call_external_selected_body_gas >> strip_tac >>
  `es0.scopes = [env]` by
    (qpat_x_assum `send_call_value _ _ _ = (INL (), es0)`
       (mp_tac o MATCH_MP (cj 1 send_call_value_with_scopes)) >>
     simp[initial_state_def]) >>
  (* the source side, at every gas observation list *)
  `!gs res ee.
     eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
       fbody (es0 with gas_obs := gs) = (res, ee) ==>
     stmt_res_ok NoLoop res /\ (res = INL () ==> ret = NoneT)` by
    (rpt gen_tac >> strip_tac >>
     qspecl_then [`tops`, `am`, `tx`, `ret`, `vs`, `mut`, `args`, `fbody`,
                  `env`, `es0`, `gs`, `res`, `ee`] mp_tac
       external_body_source_ok >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `cx_tops (initial_evaluation_context am.sources am.layouts tx NONE) =
   tops` by
    (irule gasContextTheory.cx_tops_module >>
     gvs[source_deployment_rel_def, get_module_code_def,
         initial_evaluation_context_def]) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  qpat_x_assum `cx_tops cx = tops` (SUBST_ALL_TAC o SYM) >>
  `rt = if ret = NoneT then NONE else SOME ret` by
    gvs[package_external_fn_def, set_external_package_target_def] >>
  drule guarded_body_code >> strip_tac >>
  drule_all guarded_body_stmts_env >> strip_tac >>
  qmatch_asmsub_abbrev_tac `frame_ret_ok _ _ _ RetQ _ _` >>
  `stmt_frag unit.cu_context func cx NoLoop RetQ cenv
     (stmts_env cenv NoLoop ret fbody) (eval_stmts cx fbody) es0` by
    (irule body_stmts_sim >>
     metis_tac[lookup_function_abi_decode_target_occurs]) >>
  `fn_has_code sa sb func /\ fn_has_code sb st' func` by
    (drule_all fn_has_code_split >> simp[]) >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >>
  impl_tac
  >- (fs[ret_pc_ok_def, gas_admissible_def] >> metis_tac[] >> NO_TAC) >>
  simp[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- ((* the body runs along a target path *)
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o BETA_RULE o REWRITE_RULE [gas_summary_at_def]) >>
      (qabbrev_tac `gx = gas_explicit marks s0.vs_gas_readings` >>
      `!tail. call_external_body am cx F mut (type_env (cx_tops cx))
         (es0 with gas_obs := gx ++ tail) env fbody ret =
         call_external_body am cx F mut (type_env (cx_tops cx))
         (es0 with gas_obs := gx) env fbody ret` by
        (irule (Q.INST [`res` |-> `res`, `es'` |-> `es_end`]
                  call_external_body_gas_suffix) >> simp[] >>
         fs[gas_marked_exec_def, Abbr `gx`] >>
         qexistsl_tac [`es_end`, `res`] >> simp[]) >>
      `!tail. call_external (SOME vs.vs_outcomes) (gx ++ tail) am tx =
         call_external (SOME vs.vs_outcomes) gx am tx` by simp[] >>
      `eval_stmts cx fbody (es0 with gas_obs := gx) =
         (res, es_end with gas_obs := []) /\
       gas_path unit.cu_context func s0 (LENGTH marks) r` by
        (fs[gas_marked_exec_def] >>
         conj_tac
         >- (qpat_x_assum `!tail. eval_stmts _ _ _ = _`
               (qspec_then `[]` mp_tac) >> simp[]) >>
         metis_tac[fragGasModeTheory.gas_marked_path_exec]) >>
      qabbrev_tac `es' = es_end with gas_obs := []` >>
      `stmt_res_ok NoLoop res /\ (res = INL () ==> ret = NoneT)` by
        (first_x_assum irule >> qexistsl_tac [`es'`, `gx`] >>
         gvs[Abbr `cx`]) >>
      pure_rewrite_tac[source_unit_execution_correct_def] >>
      qexists_tac `marks` >>
      `gas_explicit marks vs.vs_gas_readings = gx` by
        (qpat_assum `s0.vs_gas_readings = _`
           (fn th => simp[Abbr `gx`, th])) >>
      pop_assum SUBST1_TAC >> reverse conj_tac
      >- first_assum ACCEPT_TAC >>
      pure_rewrite_tac[source_unit_execution_correct_at_def] >>
      qspecl_then [`am`, `cx`, `mut`, `type_env (cx_tops cx)`, `env`, `fbody`, `ret`,
                   `es0 with gas_obs := gx`, `res`, `es'`] mp_tac
        call_external_body_run >>
      (impl_tac >- (simp[] >> NO_TAC)) >> disch_then strip_assume_tac >>
      disj2_tac >> simp[])
      >- ((* the body falls off its end *)
          gvs[stmt_post_def, stmt_lands_def] >>
          `~lookup_raw_return_or_F (NONE : num option) tx.function_name
              External (cx_tops cx)` by
            (irule source_typing_none_return_plain >> metis_tac[]) >>
          `state_rel func cenv' cx es' t` by fs[stmt_state_rel_def] >>
          qspecl_then [`unit.cu_context`, `cenv`, `cenv'`, `nkey`, `ut'`,
                       `iv`, `fbody`, `sa`, `()`, `st'`, `sb`, `func`, `cx`,
                       `es'`, `cx_tops cx`, `tx`, `am.sources`, `am.exports`,
                       `am.layouts`, `\s:venom_state. F`] mp_tac
            external_fallthrough_result_rel_any >>
          impl_tac >- gvs[Abbr`cx`, initial_evaluation_context_def] >>
          simp[frag_exec_def] >>
          disch_then (qspecl_then [`func`, `t`] mp_tac) >>
          impl_tac >- gvs[] >> simp[] >> strip_tac >>
          `!e. run_from fuel unit.cu_context func t <> Error e` by
            (gen_tac >> irule exit_result_not_error >>
             first_assum ACCEPT_TAC) >>
          `?fuel1. run_from fuel1 unit.cu_context func s0 =
                   run_from fuel unit.cu_context func t` by
            metis_tac[fragGasPathTheory.gas_path_normal] >>
          qpat_x_assum `!fuel. (!e. run_from _ _ _ s0 <> _) ==> _`
            (qspec_then `fuel1` mp_tac) >>
          impl_tac >- asm_rewrite_tac[] >>
          disch_then (qx_choose_then `fuel2`
                        (fn th => qexists_tac `fuel2` >> SUBST1_TAC th)) >>
          gvs[Abbr`cx`, initial_evaluation_context_def]) >>
      (* the body exits *)
      drule_all fragGasPathTheory.gas_path_exit >>
      disch_then (qx_choose_then `fuel` assume_tac) >>
      `!e. r <> Error e` by metis_tac[exit_result_not_error] >>
      qpat_x_assum `!fuel r. run_from _ _ _ s0 = r /\ _ ==> _`
        (qspecl_then [`fuel`, `r`] mp_tac) >>
      impl_tac >- asm_rewrite_tac[] >>
      disch_then (qx_choose_then `fuel2`
                    (fn th => qexists_tac `fuel2` >> SUBST1_TAC th)) >>
      qpat_x_assum `!tail. stmt_exit _ _ _ _` (qspec_then `[]` mp_tac) >>
      simp[stmt_exit_def] >> strip_tac
      >- ((* an error or an assertion *)
          Cases_on `res` >> gvs[] >> rename1 `expr_exit (INR e) _` >>
          `!v. e <> ReturnException v` by
            (rpt strip_tac >> gvs[] >>
             qpat_x_assum `expr_exit _ _` mp_tac >>
             qmatch_goalsub_abbrev_tac `expr_exit _ rr` >>
             Cases_on `rr` >> simp[expr_exit_def]) >>
          gvs[] >>
          qspecl_then [`e`, `run_from fuel unit.cu_context func s0`, `cx_tops cx`, `ret`, `tx`, `am`, `es'.requests`]
            mp_tac expr_exit_external_result >>
          impl_tac
          >- (conj_tac >- first_assum ACCEPT_TAC >>
              rpt strip_tac >> gvs[expr_exit_def]) >>
          simp[]) >>
      (* a return *)
      gvs[Abbr`RetQ`, Abbr`es'`, abstract_machine_from_state_def]) >>
  (* the body fails with an exempt error *)
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err, ee) _` >>
  drule gasExemptCertTheory.gas_exempt_cert_execution >> strip_tac >>
  qabbrev_tac `gx = gas_explicit marks s0.vs_gas_readings` >>
  `!tail. eval_stmts cx fbody (es0 with gas_obs := gx ++ tail) =
     (INR (Error err), ee with gas_obs := tail)` by
    (gen_tac >> qpat_x_assum `!tail. _` (qspec_then `tail` mp_tac) >>
     simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
          vyperStateTheory.return_def] >>
     Cases_on `eval_stmts cx fbody (es0 with gas_obs := gx ++ tail)` >>
     Cases_on `q` >> simp[]) >>
  `!tail. call_external_body am cx F mut (type_env (cx_tops cx))
     (es0 with gas_obs := gx ++ tail) env fbody ret =
     call_external_body am cx F mut (type_env (cx_tops cx))
     (es0 with gas_obs := gx) env fbody ret` by
    (irule (Q.INST [`res` |-> `INR (Error err)`, `es'` |-> `ee`]
              call_external_body_gas_suffix) >> simp[] >>
     qexistsl_tac [`ee`, `err`] >> simp[]) >>
  `!tail. call_external (SOME vs.vs_outcomes) (gx ++ tail) am tx =
     call_external (SOME vs.vs_outcomes) gx am tx` by simp[] >>
  `?ee'. eval_stmts cx fbody (es0 with gas_obs := gx) =
           (INR (Error err), ee')` by
    (qexists_tac `ee with gas_obs := []` >>
     qpat_x_assum `!tail. eval_stmts _ _ _ = _`
       (qspec_then `[]` mp_tac) >> simp[]) >>
  qspecl_then [`am`, `cx`, `mut`, `type_env (cx_tops cx)`, `env`, `fbody`, `ret`,
               `es0 with gas_obs := gx`, `INR (Error err)`, `ee'`] mp_tac
    call_external_body_run >>
  impl_tac >- simp[] >> strip_tac >>
  pure_rewrite_tac[source_unit_execution_correct_def] >>
  qexists_tac `marks` >>
  `gas_explicit marks vs.vs_gas_readings = gx` by
    (qpat_assum `s0.vs_gas_readings = _`
       (fn th => simp[Abbr `gx`, th])) >>
  pop_assum SUBST1_TAC >> reverse conj_tac
  >- first_assum ACCEPT_TAC >>
  pure_rewrite_tac[source_unit_execution_correct_at_def] >>
  disj1_tac >> gvs[source_exempt_def]
QED

(* S1, the lowering of an external call the source selects: the call's
   result and the lowered unit's run are related by
   external_call_result_rel. *)
Theorem lower_vyper_runtime_unit_correct:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes
    ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  rpt strip_tac >>
  `?mut args fbody.
     lookup_function NONE tx.function_name External tops =
       SOME (mut, F, args, [], ret, fbody) /\
     LENGTH tx.args = LENGTH args /\
     IS_SOME (bind_arguments (type_env tops) args tx.args)` by
    (fs[valid_vyper_call_def] >> metis_tac[]) >>
  `?env. bind_arguments (type_env tops) args tx.args = SOME env` by
    (Cases_on `bind_arguments (type_env tops) args tx.args` >> fs[]) >>
  Cases_on `send_call_value mut
              (initial_evaluation_context am.sources am.layouts tx NONE)
              (initial_state am [env] with
                 <| outcomes := SOME vs.vs_outcomes; requests := [] |>)` >>
  rename1 `_ = (sres, es0)` >> Cases_on `sres`
  >- (rename1 `INL u` >> Cases_on `u` >> irule lower_vyper_runtime_unit_body >> metis_tac[]) >>
  irule external_entry_value_revert >> metis_tac[]
QED
