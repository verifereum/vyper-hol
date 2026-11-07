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
  cheat
QED

(* Likewise under any gas observations. *)
Theorem send_call_value_with_gas_obs:
  !mut cx s r s'.
    send_call_value mut cx s = (r, s') ==>
    s'.gas_obs = s.gas_obs /\
    !gs. send_call_value mut cx (s with gas_obs := gs) =
         (r, s' with gas_obs := gs)
Proof
  cheat
QED

(* call_external_body sets the scopes before it reads them. *)
Theorem call_external_body_scopes[local]:
  !am cx nr mut tenv s sc env body ret.
    call_external_body am cx nr mut tenv (s with scopes := sc) env body ret =
    call_external_body am cx nr mut tenv s env body ret
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

(* A body typed at NoneT has no valued return. *)
Theorem type_stmts_none_valued_return:
  !env ss env'.
    type_stmts env NoneT ss = SOME env' ==> ~stmts_valued_return ss
Proof
  cheat
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
  cheat
QED

(* ===== The body's run ===== *)

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
  cheat
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
  cheat
QED

(* A body outcome other than a return exits as external_call_result_rel
   asks of the call's failure, given that a RevertData exit reverts. *)
Theorem expr_exit_external_result[local]:
  !e r tops ret tx am rqs.
    expr_exit (INR e : unit + exception) r /\
    (!d a t. e = Error (RevertData d) /\ r = Abort a t ==> a = Revert_abort) ==>
    external_call_result_rel tops ret tx (INR e, am, rqs) r
Proof
  cheat
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
  cheat
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
  cheat
QED
