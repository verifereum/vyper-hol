(*
 * Selected external entry of a checked contract (#608, part of #420).
 * Value transfer precedes stateful evaluation of the needed defaults.  Binding
 * then installs the argument scope, followed by lock/body/unlock and return
 * conversion.  Errors retain the original exception and requests; the call
 * rolls back the machine.  Successful calls finalize pending deletions.
 *
 * call_external_body is the continuation at the actual post-default state,
 * not a reconstruction from the original machine.  The public safety theorem
 * obtains phase typing from the shared checked entry soundness boundary.
 *
 * TOP-LEVEL: call_external_body_def, call_external_function_body,
 *            checked_selected_entry_no_static_error.
 * Helper: call_external_selected_entry_body.
 *)

Theory vyperTypeSelectedEntrySoundness
Ancestors
  list pair
  vyperAST vyperValue vyperState vyperInterpreter vyperContext
  vyperTypeExprSoundness vyperTypeInitialState vyperTypeEntryReadiness
  vyperTypeContract vyperTypeContractSoundness
  vyperTypeSelectedEntry vyperTypeEntryDefaults

val _ = Parse.hide "body";

(* call_external_function from the bound scope on, with the deployment
   constants step not taken (am_c = am). *)
Definition call_external_body_def:
  call_external_body am cx nr mut all_tenv st env body ret =
   let srcs = am.sources in
   let exps = am.exports in
   let layouts = am.layouts in
   let is_view = (mut = View ∨ mut = Pure) in
   let lock_action = if nr then
     case cx.nonreentrant_slot of
     | NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return () in
   let unlock_action = if nr ∧ ¬is_view then
     case cx.nonreentrant_slot of
     | NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return () in
   let (res, am_out, rqs) =
     (case do set_scopes [env]; lock_action; eval_stmts cx body od st
      of
       | (INL (), st) =>
           (case unlock_action st of
            | (INL (), st) => (INL NoneV, abstract_machine_from_state srcs exps layouts st, st.requests)
            | (INR e, st) => (INR e, am, st.requests))
       | (INR (ReturnException v), st) =>
           (case unlock_action st of
            | (INL (), st) =>
              (let am_ret = abstract_machine_from_state srcs exps layouts st in
               case evaluate_type all_tenv ret
               of NONE => (INR (Error (TypeError "eval ret")), am, st.requests)
                | SOME tv =>
               case safe_cast tv v
               of NONE => (INR (Error (TypeError "ext cast ret")), am, st.requests)
                | SOME v => (INL v, am_ret, st.requests))
            | (INR e, st) => (INR e, am, st.requests))
       | (INR e, st) => (INR e, am, st.requests)) in
    (res, am_out, rqs)
End

Theorem call_external_function_body:
  ~cx.in_deploy /\
  LENGTH vals <= LENGTH args /\
  LENGTH args - LENGTH vals <= LENGTH dflts /\
  send_call_value mut cx
    (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>) = (INL (),st1) /\
  eval_external_defaults cx
    (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) st1 = (INL dvs,st2) /\
  bind_arguments (type_env_all_modules mods) args (vals ++ dvs) = SOME env ==>
  call_external_function orc am cx nr mut (ts : toplevel list) mods args dflts vals body ret =
    call_external_body am cx nr mut (type_env_all_modules mods) st2 env body ret
Proof
  strip_tac >>
  `LENGTH dflts - (LENGTH args - LENGTH vals) =
   LENGTH dflts + LENGTH vals - LENGTH args` by decide_tac >>
  gvs[] >>
  simp[call_external_function_def, call_external_body_def,
       bind_def, ignore_bind_def]
QED

Theorem call_external_selected_entry_body:
  selected_entry am tx mods (mut,nr,args,dflts,ret,body) /\
  src = find_function_module am tx.target tx.function_name /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH tx.args <= LENGTH args /\
  LENGTH args - LENGTH tx.args <= LENGTH dflts /\
  send_call_value mut cx
    (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>) = (INL (),st1) /\
  eval_external_defaults cx
    (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) st1 = (INL dvs,st2) /\
  bind_arguments (type_env_all_modules mods) args (tx.args ++ dvs) = SOME scope ==>
  call_external orc am tx =
    case call_external_body am cx nr mut (type_env_all_modules mods) st2 scope body ret of
      (INL value, am', rqs) => (INL value, finalize_pending_deletions am', rqs)
    | failure => failure
Proof
  strip_tac >>
  `~cx.in_deploy` by gvs[initial_evaluation_context_def] >>
  drule_all selected_entry_module_code >> strip_tac >>
  drule_all call_external_selected_entry >> disch_then (fn th => rewrite_tac[th]) >>
  drule_all call_external_function_body >> disch_then (fn th => rewrite_tac[th])
QED

Theorem checked_selected_entry_no_static_error:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  selected_entry am tx mods (mut,nr,args,dflts,ret,body) /\
  src = find_function_module am tx.target tx.function_name /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH tx.args <= LENGTH args /\
  LENGTH args - LENGTH tx.args <= LENGTH dflts /\
  provided_args_typed (type_env_all_modules mods) args tx.args ==>
  no_type_error_result (FST (call_external orc am tx)) /\
  (!exc. FST (call_external orc am tx) = INR exc ==>
     exc <> BreakException /\ exc <> ContinueException)
Proof
  strip_tac >> Cases_on `call_external orc am tx` >>
  PairCases_on `r` >> simp[] >>
  conj_tac >- (drule_all checked_call_external_no_type_error >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all checked_call_external_no_loop_control >> simp[]
QED
