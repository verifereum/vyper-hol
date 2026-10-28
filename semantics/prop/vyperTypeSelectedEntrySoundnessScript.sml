(*
 * Selected external entry of a checked contract (#608, part of #420): once
 * call_external has selected an entry and the raw arguments fit its
 * parameters, the call ends in one of two ways.
 *
 * - Default failure: evaluate_defaults stops at a needed default whose own
 *   eval_expr fails with a runtime error that is not a TypeError, and
 *   call_external returns a RuntimeError with the machine unchanged and no
 *   requests.
 * - Body run: the needed defaults evaluate to typed values, the arguments bind
 *   to a scope, and call_external is call_external_body from that scope with
 *   pending deletions finalised on success; its result is not a TypeError and
 *   does not escape with break or continue.
 *
 * call_external_body is call_external_function's tail after argument binding,
 * outside deployment (initial_evaluation_context has in_deploy = F, so the
 * deployment constants step is skipped).
 *
 * TOP-LEVEL: call_external_body_def, call_external_function_body,
 *            checked_selected_entry_no_static_error.
 *
 * Helper: call_external_selected_entry_body,
 *         call_external_selected_entry_defaults_fail, finalize_case_FST.
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
  call_external_body orc gobs am cx nr mut all_tenv env body ret =
   let st = initial_state am [env] with <| outcomes := orc; requests := []; gas_obs := gobs |> in
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
     (case do lock_action; send_call_value mut cx; eval_stmts cx body od st
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
  evaluate_defaults cx am gobs
    (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) =
    SOME (dflt_vs, gobs') /\
  bind_arguments (type_env_all_modules mods) args (vals ++ dflt_vs) =
    SOME env ==>
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret =
    call_external_body orc gobs' am cx nr mut (type_env_all_modules mods) env body
      ret
Proof
  strip_tac >>
  `LENGTH dflts - (LENGTH args - LENGTH vals) =
   LENGTH dflts + LENGTH vals - LENGTH args` by simp[] >>
  gs[call_external_function_def, call_external_body_def]
QED

Theorem call_external_selected_entry_body[local]:
  selected_entry am tx mods (mut,nr,args,dflts,ret,body) /\
  src = find_function_module am tx.target tx.function_name /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH tx.args <= LENGTH args /\
  LENGTH args - LENGTH tx.args <= LENGTH dflts /\
  evaluate_defaults cx am gobs
    (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) =
    SOME (dflt_vs, gobs') /\
  bind_arguments (type_env_all_modules mods) args (tx.args ++ dflt_vs) =
    SOME scope ==>
  call_external orc gobs am tx =
    case call_external_body orc gobs' am cx nr mut (type_env_all_modules mods)
           scope body ret of
      (INL value, am', rqs) => (INL value, finalize_pending_deletions am', rqs)
    | failure => failure
Proof
  strip_tac >>
  `~cx.in_deploy` by gvs[initial_evaluation_context_def] >>
  drule_all selected_entry_module_code >> strip_tac >>
  drule_all call_external_selected_entry >>
  disch_then (fn th => rewrite_tac[th]) >>
  `call_external_function orc gobs am cx nr mut ts mods args dflts tx.args body ret =
   call_external_body orc gobs' am cx nr mut (type_env_all_modules mods) scope body
     ret` by
    (irule call_external_function_body >> metis_tac[]) >>
  pop_assum (fn th => rewrite_tac[th])
QED

Theorem call_external_selected_entry_defaults_fail[local]:
  selected_entry am tx mods (mut,nr,args,dflts,ret,body) /\
  src = find_function_module am tx.target tx.function_name /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH tx.args <= LENGTH args /\
  LENGTH args - LENGTH tx.args <= LENGTH dflts /\
  evaluate_defaults cx am gobs
    (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) = NONE ==>
  ?msg. call_external orc gobs am tx = (INR (Error (RuntimeError msg)), am, [])
Proof
  strip_tac >>
  drule_all selected_entry_module_code >> strip_tac >>
  `LENGTH dflts - (LENGTH args - LENGTH tx.args) =
   LENGTH dflts + LENGTH tx.args - LENGTH args` by simp[] >>
  drule_all call_external_selected_entry >>
  disch_then (fn th => gs[th, call_external_function_def])
QED

Theorem finalize_case_FST[local]:
  FST (case r of
         (INL value, am', rqs) =>
           (INL value, finalize_pending_deletions am', rqs)
       | failure => failure) = FST r
Proof
  PairCases_on `r` >> Cases_on `r0` >> simp[]
QED

(* The ABI premise is the length fit plus provided_args_typed: bind_arguments
   casts every provided value to its parameter type.  provided_args_typed
   already implies LENGTH tx.args <= LENGTH args; the bound is kept to match
   checked_selected_entry_bind_arguments.  The two cases are exclusive
   (evaluate_defaults is NONE in one and SOME in the other). *)
Theorem checked_selected_entry_no_static_error:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  call_tx_well_typed tx /\
  selected_entry am tx mods (mut,nr,args,dflts,ret,body) /\
  src = find_function_module am tx.target tx.function_name /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH tx.args <= LENGTH args /\
  LENGTH args - LENGTH tx.args <= LENGTH dflts /\
  provided_args_typed (type_env_all_modules mods) args tx.args ==>
  (evaluate_defaults cx am gobs
     (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) = NONE /\
   (?pre e post g.
      DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts =
        pre ++ e::post /\
      EVERY (\e'. ?g' v. FST (eval_expr cx e'
                         (initial_state am [FEMPTY] with gas_obs := g')) =
                        INL (Value v)) pre /\
      ?err. FST (eval_expr cx e (initial_state am [FEMPTY] with gas_obs := g)) =
              INR err /\
            no_type_error_result (INR err : toplevel_value + exception)) /\
   ?msg. call_external orc gobs am tx = (INR (Error (RuntimeError msg)), am, [])) \/
  (?dflt_vs gobs' scope.
     evaluate_defaults cx am gobs
       (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) =
       SOME (dflt_vs, gobs') /\
     args_values_typed (type_env_all_modules mods) args (tx.args ++ dflt_vs) /\
     bind_arguments (type_env_all_modules mods) args (tx.args ++ dflt_vs) =
       SOME scope /\
     call_external orc gobs am tx =
       (case call_external_body orc gobs' am cx nr mut (type_env_all_modules mods)
               scope body ret of
          (INL value, am', rqs) =>
            (INL value, finalize_pending_deletions am', rqs)
        | failure => failure) /\
     no_type_error_result
       (FST (call_external_body orc gobs' am cx nr mut (type_env_all_modules mods)
               scope body ret)) /\
     !exc.
       FST (call_external_body orc gobs' am cx nr mut (type_env_all_modules mods)
              scope body ret) = INR exc ==>
       exc <> BreakException /\ exc <> ContinueException)
Proof
  strip_tac >>
  `!orc. no_type_error_result (FST (call_external orc gobs am tx)) /\
         !exc. FST (call_external orc gobs am tx) = INR exc ==>
               exc <> BreakException /\ exc <> ContinueException` by
    (gen_tac >> Cases_on `call_external orc gobs am tx` >>
     rename1 `call_external orc gobs am tx = (res,rest)` >>
     PairCases_on `rest` >> simp[] >>
     conj_tac >- (drule_all checked_call_external_no_type_error >> simp[]) >>
     rpt gen_tac >> strip_tac >> gvs[] >>
     drule_all checked_call_external_no_loop_control >> simp[]) >>
  `lookup_exported_function cx am tx.function_name =
     SOME (mut,nr,args,dflts,ret,body)` by gvs[selected_entry_def] >>
  drule_all checked_selected_entry_defaults_cases >>
  disch_then (qspec_then `gobs` strip_assume_tac)
  >- (disj2_tac >>
      drule_all checked_selected_entry_bind_arguments >> strip_tac >>
      drule_all call_external_selected_entry_body >> strip_tac >>
      qexistsl [`vs`, `gobs'`, `scope`] >>
      qpat_x_assum `cx = _` kall_tac >> qpat_x_assum `src = _` kall_tac >>
      fs[finalize_case_FST] >> metis_tac[]) >>
  disj1_tac >>
  drule_all call_external_selected_entry_defaults_fail >> strip_tac >>
  (conj_tac >- first_assum ACCEPT_TAC >>
   conj_tac >- (qexistsl [`pre`, `e`, `post`, `g`] >> gvs[]) >>
   metis_tac[])
QED
