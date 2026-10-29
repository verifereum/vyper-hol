(*
 * Checked deployment reaches the constructor body (#618, part of #420), the
 * deployment analogue of vyperTypeSelectedEntrySoundness.
 *
 * For a checked contract and constructor arguments that fit the constructor's
 * parameters, every setup step of load_contract succeeds: the initial
 * immutables evaluate, the constructor has no defaults, the arguments bind,
 * and the deployment constants fold succeeds (#617).  load_contract is then
 * call_constructor_body from the bound scope and the folded machine, and that
 * run's result is not a TypeError and does not escape with break or
 * continue.
 *
 * TOP-LEVEL: checked_constructor_bind_arguments,
 *            load_contract_constructor_body,
 *            checked_load_contract_no_static_error.
 *
 * Helper: check_contract_initial_immutables,
 *         check_contract_constructor_no_defaults,
 *         checked_constructor_{args_distinct, nonreentrant_slot,
 *           no_control_escape, call_evaluation_safe} (static facts),
 *         checked_constructor_{constants_exist,
 *           initial_immutables_consistent} (constants setup),
 *         checked_constructor_prefix_{typing, no_type_error, return_typed,
 *           no_loop_control} (lock, value transfer and body run),
 *         call_constructor_body_no_{type_error, loop_control}_from_prefix,
 *         checked_constructor_body_no_static_error.
 *)

Theory vyperTypeDeploymentSoundness
Ancestors
  list pair alist
  vyperAST vyperValue vyperState vyperInterpreter vyperContext
  vyperTypeSystem vyperTypeExprSoundness vyperTypeInitialState
  vyperTypeEntryReadiness vyperTypeContract vyperTypeContractStaticMaps
  vyperTypeContractContext vyperTypeContractSoundness
  vyperTypeSelectedEntrySoundness vyperTypeDeploymentMachine
  vyperTypeCallGraph vyperTypeCallGraphSoundness vyperTypeCallStackSoundness
  vyperTypeExternalCallMachine vyperTypeInvariants vyperTypeBindArguments
  vyperTypeStmtSoundness vyperTypeStmtResult vyperTypeEvalSoundness
  vyperExprNoControl

val _ = Parse.hide "body";

(* Constructors have no defaults.  Transfer first, then hand the actual
   transferred state to the shared scope/lock/body continuation. *)
Definition call_constructor_body_def:
  call_constructor_body orc am cx nr mut tenv scope body ret =
    case send_call_value mut cx
      (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>) of
      (INR exc, st) => (INR exc, am, st.requests)
    | (INL (), st) => call_external_body am cx nr mut tenv st scope body ret
End

Theorem constructor_call_observed[local]:
  cx.in_deploy /\
  evaluate_all_constants cx am0 cx.txn.target mods = SOME am_c /\
  LENGTH vals = LENGTH args /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope ==>
  (case call_external_function orc am0 cx nr mut (ts:toplevel list)
          mods args [] vals body ret of
     (INR e,_,_) => INR e
   | (INL v,am',rqs) => INL (v,am',rqs)) =
  (case call_constructor_body orc am_c cx nr mut (type_env_all_modules mods)
          scope body ret of
     (INR e,_,_) => INR e
   | (INL v,am',rqs) => INL (v,am',rqs))
Proof
  strip_tac >>
  simp[call_external_function_def, call_constructor_body_def] >>
  Cases_on `send_call_value mut cx
    (initial_state am_c [FEMPTY] with <|outcomes := orc; requests := []|>)` >>
  Cases_on `q` >>
  simp[call_external_body_def, bind_def, ignore_bind_def, set_scopes_def, return_def] >>
  TRY (rename1 `send_call_value _ _ _ = (INR exc,_)` >>
       drule send_call_value_no_control_c53 >>
       Cases_on `exc` >> simp[no_control_exc_def] >> NO_TAC) >>
  qabbrev_tac `lock_action = if nr then
    case cx.nonreentrant_slot of
      NONE => raise (Error (TypeError "nonreentrant slot missing"))
    | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                     (mut = View \/ mut = Pure)
    else return ()` >>
  Cases_on `lock_action (r with scopes := [scope])` >>
  Cases_on `q` >> simp[] >>
  TRY (rename1 `eval_stmts cx body st` >>
       Cases_on `eval_stmts cx body st` >> Cases_on `q` >> simp[]) >>
  qabbrev_tac `unlock_action = if nr /\ mut <> View /\ mut <> Pure then
    case cx.nonreentrant_slot of NONE => return ()
    | SOME slot => release_nonreentrant_lock cx.txn.target slot
    else return ()` >>
  TRY (rename1 `eval_stmts _ _ _ = (INR exc,_)` >>
       Cases_on `exc` >> simp[]) >>
  TRY (rename1 `lock_action _ = (INR exc,_)` >>
       Cases_on `exc` >> simp[]) >>
  TRY (rename1 `send_call_value _ _ _ = (INR exc,_)` >>
       Cases_on `exc` >> simp[]) >>
  TRY (qmatch_goalsub_rename_tac `unlock_action final_st` >>
       Cases_on `unlock_action final_st` >> Cases_on `q` >> simp[]) >>
  rpt (CASE_TAC >> simp[])
QED

(* ===== Setup steps ===== *)

Theorem check_contract_initial_immutables:
  check_contract in_deploy layouts addr mods = SOME art ==>
  ?imms. initial_immutables (type_env_all_modules mods) mods = SOME imms
Proof
  rw[check_contract_def, contract_constants_ok_def] >>
  Cases_on `initial_immutables (type_env_all_modules mods) mods` >> gvs[]
QED


(* TOP-LEVEL: the constructor counterpart of
   checked_selected_entry_bind_arguments.  The constructor has no defaults, so
   the ABI premise is an exact length match plus provided_args_typed. *)
Theorem checked_constructor_bind_arguments:
  check_contract in_deploy layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  LENGTH tx.args = LENGTH args /\
  provided_args_typed (type_env_all_modules mods) args tx.args ==>
  dflts = [] /\
  ?scope.
    bind_arguments (type_env_all_modules mods) args tx.args = SOME scope /\
    args_values_typed (type_env_all_modules mods) args tx.args
Proof
  strip_tac >>
  conj_asm1_tac >- metis_tac[check_contract_constructor_no_defaults] >>
  `!arg. MEM arg args ==>
     ?tv. evaluate_type (type_env_all_modules mods) (SND arg) = SOME tv` by
    (drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[] >>
     gvs[check_contract_def, EVERY_MEM] >>
     drule ALOOKUP_MEM >> strip_tac >>
     first_x_assum drule >> simp[check_module_def, EVERY_MEM] >>
     strip_tac >>
     qpat_x_assum `!e. MEM e ts ==> check_toplevel_decl _ _ _ _ _ _` drule >>
     simp[check_toplevel_decl_def, params_ok_def, EVERY_MEM] >>
     rpt strip_tac >> PairCases_on `arg` >> first_x_assum drule >> simp[] >>
     metis_tac[assignable_type_well_formed, well_formed_type_def,
               optionTheory.IS_SOME_EXISTS]) >>
  drule_then (qspecl_then [`[]`,`[]`] mp_tac)
    provided_args_defaults_bind_arguments >>
  simp[DROP_LENGTH_TOO_LONG]
QED

(* TOP-LEVEL: load_contract is the constructor body run once setup has
   succeeded. *)
Theorem load_contract_constructor_body:
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,[],ret,body) /\
  cx = (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx
          NONE with in_deploy := T) /\
  LENGTH tx.args = LENGTH args /\
  bind_arguments (type_env_all_modules mods) args tx.args = SOME scope /\
  evaluate_all_constants cx
    (am with <|immutables updated_by CONS (tx.target,imms);
               exports updated_by CONS (tx.target,exps)|>)
    tx.target mods = SOME am_c ==>
  load_contract orc am tx mods exps =
    case call_constructor_body orc am_c cx nr mut (type_env_all_modules mods)
           scope body ret of
      (INR e, _, _) => INR e
    | (INL _, am', rqs) =>
        INL (finalize_pending_deletions
               (am' with sources updated_by CONS (tx.target,mods)), rqs)
Proof
  strip_tac >>
  `cx.in_deploy /\ cx.txn.target = tx.target` by
    gvs[initial_evaluation_context_def] >>
  `evaluate_all_constants cx
     (am with <|immutables updated_by CONS (tx.target,imms);
                exports updated_by CONS (tx.target,exps)|>)
     cx.txn.target mods = SOME am_c` by
    (qpat_x_assum `evaluate_all_constants _ _ tx.target _ = _` mp_tac >> simp[]) >>
  drule_all constructor_call_observed >>
  disch_then (qspecl_then [`ts`,`ret`,`orc`,`nr`,`mut`,`body`] mp_tac) >>
  simp[load_contract_def] >>
  qpat_x_assum `cx = _` (fn th => rewrite_tac[GSYM th]) >>
  rpt (CASE_TAC >> gvs[])
QED

(* ===== Constructor static boundary ===== *)

Theorem checked_constructor_args_distinct:
  check_contract T layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) ==>
  ALL_DISTINCT (MAP FST args)
Proof
  strip_tac >>
  drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[] >>
  drule_all check_contract_deploy_function_body_MEM >>
  simp[check_function_body_def, params_ok_def]
QED

Theorem checked_constructor_nonreentrant_slot:
  check_contract T layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context sources layouts tx NONE with in_deploy := T) ==>
  (nr ==> cx.nonreentrant_slot <> NONE)
Proof
  strip_tac >>
  drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[] >>
  drule_all check_contract_deploy_function_body_MEM >>
  simp[check_function_body_def, initial_evaluation_context_def] >>
  Cases_on `lookup_nonreentrant_slot layouts tx.target` >> simp[]
QED

Theorem checked_constructor_no_control_escape:
  check_contract T layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) ==>
  stmts_no_control_escape body
Proof
  strip_tac >>
  drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[]
  >- simp[stmt_no_control_escape_def] >>
  drule_all check_contract_deploy_function_body_MEM >>
  simp[check_function_body_def]
QED

Theorem checked_constructor_call_evaluation_safe:
  check_contract T layouts tx.target mods = SOME art /\
  ALOOKUP sources tx.target = SOME mods /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context sources layouts tx NONE with in_deploy := T) ==>
  call_evaluation_safe cx (int_calls_stmts body)
Proof
  strip_tac >>
  drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[]
  >- (`(initial_evaluation_context sources layouts tx NONE with in_deploy := T) =
        ((initial_evaluation_context sources layouts tx NONE with in_deploy := T)
           with stk := [(NONE,tx.function_name)])` by
        simp[initial_evaluation_context_def] >>
      pop_assum SUBST1_TAC >>
      irule (INST_TYPE [``:'a`` |-> ``:num``]
        checked_contract_call_evaluation_safe_singleton) >>
      qexistsl [`art`,`layouts`,`mods`] >>
      simp[initial_evaluation_context_def, calls_follow_call_graph_def]) >>
  irule checked_constructor_body_call_evaluation_safe >>
  qexistsl [`args`,`art`,`dflts`,`mods`,`mut`,`nr`,`raw`,`ret`,`ts`] >> simp[]
QED

(* ===== Constants setup boundary ===== *)

Theorem checked_constructor_constants_exist:
  check_contract T am.layouts tx.target mods = SOME deploy_art /\
  check_contract F am.layouts tx.target mods = SOME runtime_art /\
  machine_well_typed am /\
  cx = (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx
          NONE with in_deploy := T) /\
  context_well_typed cx /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms ==>
  ?am_c.
    evaluate_all_constants cx
      (am with <|immutables updated_by CONS (tx.target,imms);
                 exports updated_by CONS (tx.target,exps)|>)
      tx.target mods = SOME am_c /\ machine_well_typed am_c
Proof
  strip_tac >>
  drule_all checked_constructor_constants_ready >>
  disch_then (qspec_then `exps` assume_tac) >>
  `machine_well_typed
     (am with <|immutables updated_by CONS (tx.target,imms);
                exports updated_by CONS (tx.target,exps)|>)` by
    (irule deployment_initial_machine_well_typed >> simp[] >>
     qexists `mods` >> simp[]) >>
  drule_all checked_deployment_constants_establish_machine_well_typed >>
  strip_tac >> qexists `am_c` >> simp[]
QED

Theorem checked_constructor_initial_immutables_consistent:
  check_contract T am.layouts tx.target mods = SOME deploy_art /\
  check_contract F am.layouts tx.target mods = SOME runtime_art /\
  cx = (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx
          NONE with in_deploy := T) /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants cx
    (am with <|immutables updated_by CONS (tx.target,imms);
               exports updated_by CONS (tx.target,exps)|>)
    tx.target mods = SOME am_c ==>
  env_immutables_consistent (artifact_env deploy_art mods NONE) cx
    (initial_state am_c [scope] with <|outcomes := orc; requests := rqs|>)
Proof
  strip_tac >>
  irule checked_deployment_constants_establish_initial_env_immutables_consistent >>
  qexistsl [`am with exports updated_by CONS (tx.target,exps)`,`imms`,
    `am.layouts`,`runtime_art`,`(tx.target,mods)::am.sources`,`tx.target`,`tx`] >>
  simp[]
QED

Theorem checked_constructor_prefix_typing:
  check_contract T am.layouts tx.target mods = SOME deploy_art /\
  check_contract F am.layouts tx.target mods = SOME runtime_art /\
  machine_well_typed am /\ ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx
          NONE with in_deploy := T) /\ context_well_typed cx /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants cx
    (am with <|immutables updated_by CONS (tx.target,imms);
               exports updated_by CONS (tx.target,exps)|>)
    tx.target mods = SOME am_c /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  send_call_value mut cx
    (initial_state am_c [FEMPTY] with <|outcomes := orc; requests := rqs|>) =
      (INL (),send_st) /\
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                      (mut = View \/ mut = Pure)
   else return ())
    (send_st with scopes := [scope]) = (INL (),body_st) ==>
  ?env_body env_after.
    type_stmts env_body ret body = SOME env_after /\
    env_consistent env_body cx body_st /\
    env_body.type_defs = type_env_all_modules mods /\
    state_well_typed body_st /\ accounts_well_typed body_st.accounts /\
    context_well_typed cx /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body)
Proof
  strip_tac >>
  `machine_well_typed am_c` by
    (drule_all checked_constructor_constants_exist >>
     disch_then (qspec_then `exps` mp_tac) >> strip_tac >> gvs[]) >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `state_well_typed (initial_state am_c [FEMPTY] with <|outcomes := orc; requests := rqs|>) /\
   accounts_well_typed (initial_state am_c [FEMPTY] with <|outcomes := orc; requests := rqs|>).accounts` by
    gvs[machine_well_typed_def, state_well_typed_def, initial_state_def, scope_well_typed_def] >>
  `state_well_typed send_st /\ accounts_well_typed send_st.accounts /\
   send_st.immutables = am_c.immutables` by
    (drule_all send_call_value_state_sound_c53 >> simp[initial_state_def]) >>
  `body_st.scopes = [scope] /\ body_st.immutables = am_c.immutables /\
   state_well_typed body_st /\ accounts_well_typed body_st.accounts` by
    (drule call_lock_action_frame_c53 >> gvs[state_well_typed_def]) >>
  `env_immutables_consistent (artifact_env deploy_art mods NONE) cx body_st` by
    (drule_all checked_constructor_initial_immutables_consistent >>
     disch_then (qspecl_then [`scope`,`rqs`,`orc`] assume_tac) >>
     irule (iffLR env_immutables_consistent_immutables_cong) >>
     qexists `initial_state am_c [scope] with <|outcomes := orc; requests := rqs|>` >>
     simp[initial_state_def]) >>
  `ALL_DISTINCT (MAP FST args)` by
    (drule_all checked_constructor_args_distinct >> simp[]) >>
  `?env_body env_after.
     type_stmts env_body ret body = SOME env_after /\
     env_consistent env_body cx body_st /\
     context_well_typed cx /\ functions_well_typed cx /\ state_well_typed body_st` by
    (irule checked_constructor_body_setup >> simp[] >>
     qexistsl [`args`,`deploy_art`,`dflts`,`am.layouts`,`mods`,`mut`,`nr`,
       `runtime_art`,`(tx.target,mods)::am.sources`,`ts`,`tx`,`vals`] >>
     gvs[]) >>
  qexistsl [`env_body`,`env_after`] >> simp[] >> conj_tac
  >- gvs[env_consistent_def, env_context_consistent_def,
         get_tenv_def, initial_evaluation_context_def] >>
  irule checked_constructor_call_evaluation_safe >>
  qexistsl [`args`,`deploy_art`,`dflts`,`am.layouts`,`mods`,`mut`,`nr`,
    `ret`,`(tx.target,mods)::am.sources`,`ts`,`tx`] >> simp[]
QED

Theorem checked_constructor_prefix_no_type_error:
  check_contract T am.layouts tx.target mods = SOME deploy_art /\
  check_contract F am.layouts tx.target mods = SOME runtime_art /\
  machine_well_typed am /\ ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx
          NONE with in_deploy := T) /\ context_well_typed cx /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants cx
    (am with <|immutables updated_by CONS (tx.target,imms);
               exports updated_by CONS (tx.target,exps)|>)
    tx.target mods = SOME am_c /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope ==>
  no_type_error_eval
    (do
       send_call_value mut cx;
       set_scopes [scope];
       (if nr then
          case cx.nonreentrant_slot of
            NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                           (mut = View \/ mut = Pure)
        else return ());
       eval_stmts cx body
     od (initial_state am_c [FEMPTY] with <|outcomes := orc; requests := []|>))
Proof
  strip_tac >>
  `nr ==> cx.nonreentrant_slot <> NONE` by
    (strip_tac >> drule_all checked_constructor_nonreentrant_slot >> simp[]) >>
  qmatch_goalsub_abbrev_tac `ignore_bind (send_call_value mut cx)
    (ignore_bind (set_scopes [scope]) (ignore_bind lock_action (eval_stmts cx body)))` >>
  qpat_x_assum `cx = _` (assume_tac o GSYM) >>
  simp[no_type_error_eval_def, ignore_bind_def, bind_def, set_scopes_def, return_def] >>
  Cases_on `send_call_value mut cx
    (initial_state am_c [FEMPTY] with <|outcomes := orc; requests := []|>)` >>
  rename1 `_ = (send_res,send_st)` >> Cases_on `send_res`
  >- (Cases_on `lock_action (send_st with scopes := [scope])` >>
      rename1 `_ = (lock_res,body_st)` >> Cases_on `lock_res`
      >- (Cases_on `x` >> Cases_on `x'` >> fs[] >>
          qunabbrev_tac `lock_action` >>
          qpat_x_assum `_ = cx` (assume_tac o GSYM) >>
          drule_all (SRULE [] checked_constructor_prefix_typing) >> strip_tac >> gvs[] >>
          drule_all eval_stmts_no_type_error >> simp[no_type_error_eval_def]) >>
      `no_type_error_eval (lock_action (send_st with scopes := [scope]))` by
        (qunabbrev_tac `lock_action` >> irule call_lock_action_no_type_error_c53 >> simp[]) >>
      gvs[no_type_error_eval_def]) >>
  `no_type_error_eval (send_call_value mut cx
    (initial_state am_c [FEMPTY] with <|outcomes := orc; requests := []|>))` by
    simp[send_call_value_no_type_error_c53] >>
  gvs[no_type_error_eval_def]
QED

Theorem checked_constructor_prefix_return_typed:
  check_contract T am.layouts tx.target mods = SOME deploy_art /\
  check_contract F am.layouts tx.target mods = SOME runtime_art /\
  machine_well_typed am /\ ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx
          NONE with in_deploy := T) /\ context_well_typed cx /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants cx
    (am with <|immutables updated_by CONS (tx.target,imms);
               exports updated_by CONS (tx.target,exps)|>)
    tx.target mods = SOME am_c /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  (do
     send_call_value mut cx;
     set_scopes [scope];
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                         (mut = View \/ mut = Pure)
      else return ());
     eval_stmts cx body
   od (initial_state am_c [FEMPTY] with <|outcomes := orc; requests := []|>)) =
     (INR (ReturnException v),st') ==>
  ?tv. evaluate_type (type_env_all_modules mods) ret = SOME tv /\ value_has_type tv v
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `ignore_bind (send_call_value mut cx)
    (ignore_bind (set_scopes [scope]) (ignore_bind lock_action (eval_stmts cx body)))` >>
  qpat_x_assum `cx = _` (assume_tac o GSYM) >>
  gs[bind_def, ignore_bind_def, set_scopes_def, return_def, AllCaseEqs()] >>
  TRY (drule send_call_value_no_control_c53 >> simp[no_control_exc_def] >> NO_TAC) >>
  TRY (qunabbrev_tac `lock_action` >>
       drule call_lock_action_no_control_c53 >> simp[no_control_exc_def] >> NO_TAC) >>
  qunabbrev_tac `lock_action` >>
  qpat_x_assum `_ = cx` (assume_tac o GSYM) >>
  drule_all (SRULE [] checked_constructor_prefix_typing) >> strip_tac >> gvs[] >>
  drule_all eval_stmts_type_preservation_exception >>
  simp[stmt_error_ok_def, return_exception_typed_def, value_runtime_typed_def]
QED

Theorem checked_constructor_prefix_no_loop_control:
  check_contract T layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  (do
     send_call_value mut cx;
     set_scopes [scope];
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                         (mut = View \/ mut = Pure)
      else return ());
     eval_stmts cx body
   od st) = (INR exc,st') ==>
  exc <> BreakException /\ exc <> ContinueException
Proof
  strip_tac >>
  `stmts_no_control_escape body` by
    (drule_all checked_constructor_no_control_escape >> simp[]) >>
  qmatch_asmsub_abbrev_tac `ignore_bind (send_call_value mut cx)
    (ignore_bind (set_scopes [scope]) (ignore_bind lock_action (eval_stmts cx body)))` >>
  gs[bind_def, ignore_bind_def, set_scopes_def, return_def, AllCaseEqs()] >>
  FIRST_PROVE
    [metis_tac[vyperTypeEvalSoundnessTheory.stmts_no_control_escape_eval_stmts_no_loop_control],
     drule send_call_value_no_control_c53 >> rw[no_control_exc_def] >> gvs[],
     qunabbrev_tac `lock_action` >> drule call_lock_action_no_control_c53 >>
       rw[no_control_exc_def] >> gvs[]]
QED

Theorem triple_identity[local]:
  !p. (\(res,am_out,rqs). (res,am_out,rqs)) p = p
Proof
  Cases >> Cases_on `r` >> simp[]
QED

Theorem call_constructor_body_no_type_error_from_prefix:
  prefix = (do
    send_call_value mut cx;
    set_scopes [scope];
    (if nr then case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                      (mut = View \/ mut = Pure)
     else return ());
    eval_stmts cx body
  od (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>)) /\
  no_type_error_eval prefix /\
  (!v st. prefix = (INR (ReturnException v),st) ==>
    ?tv. evaluate_type tenv ret = SOME tv /\ value_has_type tv v) ==>
  no_type_error_result
    (FST (call_constructor_body orc am cx nr mut tenv scope body ret))
Proof
  strip_tac >>
  qabbrev_tac `unlock_action = if nr /\ mut <> View /\ mut <> Pure then
    case cx.nonreentrant_slot of NONE => return ()
    | SOME slot => release_nonreentrant_lock cx.txn.target slot
    else return ()` >>
  `!st. no_type_error_eval (unlock_action st)` by
    (qunabbrev_tac `unlock_action` >> simp[unlock_action_no_type_error_c53]) >>
  Cases_on `send_call_value mut cx
    (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>)` >>
  Cases_on `q`
  >- (fs[ignore_bind_def, bind_def, set_scopes_def, return_def] >>
      simp[call_constructor_body_def, call_external_body_def, triple_identity,
           ignore_bind_def, bind_def, set_scopes_def, return_def] >>
      qpat_assum `prefix = _` (fn th => rewrite_tac[GSYM th]) >>
  PairCases_on `prefix` >> Cases_on `prefix0` >>
  gvs[no_type_error_eval_def]
  >- (Cases_on `unlock_action prefix1` >>
      rename1 `_ = (unlock_res,unlock_st)` >> Cases_on `unlock_res` >>
      first_x_assum (qspec_then `prefix1` mp_tac) >>
      simp[no_type_error_eval_def, no_type_error_result_def]) >>
  Cases_on `y` >> gvs[no_type_error_result_def] >>
  simp[vyperTypingTheory.safe_cast_well_typed] >>
  Cases_on `unlock_action prefix1` >>
  rename1 `_ = (unlock_res,unlock_st)` >> Cases_on `unlock_res` >> simp[] >>
  first_x_assum (qspec_then `prefix1` mp_tac) >> simp[]) >>
  gvs[call_constructor_body_def, ignore_bind_def, bind_def, set_scopes_def,
      return_def, no_type_error_eval_def, no_type_error_result_def]
QED

Theorem call_constructor_body_no_loop_control_from_prefix:
  prefix = (do
    send_call_value mut cx;
    set_scopes [scope];
    (if nr then case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                      (mut = View \/ mut = Pure)
     else return ());
    eval_stmts cx body
  od (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>)) /\
  (!exc st. prefix = (INR exc,st) ==>
     exc <> BreakException /\ exc <> ContinueException) ==>
  !exc. FST (call_constructor_body orc am cx nr mut tenv scope body ret) = INR exc ==>
    exc <> BreakException /\ exc <> ContinueException
Proof
  strip_tac >>
  qabbrev_tac `unlock_action = if nr /\ mut <> View /\ mut <> Pure then
    case cx.nonreentrant_slot of NONE => return ()
    | SOME slot => release_nonreentrant_lock cx.txn.target slot
    else return ()` >>
  `!st exc st'. unlock_action st = (INR exc,st') ==> no_control_exc exc` by
    (qunabbrev_tac `unlock_action` >> metis_tac[unlock_action_no_control_c53]) >>
  Cases_on `send_call_value mut cx
    (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>)` >>
  Cases_on `q`
  >- (fs[ignore_bind_def, bind_def, set_scopes_def, return_def] >>
      simp[call_constructor_body_def, call_external_body_def, triple_identity,
           ignore_bind_def, bind_def, set_scopes_def, return_def] >>
      qpat_assum `prefix = _` (fn th => rewrite_tac[GSYM th]) >>
  PairCases_on `prefix` >> Cases_on `prefix0` >> gvs[]
  >- (Cases_on `unlock_action prefix1` >>
      rename1 `_ = (unlock_res,unlock_st)` >> Cases_on `unlock_res` >>
      gvs[] >> first_x_assum drule >> rw[no_control_exc_def] >> gvs[]) >>
  Cases_on `y` >> gvs[] >>
  Cases_on `unlock_action prefix1` >>
  rename1 `_ = (unlock_res,unlock_st)` >> Cases_on `unlock_res` >> gvs[]
  >- (Cases_on `evaluate_type tenv ret` >> gvs[] >>
      Cases_on `safe_cast x v` >> gvs[]) >>
  first_x_assum drule >> rw[no_control_exc_def] >> gvs[]) >>
  fs[call_constructor_body_def, ignore_bind_def, bind_def, set_scopes_def, return_def] >>
  metis_tac[]
QED

Theorem checked_constructor_body_no_static_error:
  check_contract T am.layouts tx.target mods = SOME deploy_art /\
  check_contract F am.layouts tx.target mods = SOME runtime_art /\
  machine_well_typed am /\ ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx
          NONE with in_deploy := T) /\ context_well_typed cx /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants cx
    (am with <|immutables updated_by CONS (tx.target,imms);
               exports updated_by CONS (tx.target,exps)|>)
    tx.target mods = SOME am_c /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope ==>
  no_type_error_result
    (FST (call_constructor_body orc am_c cx nr mut (type_env_all_modules mods)
            scope body ret)) /\
  (!exc. FST (call_constructor_body orc am_c cx nr mut (type_env_all_modules mods)
               scope body ret) = INR exc ==>
    exc <> BreakException /\ exc <> ContinueException)
Proof
  strip_tac >> conj_tac
  >- (irule call_constructor_body_no_type_error_from_prefix >>
      simp[NoAsms] >> conj_tac
      >- (rpt strip_tac >> drule_all checked_constructor_prefix_return_typed >>
          simp[]) >>
      drule_all checked_constructor_prefix_no_type_error >> simp[]) >>
  qx_gen_tac `exc` >> disch_tac >>
  irule call_constructor_body_no_loop_control_from_prefix >>
  simp[NoAsms] >> goal_assum (drule_at Any) >>
  rpt strip_tac >> drule_all checked_constructor_prefix_no_loop_control >> simp[]
QED

(* ===== Composition ===== *)

(* TOP-LEVEL: deployment analogue of checked_selected_entry_no_static_error.
   For a checked contract and constructor arguments that fit, load_contract
   gets through setup to the constructor body: it equals the body run from
   the bound scope and the folded machine, and that run is neither a
   TypeError nor an escaping break/continue.  Genuine runtime failures of
   the body or of value transfer are not excluded.

   Why: the lock has a slot because check_function_body requires one for a
   nonreentrant function (the synthetic constructor has nr = F); the body
   state is typed and its immutables ready as in
   checked_constructor_prefix_run_preserves_machine_well_typed, once
   checked_deployment_constants_ready_from_check discharges readiness; a
   ReturnException value is typed at ret by statement type preservation, so
   the return cast succeeds; stmts_no_control_escape comes from
   check_function_body. *)
Theorem checked_load_contract_no_static_error:
  check_contract T am.layouts tx.target mods = SOME deploy_art /\
  check_contract F am.layouts tx.target mods = SOME runtime_art /\
  machine_well_typed am /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx
          NONE with in_deploy := T) /\
  call_tx_well_typed tx /\
  LENGTH tx.args = LENGTH args /\
  provided_args_typed (type_env_all_modules mods) args tx.args ==>
  ?imms am_c scope.
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    evaluate_all_constants cx
      (am with <|immutables updated_by CONS (tx.target,imms);
                 exports updated_by CONS (tx.target,exps)|>)
      tx.target mods = SOME am_c /\
    bind_arguments (type_env_all_modules mods) args tx.args = SOME scope /\
    args_values_typed (type_env_all_modules mods) args tx.args /\
    load_contract orc am tx mods exps =
      (case call_constructor_body orc am_c cx nr mut (type_env_all_modules mods)
              scope body ret of
         (INR e, _, _) => INR e
       | (INL _, am', rqs) =>
           INL (finalize_pending_deletions
                  (am' with sources updated_by CONS (tx.target,mods)), rqs)) /\
    no_type_error_result
      (FST (call_constructor_body orc am_c cx nr mut (type_env_all_modules mods)
              scope body ret)) /\
    !exc.
      FST (call_constructor_body orc am_c cx nr mut (type_env_all_modules mods)
             scope body ret) = INR exc ==>
      exc <> BreakException /\ exc <> ContinueException
Proof
  strip_tac >>
  `context_well_typed cx` by
    gvs[call_tx_well_typed_def, context_well_typed_def,
        initial_evaluation_context_def] >>
  drule_all checked_constructor_bind_arguments >> strip_tac >>
  qpat_x_assum `dflts = []` SUBST_ALL_TAC >>
  drule check_contract_initial_immutables >> strip_tac >>
  drule_all checked_constructor_constants_exist >>
  disch_then (qspec_then `exps` strip_assume_tac) >>
  drule_all checked_constructor_body_no_static_error >>
  disch_then (qspec_then `orc` strip_assume_tac) >>
  drule_all load_contract_constructor_body >>
  disch_then (qspec_then `orc` assume_tac) >>
  qexistsl [`imms`,`am_c`,`scope`] >> simp[]
QED

(* Audit the complete dependency chain of the frozen result. *)
val _ = let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag checked_load_contract_no_static_error)
in
  if List.all (fn s => s = "DISK_THM") oracles andalso null axioms
  then () else raise Fail "unchecked oracle or axiom in checked deployment theorem"
end;
