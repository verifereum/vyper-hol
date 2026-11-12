Theory targetGuardedInternalCallStorageFrame
Ancestors
  targetInternalCallStorageFrame vyperCallOutcomeFrame vyperEvalFrame vyperTypeEvalSoundness vyperTypeEvalStoragePreservation
  vyperInterpreter vyperState vyperStorageBackend vyperTypeExprSoundness vyperTypeEnv vyperTypeInvariants pair list
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";

(* The empty defaults scope has its own typing environment.  In particular,
   this is not transport of the caller's environment across push_function. *)
Theorem intcall_defaults_runtime_entry:
  runtime_consistent env cx st /\ functions_well_typed cx /\
  env_body.current_src = src /\
  env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members ==>
  runtime_consistent (defaults_env env_body)
    (cx with stk updated_by CONS (src,fn)) (st with scopes := [FEMPTY]) /\
  functions_well_typed (cx with stk updated_by CONS (src,fn))
Proof
  strip_tac >>
  fs[runtime_consistent_def] >>
  drule_all intcall_default_env_side_conditions >> strip_tac >>
  `env_consistent (defaults_env env_body)
     (cx with stk updated_by CONS (src,fn)) (st with scopes := [FEMPTY])` by
    (irule defaults_env_empty_frame_consistent >> simp[]) >>
  gvs[runtime_consistent_def, state_well_typed_def, scope_well_typed_def]
QED

(* Successful-prefix composition keeps the guard on the actual entry state;
   it never turns a guarded recursive premise into an all-state frame. *)
Triviality guarded_bind_observer:
  (!s r t. P s /\ f s = (r,t) ==> obs t = obs s) /\
  (!s v t r u. P s /\ f s = (INL v,t) /\ g v t = (r,u) ==>
     obs u = obs t) ==>
  !s r t. P s /\ bind f g s = (r,t) ==> obs t = obs s
Proof
  strip_tac >> rpt gen_tac >>
  simp_tac bool_ss [bind_def] >>
  Cases_on `f s` >> Cases_on `q` >> gvs[] >> metis_tac[]
QED

Theorem intcall_defaults_guarded_storage_frame:
  (!st res fin. P (st with scopes := [FEMPTY]) /\
     eval_exprs cx es (st with scopes := [FEMPTY]) = (res,fin) ==>
     lookup_storage w (get_storage ocx fin tr) =
     lookup_storage w (get_storage ocx (st with scopes := [FEMPTY]) tr)) ==>
  !st res fin prev. P (st with scopes := [FEMPTY]) /\
    finally (do set_scopes [FEMPTY]; eval_exprs cx es od)
      (set_scopes prev) st = (res,fin) ==>
    lookup_storage w (get_storage ocx fin tr) =
    lookup_storage w (get_storage ocx st tr)
Proof
  strip_tac >> rpt gen_tac >>
  simp_tac bool_ss [finally_def, bind_def, ignore_bind_def,
    set_scopes_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  Cases_on `q` >>
  simp_tac bool_ss [set_scopes_def, ignore_bind_def, bind_def,
    return_def, raise_def, PAIR_EQ, sumTheory.INL_11, sumTheory.INR_11] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >>
  simp[get_storage_scopes]
QED

Theorem intcall_defaults_runtime_storage_frame:
  runtime_consistent env cx st /\ functions_well_typed cx /\
  env_body.current_src = src /\
  env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members /\
  (!s res fin. runtime_consistent (defaults_env env_body)
       (cx with stk updated_by CONS (src,fn)) s /\
     eval_exprs (cx with stk updated_by CONS (src,fn)) needed s = (res,fin) ==>
     lookup_storage w (get_storage cx fin tr) =
     lookup_storage w (get_storage cx s tr)) /\
  finally (do set_scopes [FEMPTY];
              eval_exprs (cx with stk updated_by CONS (src,fn)) needed od)
    (set_scopes prev) st = (res,fin) ==>
  lookup_storage w (get_storage cx fin tr) = lookup_storage w (get_storage cx st tr)
Proof
  strip_tac >> drule_all intcall_defaults_runtime_entry >> strip_tac >>
  irule intcall_defaults_guarded_storage_frame >>
  qexistsl_tac [`runtime_consistent (defaults_env env_body)
    (cx with stk updated_by CONS (src,fn))`,
    `cx with stk updated_by CONS (src,fn)`, `needed`, `prev`, `res`] >>
  simp[]
QED

Theorem intcall_body_runtime_entry:
  runtime_consistent env cx st /\ functions_well_typed cx /\
  env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members /\
  scope_well_typed call_env /\
  env_scopes_consistent env_body cx (st with scopes := [call_env]) /\
  lock_if_nr cx nr view st = (INL (),locked) ==>
  runtime_consistent env_body
    (cx with stk updated_by CONS (env_body.current_src,fn))
    (locked with scopes := [call_env])
Proof
  strip_tac >> fs[runtime_consistent_def] >>
  drule intcall_default_env_side_conditions >>
  disch_then (qspecl_then [`env_body`,`env_body.current_src`,`fn`] mp_tac) >>
  simp[] >> strip_tac >>
  `env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (locked with scopes := [call_env]) /\
    state_well_typed (locked with scopes := [call_env]) /\
    accounts_well_typed (locked with scopes := [call_env]).accounts` by
    (irule intcall_live_pushed_body_preconditions >>
     simp[lock_if_nr_def] >>
     conj_tac
     >- (qexistsl_tac [`st`,`env`] >> simp[]) >>
     qexistsl_tac [`st`,`view`,`nr`] >>
     gvs[env_scopes_consistent_def, vyperContextTheory.get_tenv_def] >>
     first_assum ACCEPT_TAC) >>
  gvs[runtime_consistent_def]
QED

Triviality guarded_finally_observer:
  (!s r t. P s /\ f s = (r,t) ==> obs t = obs s) /\
  state_rel_frame (\s t. obs t = obs s) g ==>
  !s r t. P s /\ finally f g s = (r,t) ==> obs t = obs s
Proof
  simp_tac bool_ss [state_rel_frame_result, finally_def] >>
  strip_tac >> rpt gen_tac >>
  Cases_on `f s` >> Cases_on `q` >>
  simp_tac bool_ss [bind_def, ignore_bind_def] >>
  Cases_on `g r'` >> Cases_on `q` >>
  gvs[return_def, raise_def] >> metis_tac[]
QED

Triviality guarded_try_observer:
  (!s r t. P s /\ f s = (r,t) ==> obs t = obs s) /\
  (!e. state_rel_frame (\s t. obs t = obs s) (h e)) ==>
  !s r t. P s /\ try f h s = (r,t) ==> obs t = obs s
Proof
  simp_tac bool_ss [state_rel_frame_result, try_def] >>
  strip_tac >> rpt gen_tac >>
  Cases_on `f s` >> Cases_on `q` >> gvs[return_def] >> metis_tac[]
QED
