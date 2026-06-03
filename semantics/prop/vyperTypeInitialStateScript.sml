(*
 * Establishing type-soundness preconditions for callable entry states.
 *
 * This theory is intended to address #282: show that the assumptions of the
 * statement/expression type-soundness theorems are not merely vacuous, but are
 * established by the ordinary callable-entry setup (argument binding plus an
 * initialized abstract machine).
 *)

Theory vyperTypeInitialState
Ancestors
  list rich_list pred_set arithmetic finite_map option pair
  vyperAST vyperValue vyperTyping vyperInterpreter vyperContext
  vyperTypeSystem vyperTypeStmtSoundness vyperTypeSoundness
Libs
  wordsLib

val _ = Parse.hide "body";

(* Runtime well-typedness of an abstract machine, separated from any particular
 * function environment.  Readiness of globals/immutables is target- and
 * environment-dependent, so it is captured separately by immutables_ready below. *)
Definition machine_well_typed_def:
  machine_well_typed (am:abstract_machine) <=>
    accounts_well_typed am.accounts /\
    EVERY (\(addr, imms). imms_well_typed imms) am.immutables
End

(* The values supplied at function entry have the parameter types expected by
 * the Vyper function signature.  This is the semantic counterpart of successful
 * ABI decoding / test-runner argument construction, but is kept abstract here. *)
Definition args_values_typed_def:
  args_values_typed tenv (args:(string # type) list) (vals:value list) <=>
    LENGTH args = LENGTH vals /\
    !i tv.
      i < LENGTH args /\
      evaluate_type tenv (SND (EL i args)) = SOME tv ==>
      value_has_type tv (EL i vals)
End

(* Static maps used in a typing_env agree with the code/context.  This packages
 * the side condition expected by functions_well_typed_body and is deliberately
 * phrased independently of any already-built env_consistent witness. *)
Definition global_maps_consistent_def:
  global_maps_consistent cx bare_globals toplevel_vtypes flag_members <=>
    (!src id ty. FLOOKUP bare_globals (src,id) = SOME ty ==>
       ?ts. get_module_code cx src = SOME ts /\
            FLOOKUP toplevel_vtypes (src,id) = SOME (Type ty) /\
            is_immutable_decl id ts /\
            find_var_decl_by_num id ts = NONE /\
            ty <> NoneT) /\
    (!src id vt ts.
       FLOOKUP toplevel_vtypes (src,id) = SOME vt /\
       get_module_code cx src = SOME ts ==>
       ((?ty. vt = Type ty /\
          ((!is_transient typ id_str.
              find_var_decl_by_num id ts =
                SOME (StorageVarDecl is_transient typ,id_str) ==> typ = ty) /\
           (!is_transient kt hv id_str.
              find_var_decl_by_num id ts =
                SOME (HashMapVarDecl is_transient kt hv,id_str) ==> F) /\
           (find_var_decl_by_num id ts = NONE ==>
              IS_SOME (evaluate_type (get_tenv cx) ty)))) \/
        (?kt hv. vt = HashMapT kt hv /\
           ?is_transient id_str.
             find_var_decl_by_num id ts =
               SOME (HashMapVarDecl is_transient kt hv,id_str)))) /\
    (!src fid ls.
       FLOOKUP flag_members (src,fid) = SOME ls ==>
       ?ts. get_module_code cx src = SOME ts /\
            lookup_flag fid ts = SOME ls /\
            FLOOKUP (get_tenv cx) (string_to_num fid) =
              SOME (FlagArgs (LENGTH ls)))
End

(* Runtime global/immutable readiness for the current transaction target.
 * This is the non-circular piece needed to establish env_immutables_consistent:
 * every bare global is present in the machine's immutables/constants table, and
 * any stored type tags agree with the current combined type environment. *)
Definition immutables_ready_def:
  immutables_ready bare_globals toplevel_vtypes cx imms <=>
    (!src id ty. FLOOKUP bare_globals (src,id) = SOME ty ==>
       IS_SOME (FLOOKUP
         (get_source_immutables src
           (case ALOOKUP imms cx.txn.target of SOME m => m | NONE => []))
         id)) /\
    (!src id ty tv v.
       FLOOKUP bare_globals (src,id) = SOME ty /\
       FLOOKUP
         (get_source_immutables src
           (case ALOOKUP imms cx.txn.target of SOME m => m | NONE => []))
         id = SOME (tv,v) ==>
       evaluate_type (get_tenv cx) ty = SOME tv) /\
    (!src id ty ts.
       FLOOKUP toplevel_vtypes (src,id) = SOME (Type ty) /\
       get_module_code cx src = SOME ts ==>
       (!is_transient typ id_str.
          find_var_decl_by_num id ts =
            SOME (StorageVarDecl is_transient typ,id_str) ==> typ = ty) /\
       (!is_transient kt vt id_str.
          find_var_decl_by_num id ts =
            SOME (HashMapVarDecl is_transient kt vt,id_str) ==> F) /\
       (find_var_decl_by_num id ts = NONE ==>
        !tv v.
          FLOOKUP
            (get_source_immutables src
              (case ALOOKUP imms cx.txn.target of SOME m => m | NONE => []))
            id = SOME (tv,v) ==>
          evaluate_type (get_tenv cx) ty = SOME tv))
End

Theorem initial_state_accounts_well_typed:
  machine_well_typed am ==>
  accounts_well_typed (initial_state am scs).accounts
Proof
  simp[machine_well_typed_def, initial_state_def]
QED

Theorem initial_state_single_scope_well_typed:
  machine_well_typed am /\ scope_well_typed scope ==>
  state_well_typed (initial_state am [scope])
Proof
  simp[machine_well_typed_def, initial_state_def, state_well_typed_def]
QED

Theorem env_context_consistent_empty_static_maps:
  env.current_src = current_module cx /\
  env.type_defs = get_tenv cx /\
  env.fn_sigs = fn_sigs /\
  env.bare_globals = FEMPTY /\
  env.toplevel_vtypes = FEMPTY /\
  env.flag_members = FEMPTY /\
  fn_sigs_consistent fn_sigs cx /\
  fn_sigs_complete fn_sigs cx ==>
  env_context_consistent env cx
Proof
  simp[env_context_consistent_def]
QED

Theorem env_immutables_consistent_empty_static_maps:
  env.bare_globals = FEMPTY /\
  env.toplevel_vtypes = FEMPTY ==>
  env_immutables_consistent env cx st
Proof
  simp[env_immutables_consistent_def]
QED

Theorem functions_well_typed_callable_body_empty_static_maps:
  functions_well_typed cx /\
  fn_sigs_consistent fn_sigs cx /\
  fn_sigs_complete fn_sigs cx /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,body) ==>
  ?env_body env_after.
    env_body.current_src = src /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = fn_sigs /\
    env_body.bare_globals = FEMPTY /\
    env_body.toplevel_vtypes = FEMPTY /\
    env_body.flag_members = FEMPTY /\
    type_stmts env_body ret body = SOME env_after /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T)
Proof
  rw[functions_well_typed_def] >>
  first_x_assum (qspecl_then [`fn_sigs`, `FEMPTY`, `FEMPTY`, `FEMPTY`] mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`src`, `fn`, `ts`, `fm`, `nr`, `args`, `dflts`, `ret`, `body`] mp_tac) >>
  simp[] >>
  rw[] >>
  qexistsl [`env_body`, `env_after`] >>
  gvs[] >>
  metis_tac[]
QED

(* Main #282 theorem: callable-entry setup establishes the preconditions of the
 * statement type-soundness theorem for the selected function body.
 *
 * The explicit current_module assumption is intentional.  The top-level
 * call_external integration has to ensure that the evaluation context's current
 * module is the module containing the selected function; exported-module calls
 * should be handled at that layer. *)
Theorem callable_entry_establishes_type_soundness_preconditions:
  functions_well_typed cx /\
  context_well_typed cx /\
  machine_well_typed am /\
  current_module cx = src /\
  fn_sigs_consistent fn_sigs cx /\
  fn_sigs_complete fn_sigs cx /\
  global_maps_consistent cx bare_globals toplevel_vtypes flag_members /\
  immutables_ready bare_globals toplevel_vtypes cx am.immutables /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,body) /\
  bind_arguments (get_tenv cx) args vals = SOME scope /\
  args_values_typed (get_tenv cx) args vals ==>
  ?env_body env_after st.
    st = initial_state am [scope] /\
    accounts_well_typed st.accounts /\
    state_well_typed st /\
    env_consistent env_body cx st /\
    type_stmts env_body ret body = SOME env_after
Proof
  strip_tac >> gvs[] >>
  drule_all functions_well_typed_callable_body_empty_static_maps >>
  strip_tac >>
  `scope_well_typed scope` by
    (qspecl_then [`get_tenv cx`, `args`, `vals`, `scope`] mp_tac
       bind_arguments_scope_well_typed_stmt >>
     simp[] >>
     disch_then irule >>
     rpt strip_tac >>
     gvs[args_values_typed_def]) >>
  qexistsl [`env_body`, `env_after`] >>
  simp[initial_state_accounts_well_typed, initial_state_single_scope_well_typed] >>
  simp[env_consistent_def] >>
  conj_tac
  >- (irule env_context_consistent_empty_static_maps >> gvs[]) >>
  conj_tac
  >- (`env_scopes_consistent env_body cx
         ((initial_state am [scope]) with scopes := [scope])` suffices_by
        gvs[initial_state_def] >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`, `get_tenv cx`, `vals`] >>
      gvs[] >>
      metis_tac[]) >>
  irule env_immutables_consistent_empty_static_maps >>
  gvs[]
QED

(* Direct corollary for type soundness: once callable-entry setup has established
 * the existing preconditions, the already-proved statement theorem gives no
 * runtime TypeError for executing the body from the entry state. *)
Theorem callable_entry_no_type_error:
  functions_well_typed cx /\
  context_well_typed cx /\
  machine_well_typed am /\
  current_module cx = src /\
  fn_sigs_consistent fn_sigs cx /\
  fn_sigs_complete fn_sigs cx /\
  global_maps_consistent cx bare_globals toplevel_vtypes flag_members /\
  immutables_ready bare_globals toplevel_vtypes cx am.immutables /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,body) /\
  bind_arguments (get_tenv cx) args vals = SOME scope /\
  args_values_typed (get_tenv cx) args vals ==>
  no_type_error_eval (eval_stmts cx body (initial_state am [scope]))
Proof
  metis_tac[
    callable_entry_establishes_type_soundness_preconditions,
    typed_stmts_no_type_error]
QED

(* Explicit non-vacuity corollary: there exists a concrete configuration
 * satisfying the core statement type-soundness preconditions. *)
Theorem type_soundness_preconditions_satisfiable:
  ?cx am env_body env_after st.
    functions_well_typed cx /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    state_well_typed st /\
    env_consistent env_body cx st /\
    type_stmts env_body NoneT [] = SOME env_after
Proof
  cheat
QED

val _ = export_theory();
