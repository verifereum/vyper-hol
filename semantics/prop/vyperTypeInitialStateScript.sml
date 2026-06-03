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
  vyperAST vyperValue vyperTyping vyperState vyperInterpreter vyperContext
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

(* We use env_context_consistent directly for static context consistency,
 * rather than duplicating its static-map clauses under a separate predicate.
 * The callable-entry theorem below takes a statically consistent base env and
 * proves that argument binding plus runtime immutable readiness establishes the
 * full env_consistent precondition for the function-body env. *)
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

(* Constants and immutables share runtime storage.  This side condition records
 * the static fact needed to show that evaluating constants cannot overwrite the
 * immutable entries needed for bare globals. *)
Definition constants_do_not_clobber_bare_globals_def:
  constants_do_not_clobber_bare_globals mods bare_globals <=>
    !src ts vis e id typ slot.
      ALOOKUP mods src = SOME ts /\
      MEM (VariableDecl vis (Constant e) id typ slot) ts ==>
      FLOOKUP bare_globals (src,string_to_num id) = NONE
End


(* Small lookup/update facts for the runtime immutable association-list and
 * finite-map layers.  Keeping these as boundary lemmas prevents downstream
 * proofs from repeatedly unfolding the representation. *)
Theorem get_source_immutables_set_same:
  get_source_immutables src (set_source_immutables src fm imms) = fm
Proof
  simp[get_source_immutables_def, set_source_immutables_def]
QED

Theorem get_source_immutables_set_other:
  src <> src' ==>
  get_source_immutables src (set_source_immutables src' fm imms) =
  get_source_immutables src imms
Proof
  simp[get_source_immutables_def, set_source_immutables_def,
       alistTheory.ALOOKUP_ADELKEY]
QED

Theorem update_immutable_lookup_same:
  FLOOKUP (get_source_immutables src (update_immutable src id tv v imms)) id =
  SOME (tv,v)
Proof
  simp[update_immutable_def, get_source_immutables_set_same,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem update_immutable_preserves_other_source:
  src <> src' ==>
  get_source_immutables src (update_immutable src' id tv v imms) =
  get_source_immutables src imms
Proof
  simp[update_immutable_def, get_source_immutables_set_other]
QED

Theorem update_immutable_preserves_lookup:
  (src' = src ==> key <> id) /\
  FLOOKUP (get_source_immutables src imms) id = SOME x ==>
  FLOOKUP (get_source_immutables src (update_immutable src' key tv v imms)) id = SOME x
Proof
  rw[update_immutable_def] >>
  Cases_on `src' = src` >>
  gvs[get_source_immutables_set_same, get_source_immutables_set_other,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem FLOOKUP_FUNION_left_none:
  FLOOKUP f k = NONE /\ FLOOKUP g k = SOME x ==>
  FLOOKUP (FUNION f g) k = SOME x
Proof
  simp[FLOOKUP_FUNION]
QED

Theorem initial_target_immutables_lookup:
  ALOOKUP ((am with immutables updated_by CONS (addr, imms)).immutables) addr = SOME imms
Proof
  simp[]
QED
(* ===== Runtime immutable setup ===== *)

Theorem initial_immutables_module_preserves_lookup:
  initial_immutables_module tenv src ts acc = SOME imms /\
  IS_SOME (FLOOKUP (get_source_immutables src acc) id) ==>
  IS_SOME (FLOOKUP (get_source_immutables src imms) id)
Proof
  qid_spec_tac `acc` >>
  Induct_on `ts` >>
  rw[initial_immutables_module_def] >>
  gvs[] >>
  Cases_on `h` >>
  gvs[initial_immutables_module_def, AllCaseEqs()] >>
  TRY (Cases_on `v0` >> gvs[initial_immutables_module_def, AllCaseEqs()]) >>
  first_x_assum drule >>
  disch_then irule >>
  Cases_on `string_to_num s = id` >>
  gvs[update_immutable_lookup_same] >>
  gvs[update_immutable_def, get_source_immutables_set_same,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem initial_immutables_module_preserves_any_lookup:
  initial_immutables_module tenv init_src ts acc = SOME imms /\
  IS_SOME (FLOOKUP (get_source_immutables query_src acc) id) ==>
  IS_SOME (FLOOKUP (get_source_immutables query_src imms) id)
Proof
  qid_spec_tac `acc` >>
  Induct_on `ts` >>
  rw[initial_immutables_module_def] >>
  gvs[] >>
  Cases_on `h` >>
  gvs[initial_immutables_module_def, AllCaseEqs()] >>
  TRY (Cases_on `v0` >> gvs[initial_immutables_module_def, AllCaseEqs()]) >>
  first_x_assum drule >>
  disch_then irule >>
  Cases_on `init_src = query_src` >>
  gvs[update_immutable_preserves_other_source] >>
  Cases_on `string_to_num s = id` >>
  gvs[update_immutable_lookup_same] >>
  gvs[update_immutable_def, get_source_immutables_set_same,
      finite_mapTheory.FLOOKUP_UPDATE]
QED


Theorem initial_immutables_module_contains_immutable:
  initial_immutables_module tenv src ts acc = SOME imms /\
  is_immutable_decl id ts /\
  find_var_decl_by_num id ts = NONE ==>
  IS_SOME (FLOOKUP (get_source_immutables src imms) id)
Proof
  qid_spec_tac `acc` >>
  Induct_on `ts` >>
  rw[initial_immutables_module_def, is_immutable_decl_def,
     find_var_decl_by_num_def] >>
  gvs[] >>
  Cases_on `h` >>
  gvs[initial_immutables_module_def, is_immutable_decl_def,
      find_var_decl_by_num_def] >>
  TRY (Cases_on `v0` >>
       gvs[initial_immutables_module_def, is_immutable_decl_def,
           find_var_decl_by_num_def]) >>
  rw[] >>
  gvs[AllCaseEqs(), update_immutable_lookup_same] >>
  FIRST_PROVE [
    irule initial_immutables_module_preserves_lookup >>
    goal_assum (drule_at Any) >>
    simp[update_immutable_lookup_same],
    first_x_assum drule >> simp[]]
QED

Theorem initial_immutables_contains_decl:
  initial_immutables tenv mods = SOME imms /\
  ALOOKUP mods src = SOME ts /\
  is_immutable_decl id ts /\
  find_var_decl_by_num id ts = NONE ==>
  IS_SOME (FLOOKUP (get_source_immutables src imms) id)
Proof
  qid_spec_tac `imms` >>
  qid_spec_tac `src` >>
  qid_spec_tac `ts` >>
  qid_spec_tac `id` >>
  Induct_on `mods` >>
  simp[initial_immutables_def] >>
  rpt gen_tac >>
  PairCases_on `h` >>
  Cases_on `h0 = src` >>
  rw[initial_immutables_def] >>
  gvs[AllCaseEqs()]
  >- (irule initial_immutables_module_contains_immutable >>
      qexistsl [`acc`,`tenv`,`h1`] >>
      simp[]) >>
  irule initial_immutables_module_preserves_any_lookup >>
  goal_assum (drule_at Any) >>
  first_x_assum irule >>
  simp[]
QED

Theorem initial_immutables_contains_bare_global:
  env_context_consistent env_base cx /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  initial_immutables (get_tenv cx) mods = SOME imms /\
  FLOOKUP env_base.bare_globals (src,id) = SOME ty ==>
  IS_SOME (FLOOKUP (get_source_immutables src imms) id)
Proof
  cheat
QED

Theorem initial_immutables_bare_global_type:
  env_context_consistent env_base cx /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  initial_immutables (get_tenv cx) mods = SOME imms /\
  FLOOKUP env_base.bare_globals (src,id) = SOME ty /\
  FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) ==>
  evaluate_type (get_tenv cx) ty = SOME tv
Proof
  cheat
QED

Theorem constants_env_no_bare_global_lookup:
  constants_do_not_clobber_bare_globals mods bare_globals /\
  ALOOKUP mods src = SOME ts /\
  constants_env cx am addr src ts FEMPTY = SOME cenv /\
  FLOOKUP bare_globals (src,id) = SOME ty ==>
  FLOOKUP cenv id = NONE
Proof
  cheat
QED

Theorem merge_constants_preserves_lookup:
  (src = src_c ==> FLOOKUP cenv id = NONE) /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am.immutables addr of SOME m => m | NONE => []))
    id = SOME x ==>
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP (merge_constants addr src_c cenv am).immutables addr of
       | SOME m => m
       | NONE => []))
    id = SOME x
Proof
  cheat
QED

Theorem evaluate_all_constants_preserves_bare_global_lookup:
  constants_do_not_clobber_bare_globals mods bare_globals /\
  ALOOKUP mods src = SOME ts /\
  FLOOKUP bare_globals (src,id) = SOME ty /\
  evaluate_all_constants cx am addr mods = SOME am_c /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am.immutables addr of SOME m => m | NONE => []))
    id = SOME x ==>
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => []))
    id = SOME x
Proof
  cheat
QED

Theorem evaluate_all_constants_preserves_bare_global_type:
  constants_do_not_clobber_bare_globals mods env_base.bare_globals /\
  env_context_consistent env_base cx /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  FLOOKUP env_base.bare_globals (src,id) = SOME ty /\
  evaluate_all_constants cx am cx.txn.target mods = SOME am_c /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am.immutables cx.txn.target of SOME m => m | NONE => []))
    id = SOME (tv,v) /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => []))
    id = SOME (tv,v)
Proof
  cheat
QED

Theorem deployment_setup_immutables_ready:
  constants_do_not_clobber_bare_globals mods env_base.bare_globals /\
  env_context_consistent env_base cx /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  initial_immutables (get_tenv cx) mods = SOME imms /\
  evaluate_all_constants cx
    (am with immutables updated_by CONS (cx.txn.target, imms))
    cx.txn.target mods = SOME am_c ==>
  immutables_ready
    env_base.bare_globals
    env_base.toplevel_vtypes
    cx
    am_c.immutables
Proof
  cheat
QED

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

Theorem env_context_consistent_static_maps_function_side_condition:
  env_context_consistent env_base cx ==>
    (!src id ty. FLOOKUP env_base.bare_globals (src,id) = SOME ty ==>
       ?ts. get_module_code cx src = SOME ts /\
            FLOOKUP env_base.toplevel_vtypes (src,id) = SOME (Type ty) /\
            is_immutable_decl id ts /\
            find_var_decl_by_num id ts = NONE /\
            ty <> NoneT) /\
    (!src id vt ts.
       FLOOKUP env_base.toplevel_vtypes (src,id) = SOME vt /\
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
       FLOOKUP env_base.flag_members (src,fid) = SOME ls ==>
       ?ts. get_module_code cx src = SOME ts /\
            lookup_flag fid ts = SOME ls /\
            FLOOKUP (get_tenv cx) (string_to_num fid) =
              SOME (FlagArgs (LENGTH ls)))
Proof
  rw[env_context_consistent_def]
  >- (Cases_on `vt` >> gvs[]
      >- (rename1 `FLOOKUP env_base.toplevel_vtypes (src,id) = SOME (Type ty)` >>
          Cases_on `FLOOKUP env_base.bare_globals (src,id)`
          >- (qpat_x_assum
                `!src id ty. FLOOKUP env_base.toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP env_base.bare_globals (src,id) = NONE ==> _`
                (qspecl_then [`src`, `id`, `ty`] mp_tac) >>
              simp[] >> rw[] >> gvs[]) >>
          rename1 `FLOOKUP env_base.bare_globals (src,id) = SOME bare_ty` >>
          qpat_x_assum
            `!src id ty. FLOOKUP env_base.bare_globals (src,id) = SOME ty ==> ?ts. _`
            (qspecl_then [`src`, `id`, `bare_ty`] mp_tac) >>
          simp[] >> strip_tac >> gvs[] >>
          qpat_x_assum
            `!src id vt. FLOOKUP env_base.toplevel_vtypes (src,id) = SOME vt ==> _`
            (qspecl_then [`src`, `id`, `Type bare_ty`] mp_tac) >>
          simp[well_formed_vtype_def, well_formed_type_def]) >>
      rename1 `FLOOKUP env_base.toplevel_vtypes (src,id) = SOME (HashMapT kt hv)` >>
      qpat_x_assum
        `!src id kt vt. FLOOKUP env_base.toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==> _`
        (qspecl_then [`src`, `id`, `kt`, `hv`] mp_tac) >>
      simp[] >> rw[] >> gvs[])
QED

Theorem functions_well_typed_callable_body_env_base:
  functions_well_typed cx /\
  env_context_consistent env_base cx /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,body) ==>
  ?env_body env_after.
    env_body.current_src = src /\
    env_body.type_defs = env_base.type_defs /\
    env_body.fn_sigs = env_base.fn_sigs /\
    env_body.bare_globals = env_base.bare_globals /\
    env_body.toplevel_vtypes = env_base.toplevel_vtypes /\
    env_body.flag_members = env_base.flag_members /\
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
  first_x_assum
    (qspecl_then [`env_base.fn_sigs`, `env_base.bare_globals`,
                  `env_base.toplevel_vtypes`, `env_base.flag_members`] mp_tac) >>
  impl_tac
  >- (drule env_context_consistent_static_maps_function_side_condition >>
      strip_tac >> gvs[env_context_consistent_def] >>
      rw[] >> first_x_assum drule_all >> simp[]) >>
  disch_then
    (qspecl_then [`src`, `fn`, `ts`, `fm`, `nr`, `args`, `dflts`, `ret`, `body`] mp_tac) >>
  simp[] >> rw[] >>
  qexistsl [`env_body`, `env_after`] >>
  rw[] >> gvs[env_context_consistent_def] >> metis_tac[]
QED

Theorem env_context_consistent_same_static_maps:
  env_context_consistent env_base cx /\
  env.current_src = env_base.current_src /\
  env.type_defs = env_base.type_defs /\
  env.fn_sigs = env_base.fn_sigs /\
  env.bare_globals = env_base.bare_globals /\
  env.toplevel_vtypes = env_base.toplevel_vtypes /\
  env.flag_members = env_base.flag_members ==>
  env_context_consistent env cx
Proof
  rw[env_context_consistent_def] >> gvs[] >> metis_tac[]
QED

Theorem immutables_ready_env_immutables_consistent:
  env.bare_globals = env_base.bare_globals /\
  env.toplevel_vtypes = env_base.toplevel_vtypes /\
  immutables_ready env_base.bare_globals env_base.toplevel_vtypes cx am.immutables ==>
  env_immutables_consistent env cx (initial_state am [scope])
Proof
  rw[immutables_ready_def, env_immutables_consistent_def, initial_state_def] >> metis_tac[]
QED

(* Main #282 theorem: callable-entry setup establishes the preconditions of the
 * statement type-soundness theorem for the selected function body.
 *
 * The source/current-module alignment is expressed through env_base:
 * env_context_consistent env_base cx ties env_base.current_src to
 * current_module cx, while env_base.current_src = src selects the callable
 * body source.  The top-level call_external integration still has to ensure
 * that the evaluation context is aligned with the selected function source;
 * exported-module calls should be handled at that layer. *)
Theorem callable_entry_establishes_type_soundness_preconditions:
  functions_well_typed cx /\
  context_well_typed cx /\
  machine_well_typed am /\
  env_context_consistent env_base cx /\
  env_base.current_src = src /\
  immutables_ready env_base.bare_globals env_base.toplevel_vtypes cx am.immutables /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,body) /\
  bind_arguments (get_tenv cx) args vals = SOME scope /\
  args_values_typed (get_tenv cx) args vals ==>
  ?env_body env_after st.
    st = initial_state am [scope] /\
    env_body.current_src = src /\
    env_body.type_defs = env_base.type_defs /\
    env_body.fn_sigs = env_base.fn_sigs /\
    env_body.bare_globals = env_base.bare_globals /\
    env_body.toplevel_vtypes = env_base.toplevel_vtypes /\
    env_body.flag_members = env_base.flag_members /\
    accounts_well_typed st.accounts /\
    state_well_typed st /\
    env_consistent env_body cx st /\
    type_stmts env_body ret body = SOME env_after
Proof
  strip_tac >> gvs[] >>
  drule_all functions_well_typed_callable_body_env_base >>
  strip_tac >>
  `scope_well_typed scope` by
    (qspecl_then [`get_tenv cx`, `args`, `vals`, `scope`] mp_tac
       bind_arguments_scope_well_typed_stmt >>
     simp[] >>
     disch_then irule >>
     rpt strip_tac >>
     gvs[args_values_typed_def]) >>
  qexistsl [`env_body`, `env_after`] >>
  rw[initial_state_accounts_well_typed, initial_state_single_scope_well_typed] >>
  rw[env_consistent_def]
  >- (irule env_context_consistent_same_static_maps >> qexists `env_base` >> gvs[])
  >- (`env_scopes_consistent env_body cx
         ((initial_state am [scope]) with scopes := [scope])` suffices_by
        gvs[initial_state_def] >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`, `get_tenv cx`, `vals`] >>
      gvs[] >> metis_tac[])
  >- (irule immutables_ready_env_immutables_consistent >> qexists `env_base` >> gvs[])
QED

(* Direct corollary for type soundness: once callable-entry setup has established
 * the existing preconditions, the already-proved statement theorem gives no
 * runtime TypeError for executing the body from the entry state. *)
Theorem callable_entry_no_type_error:
  functions_well_typed cx /\
  context_well_typed cx /\
  machine_well_typed am /\
  env_context_consistent env_base cx /\
  env_base.current_src = src /\
  immutables_ready env_base.bare_globals env_base.toplevel_vtypes cx am.immutables /\
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
    machine_well_typed am /\
    accounts_well_typed st.accounts /\
    state_well_typed st /\
    env_consistent env_body cx st /\
    type_stmts env_body NoneT [] = SOME env_after
Proof
  qexists `empty_evaluation_context` >>
  qexists `initial_machine_state` >>
  qexists `<| current_src := NONE;
              var_types := FEMPTY;
              var_assignable := FEMPTY;
              bare_globals := FEMPTY;
              toplevel_vtypes := FEMPTY;
              type_defs := FEMPTY;
              fn_sigs := FEMPTY;
              flag_members := FEMPTY |>` >>
  qexists `<| current_src := NONE;
              var_types := FEMPTY;
              var_assignable := FEMPTY;
              bare_globals := FEMPTY;
              toplevel_vtypes := FEMPTY;
              type_defs := FEMPTY;
              fn_sigs := FEMPTY;
              flag_members := FEMPTY |>` >>
  qexists `initial_state initial_machine_state [FEMPTY]` >>
  simp[type_stmt_def, initial_state_def, initial_machine_state_def,
       empty_evaluation_context_def, empty_call_txn_def, get_tenv_def,
       get_module_code_def, current_module_def, functions_well_typed_def,
       context_well_typed_def, env_consistent_def, env_context_consistent_def,
       env_scopes_consistent_def, env_immutables_consistent_def,
       fn_sigs_consistent_def, fn_sigs_complete_def, state_well_typed_def,
       scope_well_typed_def, vyperStateTheory.lookup_scopes_def,
       accounts_well_typed_def, account_well_typed_def, machine_well_typed_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.empty_accounts_def,
       vfmStateTheory.empty_account_state_def]
QED
