(*
 * Static typing-env extension/weakening facts for the executable type system.
 *)

Theory vyperTypeEnvExtension
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperMisc vyperABI vyperInterpreter vyperState
  vyperContext vyperStorage vyperTyping vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv
Libs
  wordsLib

(* ===== Static env-map well-formedness ===== *)

Definition env_maps_wf_def:
  env_maps_wf env <=>
    !id. FLOOKUP env.var_assignable id = SOME T ==>
         IS_SOME (FLOOKUP env.var_types id)
End

Theorem env_consistent_env_maps_wf:
  env_consistent env cx st ==> env_maps_wf env
Proof
  rw[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def, env_maps_wf_def]
QED

Theorem env_maps_wf_no_stale_assignable_T:
  env_maps_wf env /\ id NOTIN FDOM env.var_types ==>
  FLOOKUP env.var_assignable id <> SOME T
Proof
  rw[env_maps_wf_def, TO_FLOOKUP] >>
  first_x_assum (qspec_then `id` mp_tac) >> simp[]
QED

Theorem extend_local_env_maps_wf:
  env_maps_wf env ==> env_maps_wf (extend_local env id ty assignable)
Proof
  rw[env_maps_wf_def, extend_local_def, FLOOKUP_UPDATE] >>
  Cases_on `id = id'` >> gvs[]
QED

(* ===== Static-field preservation for executable statement typing ===== *)

Theorem extend_local_preserves_static:
  (extend_local env id ty assignable).type_defs = env.type_defs /\
  (extend_local env id ty assignable).current_src = env.current_src /\
  (extend_local env id ty assignable).fn_sigs = env.fn_sigs /\
  (extend_local env id ty assignable).bare_globals = env.bare_globals /\
  (extend_local env id ty assignable).bare_global_assignable = env.bare_global_assignable /\
  (extend_local env id ty assignable).toplevel_vtypes = env.toplevel_vtypes /\
  (extend_local env id ty assignable).flag_members = env.flag_members
Proof
  simp[extend_local_def]
QED

Theorem type_stmt_preserve_nonlocal_fields:
  type_stmt env ret_ty s = SOME env' ==>
  env'.current_src = env.current_src /\
  env'.bare_globals = env.bare_globals /\
  env'.bare_global_assignable = env.bare_global_assignable /\
  env'.toplevel_vtypes = env.toplevel_vtypes /\
  env'.type_defs = env.type_defs /\
  env'.fn_sigs = env.fn_sigs /\
  env'.flag_members = env.flag_members
Proof
  Cases_on `s` >> rw[type_stmt_def, AllCaseEqs(), extend_local_def] >>
  gvs[oneline type_stmt_def, AllCaseEqs(), extend_local_def]
QED

Theorem type_stmts_preserve_nonlocal_fields:
  type_stmts env ret_ty ss = SOME env' ==>
  env'.current_src = env.current_src /\
  env'.bare_globals = env.bare_globals /\
  env'.bare_global_assignable = env.bare_global_assignable /\
  env'.toplevel_vtypes = env.toplevel_vtypes /\
  env'.type_defs = env.type_defs /\
  env'.fn_sigs = env.fn_sigs /\
  env'.flag_members = env.flag_members
Proof
  qid_spec_tac `env` >> Induct_on `ss` >>
  rw[type_stmt_def] >>
  gvs[type_stmt_def, AllCaseEqs()] >>
  drule type_stmt_preserve_nonlocal_fields >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[]
QED

Theorem type_stmt_env_preserved_static:
  type_stmt env ret_ty s = SOME env' ==>
  env'.type_defs = env.type_defs /\ env'.current_src = env.current_src /\
  env'.fn_sigs = env.fn_sigs /\ env'.bare_globals = env.bare_globals /\
  env'.bare_global_assignable = env.bare_global_assignable /\
  env'.toplevel_vtypes = env.toplevel_vtypes /\ env'.flag_members = env.flag_members
Proof
  metis_tac[type_stmt_preserve_nonlocal_fields]
QED

Theorem type_stmts_env_preserved_static:
  type_stmts env ret_ty ss = SOME env' ==>
  env'.type_defs = env.type_defs /\ env'.current_src = env.current_src /\
  env'.fn_sigs = env.fn_sigs /\ env'.bare_globals = env.bare_globals /\
  env'.bare_global_assignable = env.bare_global_assignable /\
  env'.toplevel_vtypes = env.toplevel_vtypes /\ env'.flag_members = env.flag_members
Proof
  metis_tac[type_stmts_preserve_nonlocal_fields]
QED

Theorem type_stmt_env_consistent_preserved_static:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st ==>
  env'.type_defs = env.type_defs /\ env'.current_src = env.current_src /\
  env'.fn_sigs = env.fn_sigs /\ env'.bare_globals = env.bare_globals /\
  env'.bare_global_assignable = env.bare_global_assignable /\
  env'.toplevel_vtypes = env.toplevel_vtypes /\ env'.flag_members = env.flag_members
Proof
  metis_tac[type_stmt_env_preserved_static]
QED

Theorem type_stmts_env_consistent_preserved_static:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st ==>
  env'.type_defs = env.type_defs /\ env'.current_src = env.current_src /\
  env'.fn_sigs = env.fn_sigs /\ env'.bare_globals = env.bare_globals /\
  env'.bare_global_assignable = env.bare_global_assignable /\
  env'.toplevel_vtypes = env.toplevel_vtypes /\ env'.flag_members = env.flag_members
Proof
  metis_tac[type_stmts_env_preserved_static]
QED

(* ===== Variable-map preservation for executable statement typing ===== *)

Theorem type_stmt_env_maps_wf:
  env_maps_wf env /\ type_stmt env ret_ty s = SOME env' ==>
  env_maps_wf env'
Proof
  Cases_on `s` >> gvs[type_stmt_def, AllCaseEqs()] >>
  TRY (rename1 `Assert e a` >> Cases_on `a` >> gvs[type_stmt_def]) >>
  TRY (rename1 `Raise r` >> Cases_on `r` >> gvs[type_stmt_def]) >>
  TRY (rename1 `Return r` >> Cases_on `r` >> gvs[type_stmt_def]) >>
  TRY (rw[env_maps_wf_def, extend_local_def, FLOOKUP_UPDATE] >>
       Cases_on `string_to_num s'' = id` >> gvs[FLOOKUP_UPDATE]) >>
  strip_tac >> gvs[]
QED

Theorem type_stmts_env_maps_wf:
  env_maps_wf env /\ type_stmts env ret_ty ss = SOME env' ==>
  env_maps_wf env'
Proof
  MAP_EVERY qid_spec_tac [`env`, `env'`] >>
  Induct_on `ss` >> gvs[type_stmt_def, AllCaseEqs()] >>
  metis_tac[type_stmt_env_maps_wf]
QED

Theorem type_stmt_var_types_mono:
  type_stmt env ret_ty s = SOME env' /\ FLOOKUP env'.var_types id = NONE ==>
  FLOOKUP env.var_types id = NONE
Proof
  Cases_on `s` >> gvs[type_stmt_def, AllCaseEqs(), extend_local_def, FLOOKUP_UPDATE] >>
  TRY (rename1 `Assert e a` >> Cases_on `a` >> gvs[type_stmt_def]) >>
  TRY (rename1 `Raise r` >> Cases_on `r` >> gvs[type_stmt_def]) >>
  TRY (rename1 `Return r` >> Cases_on `r` >> gvs[type_stmt_def]) >>
  rw[] >> gvs[FLOOKUP_UPDATE]
QED

Theorem type_stmt_var_types_preserve:
  type_stmt env ret_ty s = SOME env' /\ FLOOKUP env.var_types id = SOME ty ==>
  FLOOKUP env'.var_types id = SOME ty
Proof
  Cases_on `s` >> gvs[type_stmt_def, AllCaseEqs(), extend_local_def, FLOOKUP_UPDATE] >>
  TRY (rename1 `Assert e a` >> Cases_on `a` >> gvs[type_stmt_def]) >>
  TRY (rename1 `Raise r` >> Cases_on `r` >> gvs[type_stmt_def]) >>
  TRY (rename1 `Return r` >> Cases_on `r` >> gvs[type_stmt_def]) >>
  rw[] >> gvs[FLOOKUP_UPDATE] >>
  Cases_on `string_to_num s'' = id` >> gvs[] >>
  fs[TO_FLOOKUP]
QED

Theorem type_stmts_var_types_preserve:
  type_stmts env ret_ty ss = SOME env' /\ FLOOKUP env.var_types id = SOME ty ==>
  FLOOKUP env'.var_types id = SOME ty
Proof
  MAP_EVERY qid_spec_tac [`env`, `env'`] >>
  Induct_on `ss` >> gvs[type_stmt_def, AllCaseEqs()] >>
  metis_tac[type_stmt_var_types_preserve]
QED

Theorem type_stmts_var_types_mono:
  type_stmts env ret_ty ss = SOME env' /\ FLOOKUP env'.var_types id = NONE ==>
  FLOOKUP env.var_types id = NONE
Proof
  MAP_EVERY qid_spec_tac [`env`, `env'`] >>
  Induct_on `ss` >> gvs[type_stmt_def, AllCaseEqs()] >>
  metis_tac[type_stmt_var_types_mono]
QED

Theorem type_stmt_var_assignable_T_preserve:
  env_maps_wf env /\ type_stmt env ret_ty s = SOME env' /\
  FLOOKUP env.var_assignable id = SOME T ==>
  FLOOKUP env'.var_assignable id = SOME T
Proof
  Cases_on `s` >> gvs[type_stmt_def, AllCaseEqs(), extend_local_def, FLOOKUP_UPDATE] >>
  TRY (rename1 `Assert e a` >> Cases_on `a` >> gvs[type_stmt_def]) >>
  TRY (rename1 `Raise r` >> Cases_on `r` >> gvs[type_stmt_def]) >>
  TRY (rename1 `Return r` >> Cases_on `r` >> gvs[type_stmt_def]) >>
  rw[] >> gvs[FLOOKUP_UPDATE] >>
  Cases_on `string_to_num s'' = id` >> gvs[] >>
  fs[env_maps_wf_def, TO_FLOOKUP]
QED

Theorem type_stmts_var_assignable_T_preserve:
  env_maps_wf env /\ type_stmts env ret_ty ss = SOME env' /\
  FLOOKUP env.var_assignable id = SOME T ==>
  FLOOKUP env'.var_assignable id = SOME T
Proof
  MAP_EVERY qid_spec_tac [`env`, `env'`] >>
  Induct_on `ss` >> gvs[type_stmt_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >>
  `FLOOKUP env''.var_assignable id = SOME T` by
    metis_tac[type_stmt_var_assignable_T_preserve] >>
  `env_maps_wf env''` by metis_tac[type_stmt_env_maps_wf] >>
  first_x_assum drule_all >> simp[]
QED

(* ===== Env extension relation ===== *)

Definition env_extends_def:
  env_extends env env' <=>
    env'.type_defs = env.type_defs /\ env'.current_src = env.current_src /\
    env'.fn_sigs = env.fn_sigs /\ env'.bare_globals = env.bare_globals /\
    env'.bare_global_assignable = env.bare_global_assignable /\
    env'.toplevel_vtypes = env.toplevel_vtypes /\ env'.flag_members = env.flag_members /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==> FLOOKUP env'.var_types id = SOME ty) /\
    (!id. FLOOKUP env.var_assignable id = SOME T ==> FLOOKUP env'.var_assignable id = SOME T)
End

Theorem env_extends_refl[simp]:
  env_extends env env
Proof
  simp[env_extends_def]
QED

Theorem env_extends_trans:
  env_extends env1 env2 /\ env_extends env2 env3 ==> env_extends env1 env3
Proof
  rw[env_extends_def] >> metis_tac[]
QED

Theorem type_stmt_env_extends:
  env_maps_wf env /\ type_stmt env ret_ty s = SOME env' ==> env_extends env env'
Proof
  strip_tac >>
  drule_all type_stmt_env_preserved_static >> strip_tac >>
  rw[env_extends_def] >>
  metis_tac[type_stmt_var_types_preserve, type_stmt_var_assignable_T_preserve]
QED

Theorem type_stmts_env_extends:
  env_maps_wf env /\ type_stmts env ret_ty ss = SOME env' ==> env_extends env env'
Proof
  strip_tac >>
  drule_all type_stmts_env_preserved_static >> strip_tac >>
  rw[env_extends_def] >>
  metis_tac[type_stmts_var_types_preserve, type_stmts_var_assignable_T_preserve]
QED
