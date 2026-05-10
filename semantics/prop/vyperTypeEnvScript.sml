(*
 * Environment, scope, immutable, and top-level lookup lemmas for the fresh
 * Vyper type system.
 *)

Theory vyperTypeEnv
Ancestors
  alist list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperMisc vyperABI vyperInterpreter vyperState
  vyperContext vyperStorage vyperTyping vyperTypeSystem vyperTypeValues
Libs
  wordsLib

(* ===== Local scopes ===== *)

Theorem scope_well_typed_lookup_scopes:
  EVERY scope_well_typed scopes /\ lookup_scopes id scopes = SOME entry ==>
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  qid_spec_tac `entry` >> qid_spec_tac `id` >> Induct_on `scopes` >>
  rw[lookup_scopes_def, scope_well_typed_def, AllCaseEqs()] >>
  first_x_assum drule_all >> rw[]
QED

Theorem env_consistent_lookup_var_type:
  env_consistent env cx st /\ state_well_typed st /\
  FLOOKUP env.var_types id = SOME ty /\ lookup_scopes id st.scopes = SOME entry ==>
  ?tv. evaluate_type env.type_defs ty = SOME tv /\ entry.type = tv /\
       value_has_type tv entry.value
Proof
  rw[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def, env_context_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def, state_well_typed_def]
  >> drule_all scope_well_typed_lookup_scopes
  >> strip_tac
  >> first_x_assum drule_all
  >> simp[]
QED

Theorem well_typed_Name_lookup:
  well_typed_expr env (Name ty id) /\ env_consistent env cx st /\ state_well_typed st ==>
  ?entry tv. lookup_scopes (string_to_num id) st.scopes = SOME entry /\
             evaluate_type env.type_defs ty = SOME tv /\ entry.type = tv /\
             value_has_type tv entry.value
Proof
  rw[well_typed_expr_def]
  >> `∃entry. lookup_scopes (string_to_num id) st.scopes = SOME entry`
  by (
    gvs[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def, env_scopes_consistent_def] >> last_x_assum drule
    >> rw[IS_SOME_EXISTS] )
  >> goal_assum drule
  >> conj_asm1_tac >- (
    gvs[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def, env_context_consistent_def, env_scopes_consistent_def] >>
    first_x_assum $ drule_then irule >>
    simp[] )
  >> drule_at(Pat`lookup_scopes`) $ env_consistent_lookup_var_type
  >> disch_then drule
  >> simp[]
QED

Theorem var_assignable_sound:
  env_consistent env cx st /\ FLOOKUP env.var_assignable id = SOME T ==>
  ?entry. lookup_scopes id st.scopes = SOME entry /\ entry.assignable
Proof
  rw[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def]
QED

Theorem NameTarget_sound:
  type_place_target env (NameTarget id) = SOME (Type ty) /\
  env_consistent env cx st ==>
  ?entry. lookup_scopes (string_to_num id) st.scopes = SOME entry /\ entry.assignable
Proof
  rw[well_typed_expr_def, env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def]
  >> gvs[well_typed_expr_def, AllCaseEqs(), LET_THM]
QED

Theorem lookup_scopes_head_fupdate_other:
  n1 <> n2 ==>
  lookup_scopes n2 ((h |+ (n1, entry))::rest) = lookup_scopes n2 (h::rest)
Proof
  rw[lookup_scopes_def, FLOOKUP_UPDATE]
QED

Theorem extend_local_env_consistent_after_new_variable:
  env_consistent env cx st /\ state_well_typed st /\
  evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
  string_to_num id NOTIN FDOM env.var_types /\
  new_variable id tv v st = (INL u, st') ==>
  env_consistent (extend_local env (string_to_num id) typ T) cx st'
Proof
  strip_tac >>
  simp[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def, extend_local_def] >>
  gvs[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def] >>
  gvs[new_variable_def, bind_def, AllCaseEqs(), ignore_bind_def,
      type_check_def, list_CASE_rator, raise_def, assert_def,
      set_scopes_def, return_def, get_scopes_def] >>
  gvs[lookup_scopes_def, FLOOKUP_UPDATE,AllCaseEqs()] >>
  rw[] >> gvs[] >> TRY(first_x_assum drule_all >> simp[]) >> TRY(res_tac >> gvs[])
QED


(* ===== Immutables / bare globals ===== *)

Theorem imms_well_typed_lookup:
  imms_well_typed imms /\ ALOOKUP imms src = SOME m /\ FLOOKUP m id = SOME (tv,v) ==>
  value_has_type tv v /\ well_formed_type_value tv
Proof
  rw[imms_well_typed_def]
  >> first_x_assum drule_all >> rw[]
QED

Theorem state_well_typed_immutables_ALOOKUP:
  state_well_typed st /\ ALOOKUP st.immutables addr = SOME imms ==>
  imms_well_typed imms
Proof
  rw[state_well_typed_def, EVERY_MEM, FORALL_PROD]
  >> first_x_assum irule
  >> imp_res_tac ALOOKUP_MEM
  >> goal_assum drule
QED

Theorem imms_well_typed_get_source_immutables:
  imms_well_typed imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) ==>
  value_has_type tv v /\ well_formed_type_value tv
Proof
  rw[get_source_immutables_def, AllCaseEqs()]
  >> pop_assum mp_tac >> CASE_TAC >> rw[]
  >> drule_all imms_well_typed_lookup
  >> simp[]
QED

Theorem current_immutables_well_typed:
  state_well_typed st ==>
  imms_well_typed (case ALOOKUP st.immutables addr of SOME m => m | NONE => [])
Proof
  rw[AllCaseEqs()]
  >> CASE_TAC >> rw[] >> TRY(rw[imms_well_typed_def] >> NO_TAC)
  >> drule_all state_well_typed_immutables_ALOOKUP
  >> simp[]
QED

Theorem bare_global_lookup_sound:
  well_typed_expr env (BareGlobalName ty id) /\ env_consistent env cx st /\
  state_well_typed st ==>
  ?tv v. FLOOKUP (get_source_immutables env.current_src
            (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => []))
            (string_to_num id) = SOME (tv,v) /\
         evaluate_type env.type_defs ty = SOME tv /\ value_has_type tv v
Proof
  simp[well_typed_expr_def, env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def] >>
  strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac`fl = SOME _` >>
  `IS_SOME fl` by (
    simp[Abbr`fl`] >> first_x_assum irule >> rw[] )
  >> pop_assum mp_tac >> simp_tac (srw_ss())[IS_SOME_EXISTS]
  >> strip_tac >> simp[]
  >> rename1 `fl = SOME tvv`
  >> PairCases_on `tvv`
  >> gvs[]
  >> first_x_assum drule_all
  >> strip_tac
  >> simp[]
  >> drule current_immutables_well_typed
  >> disch_then (qspec_then `cx.txn.target` assume_tac)
  >> drule_all imms_well_typed_get_source_immutables
  >> simp[]
QED

(* ===== Top-level values ===== *)

Theorem toplevel_vtype_Type_immutable_sound:
  env_consistent env cx st /\ state_well_typed st /\
  FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
  get_module_code cx src = SOME ts /\ find_var_decl_by_num id ts = NONE /\
  FLOOKUP (get_source_immutables src
    (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
  evaluate_type env.type_defs ty = SOME tv /\ value_has_type tv v
Proof
  rw[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def]
  >> first_x_assum drule_all
  >> strip_tac
  >> drule current_immutables_well_typed
  >> disch_then (qspec_then `cx.txn.target` assume_tac)
  >> drule_all imms_well_typed_get_source_immutables
  >> simp[]
QED

Theorem bare_global_well_formed_type:
  well_typed_expr env (BareGlobalName ty id) ==> well_formed_type env.type_defs ty
Proof
  rw[well_typed_expr_def]
QED

Theorem TopLevelName_well_formed_type:
  well_typed_expr env (TopLevelName ty nsid) ==> well_formed_type env.type_defs ty
Proof
  Cases_on `nsid` >> rw[well_typed_expr_def]
QED

Theorem TopLevelName_annotation_sound:
  type_place_expr env (TopLevelName ann nsid) = SOME vt ==>
  vtype_annotation_ok vt ann
Proof
  Cases_on `nsid` >> rw[well_typed_expr_def, AllCaseEqs()]
QED

Theorem TopLevelName_expr_not_hashmap:
  well_typed_expr env (TopLevelName ty nsid) ==>
  FLOOKUP env.toplevel_vtypes (FST nsid, string_to_num (SND nsid)) = SOME (Type ty)
Proof
  Cases_on `nsid` >> rw[well_typed_expr_def]
QED

Theorem flag_member_sound:
  well_typed_expr env (FlagMember ty nsid mid) /\ env_consistent env cx st ==>
  ?members. ty = FlagT (SND nsid) /\ FLOOKUP env.flag_members nsid = SOME members /\ MEM mid members
Proof
  Cases_on `nsid` >> rw[well_typed_expr_def]
QED
