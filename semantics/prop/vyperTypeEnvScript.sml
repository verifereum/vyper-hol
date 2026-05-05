(*
 * Environment, scope, immutable, and top-level lookup lemmas for the fresh
 * Vyper type system.
 *)

Theory vyperTypeEnv
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperMisc vyperABI vyperInterpreter vyperState
  vyperContext vyperStorage vyperTyping vyperTypeSystem vyperTypeValues
Libs
  wordsLib

(* ===== Local scopes ===== *)

Theorem scope_well_typed_lookup_scopes:
  EVERY scope_well_typed scopes /\ lookup_scopes id scopes = SOME entry ==>
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  cheat
QED

Theorem env_consistent_lookup_var_type:
  env_consistent env cx st /\ state_well_typed st /\
  FLOOKUP env.var_types id = SOME ty /\ lookup_scopes id st.scopes = SOME entry ==>
  ?tv. evaluate_type env.type_defs ty = SOME tv /\ entry.type = tv /\
       value_has_type tv entry.value
Proof
  rw[env_consistent_def, state_well_typed_def]
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
    gvs[env_consistent_def] >> last_x_assum drule
    >> rw[IS_SOME_EXISTS] )
  >> goal_assum drule
  >> conj_asm1_tac >- (
    gvs[env_consistent_def] >>
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
  rw[env_consistent_def]
QED

Theorem NameTarget_sound:
  type_place_target env (NameTarget id) = SOME (Type ty) /\
  env_consistent env cx st ==>
  ?entry. lookup_scopes (string_to_num id) st.scopes = SOME entry /\ entry.assignable
Proof
  rw[well_typed_expr_def, env_consistent_def]
  >> gvs[well_typed_expr_def, AllCaseEqs(), LET_THM]
QED

(* ===== Immutables / bare globals ===== *)

Theorem imms_well_typed_lookup:
  imms_well_typed imms /\ ALOOKUP imms src = SOME m /\ FLOOKUP m id = SOME (tv,v) ==>
  value_has_type tv v /\ well_formed_type_value tv
Proof
  rw[imms_well_typed_def]
  >> first_x_assum drule_all >> rw[]
QED

Theorem bare_global_lookup_sound:
  well_typed_expr env (BareGlobalName ty id) /\ env_consistent env cx st /\
  state_well_typed st ==>
  ?tv v. FLOOKUP (get_source_immutables env.current_src
            (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => []))
            (string_to_num id) = SOME (tv,v) /\
         evaluate_type env.type_defs ty = SOME tv /\ value_has_type tv v
Proof
  rw[well_typed_expr_def, env_consistent_def, state_well_typed_def]
  >> first_x_assum drule
  >> strip_tac
  >> gvs[IS_SOME_EXISTS]
  >> rename1 `FLOOKUP _ _ = SOME tvv`
  >> Cases_on `tvv`
  >> gvs[]
  >> first_x_assum drule_all
  >> strip_tac
  >> qexists_tac `q`
  >> qexists_tac `r`
  >> simp[]
  >> (* imms_well_typed lookup proof usually needs an ALOOKUP/get_source_immutables lemma. *)
     cheat
QED

(* ===== Top-level values ===== *)

Theorem toplevel_vtype_Type_sound:
  env_consistent env cx st /\ state_well_typed st /\
  FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) ==>
  well_formed_type env.type_defs ty
Proof
  cheat
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
