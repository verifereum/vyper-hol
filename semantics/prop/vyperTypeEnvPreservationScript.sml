(*
 * Fresh env_consistent preservation lemmas for the executable type system.
 *)

Theory vyperTypeEnvPreservation
Ancestors
  alist list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperMisc vyperABI vyperInterpreter vyperState
  vyperContext vyperStorage vyperTyping vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperLookup vyperStatePreservation vyperStorageBackend vyperTypeEnv vyperTypeEnvExtension
  vyperEvalPreservesScopes vyperScopePreservation vyperEvalExprPreservesScopesDom
  vyperEvalPreservesImmutablesDom vyperCallOutcomeFrame
Libs
  wordsLib

(* ===== Scope-domain lookup facts ===== *)

Theorem lookup_scopes_is_some_same_fdoms:
  !scopes1 scopes2 id.
    MAP FDOM scopes1 = MAP FDOM scopes2 ==>
    (IS_SOME (lookup_scopes id scopes1) <=> IS_SOME (lookup_scopes id scopes2))
Proof
  Induct >> Cases_on `scopes2` >>
  simp[lookup_scopes_def] >>
  rpt strip_tac >> Cases_on `FLOOKUP h id` >> Cases_on `FLOOKUP h' id` >>
  gvs[lookup_scopes_def, FLOOKUP_DEF]
QED

(* ===== Scope push/pop env_consistent lemmas ===== *)

Theorem push_scope_env_consistent:
  env_consistent env cx st ==>
  env_consistent env cx (st with scopes updated_by CONS FEMPTY)
Proof
  rw[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def, lookup_scopes_def, FLOOKUP_DEF] >>
  metis_tac[]
QED

Theorem push_scope_with_var_env_consistent:
  env_consistent env cx st /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  nm NOTIN FDOM env.var_types ==>
  env_consistent (extend_local env nm typ F) cx
    (st with scopes updated_by CONS (FEMPTY |+ (nm, <| assignable := F; type := tyv; value := v; popped := [] |>)))
Proof
  simp[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def,
       env_immutables_consistent_def, extend_local_def, FLOOKUP_UPDATE] >>
  strip_tac >>
  conj_tac >- ( rw[] >> res_tac >> gvs[]) >>
  conj_tac >- (
    rw[] >>
    Cases_on`id = nm` >>
    ASM_SIMP_TAC std_ss [lookup_scopes_def, FLOOKUP_UPDATE] >>
    FULL_SIMP_TAC std_ss [lookup_scopes_def, FLOOKUP_UPDATE, FLOOKUP_DEF,
                          FDOM_FEMPTY, NOT_IN_EMPTY] >>
    TRY (qpat_x_assum
           `<|assignable := F; type := tyv; value := v; popped := []|> = entry`
           (SUBST_ALL_TAC o SYM) >> simp[]) >>
    res_tac >>
    TRY (qpat_x_assum `env.var_types ' id = ty`
           (fn th => PURE_REWRITE_TAC [GSYM th]) >>
         first_assum ACCEPT_TAC) >>
    ASM_REWRITE_TAC[]) >>
  rw[] >> res_tac >> gvs[]
QED

(* MOVED-BY-PLAN: scope_bracket_preserves_ec belongs in the planned
   vyperTypeScopePop theory, with the stronger precondition
   env_consistent env cx st.  The old in-place proof is intentionally not
   exported from vyperTypeEnvPreservation because the st.scopes <> [] shape is
   too weak for the final architecture.  Original proof body preserved in git
   history and the rewrite plan. *)

(* ===== Main frame lemma ===== *)

(* ===== Assignability preservation for expression evaluation ===== *)

Definition preserves_assignable_lookup_def:
  preserves_assignable_lookup st st' <=>
    !id entry.
      lookup_scopes id st.scopes = SOME entry /\ entry.assignable ==>
      ?entry'. lookup_scopes id st'.scopes = SOME entry' /\ entry'.assignable
End

Theorem preserves_assignable_lookup_refl[simp]:
  !st. preserves_assignable_lookup st st
Proof
  simp[preserves_assignable_lookup_def] >> metis_tac[]
QED

(* ===== Evaluation corollaries ===== *)
