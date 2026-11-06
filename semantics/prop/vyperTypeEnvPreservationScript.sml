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

Theorem lookup_scopes_same_fdoms_some:
  !scopes1 scopes2 id entry.
    MAP FDOM scopes1 = MAP FDOM scopes2 /\ lookup_scopes id scopes1 = SOME entry ==>
    IS_SOME (lookup_scopes id scopes2)
Proof
  metis_tac[lookup_scopes_is_some_same_fdoms, IS_SOME_EXISTS]
QED

Theorem lookup_scopes_EL:
  !scopes id entry.
    lookup_scopes id scopes = SOME entry ==>
    ?i. i < LENGTH scopes /\
        FLOOKUP (EL i scopes) id = SOME entry /\
        !j. j < i ==> FLOOKUP (EL j scopes) id = NONE
Proof
  Induct >> simp[lookup_scopes_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP h id` >> simp[]
  >- (strip_tac >> res_tac >>
      qexists_tac `SUC i` >> simp[] >>
      Cases >> simp[]) >>
  strip_tac >> qexists_tac `0` >> simp[]
QED

Theorem lookup_scopes_from_EL:
  !scopes id entry i.
    i < LENGTH scopes /\
    FLOOKUP (EL i scopes) id = SOME entry /\
    (!j. j < i ==> FLOOKUP (EL j scopes) id = NONE) ==>
    lookup_scopes id scopes = SOME entry
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `i` >> gvs[lookup_scopes_def, AllCaseEqs()] >>
  first_assum(qspec_then `0` mp_tac) >> simp_tac (srw_ss())[] >>
  strip_tac >> first_x_assum irule >>
  goal_assum $ drule_at Any >> rw[] >>
  first_x_assum(qspec_then `SUC j` mp_tac) >> rw[]
QED

Theorem MAP_FDOM_EL_FDOM:
  !l1 l2 i. MAP FDOM l1 = MAP FDOM l2 /\ i < LENGTH l1 ==>
            FDOM (EL i l1) = FDOM (EL i l2)
Proof
  rpt strip_tac >>
  `LENGTH l1 = LENGTH l2` by metis_tac[LENGTH_MAP] >>
  `EL i (MAP FDOM l1) = FDOM (EL i l1)` by simp[EL_MAP] >>
  `EL i (MAP FDOM l2) = FDOM (EL i l2)` by simp[EL_MAP] >>
  metis_tac[]
QED

Theorem lookup_scopes_type_preserved_under_preserves_tv:
  !cx st st' id entry.
    preserves_tv cx st st' /\
    MAP FDOM st'.scopes = MAP FDOM st.scopes /\
    lookup_scopes id st'.scopes = SOME entry ==>
    ?entry'. lookup_scopes id st.scopes = SOME entry' /\ entry.type = entry'.type
Proof
  rpt strip_tac >>
  drule lookup_scopes_EL >> strip_tac >>
  `i < LENGTH st.scopes` by
    (qpat_x_assum `preserves_tv _ _ _` mp_tac >>
     simp[preserves_tv_def]) >>
  `FDOM (EL i st.scopes) = FDOM (EL i st'.scopes)` by
    (irule MAP_FDOM_EL_FDOM >> gvs[]) >>
  `id IN FDOM (EL i st'.scopes)` by metis_tac[TO_FLOOKUP,NOT_SOME_NONE] >>
  `id IN FDOM (EL i st.scopes)` by metis_tac[] >>
  `?entry'. FLOOKUP (EL i st.scopes) id = SOME entry'` by
    metis_tac[flookup_thm] >>
  `?entry''. FLOOKUP (EL i st'.scopes) id = SOME entry'' /\
              entry''.type = entry'.type` by (
    qpat_x_assum `preserves_tv _ _ _` mp_tac >>
    simp[preserves_tv_def] >>
    strip_tac >> first_x_assum drule_all >> simp[]) >>
  `entry'' = entry` by metis_tac[flookup_thm, SOME_11] >>
  qexists_tac `entry'` >> simp[] >> gvs[] >>
  irule lookup_scopes_from_EL >>
  qexists_tac `i` >> simp[] >>
  rpt strip_tac >>
  `id NOTIN FDOM (EL j st.scopes)` suffices_by metis_tac[flookup_thm] >>
  `FDOM (EL j st.scopes) = FDOM (EL j st'.scopes)` by
    (irule MAP_FDOM_EL_FDOM >> gvs[] >>
     qpat_x_assum `preserves_tv _ _ _` mp_tac >> simp[preserves_tv_def]) >>
  metis_tac[flookup_thm]
QED

Theorem lookup_scopes_assignable_preserved_under_preserves_tv:
  !cx st st' id entry.
    preserves_tv cx st st' /\
    MAP FDOM st'.scopes = MAP FDOM st.scopes /\
    lookup_scopes id st.scopes = SOME entry /\ entry.assignable ==>
    ?entry'. lookup_scopes id st'.scopes = SOME entry' /\ entry'.assignable
Proof
  rpt strip_tac >>
  drule lookup_scopes_EL >> strip_tac >>
  `i < LENGTH st'.scopes` by
    (qpat_x_assum `preserves_tv _ _ _` mp_tac >> simp[preserves_tv_def]) >>
  `?entry'. FLOOKUP (EL i st'.scopes) id = SOME entry' /\
              entry'.type = entry.type /\
              entry'.assignable = entry.assignable` by (
    qpat_x_assum `preserves_tv _ _ _` mp_tac >>
    simp[preserves_tv_def] >> strip_tac >>
    first_x_assum drule_all >> simp[]) >>
  qexists_tac `entry'` >> simp[] >>
  irule lookup_scopes_from_EL >>
  qexists_tac `i` >> simp[] >>
  rpt strip_tac >>
  `id NOTIN FDOM (EL j st'.scopes)` suffices_by metis_tac[flookup_thm] >>
  `FDOM (EL j st'.scopes) = FDOM (EL j st.scopes)` by
    (irule MAP_FDOM_EL_FDOM >> simp[]) >>
  metis_tac[flookup_thm]
QED

Theorem preserves_tv_immutables_type_preserved:
  !cx st st' src id tv v.
    preserves_tv cx st st' /\
    FLOOKUP (get_source_immutables src
        (case ALOOKUP st.immutables cx.txn.target of
           SOME m => m | NONE => [])) id = SOME (tv,v) ==>
    ?v'. FLOOKUP (get_source_immutables src
        (case ALOOKUP st'.immutables cx.txn.target of
           SOME m => m | NONE => [])) id = SOME (tv,v')
Proof
  rw[preserves_tv_def]
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

Theorem env_consistent_preserved_by_frame:
  env_consistent env cx st /\
  preserves_tv cx st st' /\
  (!id entry. lookup_scopes id st'.scopes = SOME entry ==>
     ?entry'. lookup_scopes id st.scopes = SOME entry' /\ entry.type = entry'.type) /\
  MAP FDOM st.scopes = MAP FDOM st'.scopes /\
  (!id entry. lookup_scopes id st.scopes = SOME entry /\ entry.assignable ==>
     ?entry'. lookup_scopes id st'.scopes = SOME entry' /\ entry'.assignable) /\
  (!src n. IS_SOME (FLOOKUP (get_source_immutables src
      (case ALOOKUP st'.immutables cx.txn.target of SOME m => m | NONE => [])) n) ==>
    IS_SOME (FLOOKUP (get_source_immutables src
      (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) n))
  ==>
  env_consistent env cx st'
Proof
  strip_tac >> gvs[env_consistent_def] >>
  conj_tac >- (
    qpat_x_assum `env_scopes_consistent env cx st` mp_tac >>
    rw[env_scopes_consistent_def]
    >- (Cases_on `st.scopes` >> gvs[] >> Cases_on `st'.scopes` >> gvs[])
    >- (last_x_assum drule >>
        rw[IS_SOME_EXISTS] >>
        drule_all lookup_scopes_same_fdoms_some >>
        rw[IS_SOME_EXISTS])
    >- (drule lookup_scopes_is_some_same_fdoms >> simp[] >>
        disch_then (qspec_then `id` mp_tac) >> simp[] >>
        rw[optionTheory.IS_SOME_EXISTS] >>
        qpat_x_assum `!id entry. lookup_scopes id st.scopes = SOME entry ==> _`
          (qspecl_then [`id`, `x`] mp_tac) >> simp[] >>
        rw[optionTheory.IS_SOME_EXISTS])
    >- (qpat_x_assum `!id entry. lookup_scopes id st'.scopes = SOME entry ==> ?entry'. _`
          (qspecl_then [`id`, `entry`] mp_tac) >> simp[] >>
        strip_tac >> gvs[] >>
        qpat_x_assum `!id ty entry. FLOOKUP env.var_types id = SOME ty /\ lookup_scopes id st.scopes = SOME entry ==> _`
          (qspecl_then [`id`, `ty`, `entry'`] mp_tac) >> simp[]) >>
    metis_tac[]) >>
  qpat_x_assum `env_context_consistent env cx` mp_tac >>
  simp[env_context_consistent_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `env_immutables_consistent env cx st` mp_tac >>
  simp[env_immutables_consistent_def] >> strip_tac >>
  conj_asm1_tac >- (
    rpt strip_tac >>
    first_x_assum drule_all >>
    strip_tac >>
    drule preserves_tv_immutables_type_preserved >>
    gvs[IS_SOME_EXISTS, FORALL_PROD, PULL_EXISTS, EXISTS_PROD] >>
    disch_then drule >>
    metis_tac[] ) >>
  conj_asm1_tac >- (
    rpt strip_tac >>
    `?old_pair. FLOOKUP (get_source_immutables src
        (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME old_pair` by (
      qpat_x_assum `!src n. IS_SOME (FLOOKUP (get_source_immutables src _) n) ==> _`
        (qspecl_then [`src`, `id`] mp_tac) >>
      metis_tac[IS_SOME_EXISTS]) >>
    PairCases_on `old_pair` >>
    `evaluate_type (get_tenv cx) ty = SOME old_pair0` by
      metis_tac[] >>
    drule_all preserves_tv_immutables_type_preserved >>
    strip_tac >>
    gvs[]) >>
  rpt strip_tac >>
  first_x_assum drule_all >>
  strip_tac >> gvs[] >>
  `?old_pair. FLOOKUP (get_source_immutables src
      (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => []))
      id = SOME old_pair` by (
    qpat_x_assum `!src n. IS_SOME (FLOOKUP (get_source_immutables src _) n) ==> _`
      (qspecl_then [`src`, `id`] mp_tac) >>
    simp[IS_SOME_EXISTS]) >>
  PairCases_on `old_pair` >>
  drule_all preserves_tv_immutables_type_preserved >>
  strip_tac >> gvs[] >>
  qpat_x_assum `!tv v. _`
    (qspecl_then [`old_pair0`, `old_pair1`] mp_tac) >>
  simp[]
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

Theorem eval_expr_preserves_assignable_lookup:
  eval_expr cx e st = (res, st') /\
  lookup_scopes id st.scopes = SOME entry /\ entry.assignable ==>
  ?entry'. lookup_scopes id st'.scopes = SOME entry' /\ entry'.assignable
Proof
  rpt strip_tac >>
  drule eval_expr_preserves_tv >> strip_tac >>
  drule eval_expr_preserves_scopes_dom >> simp[] >> strip_tac >>
  `MAP FDOM st'.scopes = MAP FDOM st.scopes` by simp[] >>
  drule_all lookup_scopes_assignable_preserved_under_preserves_tv >> simp[]
QED

Theorem eval_expr_preserves_ec:
  env_consistent env cx st /\ eval_expr cx e st = (res, st') ==>
  env_consistent env cx st'
Proof
  rpt strip_tac >>
  irule env_consistent_preserved_by_frame >>
  qexists_tac `st` >> simp[] >>
  drule eval_expr_preserves_tv >> simp[] >> strip_tac >>
  drule eval_expr_preserves_scopes_dom >> simp[] >> strip_tac >>
  `!id entry. lookup_scopes id st'.scopes = SOME entry ==>
      ?entry'. lookup_scopes id st.scopes = SOME entry' /\ entry.type = entry'.type` by
    (rpt strip_tac >> drule lookup_scopes_type_preserved_under_preserves_tv >> simp[]) >>
  conj_tac >- metis_tac[eval_expr_preserves_assignable_lookup] >>
  drule eval_expr_preserves_immutables_addr_dom >>
  drule eval_expr_preserves_immutables_dom >>
  rw[IS_SOME_EXISTS] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  Cases_on `ALOOKUP st'.immutables cx.txn.target` >>
  gvs[EQ_IMP_THM, PULL_EXISTS, SF DNF_ss] >>
  first_x_assum drule >> rw[]
QED

Theorem eval_exprs_preserves_assignable_lookup:
  eval_exprs cx es st = (res, st') /\
  lookup_scopes id st.scopes = SOME entry /\ entry.assignable ==>
  ?entry'. lookup_scopes id st'.scopes = SOME entry' /\ entry'.assignable
Proof
  rpt strip_tac >>
  drule eval_exprs_preserves_scopes_dom >> simp[] >> strip_tac >>
  drule eval_exprs_preserves_tv >> strip_tac >>
  `MAP FDOM st'.scopes = MAP FDOM st.scopes` by simp[] >>
  drule_all lookup_scopes_assignable_preserved_under_preserves_tv >> simp[]
QED

Theorem env_consistent_outcome_updates[local]:
  (env_consistent env cx (s with <|outcomes := os; requests := rqs|>) <=>
     env_consistent env cx s) /\
  (env_consistent env cx
     (s with <|accounts := accounts; tStorage := transient;
               logs := s.logs ++ logs; pending_deletions := pending|>) <=> env_consistent env cx s)
Proof
  REWRITE_TAC [env_consistent_def, env_scopes_consistent_def,
               env_immutables_consistent_def] >> simp_tac (srw_ss()) []
QED

(* Environment consistency observes scopes/immutables, not adopted accounts.
   Continuation preservation is the evaluator IH owned by TASK032/033. *)
Theorem ExtCall_outcome_preserves_ec:
  env_consistent env cx st /\
  (!bs s res t. env_consistent env cx s /\ k bs s = (res,t) ==>
                env_consistent env cx t) /\
  (do
    accounts <- get_accounts;
    (if ret_type = NoneT then
       check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success "ExtCall reverted";
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = (res,st') ==> env_consistent env cx st'
Proof
  rpt strip_tac >>
  `!s t u. (env_consistent env cx s ==> env_consistent env cx t) /\
            (env_consistent env cx t ==> env_consistent env cx u) ==>
            (env_consistent env cx s ==> env_consistent env cx u)` by metis_tac[] >>
  `!bs s res t. k bs s = (res,t) ==>
      (env_consistent env cx s ==> env_consistent env cx t)` by metis_tac[] >>
  `!s. env_consistent env cx s ==> env_consistent env cx s` by simp[] >>
  `!s os rqs. env_consistent env cx s ==>
     env_consistent env cx (s with <|outcomes := os; requests := rqs|>)` by
    simp_tac (srw_ss()) [env_consistent_outcome_updates] >>
  `!s accounts transient logs pending. env_consistent env cx s ==>
     env_consistent env cx (s with <|accounts := accounts; tStorage := transient;
                                    logs := s.logs ++ logs; pending_deletions := pending|>)` by
    simp_tac (srw_ss()) [env_consistent_outcome_updates] >>
  drule_all (ExtCall_outcome_transport |> Q.INST
    [`R` |-> `\s t. env_consistent env cx s ==> env_consistent env cx t`]
    |> BETA_RULE) >> simp[]
QED

Theorem Send_outcome_preserves_ec:
  env_consistent env cx st /\
  (do
    (rq,outcome) <- take_call_outcome target [] (SOME amount);
    check outcome.co_success "send failed";
    adopt_call_outcome rq outcome;
    return (Value NoneV)
  od) st = (res,st') ==> env_consistent env cx st'
Proof
  rpt strip_tac >> drule Send_outcome_preserves_locals >> strip_tac >>
  fs[env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem eval_exprs_preserves_ec:
  env_consistent env cx st /\ eval_exprs cx es st = (res, st') ==>
  env_consistent env cx st'
Proof
  rpt strip_tac >>
  irule env_consistent_preserved_by_frame >>
  qexists_tac `st` >> simp[] >>
  drule eval_exprs_preserves_tv >> simp[] >> strip_tac >>
  drule eval_exprs_preserves_scopes_dom >> simp[] >> strip_tac >>
  `!id entry. lookup_scopes id st'.scopes = SOME entry ==>
      ?entry'. lookup_scopes id st.scopes = SOME entry' /\ entry.type = entry'.type` by
    (rpt strip_tac >> drule lookup_scopes_type_preserved_under_preserves_tv >> simp[]) >>
  conj_tac >- metis_tac[eval_exprs_preserves_assignable_lookup] >>
  drule eval_exprs_preserves_immutables_addr_dom >>
  drule eval_exprs_preserves_immutables_dom >>
  rw[IS_SOME_EXISTS] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  Cases_on `ALOOKUP st'.immutables cx.txn.target` >>
  gvs[EQ_IMP_THM, PULL_EXISTS, SF DNF_ss] >>
  first_x_assum drule >> rw[]
QED
(* ===== Evaluation corollaries ===== *)
