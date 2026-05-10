(*
 * Fresh env_consistent preservation lemmas for the executable type system.
 *)

Theory vyperTypeEnvPreservation
Ancestors
  alist list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperMisc vyperABI vyperInterpreter vyperState
  vyperContext vyperStorage vyperTyping vyperTypeSystem vyperTypeValues
  vyperLookup vyperStatePreservation vyperTypeEnv vyperEvalPreservesScopes vyperEvalExprPreservesScopesDom
  vyperEvalPreservesImmutablesDom
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

Theorem immutable_lookup_type_preserved_by_frame:
  preserves_tv cx st st' /\
  (!src n. IS_SOME (FLOOKUP (get_source_immutables src
      (case ALOOKUP st'.immutables cx.txn.target of SOME m => m | NONE => [])) n) ==>
    IS_SOME (FLOOKUP (get_source_immutables src
      (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) n)) /\
  (!tv v. FLOOKUP (get_source_immutables src
      (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
    P tv) /\
  FLOOKUP (get_source_immutables src
      (case ALOOKUP st'.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
  P tv
Proof
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `FLOOKUP new id = SOME (tv,v)` >>
  qabbrev_tac `old = get_source_immutables src
      (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])` >>
  `IS_SOME (FLOOKUP old id)` by (
    qpat_x_assum `!src n. IS_SOME (FLOOKUP _ n) ==> IS_SOME (FLOOKUP _ n)`
      (qspecl_then [`src`, `id`] mp_tac) >>
    simp[Abbr`old`, Abbr`new`, IS_SOME_EXISTS]) >>
  gvs[IS_SOME_EXISTS] >>
  rename1 `FLOOKUP old id = SOME old_pair` >>
  PairCases_on `old_pair` >>
  qpat_x_assum `preserves_tv _ _ _` mp_tac >>
  simp[preserves_tv_def, Abbr`old`, Abbr`new`] >>
  strip_tac >>
  first_x_assum (qspecl_then [`src`, `id`, `old_pair0`, `old_pair1`] mp_tac) >>
  simp[] >>
  strip_tac >>
  gvs[] >>
  first_x_assum irule >>
  goal_assum drule
QED

(* ===== Scope push/pop env_consistent lemmas ===== *)

Theorem push_scope_env_consistent:
  env_consistent env cx st ==>
  env_consistent env cx (st with scopes updated_by CONS FEMPTY)
Proof
  rw[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def, lookup_scopes_def, FLOOKUP_DEF] >>
  metis_tac[]
QED

Theorem pop_scope_env_consistent:
  env_consistent env cx st /\ st.scopes = h::tl /\ tl <> [] /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==> FLOOKUP h id = NONE) /\
  (!id. FLOOKUP env.var_assignable id = SOME T ==> FLOOKUP h id = NONE) ==>
  env_consistent env cx (st with scopes := tl)
Proof
  strip_tac >>
  fs[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def, lookup_scopes_def] >>
  rpt strip_tac >> res_tac >> gvs[] >>
  Cases_on `FLOOKUP h id` >> gvs[] >> res_tac >> gvs[]
QED

Theorem push_scope_with_var_env_consistent:
  env_consistent env cx st /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  nm NOTIN FDOM env.var_types ==>
  env_consistent (extend_local env nm typ F) cx
    (st with scopes updated_by CONS (FEMPTY |+ (nm, <| assignable := F; type := tyv; value := v |>)))
Proof
  rw[env_consistent_def, env_context_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def, extend_local_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `id = nm` >> gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
  res_tac >> gvs[]
QED

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

Theorem extend_local_env_consistent_weaken:
  env_maps_wf env /\
  id NOTIN FDOM env.var_types /\ lookup_scopes id st.scopes = NONE /\
  env_consistent (extend_local env id ty assignable) cx st ==>
  env_consistent env cx st
Proof
  simp[env_consistent_def] >> strip_tac >>
  conj_asm1_tac >- (
    qpat_x_assum `env_context_consistent _ _` mp_tac >>
    rw[env_context_consistent_def, extend_local_def] >> metis_tac[]) >>
  conj_asm1_tac >- (
    qpat_x_assum `env_scopes_consistent (extend_local _ _ _ _) _ _` mp_tac >>
    simp[env_scopes_consistent_def, extend_local_def, FLOOKUP_UPDATE, TO_FLOOKUP] >>
    strip_tac >> gvs[] >>
    conj_tac >- (
      rpt strip_tac >> Cases_on `id = id'` >> gvs[]) >>
    conj_tac >- (
      rpt strip_tac >> Cases_on `id = id'` >> gvs[TO_FLOOKUP] >>
      ntac 2 (last_x_assum(qspec_then`id'`mp_tac)) >> rw[]) >>
    conj_tac >- (
      rpt strip_tac >> Cases_on `id = id'` >> gvs[TO_FLOOKUP] >>
      last_x_assum(qspecl_then [`id'`, `ty'`, `entry`] mp_tac) >> rw[]) >>
    conj_tac >- (
      rpt strip_tac >> Cases_on `id = id'` >> gvs[]
      >- metis_tac[env_maps_wf_no_stale_assignable_T] >>
      qpat_x_assum `!id'. (if id = id' then SOME assignable else FLOOKUP env.var_assignable id') = SOME T ==> IS_SOME _`
        (qspec_then`id'`mp_tac) >> simp[]) >>
    rpt strip_tac >> Cases_on `id = id'` >> gvs[]
    >- metis_tac[env_maps_wf_no_stale_assignable_T] >>
    metis_tac[]) >>
  qpat_x_assum `env_immutables_consistent _ _ _` mp_tac >>
  rw[env_immutables_consistent_def, extend_local_def] >> metis_tac[]
QED

Theorem extend_local_env_maps_wf:
  env_maps_wf env ==> env_maps_wf (extend_local env id ty assignable)
Proof
  rw[env_maps_wf_def, extend_local_def, FLOOKUP_UPDATE] >>
  Cases_on `id = id'` >> gvs[]
QED

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

Theorem type_stmt_env_consistent_weaken:
  env_maps_wf env /\
  type_stmt env ret_ty s = SOME env' /\ env_consistent env' cx st /\
  (!id ty. FLOOKUP env'.var_types id = SOME ty /\ FLOOKUP env.var_types id = NONE ==>
     lookup_scopes id st.scopes = NONE) ==>
  env_consistent env cx st
Proof
  Cases_on `s` >> gvs[type_stmt_def, AllCaseEqs()] >>
  TRY (rename1 `Assert e a` >> Cases_on `a` >> gvs[type_stmt_def]) >>
  TRY (rename1 `Raise r` >> Cases_on `r` >> gvs[type_stmt_def]) >>
  TRY (rename1 `Return r` >> Cases_on `r` >> gvs[type_stmt_def]) >>
  rpt strip_tac >> gvs[] >>
  irule extend_local_env_consistent_weaken >> simp[] >>
  qexists_tac `T` >> qexists_tac `string_to_num s''` >>
  qexists_tac `expr_type e` >>
  gvs[extend_local_def, FLOOKUP_UPDATE] >>
  first_x_assum irule >> simp[FLOOKUP_DEF]
QED

Theorem type_stmts_env_consistent_weaken:
  env_maps_wf env /\
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env' cx st /\
  (!id ty. FLOOKUP env'.var_types id = SOME ty /\ FLOOKUP env.var_types id = NONE ==>
     lookup_scopes id st.scopes = NONE) ==>
  env_consistent env cx st
Proof
  MAP_EVERY qid_spec_tac [`env`, `env'`] >>
  Induct_on `ss` >> gvs[type_stmt_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >>
  `env_maps_wf env''` by metis_tac[type_stmt_env_maps_wf] >>
  first_x_assum (qspecl_then [`env'`, `env''`] mp_tac) >>
  impl_tac >- (
    simp[] >> rpt gen_tac >> strip_tac >> first_x_assum irule >> gvs[] >>
    drule_all type_stmt_var_types_mono >> simp[]) >>
  strip_tac >>
  irule type_stmt_env_consistent_weaken >> simp[] >>
  qexists_tac `env''` >> qexists_tac `ret_ty` >> qexists_tac `h` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum irule >> gvs[] >>
  drule_all type_stmts_var_types_preserve >> simp[]
QED

Theorem scope_bracket_preserves_ec:
  env_maps_wf env /\
  type_stmts env ret_ty ss = SOME env_after /\
  env_consistent env_after cx st_body /\
  eval_stmts cx ss (st with scopes updated_by CONS sc) = (res, st_body) /\
  (!id. id IN FDOM env.var_types ==> id NOTIN FDOM sc) ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  cheat
QED

(* ===== Main frame lemma ===== *)

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
    `?old_pair. FLOOKUP (get_source_immutables (current_module cx)
        (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME old_pair` by (
      qpat_x_assum `!src n. IS_SOME (FLOOKUP (get_source_immutables src _) n) ==> _`
        (qspecl_then [`current_module cx`, `id`] mp_tac) >>
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
  rw[] >>
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
  gvs[]
QED

(* ===== Assignability preservation for expression evaluation ===== *)

(* Helper: updating the value of an existing scoped variable should not make any
   previously-assignable visible variable non-assignable.  This is the local
   state-update fact needed by the expression-evaluation frame proof. *)
Theorem lookup_scopes_fupdate_other:
  !sc id n entry new_entry.
    id <> n /\ lookup_scopes id sc = SOME entry ==>
    lookup_scopes id (case sc of [] => [FEMPTY |+ (n,new_entry)]
                     | h::t => (h |+ (n,new_entry))::t) = SOME entry
Proof
  Cases >> simp[lookup_scopes_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem lookup_scopes_append_cons:
  !pre id env entry rest.
    lookup_scopes id pre = NONE /\ FLOOKUP env id = SOME entry ==>
    lookup_scopes id (pre ++ env::rest) = SOME entry
Proof
  Induct >> gvs[lookup_scopes_def, AllCaseEqs()]
QED

Theorem lookup_scopes_append_fupdate_other:
  !pre id n env new_entry rest.
    id <> n ==>
    lookup_scopes id (pre ++ (env |+ (n,new_entry))::rest) =
    lookup_scopes id (pre ++ env::rest)
Proof
  Induct >> gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `FLOOKUP env id` >> gvs[]
QED

Theorem update_name_preserves_assignable_lookup:
  lookup_scopes id st.scopes = SOME entry /\ entry.assignable ==>
  ?entry'. lookup_scopes id (update_name st nm v).scopes = SOME entry' /\
           entry'.assignable
Proof
  rw[update_name_def] >>
  Cases_on `find_containing_scope (string_to_num nm) st.scopes` >> gvs[]
  >- (
    Cases_on `id = string_to_num nm` >- (
      drule find_containing_scope_none_lookup_scopes_none >> gvs[]) >>
    qexists_tac `entry` >>
    Cases_on `st.scopes` >> gvs[lookup_scopes_def, FLOOKUP_UPDATE, AllCaseEqs()]) >>
  PairCases_on `x` >>
  drule find_containing_scope_structure >>
  drule find_containing_scope_pre_none >>
  rpt strip_tac >> gvs[] >>
  Cases_on `id = string_to_num nm` >- (
    `lookup_scopes id x0 = NONE` by gvs[] >>
    `lookup_scopes id (x0 ++ x1::x3) = SOME x2` by
      metis_tac[lookup_scopes_append_cons] >>
    gvs[] >>
    qexists_tac `entry with value := v` >>
    simp[lookup_scopes_update]) >>
  qexists_tac `entry` >>
  simp[lookup_scopes_append_fupdate_other]
QED

(* Helper: expression base-target evaluation preserves assignability of any
   previously visible assignable local.  This is separated because expression
   evaluation invokes base-target evaluation in several cases. *)
Theorem materialise_preserves_assignable_lookup:
  materialise cx tvl st = (res, st') /\
  lookup_scopes id st.scopes = SOME entry /\ entry.assignable ==>
  ?entry'. lookup_scopes id st'.scopes = SOME entry' /\ entry'.assignable
Proof
  rpt strip_tac >> imp_res_tac materialise_state >> gvs[] >> metis_tac[]
QED

Theorem get_Value_preserves_assignable_lookup:
  get_Value tvl st = (res, st') /\
  lookup_scopes id st.scopes = SOME entry /\ entry.assignable ==>
  ?entry'. lookup_scopes id st'.scopes = SOME entry' /\ entry'.assignable
Proof
  Cases_on `tvl` >> gvs[get_Value_def, return_def, raise_def] >> metis_tac[]
QED

Theorem eval_base_target_preserves_assignable_lookup:
  eval_base_target cx bt st = (res, st') /\
  lookup_scopes id st.scopes = SOME entry /\ entry.assignable ==>
  ?entry'. lookup_scopes id st'.scopes = SOME entry' /\ entry'.assignable
Proof
  (* Draft proof shape: induction over eval_base_target cases from
     evaluate_ind, using update_name_preserves_assignable_lookup for any local
     update and chaining the IHs through bind cases. *)
  cheat
QED

Theorem eval_expr_preserves_assignable_lookup:
  eval_expr cx e st = (res, st') /\
  lookup_scopes id st.scopes = SOME entry /\ entry.assignable ==>
  ?entry'. lookup_scopes id st'.scopes = SOME entry' /\ entry'.assignable
Proof
  (* Proof draft.

     This should be a mutual induction over evaluate_ind with only the P7/P8
     expression predicates non-trivial, analogous to
     vyperEvalExprPreservesScopesDomScript.sml.

     Suggested predicates:
       P5 cx bt = !st res st' id entry.
         eval_base_target cx bt st = (res,st') /\
         lookup_scopes id st.scopes = SOME entry /\ entry.assignable ==>
         ?entry'. lookup_scopes id st'.scopes = SOME entry' /\ entry'.assignable
       P7 cx e = same for eval_expr
       P8 cx es = same for eval_exprs

     Case strategy:
     - Pure/read-only expression cases: unfold Once evaluate_def and close with
       return/get/lift/materialise_state facts.
     - Chained bind cases: apply the IH to the first evaluation to get an
       assignable entry in the intermediate state, then apply the next IH.
     - Any materialise in between: use materialise_state to rewrite the state.
     - Any base-target evaluation: use eval_base_target_preserves_assignable_lookup.
     - Any update_name path introduced by assignment-like expression cases:
       use update_name_preserves_assignable_lookup.

     The already-proved eval_exprs_preserves_assignable_lookup should be kept
     as the public list corollary; during mutual induction it may be easier to
     prove P8 directly and then derive that theorem, but the statement below is
     the required P7 public theorem.
  *)
  cheat
QED

Theorem eval_exprs_preserves_assignable_lookup:
  eval_exprs cx es st = (res, st') /\
  lookup_scopes id st.scopes = SOME entry /\ entry.assignable ==>
  ?entry'. lookup_scopes id st'.scopes = SOME entry' /\ entry'.assignable
Proof
  MAP_EVERY qid_spec_tac [`st'`, `st`, `res`, `entry`] >>
  Induct_on `es` >> simp[Once evaluate_def, return_def, bind_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule_all eval_expr_preserves_assignable_lookup >>
  strip_tac >>
  imp_res_tac materialise_state >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

(* ===== Evaluation corollaries ===== *)

Theorem eval_expr_preserves_ec:
  env_consistent env cx st /\ eval_expr cx e st = (res, st') ==>
  env_consistent env cx st'
Proof
  rpt strip_tac >>
  irule env_consistent_preserved_by_frame >>
  qexists_tac `st` >> simp[] >>
  drule (cj 8 eval_preserves_tv) >> simp[] >> strip_tac >>
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

Theorem eval_exprs_preserves_ec:
  env_consistent env cx st /\ eval_exprs cx es st = (res, st') ==>
  env_consistent env cx st'
Proof
  rpt strip_tac >>
  irule env_consistent_preserved_by_frame >>
  qexists_tac `st` >> simp[] >>
  drule (cj 9 eval_preserves_tv) >> simp[] >> strip_tac >>
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
