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

(* ===== Main frame lemma ===== *)

Theorem env_consistent_preserved_by_frame:
  env_consistent env cx st /\
  preserves_tv cx st st' /\
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
  strip_tac >> gvs[env_consistent_def]
  >> conj_asm1_tac >- (
    rpt strip_tac >>
    last_x_assum drule >>
    rw[IS_SOME_EXISTS] >>
    drule_all lookup_scopes_same_fdoms_some >>
    rw[IS_SOME_EXISTS]
  ) >>
  conj_asm1_tac >- (
    rpt strip_tac >>
    drule lookup_scopes_type_preserved_under_preserves_tv >>
    simp[] >>
    strip_tac >>
    first_x_assum drule >> rw[] >>
    last_x_assum $ drule_then drule >> gvs[]
  ) >>
  conj_asm1_tac >- metis_tac[] >>
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
  conj_asm1_tac >- (
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
    gvs[]) >>
  metis_tac[]
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
  (* Draft proof shape: mutual induction over expression evaluation using
     evaluate_ind.  Most cases are state-preserving for scopes or chain IHs;
     base-target cases use eval_base_target_preserves_assignable_lookup. *)
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
  drule eval_expr_preserves_immutables_addr_dom >>
  drule eval_expr_preserves_immutables_dom >>
  rw[IS_SOME_EXISTS]
  >- metis_tac[eval_expr_preserves_assignable_lookup] >>
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
  drule eval_exprs_preserves_immutables_addr_dom >>
  drule eval_exprs_preserves_immutables_dom >>
  rw[IS_SOME_EXISTS]
  >- metis_tac[eval_exprs_preserves_assignable_lookup] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  Cases_on `ALOOKUP st'.immutables cx.txn.target` >>
  gvs[EQ_IMP_THM, PULL_EXISTS, SF DNF_ss] >>
  first_x_assum drule >> rw[]
QED
