(*
 * Scope push/pop restoration facts for executable type soundness.
 *)

Theory vyperTypeScopePop
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperMisc vyperABI vyperInterpreter vyperState
  vyperContext vyperStorage vyperTyping vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperLookup vyperStatePreservation vyperTypeEnv vyperTypeEnvExtension
  vyperEvalPreservesScopes vyperTypeStatePreservation
Libs
  wordsLib

(* ===== Generic env consistency after popping a pushed runtime scope ===== *)

Theorem FLOOKUP_SOME_IN_FDOM:
  FLOOKUP fm k = SOME v ==> k IN FDOM fm
Proof
  rw[TO_FLOOKUP]
QED


Theorem env_extends_env_consistent_after_pop:
  env_maps_wf env /\ env_consistent env cx st_outer /\
  preserves_tv cx st_outer (st_body with scopes := tl) /\
  env_extends env env_body /\ env_consistent env_body cx st_body /\
  st_body.scopes = h::tl /\ tl <> [] /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==> FLOOKUP h id = NONE) /\
  (!id. FLOOKUP env.var_assignable id = SOME T ==> FLOOKUP h id = NONE) /\
  (!id ty.
     FLOOKUP env_body.var_types id = SOME ty /\ FLOOKUP env.var_types id = NONE ==>
     lookup_scopes id tl = NONE) ==>
  env_consistent env cx (st_body with scopes := tl)
Proof
  strip_tac >>
  fs[env_consistent_def] >>
  fs[env_extends_def] >>
  simp[env_consistent_def] >>
  conj_tac >- (
    qpat_x_assum `env_scopes_consistent env_body cx st_body` mp_tac >>
    simp[env_scopes_consistent_def] >> strip_tac >>
    rw[env_scopes_consistent_def]
    >- (qpat_x_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> _` drule >> strip_tac >>
        qpat_x_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> FLOOKUP env_body.var_types id = SOME ty` drule >>
        strip_tac >>
        qpat_x_assum `!id ty. FLOOKUP env_body.var_types id = SOME ty ==> _` drule >>
        simp[lookup_scopes_def] >>
        Cases_on `FLOOKUP h id` >> gvs[])
    >- (Cases_on `FLOOKUP env.var_types id` >> gvs[] >>
        qpat_x_assum `!id' entry'. lookup_scopes id' (h::tl) = SOME entry' ==> _`
          (qspec_then `id` mp_tac) >>
        simp[lookup_scopes_def] >>
        Cases_on `FLOOKUP h id` >> gvs[] >>
        Cases_on `FLOOKUP env_body.var_types id` >> gvs[] >>
        rename1 `FLOOKUP env_body.var_types id = SOME ty` >>
        first_x_assum drule_all >> simp[])
    >- (qpat_x_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> FLOOKUP env_body.var_types id = SOME ty` drule >>
        strip_tac >>
        qpat_x_assum `!id' ty' entry'. FLOOKUP env_body.var_types id' = SOME ty' /\ _ ==> _`
          (qspecl_then [`id`, `ty`, `entry`] mp_tac) >>
        simp[lookup_scopes_def] >>
        Cases_on `FLOOKUP h id` >> gvs[])
    >- (fs[env_scopes_consistent_def] >> metis_tac[]) >>
    qpat_x_assum `!id. FLOOKUP env.var_assignable id = SOME T ==> _` drule >> strip_tac >>
    qpat_x_assum `!id. FLOOKUP env.var_assignable id = SOME T ==> FLOOKUP env_body.var_assignable id = SOME T` drule >>
    strip_tac >>
    qpat_x_assum `!id'. FLOOKUP env_body.var_assignable id' = SOME T ==> _` drule >>
    simp[lookup_scopes_def] >>
    Cases_on `FLOOKUP h id` >> gvs[] >>
    metis_tac[]) >>
  qpat_x_assum `env_immutables_consistent env_body cx st_body` mp_tac >>
  simp[env_immutables_consistent_def] >> strip_tac >>
  rw[env_immutables_consistent_def]
  >- (qpat_x_assum `preserves_tv _ _ _` mp_tac >> simp[preserves_tv_def] >> metis_tac[])
  >- (qpat_x_assum `preserves_tv _ _ _` mp_tac >> simp[preserves_tv_def] >> metis_tac[]) >>
  qpat_x_assum `!src id ty ts. FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\ _ ==> _`
    (qspecl_then [`src`, `id`, `ty`, `ts`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem type_stmts_env_consistent_after_pop:
  !env cx st_outer st_body tl ret_ty ss env' h.
  env_maps_wf env /\ env_consistent env cx st_outer /\
  preserves_tv cx st_outer (st_body with scopes := tl) /\
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env' cx st_body /\
  st_body.scopes = h::tl /\ tl <> [] /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==> FLOOKUP h id = NONE) /\
  (!id. FLOOKUP env.var_assignable id = SOME T ==> FLOOKUP h id = NONE) /\
  (!id ty.
     FLOOKUP env'.var_types id = SOME ty /\ FLOOKUP env.var_types id = NONE ==>
     lookup_scopes id tl = NONE) ==>
  env_consistent env cx (st_body with scopes := tl)
Proof
  rpt strip_tac >>
  `env_extends env env'` by metis_tac[type_stmts_env_extends] >>
  irule env_extends_env_consistent_after_pop >> simp[] >>
  conj_tac >- (qexists_tac `env'` >> simp[]) >>
  qexists_tac `st_outer` >> simp[]
QED

Theorem eval_stmts_pushed_scope_env_consistent_after_pop:
  env_maps_wf env /\ env_consistent env cx st /\
  preserves_tv cx (st with scopes updated_by CONS FEMPTY) st_body /\
  eval_stmts cx ss (st with scopes updated_by CONS FEMPTY) = (res, st_body) /\
  env_extends env env_body /\ env_consistent env_body cx st_body ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  strip_tac >>
  `st with scopes updated_by CONS FEMPTY =
   st with scopes := FEMPTY::st.scopes`
  by simp[evaluation_state_component_equality] >>
  Cases_on `st_body.scopes` >> gvs[]
  >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
  irule env_extends_env_consistent_after_pop >> simp[] >>
  conj_tac >- (
    drule eval_stmts_preserves_scopes_len >> simp[] >>
    strip_tac >>
    `st.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
    Cases_on `st.scopes` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
  conj_tac >- (
    conj_tac >- (
      rpt strip_tac >> fs[] >>
      `?entry. lookup_scopes id st.scopes = SOME entry` by (
        qpat_x_assum`env_consistent _ _ st`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
      `FLOOKUP h id = NONE` suffices_by simp[] >>
      `FLOOKUP (HD st_body.scopes) id = NONE` suffices_by simp[] >>
      irule lookup_scopes_not_in_new_head >> simp[] >>
      qexists_tac `cx` >> qexists_tac `entry` >> qexists_tac `res` >>
      qexists_tac `st.scopes` >> qexists_tac `st` >> simp[] >>
      qexists_tac `FEMPTY` >> qexists_tac `ss` >> simp[]) >>
    rpt strip_tac >> fs[] >>
    `?entry. lookup_scopes id st.scopes = SOME entry` by (
      qpat_x_assum`env_consistent _ _ st`mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
    `FLOOKUP h id = NONE` suffices_by simp[] >>
    `FLOOKUP (HD st_body.scopes) id = NONE` suffices_by simp[] >>
    irule lookup_scopes_not_in_new_head >> simp[] >>
    qexists_tac `cx` >> qexists_tac `entry` >> qexists_tac `res` >>
    qexists_tac `st.scopes` >> qexists_tac `st` >> simp[] >>
    qexists_tac `FEMPTY` >> qexists_tac `ss` >> simp[]) >>
  conj_tac >- (
    qexists_tac `env_body` >> simp[] >>
    rpt strip_tac >> fs[] >>
    `lookup_scopes id st.scopes = NONE` by (
      qpat_x_assum`env_consistent env cx st`mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
      Cases_on `lookup_scopes id st.scopes` >> gvs[] >>
      metis_tac[optionTheory.IS_SOME_DEF]) >>
    qspecl_then [`cx`, `ss`, `st`, `FEMPTY`, `st.scopes`, `res`, `st_body`, `id`, `h`, `t`]
      mp_tac eval_stmts_preserves_tail_lookup_none >>
    simp[]) >>
  qexists_tac `st` >> simp[] >>
  qspecl_then [`cx`, `ss`, `FEMPTY`, `st`, `res`, `st_body`]
    mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
  simp[]
QED

Theorem eval_stmts_scope_bracket_old_var_not_in_head:
  !cx ss st sc res st_body id entry h t.
  eval_stmts cx ss (st with scopes updated_by CONS sc) = (res, st_body) /\
  lookup_scopes id st.scopes = SOME entry /\
  id NOTIN FDOM sc /\ st_body.scopes = h::t ==>
  FLOOKUP h id = NONE
Proof
  rpt strip_tac >>
  `st with scopes updated_by CONS sc = st with scopes := sc::st.scopes` by
    simp[evaluation_state_component_equality] >>
  `eval_stmts cx ss (st with scopes := sc::st.scopes) = (res,st_body)` by
    metis_tac[] >>
  `st_body.scopes <> []` by simp[] >>
  drule lookup_scopes_not_in_new_head >>
  disch_then (qspecl_then [`id`, `entry`] mp_tac) >>
  simp[] >>
  disch_then drule >> simp[]
QED

Theorem scope_bracket_var_type_notin_pushed_scope:
  !env id ty sc.
  FLOOKUP env.var_types id = SOME ty /\
  (!id. id IN FDOM env.var_types ==> id NOTIN FDOM sc) ==>
  id NOTIN FDOM sc
Proof
  rw[] >>
  `id IN FDOM env.var_types` by metis_tac[FLOOKUP_SOME_IN_FDOM] >>
  metis_tac[]
QED

Theorem scope_bracket_old_var_not_in_head:
  !cx ss st sc res st_body h t id entry.
  eval_stmts cx ss (st with scopes updated_by CONS sc) = (res, st_body) /\
  st_body.scopes = h::t /\
  id NOTIN FDOM sc /\
  lookup_scopes id st.scopes = SOME entry ==>
  FLOOKUP h id = NONE
Proof
  rpt strip_tac >>
  metis_tac[eval_stmts_scope_bracket_old_var_not_in_head]
QED

Theorem env_consistent_lookup_scopes_none:
  env_consistent env cx st /\ FLOOKUP env.var_types id = NONE ==>
  lookup_scopes id st.scopes = NONE
Proof
  rpt strip_tac >>
  fs[env_consistent_def, env_scopes_consistent_def] >>
  Cases_on `lookup_scopes id st.scopes` >> gvs[] >>
  metis_tac[optionTheory.IS_SOME_DEF]
QED

Theorem eval_stmts_scope_bracket_tail_lookup_none:
  !cx ss st sc res st_body id h t.
  eval_stmts cx ss (st with scopes updated_by CONS sc) = (res, st_body) /\
  lookup_scopes id st.scopes = NONE /\
  st_body.scopes = h::t ==>
  lookup_scopes id t = NONE
Proof
  rpt strip_tac >>
  `st with scopes updated_by CONS sc = st with scopes := sc::st.scopes` by
    simp[evaluation_state_component_equality] >>
  metis_tac[eval_stmts_preserves_tail_lookup_none]
QED

Theorem scope_bracket_var_type_head_none:
  env_consistent env cx st /\
  eval_stmts cx ss (st with scopes updated_by CONS sc) = (res, st_body) /\
  st_body.scopes = h::t /\
  FLOOKUP env.var_types id = SOME ty /\
  (!id. id IN FDOM env.var_types ==> id NOTIN FDOM sc) ==>
  FLOOKUP h id = NONE
Proof
  rpt strip_tac >>
  `id NOTIN FDOM sc` by metis_tac[scope_bracket_var_type_notin_pushed_scope] >>
  `?entry. lookup_scopes id st.scopes = SOME entry` by (
    fs[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
    metis_tac[]) >>
  metis_tac[scope_bracket_old_var_not_in_head]
QED

Theorem scope_bracket_new_var_tail_none:
  !env cx st ss sc res st_body h t id.
  env_consistent env cx st /\
  eval_stmts cx ss (st with scopes updated_by CONS sc) = (res, st_body) /\
  st_body.scopes = h::t /\
  FLOOKUP env.var_types id = NONE ==>
  lookup_scopes id t = NONE
Proof
  rpt strip_tac >>
  `lookup_scopes id st.scopes = NONE` by (
    qpat_x_assum `env_consistent env cx st` mp_tac >>
    simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
    Cases_on `lookup_scopes id st.scopes` >> gvs[] >>
    metis_tac[optionTheory.IS_SOME_DEF]) >>
  qspecl_then [`cx`, `ss`, `st`, `sc`, `res`, `st_body`, `id`, `h`, `t`]
    mp_tac eval_stmts_scope_bracket_tail_lookup_none >>
  simp[]
QED

Theorem scope_bracket_preserves_ec:
  env_maps_wf env /\
  env_consistent env cx st /\
  type_stmts env ret_ty ss = SOME env_after /\
  env_consistent env_after cx st_body /\
  eval_stmts cx ss (st with scopes updated_by CONS sc) = (res, st_body) /\
  (!id. id IN FDOM env.var_types ==> id NOTIN FDOM sc) ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  rpt strip_tac >>
  `preserves_tv cx (st with scopes updated_by CONS sc) st_body` by
    metis_tac[eval_preserves_tv] >>
  `preserves_tv cx st (st_body with scopes := TL st_body.scopes)` by (
    irule eval_stmts_scope_bracket_gen_preserves_tv >> simp[] >>
    goal_assum drule >> simp[]) >>
  Cases_on `st_body.scopes` >> gvs[]
  >- (drule eval_stmts_preserves_scopes_len >> simp[] >>
      strip_tac >> fs[env_consistent_def, env_scopes_consistent_def]) >>
  `t <> []` by (
    drule eval_stmts_preserves_scopes_len >> simp[] >> strip_tac >>
    fs[env_consistent_def, env_scopes_consistent_def] >>
    Cases_on `st.scopes` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> FLOOKUP h id = NONE` by (
    rpt strip_tac >>
    drule_all scope_bracket_var_type_head_none >> simp[]) >>
  `!id. FLOOKUP env.var_assignable id = SOME T ==> FLOOKUP h id = NONE` by (
    rpt strip_tac >>
    `IS_SOME (FLOOKUP env.var_types id)` by fs[env_maps_wf_def] >>
    Cases_on `FLOOKUP env.var_types id` >> gvs[] >>
    drule_all scope_bracket_var_type_head_none >> simp[]) >>
  `!id ty.
     FLOOKUP env_after.var_types id = SOME ty /\ FLOOKUP env.var_types id = NONE ==>
     lookup_scopes id t = NONE` by (
    rpt strip_tac >>
    qspecl_then [`env`, `cx`, `st`, `ss`, `sc`, `res`, `st_body`, `h`, `t`, `id`]
      mp_tac scope_bracket_new_var_tail_none >>
    simp[]) >>
  qspecl_then [`env`, `cx`, `st`, `st_body`, `t`, `ret_ty`, `ss`, `env_after`, `h`]
    mp_tac type_stmts_env_consistent_after_pop >>
  simp[]
QED

Theorem scope_bracket_preserves_swt:
  eval_stmts cx ss (st with scopes updated_by CONS sc) = (res, st_body) /\
  state_well_typed st_body ==>
  state_well_typed (st_body with scopes := TL st_body.scopes)
Proof
  rpt strip_tac >>
  imp_res_tac eval_stmts_preserves_scopes_len >>
  Cases_on `st_body.scopes` >> gvs[] >>
  irule pop_scope_preserves_state_well_typed >>
  qexists_tac `st_body` >>
  qexists_tac `()` >>
  simp[pop_scope_def, return_def]
QED
