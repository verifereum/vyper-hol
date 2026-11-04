Theory exprSimForeignImmutableFrame
Ancestors
  exprSimHyps vyperTypeInitialState vyperImmutableMetadataFrame
  supportedStmts vyperState vyperInterpreter vyperMisc alist
  vyperStoragePlaceProvenance supportedTargets supportedDecls supportedExprForms

(* Updating one module's immutable cells preserves every other module's map,
   including at addresses other than the active contract. *)
Theorem set_immutable_other_module:
  !cx src name tv v s res t md addr.
    set_immutable cx src name tv v s = (res,t) /\ md <> src ==>
    (case ALOOKUP t.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms) =
    (case ALOOKUP s.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[set_immutable_def, get_address_immutables_def,
      set_address_immutables_def, bind_def, lift_option_type_def,
      return_def, raise_def, option_CASE_rator, AllCaseEqs()] >>
  Cases_on `addr = cx.txn.target` >>
  gvs[alistTheory.ALOOKUP_ADELKEY,
      get_source_immutables_set_other] >>
  Cases_on `ALOOKUP s.immutables addr` >> gvs[]
QED

Theorem write_place_other_module:
  !cx src name path v s res t md addr.
    write_place cx (ImmutablePlace src name path) v s = (res,t) /\
    md <> src ==>
    (case ALOOKUP t.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms) =
    (case ALOOKUP s.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms)
Proof
  rpt gen_tac >>
  simp[write_place_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, option_CASE_rator, sum_CASE_rator,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac vyperStatePreservationTheory.get_immutables_state >> gvs[] >>
  Cases_on `ALOOKUP s.immutables addr` >> gvs[] >>
  drule_all set_immutable_other_module >>
  disch_then (qspec_then `addr` mp_tac) >>
  Cases_on `ALOOKUP t.immutables addr` >> gvs[]
QED

Theorem pop_place_other_module:
  !cx src name path s res t md addr.
    pop_place cx (ImmutablePlace src name path) s = (res,t) /\
    md <> src ==>
    (case ALOOKUP t.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms) =
    (case ALOOKUP s.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms)
Proof
  rpt gen_tac >>
  simp[pop_place_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, option_CASE_rator, sum_CASE_rator,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac vyperStatePreservationTheory.get_immutables_state >> gvs[] >>
  Cases_on `ALOOKUP s.immutables addr` >> gvs[] >>
  drule_all set_immutable_other_module >>
  disch_then (qspec_then `addr` mp_tac) >>
  rpt CASE_TAC >> gvs[]
QED

Theorem append_place_other_module:
  !cx src name path v s res t md addr.
    append_place cx (ImmutablePlace src name path) v s = (res,t) /\
    md <> src ==>
    (case ALOOKUP t.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms) =
    (case ALOOKUP s.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms)
Proof
  rpt gen_tac >>
  simp[append_place_def, bind_def, lift_sum_def, sum_CASE_rator,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac place_type_value_state >>
  imp_res_tac read_place_state >> gvs[] >>
  Cases_on `ALOOKUP s.immutables addr` >> gvs[] >>
  drule_all write_place_other_module >>
  disch_then (qspec_then `addr` mp_tac) >>
  Cases_on `ALOOKUP t.immutables addr` >> gvs[]
QED

(* Extending a place cannot change its immutable module or root name. *)
Theorem extend_place_immutable_origin:
  extend_place cx pv sb s =
    (INL (PlaceR (ImmutablePlace md name path')),t) ==>
  ?path. pv = PlaceR (ImmutablePlace md name path) /\
         path' = path ++ [sb]
Proof
  Cases_on `pv` >>
  simp[extend_place_def, bind_def, return_def,
       raise_def, lift_option_type_def, lift_sum_def, AllCaseEqs()]
  >~ [`extend_place cx (PlaceR p)`]
  >- (rename1 `extend_place cx (PlaceR p)` >> Cases_on `p` >>
      simp[extend_place_def, extend_memory_place_def, bind_def,
           ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      drule extend_storage_place_subregion >> simp[])
  >> rename1 `extend_place cx (HashMapRef tr slot kt vt)` >>
  Cases_on `sb` >> simp[extend_place_def, raise_def] >>
  Cases_on `vt` >>
  simp[extend_place_def, bind_def, return_def, raise_def,
       lift_option_type_def, AllCaseEqs()]
QED

Theorem lookup_global_immutable_module:
  lookup_global cx src name s =
    (INL (PlaceR (ImmutablePlace md root path)),t) ==> md = src
Proof
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[option_CASE_rator, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, return_def, raise_def, AllCaseEqs()])
QED

Theorem supported_base_place_immutable_module:
  !bt cx s md name path t tops bindings.
    (supported_target tops bindings bt \/
     IS_SOME (supported_target_info tops bindings bt)) /\
    eval_base_place cx bt s =
      (INL (PlaceR (ImmutablePlace md name path)),t) ==>
    md = NONE
Proof
  measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt gen_tac >>
  simp[supported_target_def, supported_target_info_def]
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- (simp[Once evaluate_def, bind_def, get_scopes_def,
           lift_option_type_def, type_check_def, assert_def,
           ignore_bind_def, return_def, raise_def, AllCaseEqs()])
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`]
  >- (Cases_on `p` >> rename1 `TopLevelNameTarget (src,root)` >>
      Cases_on `src = NONE` >>
      gvs[supported_scalar_target_def, supported_immutable_type_def,
          supported_place_root_def, supported_lookup_other_module] >>
      simp[Once evaluate_def] >> rpt strip_tac >>
      drule lookup_global_immutable_module >> simp[])
  >~ [`eval_base_place _ (SubscriptTarget _ _) _ = _`]
  >- (rpt strip_tac >>
      qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def,
           AllCaseEqs()] >>
      rpt strip_tac >> drule extend_place_immutable_origin >> strip_tac >>
      gvs[]
      >- (Cases_on `b` >> gvs[] >>
          rename1 `TopLevelNameTarget ns` >> Cases_on `ns` >>
          rename1 `TopLevelNameTarget (src,root)` >>
          gvs[Once evaluate_def] >>
          drule lookup_global_immutable_module >> strip_tac >> gvs[] >>
          Cases_on `md = NONE` >>
          gvs[supported_subscript_base_def, supported_storage_array_def,
              supported_lookup_other_module]) >>
      first_x_assum (qspec_then `b` mp_tac) >>
      simp[] >> strip_tac >> first_x_assum irule >>
      conj_tac >- (goal_assum (drule_at Any)) >>
      qexistsl [`bindings`, `tops`] >> disj2_tac >>
      Cases_on `supported_target_info tops bindings b` >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> drule extend_place_immutable_origin >> strip_tac >> gvs[]
  >- (Cases_on `b` >> gvs[] >>
      rename1 `TopLevelNameTarget ns` >> Cases_on `ns` >>
      rename1 `TopLevelNameTarget (src,root)` >>
      gvs[Once evaluate_def] >>
      drule lookup_global_immutable_module >> strip_tac >> gvs[] >>
      Cases_on `md = NONE` >>
      gvs[supported_storage_field_write_def, supported_storage_fields_def,
          supported_lookup_other_module]) >>
  first_x_assum (qspec_then `b` mp_tac) >>
  simp[] >> strip_tac >> first_x_assum irule >>
  conj_tac >- (goal_assum (drule_at Any)) >>
  qexistsl [`bindings`, `tops`] >> disj2_tac >>
  Cases_on `supported_target_info tops bindings b` >> gvs[]
QED

Theorem supported_target_place_immutable_module:
  (supported_target tops bindings bt \/
   IS_SOME (supported_target_info tops bindings bt)) /\
  eval_target_place cx bt s = (INL (ImmutablePlace md name path),t) ==>
  md = NONE
Proof
  simp[Once evaluate_def, bind_def, get_place_def, return_def,
       raise_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  irule supported_base_place_immutable_module >>
  goal_assum (drule_at Any) >>
  qexistsl [`bindings`, `tops`] >> simp[]
QED
