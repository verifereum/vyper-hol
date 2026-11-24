(* Dispatch linked assignments to existing local variables by their layout. *)
Theory bodyAssignNameRoutesMods
Ancestors
  bodyAssignNameLinkedSetup bodyAssignNameWordRouteMods bodyAssignNameEmptyRouteMods
  bodyAssignNameCopyRouteMods bodyAssignNameWidenedRouteMods
  bodyAssignNameEqualRhsWidenRouteMods bodyFullPredsMods bodyFullPostsMods
  compileEnv typedMemoryCopy

Theorem assign_name_routes_from_writes_mods:
  !mods exps cx id e.
    body_expr_full_ok_mods mods exps cx e ==>
    body_stmt_full_ok_mods mods exps cx
      (Assign (BaseTarget (NameTarget id)) e)
Proof
  rpt gen_tac >> disch_tac >> rw[body_stmt_full_ok_mods_def] >>
  `linked_assign_name_context_mods mods exps cx id e
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    src tops bindings cenv env env' ret_ty RetQ es` by
    (simp[linked_assign_name_context_mods_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac linked_assign_name_setup_mods >>
  Cases_on `is_word_type ty`
  >- (irule assign_name_word_route_mods >>
      qhdtm_assum `linked_assign_name_context_mods` (irule_at Any) >>
      qpat_assum `FLOOKUP env.var_types id = SOME ty` (irule_at Any) >> simp[]) >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- (irule assign_name_empty_route_mods >> simp[] >>
      qhdtm_assum `linked_assign_name_context_mods` (irule_at Any) >>
      qpat_assum `FLOOKUP env.var_types id = SOME ty` (irule_at Any) >> simp[]) >>
  reverse (Cases_on `lowered_value_type cenv e = expr_type e \/
                     is_bytestring_type (expr_type e) /\
                     is_bytestring_type (lowered_value_type cenv e) /\
                     arg_type_fits (lowered_value_type cenv e) (expr_type e)`)
  >- (irule assign_name_different_rhs_route_mods >>
      qhdtm_assum `linked_assign_name_context_mods` (irule_at Any) >>
      qpat_assum `FLOOKUP env.var_types id = SOME ty` (irule_at Any) >> fs[]) >>
  Cases_on `lowered_value_type cenv e = ty \/ is_bytestring_type ty`
  >- (irule assign_name_copy_route_mods >> simp[] >>
      qhdtm_assum `linked_assign_name_context_mods` (irule_at Any) >>
      qpat_assum `FLOOKUP env.var_types id = SOME ty` (irule_at Any) >>
      simp[] >> metis_tac[type_widens_from_bytestring]) >>
  `~is_bytestring_type (expr_type e)` by metis_tac[type_widens_from_bytestring] >>
  `expr_type e <> ty` by metis_tac[] >>
  irule assign_name_equal_rhs_widen_route_mods >>
  qhdtm_assum `linked_assign_name_context_mods` (irule_at Any) >>
  qpat_assum `FLOOKUP env.var_types id = SOME ty` (irule_at Any) >> fs[]
QED
