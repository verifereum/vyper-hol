(* Static target prerequisites for effectful tuple assignment. *)
Theory tupleAssignEffectfulIndexTargets
Ancestors
  bodySimExprCases bodyExprPreFacts targetPlaceSimCases bodySim
  supportedStmts supportedStmtTraverse supportedExprTraverse
  vyperTypeCallGraph gasContext allocLimits vyperTypeSystem targetPlaceSim
  vyperTypeCallStackSoundness vyperTypeEnv list

Theorem tuple_effectful_base_induct[local]:
  !P. (!id. P (NameTarget id)) /\ (!nsid. P (TopLevelNameTarget nsid)) /\
    (!bt e. P bt ==> P (SubscriptTarget bt e)) /\
    (!bt s. P bt ==> P (AttributeTarget bt s)) ==> !bt. P bt
Proof
  rpt strip_tac >>
  `(!e:expr. T) /\ !bt. P bt` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >> simp[]
QED

Theorem tuple_effectful_target_case:
  body_inv tops ctx cenv cx /\ body_base_target_ok cx bt ==>
  target_case F ctx func cenv cx bt
Proof
  strip_tac >> irule target_case_all >>
  qpat_x_assum `body_base_target_ok cx bt` mp_tac >>
  qid_spec_tac `bt` >>
  Induct using tuple_effectful_base_induct >>
  simp[body_base_target_ok_def, target_idx_case_def] >>
  metis_tac[body_expr_ok_case]
QED

Theorem tuple_effectful_member_occurs[local]:
  !gs. MEM (BaseTarget bt) gs /\ supported_target_exists p bt ==>
    supported_stmt_expr_exists p (Assign (TupleTarget gs) e)
Proof
  Induct >> gvs[supported_stmt_expr_exists_def,
    supported_assignment_exists_def] >> rpt strip_tac >>
  gvs[supported_assignment_exists_def] >> metis_tac[]
QED

Theorem tuple_effectful_member_alloc[local]:
  !gs. MEM (BaseTarget bt) gs /\ alloc_limits_assignments cenv gs ==>
    alloc_limits_target cenv bt
Proof
  Induct >> rw[alloc_limits_assignment_def] >> gvs[alloc_limits_assignment_def]
QED

Theorem tuple_effectful_member_calls[local]:
  !gs. MEM (BaseTarget bt) gs /\
    call_evaluation_safe cx (int_calls_atargets gs) ==>
    call_evaluation_safe cx (int_calls_target bt)
Proof
  Induct >> simp[int_calls_atarget_def] >> rpt strip_tac >>
  metis_tac[int_calls_atarget_def, call_evaluation_safe_append_left,
    call_evaluation_safe_append_right]
QED

Theorem tuple_effectful_member_pre:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (TupleTarget gs) e) ==> occurs_abi_decode_target target tops) /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  MEM (BaseTarget bt) gs ==>
  target_indices_pre cenv cx env bt /\
  call_evaluation_safe cx (int_calls_target bt)
Proof
  rpt strip_tac >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (irule tuple_effectful_member_calls >> goal_assum drule >>
     gvs[int_calls_stmt_def, int_calls_atarget_def] >>
     metis_tac[call_evaluation_safe_append_left]) >>
  simp[] >>
  `supported_target tops bindings bt` by
    (gvs[supported_stmt_def, supported_assignment_def, EVERY_MEM] >>
     first_x_assum drule >> simp[]) >>
  `?ty. well_typed_atarget env (BaseTarget bt) ty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
       AllCaseEqs()] >> drule_all LIST_REL_MEM_IMP >>
     metis_tac[well_typed_atarget_def]) >>
  Cases_on `bt` >> gvs[supported_target_def, target_indices_pre_def]
  >~ [`AttributeTarget t fld`]
  >- (Cases_on `t` >> gvs[target_indices_pre_def]) >>
  rename1 `target_indices_pre cenv cx env root` >>
  Cases_on `root` >> gvs[target_indices_pre_def] >>
  rename1 `SubscriptTarget (TopLevelNameTarget nsid) key` >>
  `alloc_limits_target cenv (SubscriptTarget (TopLevelNameTarget nsid) key)` by
    (irule tuple_effectful_member_alloc >> goal_assum drule >>
     gvs[stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_assignment_def]) >>
  gvs[Once alloc_limits_expr_def] >> rpt strip_tac >>
  `well_typed_expr env key` by
    gvs[well_typed_atarget_def, well_typed_target_def,
        type_place_target_SubscriptTarget] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `cx_tops cx = tops` by
    (irule cx_tops_module >> gvs[body_inv_def]) >>
  `!p. supported_expr_exists p key ==>
     supported_stmt_expr_exists p (Assign (TupleTarget gs) e)` by
    (rpt strip_tac >> irule tuple_effectful_member_occurs >>
     goal_assum drule >> simp[supported_expr_exists_def]) >>
  irule stmt_expr_body_pre >> simp[] >>
  conj_tac >- gvs[body_inv_def] >>
  conj_tac >- (gvs[stmt_exprs_ok_flat] >> metis_tac[]) >>
  conj_tac >- (strip_tac >> qexists_tac `tops` >> gvs[body_inv_def]) >>
  qexists_tac `[]` >> gvs[int_calls_expr_def]
QED
