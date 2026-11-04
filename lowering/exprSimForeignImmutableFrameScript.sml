Theory exprSimForeignImmutableFrame
Ancestors
  exprSimHyps vyperTypeInitialState vyperImmutableMetadataFrame
  supportedStmts vyperState vyperInterpreter vyperMisc alist
  vyperStoragePlaceProvenance supportedTargets supportedDecls supportedExprForms
  targetPlaceSim vyperAST supportedProgram supportedExprTraverse supportedStmtTraverse
  vyperTypeCallGraph supportedExprs bodyStorageCases vyperCallOutcomeFrame vyperPlaceFrames vyperMachineFrame

(* Use the existing target-root traversal; read permission is deliberately
   independent of this write-root restriction. *)
Definition target_root_main_def:
  target_root_main bt <=>
    !src name. target_root bt = TopLevelNameTarget (src,name) ==> src = NONE
End

Theorem target_root_main_eqs[simp]:
  target_root_main (NameTarget name) /\
  (target_root_main (TopLevelNameTarget (src,name)) <=> src = NONE) /\
  (target_root_main (SubscriptTarget bt e) <=> target_root_main bt) /\
  (target_root_main (AttributeTarget bt fname) <=> target_root_main bt)
Proof
  simp[target_root_main_def, target_root_def]
QED

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

Theorem main_root_base_place_immutable_module:
  !bt cx s md name path t.
    target_root_main bt /\
    eval_base_place cx bt s =
      (INL (PlaceR (ImmutablePlace md name path)),t) ==> md = NONE
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac >> simp[]
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- simp[Once evaluate_def, bind_def, get_scopes_def,
          lift_option_type_def, type_check_def, assert_def,
          ignore_bind_def, return_def, raise_def, AllCaseEqs()]
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`]
  >- (rename1 `TopLevelNameTarget ns` >> Cases_on `ns` >> simp[] >>
      rpt strip_tac >> gvs[Once evaluate_def] >>
      drule lookup_global_immutable_module >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> drule extend_place_immutable_origin >> strip_tac >> gvs[] >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
  strip_tac >> first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem supported_target_root_main:
  !bt tops bindings.
    (supported_target tops bindings bt \/
     IS_SOME (supported_target_info tops bindings bt)) ==>
    target_root_main bt
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac >> simp[supported_target_def, supported_target_info_def]
  >~ [`target_root_main (TopLevelNameTarget _)`]
  >- (rename1 `TopLevelNameTarget ns` >> Cases_on `ns` >>
      rename1 `TopLevelNameTarget (src,root)` >>
      Cases_on `src = NONE` >>
      simp[supported_scalar_target_def, supported_immutable_type_def,
           supported_place_root_def, supported_lookup_other_module]) >>
  rpt strip_tac
  >- (Cases_on `b` >> gvs[] >>
      rename1 `TopLevelNameTarget ns` >> Cases_on `ns` >>
      rename1 `TopLevelNameTarget (src,root)` >>
      Cases_on `src = NONE` >>
      gvs[supported_subscript_base_def, supported_storage_array_def,
          supported_lookup_other_module])
  >- (first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
      disch_then irule >> qexistsl [`bindings`, `tops`] >> disj2_tac >>
      Cases_on `supported_target_info tops bindings b` >> gvs[])
  >- (Cases_on `b` >> gvs[] >>
      rename1 `TopLevelNameTarget ns` >> Cases_on `ns` >>
      rename1 `TopLevelNameTarget (src,root)` >>
      Cases_on `src = NONE` >>
      gvs[supported_storage_field_write_def, supported_storage_fields_def,
          supported_lookup_other_module]) >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
  disch_then irule >> qexistsl [`bindings`, `tops`] >> disj2_tac >>
  Cases_on `supported_target_info tops bindings b` >> gvs[]
QED

Theorem supported_base_place_immutable_module:
  !bt cx s md name path t tops bindings.
    (supported_target tops bindings bt \/
     IS_SOME (supported_target_info tops bindings bt)) /\
    eval_base_place cx bt s =
      (INL (PlaceR (ImmutablePlace md name path)),t) ==>
    md = NONE
Proof
  metis_tac[supported_target_root_main, main_root_base_place_immutable_module]
QED

(* Syntactic proof interface for confining immutable mutations to NONE. *)
Definition foreign_frame_bad_pop_def:
  foreign_frame_bad_pop (Pop ty bt) = ~target_root_main bt /\
  foreign_frame_bad_pop _ = F
End

Definition foreign_frame_callee_def:
  foreign_frame_callee cx c <=>
    FST c = NONE /\ ?tops. supported_program tops /\
                          get_module_code cx NONE = SOME tops
End

Definition foreign_frame_bad_def:
  foreign_frame_bad cx e <=>
    expr_evm_run_root e \/ foreign_frame_bad_pop e
End

Definition foreign_frame_expr_def:
  foreign_frame_expr cx e <=>
    ~supported_expr_exists (foreign_frame_bad cx) e /\
    EVERY (foreign_frame_callee cx) (int_calls_expr e)
End

Definition foreign_frame_exprs_def:
  foreign_frame_exprs cx es <=>
    ~supported_exprs_exists (foreign_frame_bad cx) es /\
    EVERY (foreign_frame_callee cx) (int_calls_exprs es)
End

Definition foreign_frame_target_def:
  foreign_frame_target cx bt <=>
    ~supported_target_exists (foreign_frame_bad cx) bt /\
    EVERY (foreign_frame_callee cx) (int_calls_target bt)
End

Definition foreign_frame_write_target_def:
  foreign_frame_write_target cx bt <=> target_root_main bt /\ foreign_frame_target cx bt
End

Definition foreign_frame_assignment_def:
  foreign_frame_assignment cx (BaseTarget bt) = foreign_frame_write_target cx bt /\
  foreign_frame_assignment cx (TupleTarget ats) = foreign_frame_assignments cx ats /\
  foreign_frame_assignments cx [] = T /\
  foreign_frame_assignments cx (at::ats) =
    (foreign_frame_assignment cx at /\ foreign_frame_assignments cx ats)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,at) => assignment_target_size at
  | INR (_,ats) => list_size assignment_target_size ats)` >>
  simp[assignment_target_size_def, listTheory.list_size_def]
End

Definition foreign_frame_iterator_def:
  foreign_frame_iterator cx it <=>
    ~supported_iterator_exists (foreign_frame_bad cx) it /\
    EVERY (foreign_frame_callee cx) (int_calls_iterator it)
End

Definition foreign_frame_assert_def:
  foreign_frame_assert cx reason <=>
    ~supported_assert_exists (foreign_frame_bad cx) reason /\
    EVERY (foreign_frame_callee cx) (int_calls_assert_reason reason)
End

Definition foreign_frame_raise_def:
  foreign_frame_raise cx reason <=>
    ~supported_raise_exists (foreign_frame_bad cx) reason /\
    EVERY (foreign_frame_callee cx) (int_calls_raise_reason reason)
End

Definition foreign_frame_stmt_def:
  foreign_frame_stmt cx Pass = T /\
  foreign_frame_stmt cx Break = T /\
  foreign_frame_stmt cx Continue = T /\
  foreign_frame_stmt cx (Expr e) = foreign_frame_expr cx e /\
  foreign_frame_stmt cx (Return opt) =
    (~supported_opt_exists (foreign_frame_bad cx) opt /\
     EVERY (foreign_frame_callee cx) (int_calls_opt opt)) /\
  foreign_frame_stmt cx (AnnAssign name ty e) = foreign_frame_expr cx e /\
  foreign_frame_stmt cx (Assign at e) =
    (foreign_frame_assignment cx at /\ foreign_frame_expr cx e) /\
  foreign_frame_stmt cx (AugAssign ty bt op e) =
    (foreign_frame_write_target cx bt /\ foreign_frame_expr cx e) /\
  foreign_frame_stmt cx (Append bt e) =
    (foreign_frame_write_target cx bt /\ foreign_frame_expr cx e) /\
  foreign_frame_stmt cx (Log id es) = foreign_frame_exprs cx es /\
  foreign_frame_stmt cx (Assert e reason) =
    (foreign_frame_expr cx e /\ foreign_frame_assert cx reason) /\
  foreign_frame_stmt cx (Raise reason) = foreign_frame_raise cx reason /\
  foreign_frame_stmt cx (If e yes no) =
    (foreign_frame_expr cx e /\ foreign_frame_stmts cx yes /\ foreign_frame_stmts cx no) /\
  foreign_frame_stmt cx (For name ty it n body) =
    (foreign_frame_iterator cx it /\ foreign_frame_stmts cx body) /\
  foreign_frame_stmts cx [] = T /\
  foreign_frame_stmts cx (stmt::stmts) =
    (foreign_frame_stmt cx stmt /\ foreign_frame_stmts cx stmts)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,stmt) => stmt_size stmt | INR (_,stmts) => list_size stmt_size stmts)` >>
  simp[stmt_size_def, listTheory.list_size_def]
End

(* Internal-call confinement ignores the same optional fields as int_calls_expr. *)
Theorem foreign_frame_ignored_option_regression:
  let e = Call NoneT RawLog []
    (SOME (Call NoneT (IntCall (SOME 0,"f")) [] NONE)) in
  ~expr_has_pop e /\ ~expr_has_evm_run e /\
  int_calls_expr e = [] /\ foreign_frame_expr cx e
Proof
  simp[expr_has_pop_def, expr_has_evm_run_def, int_calls_expr_def,
       foreign_frame_expr_def, supported_expr_exists_def,
       foreign_frame_bad_def, foreign_frame_bad_pop_def,
       expr_evm_run_root_def, expr_pop_root_def]
QED

Theorem foreign_frame_nopop_entry_mutual[local]:
  (!p e. p = foreign_frame_bad cx /\
    ~supported_expr_exists expr_pop_root e /\
    ~supported_expr_exists expr_evm_run_root e ==>
    ~supported_expr_exists p e) /\
  (!p bt. p = foreign_frame_bad cx /\
    ~supported_target_exists expr_pop_root bt /\
    ~supported_target_exists expr_evm_run_root bt ==>
    ~supported_target_exists p bt) /\
  (!p es. p = foreign_frame_bad cx /\
    ~supported_exprs_exists expr_pop_root es /\
    ~supported_exprs_exists expr_evm_run_root es ==>
    ~supported_exprs_exists p es) /\
  (!p opt. p = foreign_frame_bad cx /\
    ~supported_opt_exists expr_pop_root opt /\
    ~supported_opt_exists expr_evm_run_root opt ==>
    ~supported_opt_exists p opt) /\
  (!p fields. p = foreign_frame_bad cx /\
    ~supported_fields_exists expr_pop_root fields /\
    ~supported_fields_exists expr_evm_run_root fields ==>
    ~supported_fields_exists p fields)
Proof
  ho_match_mp_tac supported_expr_exists_ind >>
  rw[supported_expr_exists_def, foreign_frame_bad_def,
     foreign_frame_bad_pop_def, expr_pop_root_def]
QED

Theorem foreign_frame_expr_entry:
  ~expr_has_pop e /\ ~expr_has_evm_run e /\
  EVERY (foreign_frame_callee cx) (int_calls_expr e) ==>
  foreign_frame_expr cx e
Proof
  simp[expr_has_pop_def, expr_has_evm_run_def, foreign_frame_expr_def] >>
  metis_tac[CONJUNCT1 foreign_frame_nopop_entry_mutual]
QED

Theorem foreign_frame_expr_children:
  (foreign_frame_expr cx (IfExp ty c a b) ==>
    foreign_frame_expr cx c /\ foreign_frame_expr cx a /\ foreign_frame_expr cx b) /\
  (foreign_frame_expr cx (Subscript ty obj key) ==>
    foreign_frame_expr cx obj /\ foreign_frame_expr cx key) /\
  (foreign_frame_expr cx (Attribute ty obj fname) ==> foreign_frame_expr cx obj) /\
  (foreign_frame_expr cx (Builtin ty blt es) ==> foreign_frame_exprs cx es) /\
  (foreign_frame_expr cx (TypeBuiltin ty tblt target es) ==> foreign_frame_exprs cx es) /\
  (foreign_frame_expr cx (Pop ty bt) ==> foreign_frame_write_target cx bt)
Proof
  simp[foreign_frame_expr_def, foreign_frame_exprs_def,
       foreign_frame_write_target_def, foreign_frame_target_def,
       supported_expr_exists_def, int_calls_expr_def, listTheory.EVERY_APPEND,
       foreign_frame_bad_def, foreign_frame_bad_pop_def] >>
  metis_tac[]
QED

Theorem foreign_frame_target_eqs[simp]:
  foreign_frame_target cx (NameTarget name) /\
  foreign_frame_target cx (TopLevelNameTarget id) /\
  (foreign_frame_target cx (SubscriptTarget bt key) <=>
    foreign_frame_target cx bt /\ foreign_frame_expr cx key) /\
  (foreign_frame_target cx (AttributeTarget bt fname) <=> foreign_frame_target cx bt)
Proof
  simp[foreign_frame_target_def, foreign_frame_expr_def,
       supported_expr_exists_def, int_calls_expr_def, listTheory.EVERY_APPEND] >>
  metis_tac[]
QED

Theorem foreign_frame_exprs_eqs[simp]:
  foreign_frame_exprs cx [] /\
  (foreign_frame_exprs cx (e::es) <=>
    foreign_frame_expr cx e /\ foreign_frame_exprs cx es)
Proof
  simp[foreign_frame_exprs_def, foreign_frame_expr_def,
       supported_expr_exists_def, int_calls_expr_def, listTheory.EVERY_APPEND] >>
  metis_tac[]
QED

Theorem foreign_frame_call_args:
  foreign_frame_expr cx (Call ty ct es opt) ==> foreign_frame_exprs cx es
Proof
  Cases_on `ct` >>
  simp[foreign_frame_expr_def, foreign_frame_exprs_def,
       supported_expr_exists_def, int_calls_expr_def, listTheory.EVERY_APPEND] >>
  metis_tac[]
QED

Theorem foreign_frame_intcall_callee:
  foreign_frame_expr cx (Call ty (IntCall callee) es opt) ==>
  foreign_frame_callee cx callee
Proof
  simp[foreign_frame_expr_def, int_calls_expr_def]
QED

Theorem foreign_frame_extcall_option:
  foreign_frame_expr cx (Call ty (ExtCall a b c d) es (SOME e)) ==>
  foreign_frame_expr cx e
Proof
  simp[foreign_frame_expr_def, supported_expr_exists_def,
       int_calls_expr_def, listTheory.EVERY_APPEND]
QED

Theorem foreign_frame_named_exprs:
  (~supported_fields_exists (foreign_frame_bad cx) fields /\
   EVERY (foreign_frame_callee cx) (int_calls_named_exprs fields)) <=>
  EVERY (\kv. foreign_frame_expr cx (SND kv)) fields
Proof
  Induct_on `fields` >- simp[supported_expr_exists_def, int_calls_expr_def] >>
  qx_gen_tac `kv` >> PairCases_on `kv` >>
  gvs[supported_expr_exists_def, int_calls_expr_def,
      foreign_frame_expr_def, listTheory.EVERY_APPEND] >> metis_tac[]
QED

Theorem foreign_frame_structlit_fields:
  foreign_frame_expr cx (StructLit ty id fields) ==>
  EVERY (\kv. foreign_frame_expr cx (SND kv)) fields
Proof
  simp[foreign_frame_expr_def, supported_expr_exists_def, int_calls_expr_def,
       GSYM foreign_frame_named_exprs]
QED

Theorem foreign_frame_iterator_eqs[simp]:
  (foreign_frame_iterator cx (Array e) <=> foreign_frame_expr cx e) /\
  (foreign_frame_iterator cx (Range lo hi) <=>
    foreign_frame_expr cx lo /\ foreign_frame_expr cx hi)
Proof
  simp[foreign_frame_iterator_def, supported_iterator_exists_def,
       int_calls_iterator_def, foreign_frame_expr_def, listTheory.EVERY_APPEND] >>
  metis_tac[]
QED

Theorem foreign_frame_assert_eqs[simp]:
  foreign_frame_assert cx AssertBare /\
  foreign_frame_assert cx AssertUnreachable /\
  (foreign_frame_assert cx (AssertReason e) <=> foreign_frame_expr cx e) /\
  (foreign_frame_assert cx (AssertCustomError err) <=>
    foreign_frame_exprs cx (custom_error_exprs err))
Proof
  simp[foreign_frame_assert_def, supported_assert_exists_def,
       int_calls_assert_reason_def, foreign_frame_expr_def, foreign_frame_exprs_def,
       supported_exprs_exists_every, listTheory.NOT_EXISTS]
QED

Theorem foreign_frame_raise_eqs[simp]:
  foreign_frame_raise cx RaiseBare /\
  foreign_frame_raise cx RaiseUnreachable /\
  (foreign_frame_raise cx (RaiseReason e) <=> foreign_frame_expr cx e) /\
  (foreign_frame_raise cx (RaiseCustomError err) <=>
    foreign_frame_exprs cx (custom_error_exprs err))
Proof
  simp[foreign_frame_raise_def, supported_raise_exists_def,
       int_calls_raise_reason_def, foreign_frame_expr_def, foreign_frame_exprs_def,
       supported_exprs_exists_every, listTheory.NOT_EXISTS]
QED

Theorem foreign_frame_return_eqs[simp]:
  foreign_frame_stmt cx (Return NONE) /\
  (foreign_frame_stmt cx (Return (SOME e)) <=> foreign_frame_expr cx e)
Proof
  simp[foreign_frame_stmt_def, supported_expr_exists_def,
       int_calls_expr_def, foreign_frame_expr_def]
QED

Theorem foreign_frame_read_write_regression:
  foreign_frame_expr cx (TopLevelName ty (SOME md,name)) /\
  ~foreign_frame_expr cx (Pop ty (TopLevelNameTarget (SOME md,name)))
Proof
  simp[foreign_frame_expr_def, supported_expr_exists_def, int_calls_expr_def,
       foreign_frame_bad_def, foreign_frame_bad_pop_def, expr_evm_run_root_def]
QED

Theorem main_root_target_place_immutable_module:
  target_root_main bt /\
  eval_target_place cx bt s = (INL (ImmutablePlace md name path),t) ==>
  md = NONE
Proof
  simp[Once evaluate_def, bind_def, get_place_def, return_def,
       raise_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  irule main_root_base_place_immutable_module >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem supported_target_place_immutable_module:
  (supported_target tops bindings bt \/
   IS_SOME (supported_target_info tops bindings bt)) /\
  eval_target_place cx bt s = (INL (ImmutablePlace md name path),t) ==>
  md = NONE
Proof
  metis_tac[supported_target_root_main, main_root_target_place_immutable_module]
QED

Theorem supported_pure_foreign_frame:
  (!tops e. supported_pure_expr tops e ==> foreign_frame_expr cx e) /\
  (!tops es. supported_pure_exprs tops es ==> foreign_frame_exprs cx es) /\
  (!tops fields. supported_pure_fields tops fields ==>
    ~supported_fields_exists (foreign_frame_bad cx) fields /\
    EVERY (foreign_frame_callee cx) (int_calls_named_exprs fields)) /\
  (!tops e. supported_place_expr tops e ==> foreign_frame_expr cx e)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  rw[supported_pure_expr_def, foreign_frame_expr_def, foreign_frame_exprs_def,
     supported_expr_exists_def, int_calls_expr_def, listTheory.EVERY_APPEND,
     foreign_frame_bad_def, foreign_frame_bad_pop_def, expr_evm_run_root_def] >>
  metis_tac[]
QED

Theorem supported_function_foreign_frame_callee:
  IS_SOME (supported_function_decl tops callee Internal) /\
  supported_program tops /\ get_module_code cx NONE = SOME tops ==>
  foreign_frame_callee cx callee
Proof
  PairCases_on `callee` >>
  simp[foreign_frame_callee_def] >>
  Cases_on `callee0 = NONE` >>
  simp[supported_lookup_other_module] >> metis_tac[]
QED

Theorem supported_storage_dynamic_array_root_main:
  supported_storage_dynamic_array tops id ==>
  target_root_main (TopLevelNameTarget id)
Proof
  PairCases_on `id` >> Cases_on `id0 = NONE` >>
  simp[supported_storage_dynamic_array_def, supported_lookup_other_module]
QED

Theorem supported_effect_foreign_frame:
  (!tops e. supported_effect_expr tops e ==>
    supported_program tops /\ get_module_code cx NONE = SOME tops ==>
    foreign_frame_expr cx e) /\
  (!tops e. supported_effect_place_expr tops e ==>
    supported_program tops /\ get_module_code cx NONE = SOME tops ==>
    foreign_frame_expr cx e)
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  rw[supported_effect_expr_def] >>
  gvs[foreign_frame_expr_def, foreign_frame_exprs_def,
      supported_expr_exists_def, int_calls_expr_def, listTheory.EVERY_APPEND,
      foreign_frame_bad_def, foreign_frame_bad_pop_def, expr_evm_run_root_def] >>
  metis_tac[supported_pure_foreign_frame,
            supported_function_foreign_frame_callee,
            supported_storage_dynamic_array_root_main,
            foreign_frame_expr_def, foreign_frame_exprs_def]
QED

Theorem supported_expr_foreign_frame:
  supported_expr tops e /\ supported_program tops /\
  get_module_code cx NONE = SOME tops ==> foreign_frame_expr cx e
Proof
  rw[supported_expr_def] >>
  metis_tac[supported_pure_foreign_frame, supported_effect_foreign_frame]
QED

Theorem foreign_frame_leaf_context:
  get_module_code cx NONE = get_module_code cy NONE ==>
  foreign_frame_expr cx = foreign_frame_expr cy /\
  foreign_frame_exprs cx = foreign_frame_exprs cy /\
  foreign_frame_target cx = foreign_frame_target cy /\
  foreign_frame_write_target cx = foreign_frame_write_target cy /\
  foreign_frame_iterator cx = foreign_frame_iterator cy /\
  foreign_frame_assert cx = foreign_frame_assert cy /\
  foreign_frame_raise cx = foreign_frame_raise cy
Proof
  strip_tac >>
  `(foreign_frame_callee cx : num option # string -> bool) = foreign_frame_callee cy` by
    simp[FUN_EQ_THM, foreign_frame_callee_def] >>
  `foreign_frame_bad cx = foreign_frame_bad cy` by
    simp[FUN_EQ_THM, foreign_frame_bad_def] >>
  rewrite_tac[FUN_EQ_THM, foreign_frame_expr_def, foreign_frame_exprs_def,
       foreign_frame_target_def, foreign_frame_write_target_def,
       foreign_frame_iterator_def, foreign_frame_assert_def, foreign_frame_raise_def] >>
  qpat_x_assum `foreign_frame_callee cx = _` SUBST1_TAC >>
  qpat_x_assum `foreign_frame_bad cx = _` SUBST1_TAC >> simp[]
QED

Theorem foreign_frame_assignment_context:
  (!cx at. !cy. get_module_code cx NONE = get_module_code cy NONE ==>
    foreign_frame_assignment cx at = foreign_frame_assignment cy at) /\
  (!cx ats. !cy. get_module_code cx NONE = get_module_code cy NONE ==>
    foreign_frame_assignments cx ats = foreign_frame_assignments cy ats)
Proof
  ho_match_mp_tac foreign_frame_assignment_ind >>
  rw[foreign_frame_assignment_def] >>
  metis_tac[foreign_frame_leaf_context]
QED

Theorem foreign_frame_stmt_context:
  (!cx stmt. !cy. get_module_code cx NONE = get_module_code cy NONE ==>
    foreign_frame_stmt cx stmt = foreign_frame_stmt cy stmt) /\
  (!cx stmts. !cy. get_module_code cx NONE = get_module_code cy NONE ==>
    foreign_frame_stmts cx stmts = foreign_frame_stmts cy stmts)
Proof
  ho_match_mp_tac foreign_frame_stmt_ind >>
  rw[foreign_frame_stmt_def] >>
  drule foreign_frame_leaf_context >> strip_tac >> gvs[]
  >~ [`supported_opt_exists _ opt`]
  >- (Cases_on `opt` >>
      gvs[supported_expr_exists_def, int_calls_expr_def,
          GSYM foreign_frame_expr_def])
  >~ [`foreign_frame_assignment cx at`]
  >- (drule (CONJUNCT1 foreign_frame_assignment_context) >>
      disch_then (qspec_then `at` mp_tac) >> simp[]) >>
  metis_tac[]
QED

Theorem supported_target_info_foreign_frame:
  !bt tops bindings.
    IS_SOME (supported_target_info tops bindings bt) /\
    supported_program tops /\ get_module_code cx NONE = SOME tops ==>
    foreign_frame_write_target cx bt
Proof
  measureInduct_on `base_assignment_target_size bt` >>
  rpt gen_tac >> strip_tac >>
  `target_root_main bt` by metis_tac[supported_target_root_main] >>
  simp[foreign_frame_write_target_def] >>
  Cases_on `bt` >> gvs[supported_target_info_def, foreign_frame_target_eqs,
                      optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
  disch_then (qspec_then `bindings` mp_tac) >>
  simp[foreign_frame_write_target_def] >>
  metis_tac[supported_expr_foreign_frame]
QED

Theorem supported_target_foreign_frame:
  supported_target tops bindings bt /\ supported_program tops /\
  get_module_code cx NONE = SOME tops ==> foreign_frame_write_target cx bt
Proof
  strip_tac >>
  `target_root_main bt` by metis_tac[supported_target_root_main] >>
  simp[foreign_frame_write_target_def] >>
  Cases_on `bt` >> gvs[supported_target_def, foreign_frame_target_eqs]
  >~ [`foreign_frame_target cx bt'`]
  >- (Cases_on `bt'` >> gvs[] >>
      metis_tac[supported_expr_foreign_frame, foreign_frame_target_eqs]) >>
  Cases_on `b` >> gvs[] >>
  metis_tac[supported_expr_foreign_frame, foreign_frame_target_eqs]
QED

Theorem foreign_frame_assignments_every:
  foreign_frame_assignments cx ats <=> EVERY (foreign_frame_assignment cx) ats
Proof
  Induct_on `ats` >> simp[foreign_frame_assignment_def]
QED

Theorem supported_assignment_foreign_frame:
  supported_assignment tops bindings at e /\ supported_program tops /\
  get_module_code cx NONE = SOME tops ==>
  foreign_frame_assignment cx at /\ foreign_frame_expr cx e
Proof
  simp[supported_assignment_def] >> strip_tac >>
  `foreign_frame_expr cx e` by (irule supported_expr_foreign_frame >>
                               goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> Cases_on `at` >>
  gvs[foreign_frame_assignment_def, foreign_frame_assignments_every]
  >>~- ([`foreign_frame_write_target cx bt`],
      Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
      metis_tac[supported_target_foreign_frame, supported_target_info_foreign_frame,
                optionTheory.IS_SOME_EXISTS]) >>
  irule listTheory.EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
  Cases >> simp[foreign_frame_assignment_def] >>
  metis_tac[supported_target_foreign_frame]
QED

Theorem supported_reason_foreign_frame:
  (!e. supported_string_reason tops e ==> foreign_frame_expr cx e) /\
  (supported_assert_reason tops ar ==> foreign_frame_assert cx ar) /\
  (supported_raise_reason tops rr ==> foreign_frame_raise cx rr)
Proof
  conj_asm1_tac
  >- (Cases_on `e` >> simp[supported_string_reason_def]
      >~ [`Literal ty lit`]
      >- (simp[foreign_frame_expr_def, supported_expr_exists_def,
               int_calls_expr_def, foreign_frame_bad_def,
               foreign_frame_bad_pop_def, expr_evm_run_root_def]) >>
      strip_tac >> irule (CONJUNCT1 supported_pure_foreign_frame) >>
      goal_assum (drule_at Any)) >>
  conj_tac
  >- (Cases_on `ar` >> simp[supported_assert_reason_def] >> metis_tac[]) >>
  Cases_on `rr` >> simp[supported_raise_reason_def] >> metis_tac[]
QED

Theorem foreign_frame_literal[simp]:
  foreign_frame_expr cx (Literal ty lit)
Proof
  simp[foreign_frame_expr_def, supported_expr_exists_def, int_calls_expr_def,
       foreign_frame_bad_def, foreign_frame_bad_pop_def, expr_evm_run_root_def]
QED

Theorem supported_iterator_foreign_frame:
  supported_iterator tops ty it n ==> foreign_frame_iterator cx it
Proof
  Cases_on `it`
  >- (rename1 `Array arr` >> Cases_on `arr` >>
      simp[supported_iterator_def, foreign_frame_expr_def,
           supported_expr_exists_def, int_calls_expr_def,
           foreign_frame_bad_def, foreign_frame_bad_pop_def, expr_evm_run_root_def]) >>
  rename1 `Range lo hi` >> Cases_on `lo` >>
  simp[supported_iterator_def]
  >~ [`Literal ty lit`]
  >- (Cases_on `lit` >> Cases_on `hi` >>
      simp[supported_iterator_def] >>
      metis_tac[supported_pure_foreign_frame, foreign_frame_literal]) >>
  metis_tac[supported_pure_foreign_frame]
QED

Theorem supported_aug_foreign_frame:
  supported_aug_target tops bindings bt /\ supported_program tops /\
  get_module_code cx NONE = SOME tops ==> foreign_frame_write_target cx bt
Proof
  strip_tac >> irule supported_target_info_foreign_frame >>
  goal_assum (drule_at Any) >> qexists `bindings` >> simp[] >>
  qpat_x_assum `supported_aug_target _ _ _` mp_tac >>
  Cases_on `supported_target_info tops bindings bt` >>
  simp[supported_aug_target_def]
QED

Theorem supported_append_foreign_frame:
  supported_append_target tops bt ==> foreign_frame_write_target cx bt
Proof
  Cases_on `bt` >> simp[supported_append_target_def] >> strip_tac >>
  simp[foreign_frame_write_target_def] >>
  irule supported_storage_dynamic_array_root_main >>
  goal_assum (drule_at Any)
QED

Theorem supported_stmt_foreign_frame:
  (!tops bindings stmt. supported_stmt tops bindings stmt ==>
    supported_program tops /\ get_module_code cx NONE = SOME tops ==>
    foreign_frame_stmt cx stmt) /\
  (!tops bindings stmts. supported_stmts tops bindings stmts ==>
    supported_program tops /\ get_module_code cx NONE = SOME tops ==>
    foreign_frame_stmts cx stmts)
Proof
  ho_match_mp_tac supported_stmt_ind >>
  rw[supported_stmt_def, foreign_frame_stmt_def]
  >~ [`supported_assignment tops bindings at e`]
  >- metis_tac[supported_assignment_foreign_frame]
  >>~- ([`foreign_frame_write_target cx bt`],
      metis_tac[supported_target_foreign_frame, supported_aug_foreign_frame,
                supported_append_foreign_frame])
  >>~- ([`foreign_frame_expr cx e`],
      metis_tac[supported_expr_foreign_frame, supported_pure_foreign_frame,
                supported_assignment_foreign_frame])
  >>~- ([`supported_opt_exists _ opt`],
      Cases_on `opt` >>
      gvs[supported_expr_exists_def, int_calls_expr_def,
          GSYM foreign_frame_expr_def] >>
      metis_tac[supported_expr_foreign_frame])
  >>~- ([`foreign_frame_assert cx ar`], metis_tac[supported_reason_foreign_frame])
  >>~- ([`foreign_frame_raise cx rr`], metis_tac[supported_reason_foreign_frame])
  >>~- ([`foreign_frame_iterator cx it`], metis_tac[supported_iterator_foreign_frame]) >>
  gvs[supported_log_def] >> metis_tac[supported_pure_foreign_frame]
QED

Theorem supported_callable_foreign_frame:
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  lookup_callable_function deploy name tops = SOME (mut,nr,args,defaults,ret,stmts) ==>
  defaults = [] /\ foreign_frame_stmts cx stmts
Proof
  strip_tac >> drule_all supported_callable_body_contract >> strip_tac >>
  simp[] >> irule (CONJUNCT2 supported_stmt_foreign_frame) >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Equality of the complete source map, at an arbitrary contract address. *)
Definition foreign_immutable_frame_def:
  foreign_immutable_frame md addr (s:evaluation_state) (t:evaluation_state) <=>
    (case ALOOKUP t.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms) =
    (case ALOOKUP s.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms)
End

Theorem foreign_immutable_frame_refl[simp]:
  foreign_immutable_frame md addr s s
Proof
  simp[foreign_immutable_frame_def]
QED

Theorem foreign_immutable_frame_trans:
  foreign_immutable_frame md addr s t /\ foreign_immutable_frame md addr t u ==>
  foreign_immutable_frame md addr s u
Proof
  simp[foreign_immutable_frame_def]
QED

Theorem foreign_immutable_frame_eq:
  t.immutables = s.immutables ==> foreign_immutable_frame md addr s t
Proof
  simp[foreign_immutable_frame_def]
QED

Theorem foreign_immutable_frame_bind:
  state_rel_frame (foreign_immutable_frame md addr) f /\
  (!s v t. f s = (INL v,t) ==>
    state_rel_frame (foreign_immutable_frame md addr) (g v)) ==>
  state_rel_frame (foreign_immutable_frame md addr) (bind f g)
Proof
  strip_tac >> irule state_rel_frame_bind_guarded >> simp[] >>
  metis_tac[foreign_immutable_frame_trans]
QED

Theorem foreign_immutable_frame_state:
  (!s res t. f s = (res,t) ==> t = s) ==>
  state_rel_frame (foreign_immutable_frame md addr) f
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem foreign_immutable_frame_eq_op:
  (!s res t. f s = (res,t) ==> t.immutables = s.immutables) ==>
  state_rel_frame (foreign_immutable_frame md addr) f
Proof
  simp[state_rel_frame_result] >> metis_tac[foreign_immutable_frame_eq]
QED

Theorem write_place_foreign_frame:
  (!src name path. p = ImmutablePlace src name path ==> src <> md) ==>
  state_rel_frame (foreign_immutable_frame md addr) (write_place cx p v)
Proof
  Cases_on `p` >> strip_tac >> simp[state_rel_frame_result]
  >- (rpt strip_tac >> irule foreign_immutable_frame_eq >>
      drule vyperPlaceFramesTheory.write_storage_place_immutables >> simp[])
  >- (rpt strip_tac >> irule foreign_immutable_frame_eq >>
      drule vyperPlaceFramesTheory.write_memory_place_immutables >> simp[]) >>
  rpt strip_tac >> simp[foreign_immutable_frame_def] >>
  irule write_place_other_module >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem append_place_foreign_frame:
  (!src name path. p = ImmutablePlace src name path ==> src <> md) ==>
  state_rel_frame (foreign_immutable_frame md addr) (append_place cx p v)
Proof
  Cases_on `p`
  >- (strip_tac >> irule foreign_immutable_frame_eq_op >>
      metis_tac[vyperScopePreservationTheory.append_storage_place_scopes_immutables]) >>
  strip_tac >> simp[state_rel_frame_result, append_place_def, bind_def,
    lift_sum_def, return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac vyperStateTheory.place_type_value_state >>
  imp_res_tac vyperStateTheory.read_place_state >> gvs[] >>
  gvs[GSYM lift_sum_def] >>
  imp_res_tac vyperStatePreservationTheory.lift_sum_state >> gvs[]
  >~ [`write_place cx (MemoryPlace _ _) _ _ = _`]
  >- (irule foreign_immutable_frame_eq >>
      drule write_memory_place_immutables >> simp[]) >>
  simp[foreign_immutable_frame_def] >>
  irule write_place_other_module >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem foreign_immutable_frame_reads:
  state_rel_frame (foreign_immutable_frame md addr) (read_result cx tv) /\
  state_rel_frame (foreign_immutable_frame md addr) (read_results cx results) /\
  state_rel_frame (foreign_immutable_frame md addr) (select_result cx ann tv sb) /\
  state_rel_frame (foreign_immutable_frame md addr) (conditional_result cx tv) /\
  state_rel_frame (foreign_immutable_frame md addr) (lookup_global cx src id) /\
  state_rel_frame (foreign_immutable_frame md addr) (lookup_flag_mem cx nsid mid) /\
  state_rel_frame (foreign_immutable_frame md addr) (read_storage_slot cx b slot ty) /\
  state_rel_frame (foreign_immutable_frame md addr) (result_array_length cx tv) /\
  state_rel_frame (foreign_immutable_frame md addr) (lift_sum z) /\
  state_rel_frame (foreign_immutable_frame md addr) (get_immutables cx src) /\
  state_rel_frame (foreign_immutable_frame md addr) (get_place pv) /\
  state_rel_frame (foreign_immutable_frame md addr) (read_place cx p) /\
  state_rel_frame (foreign_immutable_frame md addr) (place_type_value cx p) /\
  state_rel_frame (foreign_immutable_frame md addr) (extend_place cx pv sb) /\
  state_rel_frame (foreign_immutable_frame md addr) (resolve_array_element cx b slot ty subs)
Proof
  rpt conj_tac >> irule foreign_immutable_frame_state >> rpt strip_tac
  >~ [`read_result _ _ _ = _`] >- (drule vyperStateTheory.read_result_state >> simp[])
  >~ [`read_results _ _ _ = _`] >- (drule vyperStateTheory.read_results_state >> simp[])
  >~ [`select_result _ _ _ _ _ = _`] >- (drule vyperPlaceFramesTheory.select_result_state >> simp[])
  >~ [`conditional_result _ _ _ = _`] >- (drule vyperStatePreservationTheory.conditional_result_state >> simp[])
  >~ [`lookup_global _ _ _ _ = _`] >- (drule vyperStatePreservationTheory.lookup_global_state >> simp[])
  >~ [`lookup_flag_mem _ _ _ _ = _`] >- (drule vyperStatePreservationTheory.lookup_flag_mem_state >> simp[])
  >~ [`read_storage_slot _ _ _ _ _ = _`] >- (drule vyperStatePreservationTheory.read_storage_slot_state >> simp[])
  >~ [`result_array_length _ _ _ = _`] >- (drule vyperStatePreservationTheory.result_array_length_state >> simp[])
  >~ [`lift_sum _ _ = _`] >- (drule vyperStatePreservationTheory.lift_sum_state >> simp[])
  >~ [`get_immutables _ _ _ = _`] >- (drule vyperStatePreservationTheory.get_immutables_state >> simp[])
  >~ [`get_place _ _ = _`] >- (drule vyperPlaceFramesTheory.get_place_state >> simp[])
  >~ [`read_place _ _ _ = _`] >- (drule vyperStateTheory.read_place_state >> simp[])
  >~ [`place_type_value _ _ _ = _`] >- (drule vyperStateTheory.place_type_value_state >> simp[])
  >~ [`extend_place _ _ _ _ = _`] >- (drule vyperPlaceFramesTheory.extend_place_state >> simp[]) >>
  drule vyperStatePreservationTheory.resolve_array_element_state >> simp[]
QED


Theorem foreign_immutable_frame_primitives:
  state_rel_frame (foreign_immutable_frame md addr) get_scopes /\
  state_rel_frame (foreign_immutable_frame md addr) (set_scopes scs) /\
  state_rel_frame (foreign_immutable_frame md addr) push_scope /\
  state_rel_frame (foreign_immutable_frame md addr) pop_scope /\
  state_rel_frame (foreign_immutable_frame md addr) (push_scope_with_var nm ty v) /\
  state_rel_frame (foreign_immutable_frame md addr) (new_variable id ty v) /\
  state_rel_frame (foreign_immutable_frame md addr) (append_logs ls) /\
  state_rel_frame (foreign_immutable_frame md addr) (push_log lg) /\
  state_rel_frame (foreign_immutable_frame md addr) (get_pending_deletions) /\
  state_rel_frame (foreign_immutable_frame md addr) (update_pending_deletions fp) /\
  state_rel_frame (foreign_immutable_frame md addr) (push_function fn sc cx) /\
  state_rel_frame (foreign_immutable_frame md addr) (pop_function scs)
Proof
  rpt conj_tac >> irule foreign_immutable_frame_eq_op >>
  simp[get_scopes_def, set_scopes_def, push_scope_def, pop_scope_def,
    push_scope_with_var_def, new_variable_def, append_logs_def, push_log_def,
    get_pending_deletions_def, update_pending_deletions_def,
    push_function_def, pop_function_def, bind_def, ignore_bind_def,
    return_def, raise_def, lift_option_type_def, type_check_def,
    assert_def, check_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `s.scopes` >> gvs[set_scopes_def, return_def, raise_def]
QED

Theorem pop_place_foreign_frame:
  (!src name path. p = ImmutablePlace src name path ==> src <> md) ==>
  state_rel_frame (foreign_immutable_frame md addr) (pop_place cx p)
Proof
  Cases_on `p`
  >- (strip_tac >> irule foreign_immutable_frame_eq_op >>
      metis_tac[vyperScopePreservationTheory.pop_storage_place_scopes_immutables])
  >- (rename1 `MemoryPlace id path` >> strip_tac >>
      irule foreign_immutable_frame_eq_op >> rpt strip_tac >>
      rename1 `pop_place cx (MemoryPlace id path) st = (res,st')` >>
      `machine_frame st st'` by
        (metis_tac[SRULE [state_rel_frame_result] machine_frame_pop_memory_place]) >>
      gvs[machine_frame_def]) >>
  strip_tac >> simp[state_rel_frame_result, foreign_immutable_frame_def] >>
  rpt strip_tac >> irule pop_place_other_module >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem foreign_frame_exprs_every:
  foreign_frame_exprs cx es <=> EVERY (foreign_frame_expr cx) es
Proof
  Induct_on `es` >> simp[]
QED

Theorem foreign_frame_custom_error_args:
  foreign_frame_exprs cx (custom_error_exprs err) /\
  order_custom_error_args params err = SOME es ==> foreign_frame_exprs cx es
Proof
  strip_tac >> drule order_custom_error_args_perm >>
  gvs[foreign_frame_exprs_every] >>
  metis_tac[sortingTheory.PERM_EVERY]
QED

Theorem foreign_immutable_frame_locks:
  state_rel_frame (foreign_immutable_frame md addr) (lock_if_nr cx nr view) /\
  state_rel_frame (foreign_immutable_frame md addr) (unlock_if_nr cx nr view)
Proof
  Cases_on `nr` >> Cases_on `view` >>
  Cases_on `cx.nonreentrant_slot` >>
  simp[lock_if_nr_def, unlock_if_nr_def] >> rpt conj_tac >>
  irule foreign_immutable_frame_eq_op >> rpt strip_tac >>
  gvs[return_def, raise_def] >>
  metis_tac[vyperStatePreservationTheory.acquire_nonreentrant_lock_immutables,
    vyperStatePreservationTheory.release_nonreentrant_lock_immutables]
QED

Theorem foreign_immutable_frame_empty_defaults:
  state_rel_frame (foreign_immutable_frame md addr)
    (finally (do set_scopes [FEMPTY]; eval_exprs cx [] od) (set_scopes prev))
Proof
  irule state_rel_frame_finally >>
  conj_tac >- metis_tac[foreign_immutable_frame_trans] >>
  simp[foreign_immutable_frame_primitives] >>
  rewrite_tac[ignore_bind_def] >> irule foreign_immutable_frame_bind >>
  simp[foreign_immutable_frame_primitives] >> rpt strip_tac >>
  simp[Once evaluate_def, state_rel_frame_def, return_def]
QED

Theorem foreign_immutable_frame_function_tail:
  !body. state_rel_frame (foreign_immutable_frame md addr) (eval_stmts cxf body) ==>
  state_rel_frame (foreign_immutable_frame md addr)
    (finally (try (do eval_stmts cxf body; return NoneV od) handle_function)
      (do pop_function prev; unlock_if_nr cx nr view od))
Proof
  rpt strip_tac >> irule state_rel_frame_finally >>
  conj_tac >- metis_tac[foreign_immutable_frame_trans] >>
  conj_tac
  >- (irule state_rel_frame_try >>
      conj_tac >- metis_tac[foreign_immutable_frame_trans] >>
      conj_tac
      >- (gen_tac >> Cases_on `e` >>
          simp[handle_function_def, state_rel_frame_def, return_def, raise_def]) >>
      rewrite_tac[ignore_bind_def] >>
      irule foreign_immutable_frame_bind >> simp[] >> rpt strip_tac >>
      simp[state_rel_frame_def, return_def]) >>
  rewrite_tac[ignore_bind_def] >> irule foreign_immutable_frame_bind >>
  simp[foreign_immutable_frame_primitives] >> rpt strip_tac >>
  rewrite_tac[GSYM unlock_if_nr_def] >>
  metis_tac[foreign_immutable_frame_locks]
QED

Theorem foreign_frame_stmts_push_function:
  !stmts. foreign_frame_stmts cx stmts /\
    push_function fn sc cx s = (INL cxf,t) ==>
    foreign_frame_stmts cxf stmts
Proof
  rpt strip_tac >> gvs[push_function_def, return_def] >>
  qspecl_then [`cx`, `stmts`, `cx with stk updated_by CONS fn`] mp_tac
    (CONJUNCT2 foreign_frame_stmt_context) >>
  simp[vyperContextTheory.get_module_code_def]
QED

Theorem eval_bind_return[local]:
  bind (return v) k = k v
Proof
  simp[FUN_EQ_THM, bind_def, return_def]
QED

Theorem eval_bind_assert_true[local]:
  bind (assert T e) k = k ()
Proof
  simp[FUN_EQ_THM, bind_def, assert_def]
QED

Theorem eval_foreign_immutable_frame_mutual:
  (!cx stmt s res t md addr.
    md <> NONE /\ foreign_frame_stmt cx stmt /\ eval_stmt cx stmt s = (res,t) ==>
    foreign_immutable_frame md addr s t) /\
  (!cx stmts s res t md addr.
    md <> NONE /\ foreign_frame_stmts cx stmts /\ eval_stmts cx stmts s = (res,t) ==>
    foreign_immutable_frame md addr s t) /\
  (!cx it s res t md addr.
    md <> NONE /\ foreign_frame_iterator cx it /\ eval_iterator cx it s = (res,t) ==>
    foreign_immutable_frame md addr s t) /\
  (!cx tyv nm body vs s res t md addr.
    md <> NONE /\ foreign_frame_stmts cx body /\ eval_for cx tyv nm body vs s = (res,t) ==>
    foreign_immutable_frame md addr s t) /\
  (!cx e s res t md addr.
    md <> NONE /\ foreign_frame_expr cx e /\ eval_expr cx e s = (res,t) ==>
    foreign_immutable_frame md addr s t) /\
  (!cx es s res t md addr.
    md <> NONE /\ foreign_frame_exprs cx es /\ eval_exprs cx es s = (res,t) ==>
    foreign_immutable_frame md addr s t) /\
  (!cx bt s res t md addr.
    md <> NONE /\ foreign_frame_target cx bt /\ eval_base_place cx bt s = (res,t) ==>
    foreign_immutable_frame md addr s t) /\
  (!cx bt s res t md addr.
    md <> NONE /\ foreign_frame_target cx bt /\ eval_target_place cx bt s = (res,t) ==>
    foreign_immutable_frame md addr s t) /\
  (!cx at v s res t md addr.
    md <> NONE /\ foreign_frame_assignment cx at /\ assign_tuple_targets cx at v s = (res,t) ==>
    foreign_immutable_frame md addr s t) /\
  (!cx ats vs s res t md addr.
    md <> NONE /\ EVERY (foreign_frame_assignment cx) ats /\ assign_tuple_target_list cx ats vs s = (res,t) ==>
    foreign_immutable_frame md addr s t) /\
  (!cx es s res t md addr.
    md <> NONE /\ foreign_frame_exprs cx es /\ eval_expr_results cx es s = (res,t) ==>
    foreign_immutable_frame md addr s t)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`eval_stmt cx Pass`]
  >- (simp[Once evaluate_def, return_def] >> rpt strip_tac >> gvs[])
  >~ [`eval_stmt cx Break`]
  >- (simp[Once evaluate_def, raise_def] >> rpt strip_tac >> gvs[])
  >~ [`eval_stmt cx Continue`]
  >- (simp[Once evaluate_def, raise_def] >> rpt strip_tac >> gvs[])
  >~ [`eval_stmts cx []`]
  >- (simp[Once evaluate_def, return_def] >> rpt strip_tac >> gvs[])
  >~ [`eval_exprs cx []`]
  >- (simp[Once evaluate_def, return_def] >> rpt strip_tac >> gvs[])
  >~ [`eval_expr_results cx []`]
  >- (simp[Once evaluate_def, return_def] >> rpt strip_tac >> gvs[]) >>
  all_tac
  >~ [`eval_stmt cx (Return NONE)`]
  >- (simp[Once evaluate_def, raise_def] >> rpt strip_tac >> gvs[])
  >~ [`eval_expr cx (Literal ty lit)`]
  >- (simp[Once evaluate_def, return_def] >> rpt strip_tac >> gvs[]) >>
  all_tac
  >~ [`eval_stmt cx (Return (SOME e))`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def, Once evaluate_def,
        bind_def, raise_def, AllCaseEqs()] >>
      imp_res_tac read_result_state >> gvs[] >> metis_tac[]) >>
  all_tac
  >~ [`eval_stmt cx (Raise RaiseBare)`]
  >- (simp[Once evaluate_def, raise_def] >> rpt strip_tac >> gvs[])
  >~ [`eval_stmt cx (Raise RaiseUnreachable)`]
  >- (simp[Once evaluate_def, raise_def] >> rpt strip_tac >> gvs[])
  >~ [`eval_expr cx (Name ty id)`]
  >- (simp[Once evaluate_def, get_scopes_def, bind_def, ignore_bind_def,
        type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >~ [`eval_expr cx (TopLevelName ty src_name)`]
  >- (PairCases_on `src_name` >> rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac vyperStatePreservationTheory.lookup_global_state >> gvs[])
  >~ [`eval_expr cx (FlagMember ty nsid mid)`]
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac vyperStatePreservationTheory.lookup_flag_mem_state >> gvs[]) >>
  (* Statement results. *)
  all_tac
  >~ [`eval_stmt cx (Raise (RaiseReason e))`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def, Once evaluate_def,
        bind_def, raise_def, lift_option_type_def, AllCaseEqs()] >>
      imp_res_tac read_result_state >> gvs[GSYM lift_option_type_def] >>
      imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
      gvs[] >> metis_tac[])
  >~ [`eval_stmt cx (Expr e)`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def, Once evaluate_def,
        bind_def, type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      metis_tac[])
  >~ [`eval_stmts cx (stmt::stmts)`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def, Once evaluate_def,
        ignore_bind_def, bind_def, AllCaseEqs()] >>
      metis_tac[foreign_immutable_frame_trans])
  >~ [`eval_exprs cx (e::es)`]
  >- (rpt strip_tac >> gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
      imp_res_tac read_result_state >> gvs[] >>
      metis_tac[foreign_immutable_frame_trans])
  >~ [`eval_expr_results cx (e::es)`]
  >- (rpt strip_tac >> gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
      metis_tac[foreign_immutable_frame_trans]) >>
  all_tac
  >~ [`eval_stmt cx (Raise (RaiseCustomError err))`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def] >>
      Cases_on `err` >> gvs[Once evaluate_def, bind_def, raise_def,
        lift_option_def, option_CASE_rator, AllCaseEqs()] >>
      imp_res_tac foreign_frame_custom_error_args >>
      gvs[GSYM lift_option_def] >>
      imp_res_tac vyperStatePreservationTheory.lift_option_state >> gvs[return_def] >>
      metis_tac[]) >>
  (* Assertions and declarations. *)
  all_tac
  >~ [`eval_stmt cx (Assert e AssertBare)`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def, Once evaluate_def,
        switch_BoolV_def, bind_def, return_def, raise_def, COND_RATOR, AllCaseEqs()] >>
      imp_res_tac read_result_state >> gvs[] >> metis_tac[])
  >~ [`eval_stmt cx (Assert e AssertUnreachable)`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def, Once evaluate_def,
        switch_BoolV_def, bind_def, return_def, raise_def, COND_RATOR, AllCaseEqs()] >>
      imp_res_tac read_result_state >> gvs[] >> metis_tac[]) >>
  all_tac
  >~ [`eval_stmt cx (Assert e (AssertReason reason))`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def, Once evaluate_def,
        switch_BoolV_def, bind_def, raise_def, return_def, lift_option_type_def,
        option_CASE_rator, COND_RATOR, AllCaseEqs()] >>
      imp_res_tac read_result_state >> gvs[] >>
      metis_tac[foreign_immutable_frame_trans]) >>
  all_tac
  >~ [`eval_stmt cx (Assert e (AssertCustomError err))`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def] >> Cases_on `err` >>
      gvs[Once evaluate_def, switch_BoolV_def, bind_def, raise_def, return_def,
        lift_option_def, option_CASE_rator, COND_RATOR, AllCaseEqs()] >>
      imp_res_tac foreign_frame_custom_error_args >>
      imp_res_tac read_result_state >> gvs[return_def] >>
      metis_tac[foreign_immutable_frame_trans]) >>
  all_tac
  >~ [`eval_stmt cx (Log id es)`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def, Once evaluate_def, bind_def,
        lift_option_def, option_CASE_rator, push_log_def, append_logs_def,
        return_def, raise_def, AllCaseEqs()] >>
      gvs[foreign_immutable_frame_def] >> metis_tac[]) >>
  all_tac
  >~ [`eval_stmt cx (AnnAssign id typ e)`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def, Once evaluate_def,
        bind_def, AllCaseEqs()] >>
      imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
      imp_res_tac read_result_state >> gvs[] >>
      imp_res_tac (SRULE [state_rel_frame_result] (cj 6 foreign_immutable_frame_primitives)) >>
      qpat_x_assum `!st tyv t. _ ==> _` (drule_then assume_tac) >>
      gvs[foreign_immutable_frame_def] >> metis_tac[]) >>
  (* Append and assignment. *)
  all_tac
  >~ [`eval_stmt cx (Append bt e)`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def, foreign_frame_write_target_def] >>
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >> gvs[] >>
      qpat_x_assum `!st p t. _ ==> _` (drule_then assume_tac) >>
      `!src name path. p = ImmutablePlace src name path ==> src <> md` by
        (rpt strip_tac >> gvs[] >>
         drule_all main_root_target_place_immutable_module >> simp[]) >>
      qpat_x_assum `!st res t md addr. _ /\ eval_target_place _ _ _ = _ ==> _`
        (drule_all_then assume_tac) >>
      qpat_x_assum `!st res t md addr. _ /\ eval_expr _ _ _ = _ ==> _`
        (drule_all_then assume_tac) >>
      drule append_place_foreign_frame >>
      simp[state_rel_frame_result] >> strip_tac >>
      gvs[foreign_immutable_frame_def] >> metis_tac[]) >>
  all_tac
  >~ [`eval_stmt cx (Assign (BaseTarget bt) e)`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def, foreign_frame_assignment_def,
        foreign_frame_write_target_def] >>
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >> gvs[] >>
      qpat_x_assum `!st pv t. _ ==> _` (drule_then assume_tac)
      >~ [`write_place cx p v u = (res,t)`]
      >- (`!src name path. p = ImmutablePlace src name path ==> src <> md` by
        (rpt strip_tac >> gvs[] >>
         drule_all main_root_target_place_immutable_module >> simp[]) >>
      qpat_x_assum `!st res t md addr. _ /\ eval_target_place _ _ _ = _ ==> _`
        (drule_all_then assume_tac) >>
      qpat_x_assum `!st res t md addr. _ /\ eval_expr _ _ _ = _ ==> _`
        (drule_all_then assume_tac) >>
      drule write_place_foreign_frame >>
      simp[state_rel_frame_result] >> strip_tac >>
      gvs[foreign_immutable_frame_def] >> metis_tac[]) >>
      metis_tac[foreign_immutable_frame_trans]) >>
  (* Tuple and augmented assignment. *)
  all_tac
  >~ [`eval_stmt cx (Assign (TupleTarget gs) e)`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def] >>
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >> gvs[] >>
      qpat_x_assum `!st tv t st' v t'. _ ==> _` (drule_all_then assume_tac) >>
      metis_tac[foreign_immutable_frame_trans]) >>
  all_tac
  >~ [`eval_stmt cx (AugAssign ty bt bop e)`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def, foreign_frame_write_target_def] >>
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >> imp_res_tac read_place_state >>
      imp_res_tac place_type_value_state >>
      imp_res_tac vyperStatePreservationTheory.lift_sum_state >> gvs[] >>
      qpat_x_assum `!st p t st' cur t' st'' ptv t''. _ ==> _`
        (drule_all_then assume_tac)
      >~ [`write_place cx p v u = (res,t)`]
      >- (`!src name path. p = ImmutablePlace src name path ==> src <> md` by
            (rpt strip_tac >> gvs[] >>
             drule_all main_root_target_place_immutable_module >> simp[]) >>
          qpat_x_assum `!st res t md addr. _ /\ eval_target_place _ _ _ = _ ==> _`
            (drule_all_then assume_tac) >>
          drule write_place_foreign_frame >>
          simp[state_rel_frame_result] >> strip_tac >>
          gvs[foreign_immutable_frame_def] >> metis_tac[]) >>
      metis_tac[foreign_immutable_frame_trans]) >>
  (* Conditionals and for loops. *)
  all_tac
  >~ [`eval_stmt cx (If e ss1 ss2)`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def] >>
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      gvs[ignore_bind_def, bind_def, finally_def, switch_BoolV_def,
        return_def, raise_def, COND_RATOR, AllCaseEqs()] >>
      imp_res_tac read_result_state >> gvs[] >>
      imp_res_tac (SRULE [state_rel_frame_result] (cj 3 foreign_immutable_frame_primitives)) >>
      imp_res_tac (SRULE [state_rel_frame_result] (cj 4 foreign_immutable_frame_primitives)) >>
      gvs[push_scope_def, set_scopes_def, return_def]
      >>~- ([`eval_expr cx e s = (INL tv,u)`],
            ntac 2 (qpat_x_assum `!st tv t. _ ==> _` (drule_then assume_tac)) >>
            qpat_x_assum `!st res t md addr. _ /\ eval_expr _ _ _ = _ ==> _`
              (drule_all_then assume_tac)
            >>~- ([`eval_stmts cx ss u = (r,t)`],
                  first_x_assum (drule_all_then assume_tac) >>
                  gvs[foreign_immutable_frame_def] >> metis_tac[]) >>
            gvs[foreign_immutable_frame_def] >> metis_tac[]) >>
      gvs[foreign_immutable_frame_def] >> metis_tac[]) >>
  all_tac
  >~ [`eval_stmt cx (For nm typ it n stmts)`]
  >- (rpt strip_tac >> gvs[foreign_frame_stmt_def] >>
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
      gvs[check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      gvs[ignore_bind_def, bind_def, assert_def, return_def, raise_def,
        COND_RATOR, AllCaseEqs()] >>
      qpat_x_assum `!st tyv t. _ ==> _` (drule_then assume_tac)
      >>~- ([`eval_for cx tyv nm stmts vs u = (res,t)`],
            qpat_x_assum `!st tyv t st' vs t'. _ ==> _` (drule_all_then assume_tac) >>
            metis_tac[foreign_immutable_frame_trans]) >>
      metis_tac[]) >>
  (* Iterators and remaining cases. *)
  all_tac
  >~ [`eval_iterator cx (Array e)`]
  >- (rpt strip_tac >> gvs[foreign_frame_iterator_def] >>
      qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >>
      imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
      gvs[] >> metis_tac[])
  >~ [`eval_iterator cx (Range e1 e2)`]
  >- (rpt strip_tac >> gvs[foreign_frame_iterator_def] >>
      qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >>
      imp_res_tac vyperStatePreservationTheory.lift_sum_state >> gvs[] >>
      qpat_x_assum `!st tv t st' v t'. _ ==> _` (drule_all_then assume_tac) >>
      metis_tac[foreign_immutable_frame_trans]) >>
  all_tac
  >~ [`eval_for cx tyv nm stmts [] s`]
  >- (simp[Once evaluate_def, return_def] >> rpt strip_tac >> gvs[]) >>
  all_tac
  >~ [`eval_target_place cx bt`, `eval_base_place cx bt`]
  >- (rpt strip_tac >>
      qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac vyperPlaceFramesTheory.get_place_state >> gvs[] >> metis_tac[]) >>
  (* Target and expression clauses. *)
  all_tac
  >~ [`eval_base_place cx (NameTarget id)`]
  >- (rpt strip_tac >> gvs[Once evaluate_def, get_scopes_def, bind_def,
        ignore_bind_def, type_check_def, assert_def, return_def, raise_def,
        COND_RATOR, AllCaseEqs()])
  >~ [`eval_base_place cx (TopLevelNameTarget src_name)`]
  >- (PairCases_on `src_name` >> rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac vyperStatePreservationTheory.lookup_global_state >> gvs[])
  >~ [`eval_base_place cx (AttributeTarget bt id)`]
  >- (rpt strip_tac >> gvs[foreign_frame_target_def] >>
      qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac vyperPlaceFramesTheory.extend_place_state >> gvs[] >> metis_tac[])
  >~ [`eval_base_place cx (SubscriptTarget bt e)`]
  >- (rpt strip_tac >> gvs[foreign_frame_target_def] >>
      qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >>
      imp_res_tac vyperPlaceFramesTheory.extend_place_state >> gvs[] >>
      qpat_x_assum `!st pv t. _ ==> _` (drule_then assume_tac) >>
      metis_tac[foreign_immutable_frame_trans]) >>
  all_tac
  >~ [`assign_tuple_targets cx (TupleTarget ats)`]
  >- (rpt strip_tac >> gvs[foreign_frame_assignment_def, foreign_frame_assignments_every] >>
      qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, vyperValueTheory.value_CASE_rator,
        vyperValueTheory.array_value_CASE_rator,
        raise_def, AllCaseEqs()] >> strip_tac >> gvs[] >> metis_tac[])
  >~ [`assign_tuple_targets cx (BaseTarget bt)`]
  >- (rpt strip_tac >> gvs[foreign_frame_assignment_def, foreign_frame_write_target_def] >>
      qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac
      >~ [`write_place cx p v u = (res,t)`]
      >- (`!src name path. p = ImmutablePlace src name path ==> src <> md` by
            (rpt strip_tac >> gvs[] >>
             drule_all main_root_target_place_immutable_module >> simp[]) >>
          drule write_place_foreign_frame >> simp[state_rel_frame_result] >> strip_tac >>
          gvs[foreign_immutable_frame_def] >> metis_tac[]) >> metis_tac[]) >>
  (* Pop, lists and expressions. *)
  all_tac
  >~ [`eval_expr cx (Pop ty bt)`]
  >- (rpt strip_tac >> imp_res_tac (cj 6 foreign_frame_expr_children) >>
      gvs[foreign_frame_write_target_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac
      >~ [`pop_place cx p u = (res,t)`]
      >- (`!src name path. p = ImmutablePlace src name path ==> src <> md` by
            (rpt strip_tac >> gvs[] >>
             drule_all main_root_target_place_immutable_module >> simp[]) >>
          drule pop_place_foreign_frame >> simp[state_rel_frame_result] >> strip_tac >>
          gvs[foreign_immutable_frame_def] >> metis_tac[]) >> metis_tac[]) >>
  all_tac
  >~ [`eval_expr cx (Attribute ty e id)`]
  >- (rpt strip_tac >> imp_res_tac (cj 3 foreign_frame_expr_children) >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >> metis_tac[])
  >~ [`eval_expr cx (Subscript ty obj key)`]
  >- (rpt strip_tac >> imp_res_tac (cj 2 foreign_frame_expr_children) >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >>
      imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >>
      qpat_x_assum `!st res t. _ ==> _` (drule_then assume_tac) >>
      metis_tac[foreign_immutable_frame_trans]) >>
  all_tac
  >~ [`eval_expr cx (Call ty RawLog es opt)`]
  >- (rpt strip_tac >> imp_res_tac foreign_frame_call_args >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
        assert_def, lift_option_type_def, push_log_def, append_logs_def,
        return_def, raise_def, COND_RATOR, option_CASE_rator, AllCaseEqs()] >> strip_tac >>
      gvs[foreign_immutable_frame_def] >> metis_tac[])
  >~ [`eval_expr cx (Call ty RawRevert es opt)`]
  >- (rpt strip_tac >> imp_res_tac foreign_frame_call_args >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
        assert_def, return_def, raise_def, COND_RATOR, AllCaseEqs()] >>
      strip_tac >> gvs[] >> metis_tac[]) >>
  all_tac
  >~ [`eval_expr cx (Call ty SelfDestructTarget es opt)`]
  >- (rpt strip_tac >> imp_res_tac foreign_frame_call_args >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
        lift_option_type_def, option_CASE_rator, get_accounts_def,
        return_def, raise_def, COND_RATOR, AllCaseEqs()] >> strip_tac >>
      imp_res_tac vyperStatePreservationTheory.transfer_value_immutables >>
      gvs[foreign_immutable_frame_def] >> metis_tac[])
  >~ [`eval_expr cx (Call ty (RawCallTarget flags) es opt)`]
  >- (rpt strip_tac >> gvs[foreign_frame_expr_def, supported_expr_exists_def,
        foreign_frame_bad_def, expr_evm_run_root_def])
  >~ [`eval_expr cx (Call ty (RawCallCalldataTarget flags) es opt)`]
  >- (rpt strip_tac >> gvs[foreign_frame_expr_def, supported_expr_exists_def,
        foreign_frame_bad_def, expr_evm_run_root_def])
  >~ [`eval_expr cx (Call ty (Send gas) es opt)`]
  >- (rpt strip_tac >> imp_res_tac foreign_frame_call_args >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
        assert_def, return_def, raise_def, COND_RATOR, AllCaseEqs()] >>
      strip_tac >> imp_res_tac eval_send_preserves_non_accounts >>
      gvs[foreign_immutable_frame_def, type_check_def, assert_def, return_def] >>
      metis_tac[]) >>
  (* Remaining calls and lists. *)
  all_tac
  >~ [`assign_tuple_target_list cx [] []`]
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >~ [`assign_tuple_target_list cx (at::ats) (v::vs)`]
  >- (rpt strip_tac >> gvs[] >>
      qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
      strip_tac >> gvs[] >>
      metis_tac[foreign_immutable_frame_trans]) >>
  all_tac
  >~ [`eval_expr cx (StructLit ty (src,name) fields)`]
  >- (rpt strip_tac >> drule foreign_frame_structlit_fields >>
      simp[listTheory.EVERY_MAP] >> strip_tac >>
      `foreign_frame_exprs cx (MAP SND fields)` by
        (qpat_x_assum `EVERY _ fields` mp_tac >>
         qid_spec_tac `fields` >> Induct >> simp[]) >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
      strip_tac >> metis_tac[])
  >~ [`eval_expr cx (TypeBuiltin ty tb typ es)`]
  >- (rpt strip_tac >> imp_res_tac (cj 5 foreign_frame_expr_children) >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
        assert_def, lift_sum_def, return_def, raise_def, COND_RATOR,
        sum_CASE_rator, AllCaseEqs()] >> strip_tac >>
      gvs[type_check_def, assert_def, return_def] >> metis_tac[]) >>
  all_tac
  >~ [`eval_expr cx (IfExp ty c a b)`]
  >- (rpt strip_tac >> imp_res_tac (cj 1 foreign_frame_expr_children) >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, switch_BoolV_def, bind_def, return_def,
        raise_def, COND_RATOR, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >>
      imp_res_tac vyperStatePreservationTheory.conditional_result_state >>
      gvs[] >> metis_tac[foreign_immutable_frame_trans]) >>
  all_tac
  >~ [`eval_expr cx (Builtin ty bt es)`]
  >- (rpt strip_tac >> imp_res_tac (cj 4 foreign_frame_expr_children) >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
        assert_def, lift_sum_def, return_def, raise_def, get_accounts_def,
        COND_RATOR, sum_CASE_rator, AllCaseEqs()] >> strip_tac >>
      imp_res_tac vyperStatePreservationTheory.result_array_length_state >>
      imp_res_tac vyperStatePreservationTheory.next_gas_reading_state >>
      gvs[foreign_immutable_frame_def, type_check_def, assert_def, return_def]
      >>~- ([`foreign_frame_expr cx (Builtin ty Len es)`],
        `foreign_frame_expr cx (HD es)` by
          (Cases_on `es` >> gvs[vyperContextTheory.builtin_args_length_ok_def]) >>
        metis_tac[]) >> metis_tac[]) >>
  (* Loops and calls. *)
  all_tac
  >~ [`eval_expr cx (Call ty (CreateTarget kind salt rof) es opt)`]
  >- (rpt strip_tac >> gvs[foreign_frame_expr_def, supported_expr_exists_def,
        foreign_frame_bad_def, expr_evm_run_root_def])
  >~ [`assign_tuple_target_list cx (a::ats) []`]
  >- (rpt strip_tac >> gvs[Once evaluate_def, raise_def])
  >~ [`assign_tuple_target_list cx [] (v::vs)`]
  >- (rpt strip_tac >> gvs[Once evaluate_def, raise_def]) >>
  all_tac
  >~ [`eval_for cx ty nm ss (v::vs)`]
  >- (rpt strip_tac >>
      qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
      strip_tac >>
      imp_res_tac (SRULE [state_rel_frame_result] (cj 5 foreign_immutable_frame_primitives)) >>
      gvs[]
      >~ [`push_scope_with_var nm ty v s = (INL (),u)`]
      >- (first_x_assum (drule_then assume_tac) >>
          Cases_on `broke` >> gvs[COND_RATOR, return_def, ignore_bind_def]
          >>~- ([`eval_for cx ty nm ss vs u' = (res,t)`],
            first_x_assum (drule_all_then assume_tac) >>
            gvs[finally_def, try_def, bind_def, ignore_bind_def, return_def,
              handle_loop_exception_def, raise_def, COND_RATOR, AllCaseEqs()] >>
            imp_res_tac (SRULE [state_rel_frame_result] (cj 4 foreign_immutable_frame_primitives)) >>
            gvs[foreign_immutable_frame_def] >> metis_tac[]) >>
          gvs[finally_def, try_def, bind_def, ignore_bind_def, return_def,
            handle_loop_exception_def, raise_def, COND_RATOR, AllCaseEqs()] >>
          imp_res_tac (SRULE [state_rel_frame_result] (cj 4 foreign_immutable_frame_primitives)) >>
          gvs[foreign_immutable_frame_def] >> metis_tac[]) >>
      all_tac
      >~ [`push_scope_with_var nm ty v s = (INL (),u)`]
      >- (first_x_assum (drule_then assume_tac) >>
          gvs[finally_def, try_def, bind_def, ignore_bind_def, return_def,
            handle_loop_exception_def, raise_def, COND_RATOR, AllCaseEqs()] >>
          imp_res_tac (SRULE [state_rel_frame_result] (cj 4 foreign_immutable_frame_primitives)) >>
          gvs[foreign_immutable_frame_def] >> metis_tac[]) >>
      metis_tac[]) >>
  (* Internal and external calls. *)
  all_tac
  >~ [`eval_expr cx (Call ty (ExtCall static skip sig opts) es opt)`]
  >- (rpt strip_tac >> imp_res_tac foreign_frame_call_args >>
      `!n. foreign_frame_exprs cx (TAKE n es) /\
           foreign_frame_exprs cx (DROP n es)` by
        (gvs[foreign_frame_exprs_every] >>
         metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]) >>
      `!n m. foreign_frame_exprs cx (TAKE n (DROP m es))` by
        (gvs[foreign_frame_exprs_every] >>
         metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]) >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_results_state >>
      imp_res_tac eval_ext_call_preserves_non_accounts >> gvs[]
      >>~- ([`eval_expr_results cx xs u = (INL results,w)`],
        qpat_x_assum `!a b c d e f. _ ==> _` (drule_all_then assume_tac) >>
        qpat_x_assum `!a b c. _ ==> _` (drule_then assume_tac) >>
        gvs[foreign_immutable_frame_def] >> metis_tac[])
      >>~- ([`eval_expr_results cx xs u = (INR err,w)`],
        qpat_x_assum `!a b c. _ ==> _` (drule_then assume_tac) >>
        gvs[foreign_immutable_frame_def] >> metis_tac[]) >>
      metis_tac[]) >>
  (* Internal call: guarded composition of administrative frames. *)
  rpt strip_tac >> imp_res_tac foreign_frame_call_args >>
  drule foreign_frame_intcall_callee >>
  simp[foreign_frame_callee_def] >> strip_tac >>
  rule_assum_tac (SIMP_RULE (srw_ss())
    [type_check_def, assert_def, lift_option_type_def, option_CASE_rator,
     return_def, raise_def, AllCaseEqs()]) >>
  qpat_x_assum `src_id_opt = NONE` SUBST_ALL_TAC >>
  Cases_on `lookup_callable_function cx.in_deploy fn tops`
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, type_check_def, assert_def, bind_def,
        ignore_bind_def, lift_option_type_def, return_def, raise_def,
        COND_RATOR, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  rename1 `lookup_callable_function cx.in_deploy fn tops = SOME tup` >>
  PairCases_on `tup` >>
  drule_all supported_callable_foreign_frame >> strip_tac >>
  gvs[] >>
  Cases_on `MEM (NONE,fn) cx.stk`
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, type_check_def, assert_def, bind_def,
        return_def, raise_def, ignore_bind_def] >> strip_tac >>
      gvs[assert_def, ignore_bind_def, bind_def, raise_def]) >>
  reverse (Cases_on `LENGTH es = LENGTH tup2`)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, type_check_def, assert_def, bind_def,
        ignore_bind_def, lift_option_type_def, return_def, raise_def] >>
      strip_tac >> gvs[]) >>
  qpat_x_assum `_ ==> !s'' res t' md' addr. _` (mp_tac) >>
  simp[] >> disch_tac >>
  qpat_assum `eval_expr _ _ _ = _` (mp_then Any irule state_rel_frame_at) >>
  qpat_x_assum `eval_expr _ _ _ = _` kall_tac >>
  simp[Once evaluate_def, type_check_def, assert_def,
    lift_option_type_def, return_def, ignore_bind_def] >>
  simp[eval_bind_return, eval_bind_assert_true] >>
  irule foreign_immutable_frame_bind >>
  reverse conj_tac
  >- (simp[state_rel_frame_result] >> rpt strip_tac >>
      first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  rpt strip_tac >> BETA_TAC >>
  irule foreign_immutable_frame_bind >>
  reverse conj_tac >- simp[foreign_immutable_frame_primitives] >>
  rpt strip_tac >> BETA_TAC >>
  irule foreign_immutable_frame_bind >>
  reverse conj_tac
  >- (rewrite_tac[GSYM ignore_bind_def] >>
      irule foreign_immutable_frame_empty_defaults) >>
  rpt strip_tac >> BETA_TAC >>
  irule foreign_immutable_frame_bind >>
  reverse conj_tac >- simp[foreign_immutable_frame_reads] >>
  rpt strip_tac >> BETA_TAC >>
  rename1 `bind_arguments (get_tenv cx) tup2 (vs ++ dflt_vs)` >>
  Cases_on `bind_arguments (get_tenv cx) tup2 (vs ++ dflt_vs)`
  >- (irule foreign_immutable_frame_state >>
      simp[bind_def, raise_def]) >>
  simp[eval_bind_return] >>
  Cases_on `evaluate_type (get_tenv cx) tup4`
  >- (irule foreign_immutable_frame_state >>
      simp[bind_def, raise_def]) >>
  simp[eval_bind_return] >>
  irule foreign_immutable_frame_bind >>
  reverse conj_tac
  >- (rewrite_tac[GSYM lock_if_nr_def] >>
      metis_tac[foreign_immutable_frame_locks]) >>
  rpt strip_tac >> BETA_TAC >>
  irule foreign_immutable_frame_bind >>
  reverse conj_tac >- simp[foreign_immutable_frame_primitives] >>
  rpt strip_tac >> BETA_TAC >>
  rename1 `(if tup1 then _ else _) lockst = (INL lockval,lockend)` >>
  Cases_on `lockval` >>
  `LENGTH es <= LENGTH tup2 /\ LENGTH tup2 <= LENGTH es` by simp[] >>
  rule_assum_tac (REWRITE_RULE [ignore_bind_def]) >>
  qpat_x_assum `!a b c d e f g h i j. _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `!a b c d e f g h i j. _` mp_tac >>
  rpt (disch_then drule) >> strip_tac >>
  drule_all foreign_frame_stmts_push_function >> strip_tac >>
  irule foreign_immutable_frame_bind >>
  reverse conj_tac
  >- (rewrite_tac[GSYM ignore_bind_def, CONJ_ASSOC] >>
      irule (REWRITE_RULE [unlock_if_nr_def, DE_MORGAN_THM, CONJ_ASSOC]
        foreign_immutable_frame_function_tail) >>
      simp[state_rel_frame_result] >> rpt strip_tac >>
      first_x_assum irule >> simp[] >> goal_assum (drule_at Any)) >>
  rpt strip_tac >> BETA_TAC >>
  irule foreign_immutable_frame_state >>
  simp[bind_def, return_def, raise_def, option_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED
