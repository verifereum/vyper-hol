Theory exprSimForeignImmutableFrame
Ancestors
  exprSimHyps vyperTypeInitialState vyperImmutableMetadataFrame
  supportedStmts vyperState vyperInterpreter vyperMisc alist
  vyperStoragePlaceProvenance supportedTargets supportedDecls supportedExprForms
  targetPlaceSim vyperAST supportedProgram supportedExprTraverse supportedStmtTraverse
  vyperTypeCallGraph supportedExprs bodyStorageCases

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
