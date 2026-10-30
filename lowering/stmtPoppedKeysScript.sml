(*
 * Statement evaluation keeps popped_keys_indexed
 *
 * TOP-LEVEL:
 *   eval_statement_loop_popped_keys_indexed — eval_stmt, eval_stmts and
 *     eval_for keep popped_keys_indexed: the statement counterpart of
 *     exprSimHyps's eval_expr_popped_keys_indexed
 *
 * Helper:
 *   *_popped_keys_indexed — one lemma per scope write (push_scope,
 *     pop_scope, new_variable, write_place, append_place, ...) and per
 *     statement case of evaluate_ind
 *)

Theory stmtPoppedKeys
Ancestors
  list finite_map exprSimHyps vyperInterpreter vyperState
  vyperPlaceResultTyping vyperScopePreservation vyperLookup
Libs
  pairLib

Theorem scope_pop_effect_popped_keys_indexed:
  !f st res st'.
    scope_pop_effect f /\ f st = (res,st') /\
    popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> gvs[scope_pop_effect_def] >>
  first_x_assum drule >> strip_tac >>
  drule_all scope_pop_trace_keys_indexed >> simp[]
QED

Theorem eval_exprs_popped_keys_indexed:
  !cx es st res st'.
    eval_exprs cx es st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  metis_tac[scope_pop_effect_popped_keys_indexed,
            cj 6 eval_mutual_scope_pop_effect]
QED

Theorem eval_base_place_popped_keys_indexed:
  !cx e st res st'.
    eval_base_place cx e st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  metis_tac[scope_pop_effect_popped_keys_indexed,
            cj 7 eval_mutual_scope_pop_effect]
QED

Theorem eval_target_place_popped_keys_indexed:
  !cx e st res st'.
    eval_target_place cx e st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  metis_tac[scope_pop_effect_popped_keys_indexed,
            cj 8 eval_mutual_scope_pop_effect]
QED

Theorem popped_keys_indexed_update:
  !pre env rest id entry.
    popped_keys_indexed (pre ++ env::rest) /\
    EVERY (\k. ?p i. k = p ++ [ValueSubscript i]) (MAP FST entry.popped) ==>
    popped_keys_indexed (pre ++ (env |+ (id,entry))::rest)
Proof
  rw[popped_keys_indexed_def, FLOOKUP_UPDATE] >>
  Cases_on `id = id'` >> gvs[] >> metis_tac[]
QED

Theorem replace_memory_entry_popped:
  !entry path v entry'.
    replace_memory_entry entry path v = INL entry' ==>
    entry' = entry \/ entry'.popped = []
Proof
  rw[replace_memory_entry_def, AllCaseEqs()] >> simp[]
QED

Theorem push_scope_popped_keys_indexed:
  !st res st'.
    push_scope st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rw[push_scope_def, return_def] >>
  gvs[popped_keys_indexed_def]
QED

Theorem push_scope_with_var_popped_keys_indexed:
  !nm tv v st res st'.
    push_scope_with_var nm tv v st = (res,st') /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rw[push_scope_with_var_def, return_def, popped_keys_indexed_def,
     FLOOKUP_UPDATE] >> gvs[FLOOKUP_UPDATE, AllCaseEqs()]
QED

Theorem pop_scope_popped_keys_indexed:
  !st res st'.
    pop_scope st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `st.scopes` >>
  rw[pop_scope_def, return_def, raise_def, popped_keys_indexed_def] >>
  gvs[]
QED

Theorem new_variable_popped_keys_indexed:
  !id tv v st res st'.
    new_variable id tv v st = (res,st') /\
    popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `st.scopes` >>
  simp[new_variable_def, get_scopes_def, set_scopes_def, bind_def,
       ignore_bind_def, return_def, type_check_def, assert_def,
       raise_def, AllCaseEqs()] >>
  rw[] >> gvs[popped_keys_indexed_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
  rw[] >> gvs[] >> metis_tac[]
QED

Theorem write_place_popped_keys_indexed:
  !cx p v st res st'.
    write_place cx p v st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `p`
  >- metis_tac[write_storage_place_scopes_immutables]
  >- (rename1 `MemoryPlace id path` >> strip_tac >>
      Cases_on `find_containing_scope id st.scopes` >>
      gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
          return_def, raise_def] >> PairCases_on `x` >>
      gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
          set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
      BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def] >>
      drule find_containing_scope_structure >> strip_tac >>
      drule replace_memory_entry_popped >> strip_tac >>
      irule popped_keys_indexed_update >> gvs[popped_keys_indexed_def] >>
      metis_tac[]) >>
  simp[write_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
           get_immutables_def, get_address_immutables_def, return_def, raise_def]) >>
  metis_tac[set_immutable_scopes]
QED

Theorem append_place_popped_keys_indexed:
  !cx p v st res st'.
    append_place cx p v st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `p`
  >- metis_tac[append_storage_place_scopes_immutables] >>
  simp[append_place_def, bind_def, lift_sum_def, return_def, raise_def] >>
  strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
           get_immutables_def, get_address_immutables_def, return_def, raise_def]) >>
  metis_tac[place_type_value_state, read_place_state,
            write_place_popped_keys_indexed]
QED

Theorem assign_tuple_popped_keys_indexed:
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') /\
     popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') /\
     popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes)
Proof
  `(!(cx:evaluation_context) (s:stmt). T) /\
   (!(cx:evaluation_context) (ss:stmt list). T) /\
   (!(cx:evaluation_context) (it:iterator). T) /\
   (!(cx:evaluation_context) (ty:type_value) (nm:string) (body:stmt list) (vs:value list). T) /\
   (!(cx:evaluation_context) (e:expr). T) /\
   (!(cx:evaluation_context) (es:expr list). T) /\
   (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
   (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
   (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') /\
      popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
   (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') /\
      popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
   (!(cx:evaluation_context) (es:expr list). T)` suffices_by metis_tac[] >>
  ho_match_mp_tac evaluate_ind >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `assign_tuple_targets _ (BaseTarget _) _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac eval_target_place_popped_keys_indexed >>
      imp_res_tac write_place_popped_keys_indexed >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> Cases_on `v` >>
      simp[Once evaluate_def, raise_def] >>
      Cases_on `a` >> gvs[Once evaluate_def, raise_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def, raise_def, AllCaseEqs()]) >>
  rpt strip_tac >>
  qpat_x_assum `assign_tuple_target_list cx _ _ st = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), raise_def] >>
  strip_tac >> metis_tac[]
QED

Theorem eval_iterator_popped_keys_indexed:
  !cx it st res st'.
    eval_iterator cx it st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `it` >> strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac read_result_scopes >>
  imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes >>
  imp_res_tac lift_sum_scopes >> imp_res_tac lift_sum_runtime_scopes >>
  imp_res_tac return_scopes >> gvs[] >>
  metis_tac[eval_expr_popped_keys_indexed]
QED

Theorem stmt_return_popped_keys_indexed:
  !cx e st res st'.
    eval_stmt cx (Return e) st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `e` >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, raise_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac read_result_scopes >> gvs[] >>
  metis_tac[eval_expr_popped_keys_indexed]
QED

Theorem stmt_expr_popped_keys_indexed:
  !cx e st res st'.
    eval_stmt cx (Expr e) st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac type_check_scopes >> gvs[] >>
  metis_tac[eval_expr_popped_keys_indexed]
QED

Theorem stmt_log_popped_keys_indexed:
  !cx id es st res st'.
    eval_stmt cx (Log id es) st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac lift_option_scopes >> imp_res_tac push_log_scopes >> gvs[] >>
  metis_tac[eval_exprs_popped_keys_indexed]
QED

Theorem stmt_annassign_popped_keys_indexed:
  !cx id typ e st res st'.
    eval_stmt cx (AnnAssign id typ e) st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac lift_option_type_scopes >> imp_res_tac read_result_scopes >> gvs[] >>
  metis_tac[eval_expr_popped_keys_indexed, new_variable_popped_keys_indexed]
QED

Theorem stmt_append_popped_keys_indexed:
  !cx t e st res st'.
    eval_stmt cx (Append t e) st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_scopes >> gvs[] >>
  imp_res_tac eval_target_place_popped_keys_indexed >>
  imp_res_tac eval_expr_popped_keys_indexed >>
  metis_tac[append_place_popped_keys_indexed]
QED

Theorem stmt_assign_popped_keys_indexed:
  !cx g e st res st'.
    eval_stmt cx (Assign g e) st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `g` >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_scopes >> gvs[] >>
  imp_res_tac eval_expr_popped_keys_indexed >>
  imp_res_tac eval_target_place_popped_keys_indexed >>
  metis_tac[write_place_popped_keys_indexed, cj 1 assign_tuple_popped_keys_indexed]
QED

Theorem stmt_augassign_popped_keys_indexed:
  !cx ty t bop e st res st'.
    eval_stmt cx (AugAssign ty t bop e) st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_scopes >> imp_res_tac read_place_state >>
  imp_res_tac place_type_value_state >> imp_res_tac lift_sum_scopes >> gvs[] >>
  imp_res_tac eval_target_place_popped_keys_indexed >>
  imp_res_tac eval_expr_popped_keys_indexed >>
  metis_tac[write_place_popped_keys_indexed]
QED

Theorem stmt_raise_popped_keys_indexed:
  !cx reason st res st'.
    eval_stmt cx (Raise reason) st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `reason` >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, raise_def, AllCaseEqs()]
  >- (strip_tac >> gvs[])
  >- (strip_tac >> gvs[])
  >- (strip_tac >> imp_res_tac read_result_scopes >>
      imp_res_tac lift_option_type_scopes >> gvs[] >>
      metis_tac[eval_expr_popped_keys_indexed]) >>
  Cases_on `c` >> simp[bind_def, raise_def, AllCaseEqs()] >> strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, raise_def, AllCaseEqs()]) >>
  imp_res_tac lift_option_scopes >> gvs[] >>
  metis_tac[eval_exprs_popped_keys_indexed]
QED

Theorem stmt_assert_popped_keys_indexed:
  !cx e reason st res st'.
    eval_stmt cx (Assert e reason) st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rpt gen_tac >> Cases_on `reason` >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, switch_BoolV_def, bind_def, return_def,
       raise_def, COND_RATOR, AllCaseEqs()]
  >- (strip_tac >> imp_res_tac read_result_scopes >> gvs[] >>
      metis_tac[eval_expr_popped_keys_indexed])
  >- (strip_tac >> imp_res_tac read_result_scopes >> gvs[] >>
      metis_tac[eval_expr_popped_keys_indexed])
  >- (strip_tac >> imp_res_tac read_result_scopes >>
      imp_res_tac lift_option_type_scopes >> gvs[] >>
      metis_tac[eval_expr_popped_keys_indexed]) >>
  Cases_on `c` >> simp[bind_def, raise_def, AllCaseEqs()] >> strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, raise_def, AllCaseEqs()]) >>
  imp_res_tac read_result_scopes >> imp_res_tac lift_option_scopes >> gvs[] >>
  imp_res_tac eval_expr_popped_keys_indexed >>
  metis_tac[eval_exprs_popped_keys_indexed]
QED

Theorem stmt_if_popped_keys_indexed:
  !cx e ss1 ss2.
    (!s0 tv t s1 t1.
       eval_expr cx e s0 = (INL tv,t) /\ push_scope s1 = (INL (),t1) ==>
       !st res st'. eval_stmts cx ss1 st = (res,st') /\
         popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
    (!s0 tv t s1 t1.
       eval_expr cx e s0 = (INL tv,t) /\ push_scope s1 = (INL (),t1) ==>
       !st res st'. eval_stmts cx ss2 st = (res,st') /\
         popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) ==>
    !st res st'. eval_stmt cx (If e ss1 ss2) st = (res,st') /\
       popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, finally_def,
       switch_BoolV_def, COND_RATOR, AllCaseEqs(), return_def, raise_def] >>
  strip_tac >> imp_res_tac read_result_scopes >> gvs[] >>
  imp_res_tac eval_expr_popped_keys_indexed >>
  imp_res_tac push_scope_popped_keys_indexed >>
  metis_tac[pop_scope_popped_keys_indexed]
QED

Theorem stmt_for_popped_keys_indexed:
  !cx nm typ it n body.
    (!s0 tyv t s1 vs t1 s2 t2.
       lift_option_type (evaluate_type (get_tenv cx) typ) "For evaluate_type" s0 = (INL tyv,t) /\
       eval_iterator cx it s1 = (INL vs,t1) /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s2 = (INL (),t2) ==>
       !st res st'. eval_for cx tyv nm body vs st = (res,st') /\
         popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) ==>
    !st res st'. eval_stmt cx (For nm typ it n body) st = (res,st') /\
       popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac lift_option_type_scopes >>
  imp_res_tac check_scopes >> gvs[] >>
  imp_res_tac eval_iterator_popped_keys_indexed >> metis_tac[]
QED

Theorem eval_stmts_cons_popped_keys_indexed:
  !cx s ss.
    (!s0 t. eval_stmt cx s s0 = (INL (),t) ==>
       !st res st'. eval_stmts cx ss st = (res,st') /\
         popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
    (!st res st'. eval_stmt cx s st = (res,st') /\
       popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) ==>
    !st res st'. eval_stmts cx (s::ss) st = (res,st') /\
       popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, AllCaseEqs()] >>
  strip_tac >> metis_tac[]
QED

Theorem eval_for_cons_popped_keys_indexed:
  !cx tyv nm body v vs.
    (!s0 t s1 t1.
       push_scope_with_var nm tyv v s0 = (INL (),t) /\
       finally (try (ignore_bind (eval_stmts cx body) (return F)) handle_loop_exception)
         pop_scope s1 = (INL F,t1) ==>
       !st res st'. eval_for cx tyv nm body vs st = (res,st') /\
         popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
    (!s0 t. push_scope_with_var nm tyv v s0 = (INL (),t) ==>
       !st res st'. eval_stmts cx body st = (res,st') /\
         popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) ==>
    !st res st'. eval_for cx tyv nm body (v::vs) st = (res,st') /\
       popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, COND_RATOR,
       AllCaseEqs(), return_def, raise_def] >> strip_tac >> gvs[] >>
  imp_res_tac push_scope_with_var_popped_keys_indexed >>
  qpat_x_assum `!s0 t. push_scope_with_var _ _ _ s0 = _ ==> _` drule >>
  strip_tac >>
  qpat_assum `finally _ _ _ = _` mp_tac >>
  simp[NoAsms, finally_def, try_def, bind_def, ignore_bind_def,
       handle_loop_exception_def, COND_RATOR, AllCaseEqs(), return_def, raise_def] >>
  strip_tac >> gvs[] >>
  qpat_assum `!st res st'. eval_stmts _ _ st = _ /\ _ ==> _` imp_res_tac >>
  imp_res_tac pop_scope_popped_keys_indexed >>
  gvs[ignore_bind_def] >> metis_tac[]
QED

Theorem stmt_trivial_popped_keys_indexed:
  !cx s st res st'.
    (s = Pass \/ s = Continue \/ s = Break) /\
    eval_stmt cx s st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rw[] >> gvs[Once evaluate_def, return_def, raise_def]
QED

Theorem eval_for_nil_popped_keys_indexed:
  !cx tyv nm body st res st'.
    eval_for cx tyv nm body [] st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rw[Once evaluate_def, return_def] >> gvs[]
QED

Theorem eval_stmts_nil_popped_keys_indexed:
  !cx st res st'.
    eval_stmts cx [] st = (res,st') /\ popped_keys_indexed st.scopes ==>
    popped_keys_indexed st'.scopes
Proof
  rw[Once evaluate_def, return_def] >> gvs[]
QED

Theorem eval_statement_loop_popped_keys_indexed:
  (!cx s st res st'. eval_stmt cx s st = (res,st') /\
     popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') /\
     popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res,st') /\
     popped_keys_indexed st.scopes ==> popped_keys_indexed st'.scopes) /\
  (!(cx:evaluation_context) (e:expr). T) /\
  (!(cx:evaluation_context) (es:expr list). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T) /\
  (!(cx:evaluation_context) (es:expr list). T)
Proof
  ho_match_mp_tac evaluate_ind >> simp[] >> rpt conj_tac
  >- metis_tac[stmt_trivial_popped_keys_indexed]
  >- metis_tac[stmt_trivial_popped_keys_indexed]
  >- metis_tac[stmt_trivial_popped_keys_indexed]
  >- metis_tac[stmt_return_popped_keys_indexed]
  >- metis_tac[stmt_return_popped_keys_indexed]
  >- metis_tac[stmt_raise_popped_keys_indexed]
  >- metis_tac[stmt_raise_popped_keys_indexed]
  >- metis_tac[stmt_raise_popped_keys_indexed]
  >- metis_tac[stmt_raise_popped_keys_indexed]
  >- metis_tac[stmt_assert_popped_keys_indexed]
  >- metis_tac[stmt_assert_popped_keys_indexed]
  >- metis_tac[stmt_assert_popped_keys_indexed]
  >- metis_tac[stmt_assert_popped_keys_indexed]
  >- metis_tac[stmt_log_popped_keys_indexed]
  >- metis_tac[stmt_annassign_popped_keys_indexed]
  >- metis_tac[stmt_append_popped_keys_indexed]
  >- metis_tac[stmt_assign_popped_keys_indexed]
  >- metis_tac[stmt_assign_popped_keys_indexed]
  >- metis_tac[stmt_augassign_popped_keys_indexed]
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC stmt_if_popped_keys_indexed)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC stmt_for_popped_keys_indexed)
  >- metis_tac[stmt_expr_popped_keys_indexed]
  >- metis_tac[eval_stmts_nil_popped_keys_indexed]
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC eval_stmts_cons_popped_keys_indexed)
  >- metis_tac[eval_for_nil_popped_keys_indexed]
  >> rpt gen_tac >> MATCH_ACCEPT_TAC eval_for_cons_popped_keys_indexed
QED
