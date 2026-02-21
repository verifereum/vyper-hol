Theory vyperEvalPreservesImmutablesDom

Ancestors
  vyperInterpreter vyperLookup vyperScopePreservation vyperStatePreservation
    vyperAssignTarget vyperEvalExprPreservesScopesDom

(* ========================================================================
   Preservation of immutables domain through eval_expr / eval_stmts.

   TOP-LEVEL:
     eval_expr_preserves_immutables_addr_dom
     eval_expr_preserves_immutables_dom
     eval_base_target_preserves_immutables_addr_dom
     eval_base_target_preserves_immutables_dom
     eval_exprs_preserves_immutables_addr_dom
     eval_stmts_preserves_immutables_addr_dom
     eval_stmts_preserves_immutables_dom
   ======================================================================== *)

(* ===== Predicate bundling both domain properties ===== *)

Definition preserves_immutables_dom_def:
  preserves_immutables_dom cx (st:evaluation_state) (st':evaluation_state) ⇔
    (∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒
           IS_SOME (ALOOKUP st'.immutables tgt)) ∧
    (∀src n imms imms'.
       ALOOKUP st.immutables cx.txn.target = SOME imms ∧
       ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
       (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
        IS_SOME (FLOOKUP (get_source_immutables src imms') n)))
End

Theorem preserves_immutables_dom_refl[local]:
  ∀cx st. preserves_immutables_dom cx st st
Proof
  rw[preserves_immutables_dom_def] >> gvs[]
QED

Theorem preserves_immutables_dom_trans[local]:
  ∀cx st1 st2 st3.
    preserves_immutables_dom cx st1 st2 ∧
    preserves_immutables_dom cx st2 st3 ⇒
    preserves_immutables_dom cx st1 st3
Proof
  rw[preserves_immutables_dom_def] >>
  `IS_SOME (ALOOKUP st2.immutables cx.txn.target)` by (first_x_assum irule >> simp[]) >>
  Cases_on `ALOOKUP st2.immutables cx.txn.target` >> gvs[]
QED

Theorem preserves_immutables_dom_eq[local]:
  ∀cx st st'.
    st'.immutables = st.immutables ⇒ preserves_immutables_dom cx st st'
Proof
  rw[preserves_immutables_dom_def] >> gvs[]
QED

(* ===== Trivial monad helpers ===== *)

Theorem get_Value_immutables[local]:
  ∀tv st res st'. get_Value tv st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  Cases_on `tv` >> rw[get_Value_def, return_def, raise_def]
QED

Theorem transfer_value_immutables[local]:
  ∀f t a st res st'.
    transfer_value f t a st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def,
     check_def, type_check_def, assert_def, update_accounts_def] >> gvs[raise_def]
QED

Theorem lookup_flag_mem_immutables[local]:
  ∀cx nsid mid st res st'.
    lookup_flag_mem cx nsid mid st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  rpt gen_tac >> PairCases_on `nsid` >>
  simp[lookup_flag_mem_def, return_def, raise_def] >>
  rpt CASE_TAC >> simp[return_def, raise_def]
QED

(* ===== assign_target preserves immutables domain for any result ===== *)

Theorem assign_target_imm_dom_ScopedVar[local]:
  ∀cx id is ao st res st'.
    assign_target cx (BaseTargetV (ScopedVar id) is) ao st = (res, st') ⇒
    st'.immutables = st.immutables
Proof
  rpt strip_tac >>
  qpat_x_assum `_ = (_, _)` mp_tac >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def, lift_sum_def, AllCaseEqs(), raise_def, LET_THM,
       ignore_bind_def, set_scopes_def] >>
  rpt CASE_TAC >> gvs[return_def, raise_def, set_scopes_def, bind_def] >>
  PairCases_on `x` >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def, set_scopes_def] >>
  rpt CASE_TAC >> gvs[return_def, raise_def, set_scopes_def] >>
  rpt strip_tac >>
  gvs[oneline assign_result_def, return_def, bind_def, lift_sum_def, raise_def,
      AllCaseEqs(), assign_operation_CASE_rator, sum_CASE_rator]
QED

(* Helper: the HashMap do-block in assign_target preserves immutables *)
Theorem hashmap_do_block_immutables[local]:
  ∀cx b c t' tenv key_types remaining_subs final_type h t ao r res st'.
    (λ(final_type,key_types,remaining_subs).
       do
         final_slot <-
           case
             compute_hashmap_slot c (t'::key_types)
               (h::TAKE (LENGTH t − LENGTH remaining_subs) t)
           of
             NONE => raise (TypeError "assign_target compute_hashmap_slot")
           | SOME v => return v;
         final_tv <-
           case evaluate_type tenv final_type of
             NONE => raise (TypeError "assign_target evaluate_type")
           | SOME v => return v;
         current_val <- read_storage_slot cx b final_slot final_tv;
         new_val <-
           case assign_subscripts current_val remaining_subs ao of
             INL v => return v
           | INR e => raise e;
         x <- write_storage_slot cx b final_slot final_tv new_val;
         assign_result ao current_val remaining_subs
       od) (final_type,key_types,remaining_subs) r = (res,st') ⇒
    st'.immutables = r.immutables
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  simp[bind_def, return_def, raise_def] >> strip_tac >>
  (* Step 1: compute_hashmap_slot *)
  Cases_on `compute_hashmap_slot c (t'::key_types)
              (h::TAKE (LENGTH t − LENGTH remaining_subs) t)` >>
  gvs[return_def, raise_def] >>
  rename1 `compute_hashmap_slot _ _ _ = SOME slot` >>
  (* Step 2: evaluate_type *)
  Cases_on `evaluate_type tenv final_type` >>
  gvs[return_def, raise_def] >>
  rename1 `evaluate_type _ _ = SOME tv` >>
  (* Step 3: read_storage_slot *)
  `∃rr sr. read_storage_slot cx b slot tv r = (rr, sr)` by
    metis_tac[pairTheory.PAIR] >>
  Cases_on `rr` >> gvs[] >>
  imp_res_tac read_storage_slot_immutables >>
  (* Step 4: assign_subscripts *)
  Cases_on `assign_subscripts x remaining_subs ao` >>
  gvs[return_def, raise_def] >>
  rename1 `assign_subscripts _ _ _ = INL new_val` >>
  (* Step 5: write_storage_slot *)
  `∃rw sw. write_storage_slot cx b slot tv new_val sr = (rw, sw)` by
    metis_tac[pairTheory.PAIR] >>
  Cases_on `rw` >> gvs[] >>
  imp_res_tac write_storage_slot_immutables >> gvs[] >>
  (* Step 6: assign_result *)
  imp_res_tac assign_result_state >> gvs[]
QED

Theorem lift_option_same_state[local]:
  lift_option v msg s = (r, s') ⇒ s' = s
Proof
  rw[lift_option_def, lift_option_type_def] >> Cases_on `v` >> gvs[return_def, raise_def]
QED

Theorem lift_option_type_same_state[local]:
  lift_option_type v msg s = (r, s') ⇒ s' = s
Proof
  rw[lift_option_type_def] >> Cases_on `v` >> gvs[return_def, raise_def]
QED

Theorem assign_target_imm_dom_TopLevelVar[local]:
  ∀cx src_id_opt id is ao st res st'.
    assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) is) ao st = (res, st') ⇒
    st'.immutables = st.immutables
Proof
  rw[assign_target_def, bind_def, ignore_bind_def, AllCaseEqs(),
     toplevel_value_CASE_rator, sum_CASE_rator, prod_CASE_rator,
     type_value_CASE_rator] >>
  imp_res_tac lookup_global_immutables >>
  imp_res_tac lift_option_same_state >> imp_res_tac lift_option_type_same_state >>
  imp_res_tac lift_sum_state >>
  imp_res_tac assign_result_state >>
  imp_res_tac set_global_immutables >>
  imp_res_tac resolve_array_element_state >>
  gvs[] >>
  pairarg_tac >>
  gvs[bind_def, AllCaseEqs(), type_value_CASE_rator,
      assign_operation_CASE_rator, bound_CASE_rator,
      return_def, raise_def, check_def, type_check_def, assert_def] >>
  imp_res_tac lift_option_same_state >> imp_res_tac lift_option_type_same_state >>
  imp_res_tac lift_sum_state >>
  imp_res_tac read_storage_slot_immutables >>
  imp_res_tac write_storage_slot_immutables >>
  imp_res_tac assign_result_state >>
  imp_res_tac resolve_array_element_state >>
  imp_res_tac get_storage_backend_state >>
  gvs[] >>
  pairarg_tac >>
  gvs[bind_def, AllCaseEqs()] >>
  imp_res_tac lift_option_same_state >> imp_res_tac lift_option_type_same_state >>
  imp_res_tac lift_sum_state >>
  imp_res_tac read_storage_slot_immutables >>
  imp_res_tac write_storage_slot_immutables >>
  imp_res_tac assign_result_state >>
  gvs[]
QED

Theorem assign_target_imm_dom_ImmutableVar[local]:
  ∀cx id is ao st res st'.
    assign_target cx (BaseTargetV (ImmutableVar id) is) ao st = (res, st') ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `_ = (_, _)` mp_tac >>
  simp[Once assign_target_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, get_immutables_def, return_def, lift_option_def, lift_option_type_def, lift_sum_def,
       AllCaseEqs(), raise_def, set_immutable_def, get_address_immutables_def,
       set_address_immutables_def] >>
  rpt strip_tac >>
  gvs[return_def, raise_def, AllCaseEqs(), preserves_immutables_dom_refl] >>
  (* resolve error paths by case-splitting on each case expression *)
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[return_def, raise_def, preserves_immutables_dom_refl] >>
  Cases_on `FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num id)` >>
  gvs[return_def, raise_def, preserves_immutables_dom_refl] >>
  Cases_on `assign_subscripts a (REVERSE is) ao` >>
  gvs[return_def, raise_def, preserves_immutables_dom_refl] >>
  imp_res_tac assign_result_state >> gvs[] >>
  Cases_on `ALOOKUP s''.immutables cx.txn.target` >>
  gvs[return_def, raise_def, preserves_immutables_dom_refl] >>
  (* success path: prove preserves_immutables_dom for the updated state *)
  simp[preserves_immutables_dom_def] >> conj_tac
  >- (rpt strip_tac >>
      Cases_on `cx.txn.target = tgt` >>
      gvs[alistTheory.ALOOKUP_ADELKEY])
  >> simp[set_source_immutables_def, get_source_immutables_def,
          alistTheory.ALOOKUP_ADELKEY,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     rpt gen_tac >>
     TRY (rename1 `IS_SOME (FLOOKUP (get_source_immutables src _) n)`) >>
     TRY (Cases_on `src = current_module cx` >> gvs[]) >>
     Cases_on `n = string_to_num id` >>
     gvs[get_source_immutables_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem assign_target_imm_dom_TupleV[local]:
  ∀cx gvs vs st res st'.
    (∀st res st'.
       assign_targets cx gvs vs st = (res, st') ⇒
       preserves_immutables_dom cx st st') ⇒
    assign_target cx (TupleTargetV gvs) (Replace (ArrayV (TupleV vs))) st =
    (res, st') ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, check_def, type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl]
QED

Theorem assign_targets_imm_dom_cons[local]:
  ∀cx av v gvs vs st res st'.
    (∀st res st'.
       assign_target cx av (Replace v) st = (res, st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀st res st'.
       assign_targets cx gvs vs st = (res, st') ⇒
       preserves_immutables_dom cx st st') ⇒
    assign_targets cx (av::gvs) (v::vs) st = (res, st') ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_targets _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def,
       AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> metis_tac[]
QED

Theorem assign_target_imm_dom_any[local]:
  (∀cx av ao st res st'.
     assign_target cx av ao st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx gvs vs st res st'.
     assign_targets cx gvs vs st = (res, st') ⇒ preserves_immutables_dom cx st st')
Proof
  ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac
  (* ScopedVar *)
  >- (rpt strip_tac >> irule preserves_immutables_dom_eq >>
      imp_res_tac assign_target_imm_dom_ScopedVar >> simp[])
  (* TopLevelVar *)
  >- (rpt strip_tac >> irule preserves_immutables_dom_eq >>
      imp_res_tac assign_target_imm_dom_TopLevelVar >> simp[])
  (* ImmutableVar *)
  >- (rpt strip_tac >> imp_res_tac assign_target_imm_dom_ImmutableVar)
  (* TupleTargetV + TupleV *)
  >- (rpt strip_tac >> irule assign_target_imm_dom_TupleV >> metis_tac[])
  (* All remaining 16 subgoals: TupleTargetV raise cases, assign_targets *)
  >> rpt strip_tac
  >> TRY (irule assign_targets_imm_dom_cons >> metis_tac[])
  >> gvs[Once assign_target_def, raise_def, return_def,
         preserves_immutables_dom_refl]
QED

(* ===== IntCall helper ===== *)

Theorem handle_function_immutables[local]:
  ∀exc st res st'.
    handle_function exc st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  Cases_on `exc` >> simp[handle_function_def, return_def, raise_def]
QED

Theorem preserves_immutables_dom_txn_eq[local]:
  ∀cx cx' st st'.
    cx'.txn = cx.txn ⇒
    (preserves_immutables_dom cx' st st' ⇔ preserves_immutables_dom cx st st')
Proof
  simp[preserves_immutables_dom_def]
QED

Theorem case_IntCall_imm_dom_inner[local]:
  ∀cx src_id_opt fname body env st0 vs sevl dflt_vs sdfl
   fres sfnl es needed_dflts prev.
    (∀st res st'.
       eval_exprs cx es st = (res,st') ⇒ preserves_immutables_dom cx st st') ∧
    (∀st res st'.
       eval_exprs (cx with stk updated_by CONS (src_id_opt,fname))
         needed_dflts st = (res,st') ⇒
       preserves_immutables_dom
         (cx with stk updated_by CONS (src_id_opt,fname)) st st') ∧
    (∀st res st'.
       eval_stmts (cx with stk updated_by CONS (src_id_opt,fname)) body st =
       (res,st') ⇒
       preserves_immutables_dom
         (cx with stk updated_by CONS (src_id_opt,fname)) st st') ∧
    eval_exprs cx es st0 = (INL vs, sevl) ∧
    eval_exprs (cx with stk updated_by CONS (src_id_opt,fname))
      needed_dflts sevl = (INL dflt_vs, sdfl) ∧
    finally
      (try (bind (eval_stmts (cx with stk updated_by CONS (src_id_opt,fname))
         body) (λx. return NoneV)) handle_function)
      (pop_function prev)
      (sdfl with scopes := [env]) = (fres, sfnl) ⇒
    preserves_immutables_dom cx st0 sfnl
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `sevl` >> conj_tac >- gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sdfl` >> conj_tac
  >- (irule (iffLR preserves_immutables_dom_txn_eq) >>
      qexists_tac `cx with stk updated_by CONS (src_id_opt,fname)` >>
      simp[] >> gvs[]) >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, AllCaseEqs(), pop_function_def, set_scopes_def,
       return_def, ignore_bind_def, bind_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_eq, preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sdfl with scopes := [env]` >>
  gvs[preserves_immutables_dom_eq] >>
  irule (iffLR preserves_immutables_dom_txn_eq) >>
  qexists_tac `cx with stk updated_by CONS (src_id_opt,fname)` >> simp[] >>
  qpat_x_assum `try _ _ _ = _` mp_tac >>
  simp[try_def, bind_def, AllCaseEqs(), return_def, raise_def,
       handle_function_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl, preserves_immutables_dom_eq] >>
  first_x_assum drule >> gvs[preserves_immutables_dom_eq] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[handle_function_def, return_def, raise_def, preserves_immutables_dom_eq] >>
  first_x_assum drule >> gvs[preserves_immutables_dom_eq] >>
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
  irule preserves_immutables_dom_eq >>
  gvs[handle_function_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac handle_function_immutables
QED

(* ----- Case 5: Return (SOME e) ----- *)
Theorem case_Return_SOME_imm_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Return (SOME e)) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[]
QED

(* ----- Case 6: Raise e ----- *)
Theorem case_Raise_imm_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Raise e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), raise_def,
       lift_option_def, lift_option_type_def, return_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[preserves_immutables_dom_eq] >>
  Cases_on `dest_StringV v''` >>
  gvs[return_def, raise_def, preserves_immutables_dom_eq]
QED

(* ----- Case 7: Assert e se ----- *)
Theorem case_Assert_imm_dom[local]:
  ∀cx e se.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv t. eval_expr cx e s'' = (INL tv,t) ⇒
       ∀st res st'. eval_expr cx se st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Assert e se) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >> Cases_on `q` >>
  simp[return_def, raise_def, preserves_immutables_dom_refl] >>
  (* Derive unconditional IH for se from the conditional one *)
  sg `∀st res st'. eval_expr cx se st = (res,st') ⇒
        preserves_immutables_dom cx st st'`
  >- (rpt strip_tac >> gvs[] >>
      first_x_assum (drule_then (fn th =>
        first_x_assum (fn th2 => mp_tac (MATCH_MP th th2)))) >>
      simp[])
  >> strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `r` >> conj_tac
  >- gvs[]
  >> qpat_x_assum `switch_BoolV _ _ _ _ = _` mp_tac >>
     simp[switch_BoolV_def] >>
     IF_CASES_TAC >> simp[return_def, raise_def, preserves_immutables_dom_refl] >>
     IF_CASES_TAC >> simp[raise_def, preserves_immutables_dom_refl] >>
     simp[bind_def, AllCaseEqs(), return_def, raise_def,
          lift_option_def, lift_option_type_def] >>
     rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
     imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
     irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
     gvs[preserves_immutables_dom_eq] >>
     Cases_on `dest_StringV sv` >>
     gvs[return_def, raise_def, preserves_immutables_dom_eq]
QED

(* ----- Case 8: Log id es ----- *)
Theorem case_Log_imm_dom[local]:
  ∀cx id es.
    (∀st res st'. eval_exprs cx es st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Log id es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def, push_log_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[preserves_immutables_dom_eq]
QED

(* ----- Case 9: AnnAssign id typ e ----- *)
Theorem case_AnnAssign_imm_dom[local]:
  ∀cx id typ e.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (AnnAssign id typ e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       new_variable_def, LET_THM, get_scopes_def, check_def, type_check_def, assert_def,
       set_scopes_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[preserves_immutables_dom_eq] >>
  irule preserves_immutables_dom_eq >>
  qpat_x_assum `_ s'³' = (res, st')` mp_tac >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, assert_def, return_def, raise_def, set_scopes_def,
       AllCaseEqs()] >>
  Cases_on `s'³'.scopes` >>
  simp[raise_def, set_scopes_def, return_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `s''.scopes` >>
  gvs[raise_def, set_scopes_def, return_def]
QED

(* ----- Case 10: Append bt e ----- *)
Theorem case_Append_imm_dom[local]:
  ∀cx bt e.
    (∀st res st'. eval_base_target cx bt st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' loc sbs t'. eval_base_target cx bt s'' = (INL (loc,sbs),t') ⇒
       ∀st res st'. eval_expr cx e st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Append bt e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def, lift_option_def, lift_option_type_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  Cases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  imp_res_tac (cj 1 assign_target_imm_dom_any) >>
  first_x_assum (qspecl_then [`st`, `q`, `r`, `s''`] mp_tac) >> simp[] >>
  strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'⁴'` >> conj_tac
    >- (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
        gvs[preserves_immutables_dom_eq])
    >> gvs[] >> NO_TAC) >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
       gvs[preserves_immutables_dom_eq] >> NO_TAC) >>
  gvs[]
QED

(* ----- Case 11: Assign g e ----- *)
Theorem case_Assign_imm_dom[local]:
  ∀cx g e.
    (∀st res st'. eval_target cx g st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' gv t. eval_target cx g s'' = (INL gv,t) ⇒
       ∀st res st'. eval_expr cx e st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Assign g e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  imp_res_tac (cj 1 assign_target_imm_dom_any) >>
  first_x_assum (qspecl_then [`st`, `gv`, `s''`] mp_tac) >> simp[] >>
  strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'⁴'` >> conj_tac
    >- (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
        gvs[preserves_immutables_dom_eq])
    >> gvs[] >> NO_TAC) >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
       gvs[preserves_immutables_dom_eq] >> NO_TAC) >>
  gvs[]
QED

(* ----- Case 12: AugAssign bt bop e ----- *)
Theorem case_AugAssign_imm_dom[local]:
  ∀cx bt bop e.
    (∀st res st'. eval_base_target cx bt st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' loc sbs t'. eval_base_target cx bt s'' = (INL (loc,sbs),t') ⇒
       ∀st res st'. eval_expr cx e st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (AugAssign bt bop e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def, lift_option_def, lift_option_type_def,
       lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  Cases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  imp_res_tac (cj 1 assign_target_imm_dom_any) >>
  first_x_assum (qspecl_then [`st`, `q`, `r`, `s''`] mp_tac) >> simp[] >>
  strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'⁵'` >> conj_tac
    >- (irule preserves_immutables_dom_trans >> qexists_tac `s'⁴'` >> conj_tac
        >- (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
            gvs[preserves_immutables_dom_eq])
        >> gvs[preserves_immutables_dom_eq])
    >> gvs[] >> NO_TAC) >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'⁴'` >> conj_tac
    >- (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
        gvs[preserves_immutables_dom_eq])
    >> gvs[preserves_immutables_dom_eq] >> NO_TAC) >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
       gvs[preserves_immutables_dom_eq] >> NO_TAC) >>
  gvs[]
QED

(* ----- Case 13: If e ss1 ss2 ----- *)
Theorem case_If_imm_dom[local]:
  ∀cx e ss1 ss2.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv t s'³' x t'.
       eval_expr cx e s'' = (INL tv,t) ∧ push_scope s'³' = (INL x,t') ⇒
       ∀st res st'. eval_stmts cx ss1 st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀s'' tv t s'³' x t'.
       eval_expr cx e s'' = (INL tv,t) ∧ push_scope s'³' = (INL x,t') ⇒
       ∀st res st'. eval_stmts cx ss2 st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (If e ss1 ss2) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def, push_scope_def,
       switch_BoolV_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  (* Simplify push_scope conditions and derive unconditional IHs *)
  RULE_ASSUM_TAC (REWRITE_RULE [push_scope_def, return_def]) >> gvs[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  last_x_assum (drule_then strip_assume_tac) >>
  first_x_assum (drule_then strip_assume_tac) >>
  irule preserves_immutables_dom_trans >>
  qexists_tac `s''` >> conj_tac >- gvs[] >>
  irule preserves_immutables_dom_trans >>
  qexists_tac `s'' with scopes updated_by CONS FEMPTY` >>
  conj_tac >- (irule preserves_immutables_dom_eq >> simp[]) >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, AllCaseEqs(), pop_scope_def, return_def, raise_def,
       bind_def, ignore_bind_def] >>
  rpt strip_tac >> gvs[] >>
  irule preserves_immutables_dom_trans >>
  rename1 `_ (s'' with scopes updated_by CONS FEMPTY) = (_, s_body)` >>
  qexists_tac `s_body` >>
  (conj_tac
   >- (Cases_on `tv = Value (BoolV T)` >> gvs[raise_def, preserves_immutables_dom_refl] >>
       Cases_on `tv = Value (BoolV F)` >> gvs[raise_def, preserves_immutables_dom_refl])
   >> irule preserves_immutables_dom_eq >> gvs[])
QED

(* ----- Case 14: For id typ it n body ----- *)
Theorem case_For_imm_dom[local]:
  ∀cx id typ it n body.
    (∀st res st'. eval_iterator cx it st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' vs t s'³' x t'.
       eval_iterator cx it s'' = (INL vs,t) ∧
       check (compatible_bound (Dynamic n) (LENGTH vs))
             "For too long" s'³' = (INL x,t') ⇒
       ∀st res st'. eval_for cx (string_to_num id) body vs st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (For id typ it n body) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def, check_def, type_check_def, assert_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  (* Derive unconditional IH for eval_for from the conditional one *)
  first_x_assum (drule_then mp_tac) >>
  simp[check_def, type_check_def, assert_def] >> strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >> first_x_assum irule >> metis_tac[]
QED

(* ----- Case 15: Expr e ----- *)
Theorem case_Expr_imm_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Expr e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  imp_res_tac check_state >> imp_res_tac type_check_state >>
  gvs[preserves_immutables_dom_eq]
QED

(* ----- Case 17: eval_stmts (s::ss) ----- *)
Theorem case_eval_stmts_cons_imm_dom[local]:
  ∀cx s ss.
    (∀st res st'. eval_stmt cx s st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' x t. eval_stmt cx s s'' = (INL x,t) ⇒
       ∀st res st'. eval_stmts cx ss st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmts cx (s::ss) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- (last_x_assum irule >> metis_tac[]) >>
  first_x_assum irule >> first_assum (irule_at Any) >> metis_tac[]
QED

(* ----- Case 18: eval_iterator (Array e) ----- *)
Theorem case_Array_imm_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_iterator cx (Array e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       lift_option_def, lift_option_type_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >> (
    irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
    conj_tac >- gvs[] >>
    irule preserves_immutables_dom_eq >>
    TRY (qpat_x_assum `(case _ of NONE => _ | SOME _ => _) _ = _` mp_tac >>
         CASE_TAC >> simp[return_def, raise_def] >> rpt strip_tac >> gvs[]))
QED

(* ----- Case 19: eval_iterator (Range e1 e2) ----- *)
Theorem case_Range_imm_dom[local]:
  ∀cx e1 e2.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv1 t s'³' s t'.
       eval_expr cx e1 s'' = (INL tv1,t) ∧ get_Value tv1 s'³' = (INL s,t') ⇒
       ∀st res st'. eval_expr cx e2 st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_iterator cx (Range e1 e2) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       lift_sum_def, LET_THM] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  (* Derive unconditional IH for e2 from the conditional one *)
  TRY (
    `∀st res st'. eval_expr cx e2 st = (res,st') ⇒
       preserves_immutables_dom cx st st'` by (
      rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
    (* get_range_limits cases: prove final immutables equality *)
    TRY (
      `s'⁶'.immutables = s'⁵'.immutables` by (
        qpat_x_assum `(case _ of _ => _ | _ => _) _ = _` mp_tac >>
        BasicProvers.EVERY_CASE_TAC >>
        gvs[return_def, raise_def])) >>
    (* Chain transitions: st -> s'' -> s'³' -> s'⁴' -> ... *)
    irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
    conj_tac >- gvs[] >>
    irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
    conj_tac >- (irule preserves_immutables_dom_eq >> gvs[]) >>
    TRY (
      irule preserves_immutables_dom_trans >> qexists_tac `s'⁴'` >>
      conj_tac >- gvs[] >>
      irule preserves_immutables_dom_eq >> gvs[]) >>
    gvs[] >> NO_TAC) >>
  (* get_Value tv1 error: chain st -> s'' -> s'³' *)
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[preserves_immutables_dom_eq]
QED

(* ----- Case 23: eval_targets (g::gs) ----- *)
Theorem case_eval_targets_cons_imm_dom[local]:
  ∀cx g gs.
    (∀st res st'. eval_target cx g st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' gv t. eval_target cx g s'' = (INL gv,t) ⇒
       ∀st res st'. eval_targets cx gs st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_targets cx (g::gs) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_targets _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  first_x_assum drule >> disch_then drule >> simp[]
QED

(* ----- Case 27: eval_base_target (SubscriptTarget bt e) ----- *)
Theorem case_SubscriptTarget_imm_dom[local]:
  ∀cx bt e.
    (∀st res st'. eval_base_target cx bt st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' loc sbs t'. eval_base_target cx bt s'' = (INL (loc,sbs),t') ⇒
       ∀st res st'. eval_expr cx e st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_base_target cx (SubscriptTarget bt e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       lift_option_def, lift_option_type_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  (* Case split on x to get (loc, sbs) and unfold the lambda *)
  Cases_on `x` >> gvs[] >>
  (* Derive unconditional eval_expr IH and base_target preservation *)
  first_x_assum (qspecl_then [`st`, `q`, `r`, `s''`] mp_tac) >> simp[] >>
  strip_tac >>
  (* Unfold the do-block *)
  qpat_x_assum `_ s'' = (res, st')` mp_tac >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
  conj_tac >- (first_x_assum drule >> simp[]) >>
  TRY (irule preserves_immutables_dom_eq >> gvs[] >> NO_TAC) >>
  Cases_on `value_to_key v''` >> gvs[return_def, raise_def] >>
  irule preserves_immutables_dom_eq >> gvs[]
QED

(* ----- Case 29: eval_for (v::vs) ----- *)
Theorem case_eval_for_cons_imm_dom[local]:
  ∀cx nm body v vs.
    (∀s'' x t. push_scope_with_var nm v s'' = (INL x,t) ⇒
       ∀st res st'. eval_stmts cx body st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀s'' x t s'³' broke t'.
       push_scope_with_var nm v s'' = (INL x,t) ∧
       finally
         (try do eval_stmts cx body; return F od handle_loop_exception)
         pop_scope s'³' = (INL broke,t') ∧ ¬broke ⇒
       ∀st res st'. eval_for cx nm body vs st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_for cx nm body (v::vs) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  (* Simplify IHs: push_scope_with_var always succeeds *)
  RULE_ASSUM_TAC (REWRITE_RULE [push_scope_with_var_def, return_def]) >>
  gvs[] >>
  (* Unfold eval_for (v::vs) *)
  qpat_x_assum `eval_for _ _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, push_scope_with_var_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >|
  [ (* Success case: finally returned INL broke *)
    irule preserves_immutables_dom_trans >>
    qexists_tac `st with scopes updated_by CONS (FEMPTY |+ (nm,v))` >>
    conj_tac >- (irule preserves_immutables_dom_eq >> simp[]) >>
    qpat_x_assum `finally _ _ _ = _` mp_tac >>
    simp[finally_def, AllCaseEqs(), pop_scope_def, return_def, raise_def,
         bind_def, ignore_bind_def] >>
    rpt strip_tac >> gvs[] >>
    rename1 `try _ _ _ = (_, s_try)` >>
    irule preserves_immutables_dom_trans >>
    qexists_tac `s_try with scopes := tl` >> conj_tac
    >- (irule preserves_immutables_dom_trans >> qexists_tac `s_try` >> conj_tac
        >- (qpat_x_assum `try _ _ _ = _` mp_tac >>
            PURE_REWRITE_TAC [ignore_bind_def] >>
            simp[try_def, bind_def, return_def, AllCaseEqs(),
                 handle_loop_exception_def, raise_def] >>
            rpt strip_tac >> gvs[return_def, raise_def] >>
            TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
            first_x_assum drule >> simp[] >> strip_tac >>
            BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def])
        >- (irule preserves_immutables_dom_eq >> simp[]))
    >- (Cases_on `broke` >> gvs[return_def, preserves_immutables_dom_refl] >>
        first_x_assum (qspecl_then [
            `st with scopes updated_by CONS (FEMPTY |+ (nm,v))`,
            `s_try with scopes := tl`] mp_tac) >>
        simp[finally_def, ignore_bind_def, bind_def,
             pop_scope_def, return_def] >>
        disch_then drule >> simp[]),
    (* Error case: finally returned INR e *)
    irule preserves_immutables_dom_trans >>
    qexists_tac `st with scopes updated_by CONS (FEMPTY |+ (nm,v))` >>
    conj_tac >- (irule preserves_immutables_dom_eq >> simp[]) >>
    qpat_x_assum `finally _ _ _ = _` mp_tac >>
    simp[finally_def, AllCaseEqs(), pop_scope_def, return_def, raise_def,
         bind_def, ignore_bind_def] >>
    rpt strip_tac >> gvs[] >>
    TRY (rename1 `try _ _ _ = (_, s_try)` >>
         irule preserves_immutables_dom_trans >> qexists_tac `s_try` >>
         conj_tac
         >- (qpat_x_assum `try _ _ _ = _` mp_tac >>
             PURE_REWRITE_TAC [ignore_bind_def] >>
             simp[try_def, bind_def, return_def, AllCaseEqs(),
                  handle_loop_exception_def, raise_def] >>
             rpt strip_tac >> gvs[return_def, raise_def] >>
             TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
             first_x_assum drule >> simp[] >> strip_tac >>
             BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def])
         >- (irule preserves_immutables_dom_eq >> simp[]) >> NO_TAC) >>
    qpat_x_assum `try _ _ _ = _` mp_tac >>
    PURE_REWRITE_TAC [ignore_bind_def] >>
    simp[try_def, bind_def, return_def, AllCaseEqs(),
         handle_loop_exception_def, raise_def] >>
    rpt strip_tac >> gvs[return_def, raise_def] >>
    TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
    first_x_assum drule >> simp[] >> strip_tac >>
    BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def]
  ]
QED

(* ----- Case 33: eval_expr (IfExp e e' e'') ----- *)
Theorem case_IfExp_imm_dom[local]:
  ∀cx e e' e''.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv t. eval_expr cx e s'' = (INL tv,t) ⇒
       ∀st res st'. eval_expr cx e'' st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀s'' tv t. eval_expr cx e s'' = (INL tv,t) ⇒
       ∀st res st'. eval_expr cx e' st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (IfExp e e' e'') st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       switch_BoolV_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  (* Derive unconditional IHs for e' and e'' *)
  `∀st res st'. eval_expr cx e' st = (res,st') ⇒
     preserves_immutables_dom cx st st'` by metis_tac[] >>
  `∀st res st'. eval_expr cx e'' st = (res,st') ⇒
     preserves_immutables_dom cx st st'` by metis_tac[] >>
  Cases_on `tv = Value (BoolV T)` >>
  gvs[raise_def, preserves_immutables_dom_refl] >>
  Cases_on `tv = Value (BoolV F)` >>
  gvs[raise_def, preserves_immutables_dom_refl]
QED

(* ----- Subscript helper lemmas ----- *)

(* Subgoal 1: success path - res' branches into value or storage read.
   Need to show preserves_immutables_dom cx s_e2 st'
   where s_e2 is the state after eval_expr e2. *)
Theorem subscript_helper_success_path[local]:
  ∀cx s_cab s_es st' tv1 v2 res' res.
    s_cab.immutables = s_es.immutables ⇒
    lift_sum (evaluate_subscript (get_tenv cx) tv1 v2) s_cab = (INL res', s_es) ⇒
    (case res' of
       INL v => return v
     | INR (is_transient,slot,tv) =>
       do
         v <- read_storage_slot cx is_transient slot tv;
         return (Value v)
       od) s_es = (res, st') ⇒
    preserves_immutables_dom cx s_cab st'
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_eq >>
  gvs[lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `res'` >> gvs[return_def] >>
  rename1 `INR trip` >> PairCases_on `trip` >>
  gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_storage_slot_immutables
QED

(* Subgoal 2: evaluate_subscript returns INR (error) -
   need preserves_immutables_dom cx st s_e2
   (chaining st → s_e1 → s_e2 via e1 and e2 IHs) *)
Theorem subscript_helper_eval_sub_err_fwd[local]:
  ∀cx e1 e2 st s_e1 s_e2 tv1 tv2 v2 s_gv s_es e'.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    (∀st' res st''. eval_expr cx e2 st' = (res,st'') ⇒
       preserves_immutables_dom cx st' st'') ⇒
    preserves_immutables_dom cx st s_e1 ⇒
    s_gv.immutables = s_e2.immutables ⇒
    eval_expr cx e1 st = (INL tv1, s_e1) ⇒
    eval_expr cx e2 s_e1 = (INL tv2, s_e2) ⇒
    get_Value tv2 s_e2 = (INL v2, s_gv) ⇒
    (case evaluate_subscript (get_tenv cx) tv1 v2 of
       INL v => return v
     | INR e => raise e) s_gv = (INR e', s_es) ⇒
    preserves_immutables_dom cx st s_e2
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s_e1` >>
  conj_tac >- gvs[] >>
  first_x_assum drule >> simp[]
QED

(* Subgoal 3: evaluate_subscript returns INR (error) -
   need preserves_immutables_dom cx s_e2 s_es *)
Theorem subscript_helper_eval_sub_err_bwd[local]:
  ∀cx s_e2 s_gv s_es tv1 tv2 v2 e'.
    s_gv.immutables = s_e2.immutables ⇒
    get_Value tv2 s_e2 = (INL v2, s_gv) ⇒
    (case evaluate_subscript (get_tenv cx) tv1 v2 of
       INL v => return v
     | INR e => raise e) s_gv = (INR e', s_es) ⇒
    preserves_immutables_dom cx s_e2 s_es
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_eq >>
  Cases_on `evaluate_subscript (get_tenv cx) tv1 v2` >> gvs[raise_def, return_def]
QED

(* Subgoal 6: get_Value returns INR (error) -
   need preserves_immutables_dom cx st s_e2 *)
Theorem subscript_helper_get_value_err_fwd[local]:
  ∀cx e1 e2 st s_e1 s_e2 tv1 tv2 s_gv e'.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    (∀st' res st''. eval_expr cx e2 st' = (res,st'') ⇒
       preserves_immutables_dom cx st' st'') ⇒
    preserves_immutables_dom cx st s_e1 ⇒
    s_gv.immutables = s_e2.immutables ⇒
    eval_expr cx e1 st = (INL tv1, s_e1) ⇒
    eval_expr cx e2 s_e1 = (INL tv2, s_e2) ⇒
    get_Value tv2 s_e2 = (INR e', s_gv) ⇒
    preserves_immutables_dom cx st s_e2
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s_e1` >>
  conj_tac >- gvs[] >>
  first_x_assum drule >> simp[]
QED

(* Subgoal 7: get_Value returns INR (error) -
   need preserves_immutables_dom cx s_e2 s_gv *)
Theorem subscript_helper_get_value_err_bwd[local]:
  ∀cx s_e2 s_gv tv2 e'.
    s_gv.immutables = s_e2.immutables ⇒
    get_Value tv2 s_e2 = (INR e', s_gv) ⇒
    preserves_immutables_dom cx s_e2 s_gv
Proof
  rpt strip_tac >> irule preserves_immutables_dom_eq >> gvs[]
QED

(* Subgoal 8: eval_expr e2 returns INR (error) -
   need preserves_immutables_dom cx st s_e2 *)
Theorem subscript_helper_e2_err_fwd[local]:
  ∀cx e1 e2 st s_e1 s_e2 tv1 e'.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    (∀st' res st''. eval_expr cx e2 st' = (res,st'') ⇒
       preserves_immutables_dom cx st' st'') ⇒
    preserves_immutables_dom cx st s_e1 ⇒
    eval_expr cx e1 st = (INL tv1, s_e1) ⇒
    eval_expr cx e2 s_e1 = (INR e', s_e2) ⇒
    preserves_immutables_dom cx st s_e2
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s_e1` >>
  conj_tac >- gvs[] >>
  first_x_assum drule >> simp[]
QED

(* ----- Case 36: eval_expr (Subscript e1 e2) ----- *)
Theorem case_Subscript_imm_dom[local]:
  ∀cx e1 e2.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv1 t. eval_expr cx e1 s'' = (INL tv1,t) ⇒
       ∀st res st'. eval_expr cx e2 st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Subscript e1 e2) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def,
       lift_option_def, lift_option_type_def, lift_sum_def, sum_CASE_rator] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >>
  imp_res_tac check_array_bounds_state >>
  imp_res_tac lift_sum_state >>
  imp_res_tac read_storage_slot_immutables >>
  gvs[] >>
  (* Derive unconditional e2 IH *)
  `∀st res st'. eval_expr cx e2 st = (res,st') ⇒
     preserves_immutables_dom cx st st'` by metis_tac[] >>
  (* All remaining goals: chain st → s'' → s'³' with IHs, rest by eq *)
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
       conj_tac >- gvs[] >>
       irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
       conj_tac >- gvs[] >>
       irule preserves_immutables_dom_eq >> gvs[] >> NO_TAC) >>
  (* Storage read case: decompose the triple v2' and chain *)
  TRY (PairCases_on `v2'` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
       imp_res_tac read_storage_slot_immutables >> gvs[]) >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
       conj_tac >- gvs[] >>
       irule preserves_immutables_dom_eq >> gvs[] >> NO_TAC) >>
  gvs[]
QED

(* ----- Case 37: eval_expr (Attribute e id) ----- *)
Theorem case_Attribute_imm_dom[local]:
  ∀cx e id.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Attribute e id) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[preserves_immutables_dom_eq] >>
  Cases_on `evaluate_attribute sv id` >>
  gvs[return_def, raise_def, preserves_immutables_dom_eq]
QED

(* ----- Case 39: eval_expr (Pop bt) ----- *)
Theorem case_Pop_imm_dom[local]:
  ∀cx bt.
    (∀st res st'. eval_base_target cx bt st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Pop bt) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       lift_option_def, lift_option_type_def, lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  (* Chain through eval_base_target state s'' *)
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  (* Now case-split on x = (loc, sbs) and unfold the do block *)
  PairCases_on `x` >>
  gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  (* assign_target: s'' -> s_at *)
  imp_res_tac (cj 1 assign_target_imm_dom_any) >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
  irule preserves_immutables_dom_eq >>
  gvs[] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[return_def, raise_def]
QED

(* ----- Case 41: eval_expr (Call Send es drv) ----- *)
Theorem case_Send_imm_dom[local]:
  ∀cx es drv.
    (∀s'' x t. type_check (LENGTH es = 2) "Send args" s'' = (INL x,t) ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Call Send es drv) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def, check_def, type_check_def, assert_def,
       lift_option_def, lift_option_type_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  (* Simplify conditional IH *)
  RULE_ASSUM_TAC (REWRITE_RULE [check_def, type_check_def, assert_def, return_def]) >>
  gvs[] >>
  (* Resolve case expressions on dest_AddressV/dest_NumV *)
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[return_def, raise_def]) >>
  imp_res_tac transfer_value_immutables >> gvs[] >>
  first_x_assum drule >>
  metis_tac[preserves_immutables_dom_trans, preserves_immutables_dom_eq]
QED

(* ----- Case 45: eval_exprs (e::es) ----- *)
Theorem case_eval_exprs_cons_imm_dom[local]:
  ∀cx e es.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv t s'³' v t'.
       eval_expr cx e s'' = (INL tv,t) ∧ materialise cx tv s'³' = (INL v,t') ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_exprs cx (e::es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac materialise_state >> gvs[] >>
  (* materialise succeeded: chain st -> s'' -> s'⁴' *)
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
       conj_tac >- gvs[] >> NO_TAC) >>
  qpat_x_assum `∀s''. _` (qspecl_then [`st`, `tv`, `s''`, `s''`, `v''`, `s''`] mp_tac) >>
  simp[] >> disch_then drule >> strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[]
QED

(* ----- Case: eval_target (BaseTarget bt) ----- *)
Theorem case_BaseTarget_imm_dom[local]:
  ∀cx bt.
    (∀st res st'.
       eval_base_target cx bt st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_target cx (BaseTarget bt) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  PairCases_on `x` >>
  gvs[return_def]
QED

(* ----- Case: eval_base_target (NameTarget id) ----- *)
Theorem case_NameTarget_imm_dom[local]:
  ∀cx id.
    ∀st res st'.
      eval_base_target cx (NameTarget id) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >> irule preserves_immutables_dom_eq >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def, raise_def,
       LET_THM, get_immutables_def, get_address_immutables_def,
       lift_option_def, lift_option_type_def, lift_sum_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[return_def, raise_def] >>
  Cases_on `cx.txn.is_creation` >>
  gvs[return_def, raise_def, bind_def, get_address_immutables_def,
      lift_option_def, lift_option_type_def, immutable_target_def,
      option_CASE_rator, sum_CASE_rator, prod_CASE_rator,
      get_module_code_def, check_def, type_check_def, ignore_bind_def, assert_def,
      AllCaseEqs(), exactly_one_option_def, lift_sum_def]
QED

(* ----- Case: eval_base_target (AttributeTarget bt id) ----- *)
Theorem case_AttributeTarget_imm_dom[local]:
  ∀cx bt id.
    (∀st res st'.
       eval_base_target cx bt st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_base_target cx (AttributeTarget bt id) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, pairTheory.UNCURRY] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl]
QED

(* ----- Case: eval_expr (Name id) ----- *)
Theorem case_Name_imm_dom[local]:
  ∀cx id.
    ∀st res st'.
      eval_expr cx (Name id) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       get_scopes_def, get_immutables_def, get_address_immutables_def,
       lift_option_def, lift_option_type_def, lift_sum_def, LET_THM] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[return_def, raise_def, preserves_immutables_dom_refl]
QED

(* ----- Case: eval_expr (Builtin bt es) ----- *)
Theorem case_Builtin_imm_dom[local]:
  ∀cx bt es.
    (∀s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) ∧ bt ≠ Len ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) ∧ bt = Len ⇒
       ∀st res st'.
         eval_expr cx (HD es) st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Builtin bt es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, type_check_def, assert_def, get_accounts_def, lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  Cases_on `bt = Len` >> gvs[] >>
  (* bt = Len branch: eval_expr (HD es) then toplevel_array_length *)
  TRY (gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
       imp_res_tac toplevel_array_length_state >> gvs[] >>
       irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
       gvs[preserves_immutables_dom_eq] >>
       first_x_assum (qspec_then `st` mp_tac) >>
       simp[check_def, type_check_def, assert_def, return_def] >> NO_TAC) >>
  (* bt ≠ Len branch *)
  `∀st res st'. eval_exprs cx es st = (res,st') ⇒
     preserves_immutables_dom cx st st'` by
    (first_x_assum (qspec_then `st` mp_tac) >>
     simp[check_def, type_check_def, assert_def, return_def]) >>
  gvs[bind_def, AllCaseEqs(), return_def, raise_def, get_accounts_def] >>
  Cases_on `evaluate_builtin cx s'³'.accounts bt vs` >>
  gvs[return_def, raise_def]
QED

(* ----- Case: eval_expr (TypeBuiltin tb typ es) ----- *)
Theorem case_TypeBuiltin_imm_dom[local]:
  ∀cx tb typ es.
    (∀s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (TypeBuiltin tb typ es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, type_check_def, assert_def, lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  TRY (Cases_on `evaluate_type_builtin cx tb typ vs` >>
       gvs[return_def, raise_def]) >>
  first_x_assum (qspec_then `st` mp_tac) >>
  simp[check_def, type_check_def, assert_def, return_def]
QED

Theorem check_same_state[local]:
  check b msg s = (r, s') ⇒ s' = s
Proof
  rw[check_def, type_check_def, assert_def]
QED

Theorem type_check_same_state[local]:
  type_check b msg s = (r, s') ⇒ s' = s
Proof
  rw[type_check_def, assert_def]
QED

(* Helper: inner pipeline after run_ext_call result destructuring *)
Theorem extcall_inner_pipeline_imm_dom[local]:
  ∀cx drv tenv ret_type success returnData accounts' tStorage' s res s'.
    (success ∧ returnData = [] ∧ IS_SOME drv ⇒
       ∀st res st'. eval_expr cx (THE drv) st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    do
      x <- check success "ExtCall reverted";
      x <- update_accounts (K accounts');
      x <- update_transient (K tStorage');
      if returnData = [] ∧ IS_SOME drv then eval_expr cx (THE drv)
      else
        do
          ret_val <-
            lift_sum_error (evaluate_abi_decode_return tenv ret_type returnData);
          return (Value ret_val)
        od
    od s = (res, s') ⇒
    preserves_immutables_dom cx s s'
Proof
  rw[bind_def, ignore_bind_def, check_def, type_check_def, assert_def,
     update_accounts_def, update_transient_def, return_def,
     raise_def, lift_sum_def, lift_sum_error_def]
  \\ rpt strip_tac \\ gvs[AllCaseEqs(), preserves_immutables_dom_refl]
  \\ TRY (irule preserves_immutables_dom_eq
          >> Cases_on `evaluate_abi_decode_return tenv ret_type returnData`
          >> gvs[return_def, raise_def] >> NO_TAC)
  \\ irule preserves_immutables_dom_trans
  \\ qmatch_asmsub_abbrev_tac `eval_expr cx (THE drv) s_mid`
  \\ qexists_tac `s_mid`
  \\ conj_tac
  \\ TRY (irule preserves_immutables_dom_eq >> simp[Abbr`s_mid`] >> NO_TAC)
  \\ first_x_assum match_mp_tac \\ metis_tac[]
QED

(* Helper: full ExtCall pipeline preserves immutables dom *)
Theorem extcall_pipeline_preserves_imm_dom[local]:
  ∀cx drv func_name arg_types ret_type target_addr value_opt arg_vals
     caller txParams s res s'.
    (∀ts calldata accounts tStorage success returnData accounts' tStorage'.
       get_self_code cx = SOME ts ⇒
       build_ext_calldata (type_env ts) func_name arg_types arg_vals =
         SOME calldata ⇒
       run_ext_call caller target_addr calldata value_opt accounts tStorage
         txParams = SOME (success, returnData, accounts', tStorage') ⇒
       success ∧ returnData = [] ∧ IS_SOME drv ⇒
       ∀st res st'. eval_expr cx (THE drv) st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    do
      ts <- lift_option (get_self_code cx) "ExtCall get_self_code";
      calldata <-
        lift_option
          (build_ext_calldata (type_env ts) func_name arg_types arg_vals)
          "ExtCall build_calldata";
      accounts <- get_accounts;
      tStorage <- get_transient_storage;
      result <-
        lift_option
          (run_ext_call caller target_addr calldata value_opt accounts
             tStorage txParams) "ExtCall run failed";
      (λ(success,returnData,accounts',tStorage').
           do
             x <- check success "ExtCall reverted";
             x <- update_accounts (K accounts');
             x <- update_transient (K tStorage');
             if returnData = [] ∧ IS_SOME drv then eval_expr cx (THE drv)
             else
               do
                 ret_val <-
                   lift_sum_error
                     (evaluate_abi_decode_return (type_env ts) ret_type
                        returnData);
                 return (Value ret_val)
               od
           od) result
    od s = (res, s') ⇒
    preserves_immutables_dom cx s s'
Proof
  rpt strip_tac
  \\ qpat_x_assum `do _ od _ = _` mp_tac
  \\ simp[bind_def, ignore_bind_def, lift_option_def, lift_option_type_def,
          get_accounts_def, get_transient_storage_def,
          return_def, raise_def]
  \\ Cases_on `get_self_code cx`
  \\ simp[return_def, raise_def, preserves_immutables_dom_refl]
  \\ Cases_on `build_ext_calldata (type_env x) func_name arg_types arg_vals`
  \\ simp[return_def, raise_def, preserves_immutables_dom_refl]
  \\ Cases_on `run_ext_call caller target_addr x' value_opt s.accounts
                 s.tStorage txParams`
  \\ simp[return_def, raise_def, preserves_immutables_dom_refl]
  \\ PairCases_on `x''` \\ simp[]
  \\ strip_tac
  \\ irule extcall_inner_pipeline_imm_dom
  \\ first_assum (irule_at Any)
  \\ rpt strip_tac
  \\ first_x_assum irule \\ simp[]
  \\ qexists_tac `s.accounts` \\ qexists_tac `x''2`
  \\ qexists_tac `s.tStorage` \\ qexists_tac `x''3`
  \\ gvs[]
QED

(* ===== Helper lemmas for ExtCall/IntCall cases ===== *)

Theorem case_ExtCall_imm_dom[local]:
  ∀cx is_static' func_name arg_types ret_type es drv st res st'.
  eval_expr cx
    (Call (ExtCall is_static' (func_name,arg_types,ret_type)) es drv) st =
    (res,st') ⇒
  (∀st res st'.
    eval_exprs cx es st = (res,st') ⇒ preserves_immutables_dom cx st st') ⇒
  (∀s'' vs t s'³' x t' s'⁴' target_addr t'' s'⁵' value_opt arg_vals t'³' tenv
      s'⁶' calldata t'⁴' s'⁷' accounts t'⁵' s'⁸' tStorage t'⁶' txParams caller
      s'⁹' result t'⁷' success returnData accounts' tStorage' s'¹⁰' x' t'⁸'
      s'¹¹' x'' t'⁹' s'¹²' x'³' t'¹⁰'.
    eval_exprs cx es s'' = (INL vs,t) ∧
    check (vs ≠ []) "ExtCall no target" s'³' = (INL x,t') ∧
    lift_option_type (dest_AddressV (HD vs)) "ExtCall target not address" s'⁴' =
    (INL target_addr,t'') ∧
    (if is_static' then return (NONE,TL vs)
     else
       do
         check (TL vs ≠ []) "ExtCall no value";
         v <- lift_option_type (dest_NumV (HD (TL vs))) "ExtCall value not int";
         return (SOME v,TL (TL vs))
       od) s'⁵' = (INL (value_opt,arg_vals),t'³') ∧ tenv = get_tenv cx ∧
    lift_option (build_ext_calldata tenv func_name arg_types arg_vals)
      "ExtCall build_calldata" s'⁶' = (INL calldata,t'⁴') ∧
    get_accounts s'⁷' = (INL accounts,t'⁵') ∧
    get_transient_storage s'⁸' = (INL tStorage,t'⁶') ∧
    txParams = vyper_to_tx_params cx.txn ∧ caller = cx.txn.target ∧
    lift_option
      (run_ext_call caller target_addr calldata value_opt accounts tStorage
         txParams) "ExtCall run failed" s'⁹' = (INL result,t'⁷') ∧
    (success,returnData,accounts',tStorage') = result ∧
    check success "ExtCall reverted" s'¹⁰' = (INL x',t'⁸') ∧
    update_accounts (K accounts') s'¹¹' = (INL x'',t'⁹') ∧
    update_transient (K tStorage') s'¹²' = (INL x'³',t'¹⁰') ∧ returnData = [] ∧
    IS_SOME drv ⇒
    ∀st res st'.
      eval_expr cx (THE drv) st = (res,st') ⇒
      preserves_immutables_dom cx st st') ⇒
  preserves_immutables_dom cx st st'
Proof
  rpt strip_tac
  \\ qpat_x_assum `eval_expr _ _ _ = _` mp_tac
  \\ simp[Once evaluate_def, bind_def, LET_THM]
  \\ Cases_on `eval_exprs cx es st` \\ Cases_on `q`
  \\ simp[return_def, raise_def, preserves_immutables_dom_refl]
  \\ strip_tac
  \\ irule preserves_immutables_dom_trans \\ qexists_tac `r`
  \\ conj_tac >- (last_x_assum match_mp_tac \\ simp[])
  \\ qpat_x_assum `do _ od _ = _` mp_tac
  \\ last_x_assum drule \\ strip_tac
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ drule check_same_state \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rw[] \\ rw[preserves_immutables_dom_refl])
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    last_x_assum(qspec_then`ARB`kall_tac)
    \\ rw[] \\ gvs[preserves_immutables_dom_refl] )
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ qmatch_asmsub_rename_tac`_ s1 = (_, s2)`
  \\ sg `s1 = s2`
  >- (
    last_x_assum(qspec_then`ARB`kall_tac)
    \\ gvs[CaseEq"bool", return_def, COND_RATOR, bind_def]
    \\ gvs[CaseEq"sum", CaseEq"prod"]
    \\ imp_res_tac check_same_state
    \\ imp_res_tac lift_option_same_state
    \\ imp_res_tac lift_option_type_same_state
    \\ gvs[] )
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- rw[preserves_immutables_dom_refl]
  \\ pairarg_tac
  \\ asm_simp_tac std_ss []
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ drule lift_option_same_state
  \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    last_x_assum(qspec_then`ARB`kall_tac)
    \\ rw[] \\ gvs[preserves_immutables_dom_refl] )
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ qmatch_asmsub_rename_tac`_ s2 = (_, s3)`
  \\ sg `s2 = s3`
  >- (
    last_x_assum(qspec_then`ARB`kall_tac)
    \\ gvs[get_accounts_def, return_def] )
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- rw[preserves_immutables_dom_refl]
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ qmatch_asmsub_rename_tac`_ s3 = (_, s4)`
  \\ sg `s3 = s4`
  >- (
    last_x_assum(qspec_then`ARB`kall_tac)
    \\ gvs[get_transient_storage_def, return_def] )
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- rw[preserves_immutables_dom_refl]
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ drule lift_option_same_state
  \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    last_x_assum(qspec_then`ARB`kall_tac)
    \\ rw[] \\ gvs[preserves_immutables_dom_refl] )
  \\ pairarg_tac \\ asm_simp_tac std_ss []
  \\ last_x_assum drule \\ strip_tac
  \\ strip_tac
  \\ irule extcall_inner_pipeline_imm_dom
  \\ first_assum (irule_at Any)
  \\ rpt strip_tac
  \\ first_x_assum $ drule_then drule
  \\ gvs[ignore_bind_def]
  \\ disch_then $ funpow 4 drule_then drule
  \\ gvs[bind_def, CaseEq"prod", CaseEq"sum"]
  \\ gvs[update_accounts_def, update_transient_def, return_def,
         check_def, type_check_def, raise_def, assert_def]
QED

Theorem case_IntCall_imm_dom[local]:
  ∀cx src_id_opt fn es vs st res st'.
  eval_expr cx (Call (IntCall (src_id_opt,fn)) es vs) st = (res,st') ⇒
  (∀s'' x t s'³' ts t' s'⁴' tup t'' stup args sstup dflts sstup2 ret body' s'⁵'
      x' t'³'.
    check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
    (INL ts,t') ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ stup = SND tup ∧
    args = FST stup ∧ sstup = SND stup ∧ dflts = FST sstup ∧
    sstup2 = SND sstup ∧ ret = FST sstup2 ∧ body' = SND sstup2 ∧
    type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
      "IntCall args length" s'⁵' = (INL x',t'³') ⇒
    ∀st res st'.
      eval_exprs cx es st = (res,st') ⇒ preserves_immutables_dom cx st st') ⇒
  (∀s'' x t s'³' ts t' s'⁴' tup t'' stup args sstup dflts sstup2 ret body' s'⁵'
      x' t'³' s'⁶' vs t'⁴' es' cx'.
    check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
    (INL ts,t') ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ stup = SND tup ∧
    args = FST stup ∧ sstup = SND stup ∧ dflts = FST sstup ∧
    sstup2 = SND sstup ∧ ret = FST sstup2 ∧ body' = SND sstup2 ∧
    type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
      "IntCall args length" s'⁵' = (INL x',t'³') ∧
    eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
    es' = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cx' = cx with stk updated_by CONS (src_id_opt,fn) ⇒
    ∀st res st'.
      eval_exprs cx' es' st = (res,st') ⇒ preserves_immutables_dom cx' st st') ⇒
  (∀s'' x t s'³' ts t' s'⁴' tup t'' stup args sstup dflts sstup2 ret ss s'⁵' x'
      t'³' s'⁶' vs t'⁴' needed_dflts cxd s'⁷' dflt_vs t'⁵' all_tenv s'⁸' env
      t'⁶' s'⁹' prev t'⁷' s'¹⁰' rtv t'⁸' s'¹¹' cx' t'⁹'.
    check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
    (INL ts,t') ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ stup = SND tup ∧
    args = FST stup ∧ sstup = SND stup ∧ dflts = FST sstup ∧
    sstup2 = SND sstup ∧ ret = FST sstup2 ∧ ss = SND sstup2 ∧
    type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
      "IntCall args length" s'⁵' = (INL x',t'³') ∧
    eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
    needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    eval_exprs cxd needed_dflts s'⁷' = (INL dflt_vs,t'⁵') ∧
    all_tenv = get_tenv cx ∧
    lift_option_type (bind_arguments all_tenv args (vs ⧺ dflt_vs))
      "IntCall bind_arguments" s'⁸' = (INL env,t'⁶') ∧
    get_scopes s'⁹' = (INL prev,t'⁷') ∧
    lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'¹⁰' =
    (INL rtv,t'⁸') ∧
    push_function (src_id_opt,fn) env cx s'¹¹' = (INL cx',t'⁹') ⇒
    ∀st res st'.
      eval_stmts cx' ss st = (res,st') ⇒ preserves_immutables_dom cx' st st') ⇒
  preserves_immutables_dom cx st st'
Proof
  rpt strip_tac
  \\ qpat_x_assum `eval_expr _ _ _ = _` mp_tac
  \\ simp[Once evaluate_def, bind_def, LET_THM]
  \\ rewrite_tac[bind_def, ignore_bind_def]
  (* Peel: check recursion *)
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule type_check_same_state, drule check_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rw[] \\ rw[preserves_immutables_dom_refl])
  (* Peel: lift_option get_module_code *)
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac))
      \\ rw[] \\ gvs[preserves_immutables_dom_refl])
  (* Peel: lift_option lookup_callable_function *)
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac))
      \\ gvs[preserves_immutables_dom_refl])
  (* Peel: check args length *)
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule type_check_same_state, drule check_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac))
      \\ rw[] \\ gvs[preserves_immutables_dom_refl])
  (* eval_exprs cx es: specialize first IH using drule_all *)
  \\ BasicProvers.TOP_CASE_TAC
  \\ last_x_assum $ funpow 2 drule_then drule
  \\ simp_tac std_ss []
  \\ disch_then $ drule_then drule
  \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac)) \\ strip_tac \\ gvs[])
  (* eval_exprs cx es succeeded *)
  \\ BasicProvers.TOP_CASE_TAC
  \\ last_x_assum $ funpow 2 drule_then drule
  \\ simp_tac std_ss []
  \\ disch_then $ funpow 2 drule_then drule
  \\ strip_tac
  \\ drule_at Any (iffLR preserves_immutables_dom_txn_eq)
  \\ disch_then(qspec_then`cx`mp_tac)
  \\ impl_tac >- rw[] \\ strip_tac
  \\ drule_then drule preserves_immutables_dom_trans
  \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac)) \\ strip_tac \\ gvs[])
  (* INL branch: peel remaining pipeline *)
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac)) \\ strip_tac \\ gvs[])
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ first_x_assum $ funpow 2 drule_then drule
  \\ simp_tac std_ss []
  \\ disch_then $ funpow 3 drule_then drule
  \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac))
      \\ strip_tac \\ gvs[get_scopes_def, return_def])
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac))
      \\ strip_tac \\ gvs[get_scopes_def, return_def])
  \\ first_x_assum $ drule_then drule
  \\ simp[bind_def, push_function_def, return_def, finally_def, try_def]
  \\ CASE_TAC
  \\ disch_then drule
  \\ qmatch_goalsub_rename_tac`preserves_immutables_dom _ _ s2`
  \\ strip_tac
  \\ qmatch_goalsub_rename_tac`preserves_immutables_dom _ _ s3`
  \\ strip_tac
  \\ sg `s2.immutables = s3.immutables`
  >- (
    gvs[CaseEq"sum",CaseEq"prod", bind_def, pop_function_def, set_scopes_def,
        return_def, ignore_bind_def]
    \\ imp_res_tac lift_option_same_state >> imp_res_tac lift_option_type_same_state
    \\ imp_res_tac handle_function_immutables
    \\ gvs[raise_def] )
  \\ gvs[get_scopes_def, return_def]
  \\ irule preserves_immutables_dom_trans
  \\ goal_assum drule
  \\ irule preserves_immutables_dom_trans
  \\ qexists_tac`s2`
  \\ reverse conj_tac
  >- ( rw[preserves_immutables_dom_def] \\ gvs[] )
  \\ drule_at Any $ iffLR preserves_immutables_dom_txn_eq
  \\ disch_then(qspec_then`cx`mp_tac)
  \\ rw[]
  \\ irule preserves_immutables_dom_trans
  \\ goal_assum $ drule_at Any
  \\ rw[preserves_immutables_dom_def]
  \\ gvs[]
QED

(* ===== Main Mutual Induction ===== *)

Theorem immutables_dom_mutual[local]:
  (∀cx s st res st'. eval_stmt cx s st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx ss st res st'. eval_stmts cx ss st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx it st res st'. eval_iterator cx it st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx g st res st'. eval_target cx g st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx gs st res st'. eval_targets cx gs st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx bt st res st'. eval_base_target cx bt st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx nm body vs st res st'. eval_for cx nm body vs st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx e st res st'. eval_expr cx e st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx es st res st'. eval_exprs cx es st = (res, st') ⇒ preserves_immutables_dom cx st st')
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt strip_tac
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  >- (drule_all case_Return_SOME_imm_dom >> simp[])
  >- (drule_all case_Raise_imm_dom >> simp[])
  >- (drule_all case_Assert_imm_dom >> simp[])
  >- (drule_all case_Log_imm_dom >> simp[])
  >- (drule_all case_AnnAssign_imm_dom >> simp[])
  >- (drule_all case_Append_imm_dom >> simp[])
  >- (drule_all case_Assign_imm_dom >> simp[])
  >- (drule_all case_AugAssign_imm_dom >> simp[])
  >- (drule_all case_If_imm_dom >> simp[])
  >- (drule_all case_For_imm_dom >> simp[])
  >- (drule_all case_Expr_imm_dom >> simp[])
  >- (gvs[evaluate_def, return_def, preserves_immutables_dom_refl])
  >- (drule_all case_eval_stmts_cons_imm_dom >> simp[])
  >- (drule_all case_Array_imm_dom >> simp[])
  >- (drule_all case_Range_imm_dom >> simp[])
  >- (drule_all case_BaseTarget_imm_dom >> simp[])
  >- (qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
       simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
       rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
       first_x_assum irule >> first_assum (irule_at Any))
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- (drule_all case_eval_targets_cons_imm_dom >> simp[])
  >- (drule_all case_NameTarget_imm_dom >> simp[])
  >- (qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
       simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
            get_scopes_def, LET_THM, get_immutables_def, get_address_immutables_def,
            lift_option_def, lift_option_type_def, lift_sum_def] >>
       rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
       first_x_assum irule >> first_assum (irule_at Any))
  >- (drule_all case_AttributeTarget_imm_dom >> simp[])
  >- (drule_all case_SubscriptTarget_imm_dom >> simp[])
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- (drule_all case_eval_for_cons_imm_dom >> simp[])
  >- (drule_all case_Name_imm_dom >> simp[])
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
       simp[Once evaluate_def] >> strip_tac >>
       imp_res_tac lookup_global_immutables >>
       irule preserves_immutables_dom_eq >> gvs[])
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
       simp[Once evaluate_def] >> strip_tac >>
       imp_res_tac lookup_flag_mem_immutables >>
       irule preserves_immutables_dom_eq >> gvs[])
  >- (drule_all case_IfExp_imm_dom >> simp[])
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
       simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
            get_scopes_def, get_immutables_def, get_address_immutables_def,
            lift_option_def, lift_option_type_def, lift_sum_def, LET_THM, check_def, type_check_def, assert_def,
            ignore_bind_def, get_accounts_def, lift_sum_def,
            get_transient_storage_def, update_accounts_def, update_transient_def] >>
       rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
       first_x_assum irule >> first_assum (irule_at Any) >>
            simp[check_def, type_check_def, assert_def])
  >- (drule_all case_Subscript_imm_dom >> simp[])
  >- (drule_all case_Attribute_imm_dom >> simp[])
  >- (drule_all case_Builtin_imm_dom >> simp[])
  >- (drule_all case_Pop_imm_dom >> simp[])
  >- (drule_all case_TypeBuiltin_imm_dom >> simp[])
  >- (drule_all case_Send_imm_dom >> simp[])
  >- (drule_all case_ExtCall_imm_dom >> simp[])
  >- (drule_all case_IntCall_imm_dom >> simp[])
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- (drule_all case_eval_exprs_cons_imm_dom >> simp[])
QED

(* ===== Main theorems ===== *)

Theorem eval_expr_preserves_immutables_addr_dom:
  ∀cx e st res st'.
    eval_expr cx e st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_mutual, preserves_immutables_dom_def]
QED

Theorem eval_expr_preserves_immutables_dom:
  ∀cx e st res st'.
    eval_expr cx e st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 8 immutables_dom_mutual) >>
  rw[preserves_immutables_dom_def]
QED

Theorem eval_base_target_preserves_immutables_addr_dom:
  ∀cx bt st res st'.
    eval_base_target cx bt st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_mutual, preserves_immutables_dom_def]
QED

Theorem eval_base_target_preserves_immutables_dom:
  ∀cx bt st res st'.
    eval_base_target cx bt st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 6 immutables_dom_mutual) >>
  rw[preserves_immutables_dom_def]
QED

Theorem eval_exprs_preserves_immutables_addr_dom:
  ∀cx es st res st'.
    eval_exprs cx es st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_mutual, preserves_immutables_dom_def]
QED

Theorem eval_stmts_preserves_immutables_addr_dom:
  ∀cx ss st res st'.
    eval_stmts cx ss st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_mutual, preserves_immutables_dom_def]
QED

Theorem eval_stmts_preserves_immutables_dom:
  ∀cx ss st res st'.
    eval_stmts cx ss st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 2 immutables_dom_mutual) >>
  rw[preserves_immutables_dom_def]
QED
