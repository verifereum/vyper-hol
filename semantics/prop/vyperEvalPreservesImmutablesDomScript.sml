Theory vyperEvalPreservesImmutablesDom

Ancestors
  vyperInterpreter vyperLookup vyperScopePreservation vyperAssignTarget
    vyperEvalExprPreservesScopesDom

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
    (∀n imms imms'.
       ALOOKUP st.immutables cx.txn.target = SOME imms ∧
       ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
       (IS_SOME (FLOOKUP (get_source_immutables NONE imms) n) ⇔
        IS_SOME (FLOOKUP (get_source_immutables NONE imms') n)))
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
  Cases_on `ALOOKUP st2.immutables cx.txn.target` >> gvs[] >>
  metis_tac[]
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
     check_def, assert_def, update_accounts_def] >> gvs[raise_def] >> simp[]
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
       lift_option_def, lift_sum_def, AllCaseEqs(), raise_def, LET_THM,
       ignore_bind_def, set_scopes_def] >>
  rpt CASE_TAC >> gvs[return_def, raise_def, set_scopes_def, bind_def] >>
  PairCases_on `x` >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def, set_scopes_def] >>
  rpt CASE_TAC >> gvs[return_def, raise_def, set_scopes_def] >>
  rpt strip_tac >> gvs[]
QED

(* Helper: the HashMap do-block in assign_target preserves immutables *)
Theorem hashmap_do_block_immutables[local]:
  ∀cx b c t' v' x key_types remaining_subs final_type h t ao r res st'.
    (λ(final_type,key_types,remaining_subs).
       do
         final_slot <-
           case
             compute_hashmap_slot c (t'::key_types)
               (h::TAKE (LENGTH t − LENGTH remaining_subs) t)
           of
             NONE => raise (Error "assign_target compute_hashmap_slot")
           | SOME v => return v;
         final_tv <-
           case evaluate_type (type_env x) final_type of
             NONE => raise (Error "assign_target evaluate_type")
           | SOME v => return v;
         current_val <- read_storage_slot cx b final_slot final_tv;
         new_val <-
           case assign_subscripts current_val remaining_subs ao of
             INL v => return v
           | INR str => raise (Error str);
         x <- write_storage_slot cx b final_slot final_tv new_val;
         return (HashMapRef b c t' v')
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
  Cases_on `evaluate_type (type_env x) final_type` >>
  gvs[return_def, raise_def] >>
  rename1 `evaluate_type _ _ = SOME tv` >>
  (* Step 3: read_storage_slot *)
  `∃rr sr. read_storage_slot cx b slot tv r = (rr, sr)` by
    metis_tac[pairTheory.PAIR] >>
  Cases_on `rr` >> gvs[] >>
  imp_res_tac read_storage_slot_immutables >>
  (* Step 4: assign_subscripts *)
  Cases_on `assign_subscripts x' remaining_subs ao` >>
  gvs[return_def, raise_def] >>
  rename1 `assign_subscripts _ _ _ = INL new_val` >>
  (* Step 5: write_storage_slot *)
  `∃rw sw. write_storage_slot cx b slot tv new_val sr = (rw, sw)` by
    metis_tac[pairTheory.PAIR] >>
  Cases_on `rw` >> gvs[] >>
  imp_res_tac write_storage_slot_immutables >> gvs[]
QED

Theorem assign_target_imm_dom_TopLevelVar[local]:
  ∀cx src_id_opt id is ao st res st'.
    assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) is) ao st = (res, st') ⇒
    st'.immutables = st.immutables
Proof
  rpt strip_tac >>
  qpat_x_assum `_ = (_, _)` mp_tac >>
  simp[Once assign_target_def, AllCaseEqs(), return_def, raise_def,
       bind_def, lift_option_def, lift_sum_def, ignore_bind_def] >>
  Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def] >>
  Cases_on `lookup_global cx src_id_opt (string_to_num id) st` >>
  Cases_on `q` >> gvs[return_def, raise_def] >>
  imp_res_tac lookup_global_immutables >> gvs[] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def, bind_def] >>
  rpt strip_tac >> gvs[] >>
  (* subgoals 1-2: set_global case expression *)
  TRY (
    `∃rsg ssg. set_global cx src_id_opt (string_to_num id) x' r = (rsg, ssg)` by
      metis_tac[pairTheory.PAIR] >>
    Cases_on `rsg` >> gvs[] >>
    imp_res_tac set_global_immutables >> gvs[] >> NO_TAC) >>
  (* HashMap branch *)
  Cases_on `split_hashmap_subscripts v t` >> gvs[return_def, raise_def] >>
  PairCases_on `x'` >>
  imp_res_tac hashmap_do_block_immutables >> gvs[]
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
  simp[bind_def, get_immutables_def, return_def, lift_option_def, lift_sum_def,
       AllCaseEqs(), raise_def, set_immutable_def, get_address_immutables_def,
       set_address_immutables_def] >>
  rpt strip_tac >>
  gvs[return_def, raise_def, AllCaseEqs(), preserves_immutables_dom_refl] >>
  (* resolve error paths by case-splitting on each case expression *)
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[return_def, raise_def, preserves_immutables_dom_refl] >>
  Cases_on `FLOOKUP (get_source_immutables NONE imms) (string_to_num id)` >>
  gvs[return_def, raise_def, preserves_immutables_dom_refl] >>
  Cases_on `assign_subscripts a (REVERSE is) ao` >>
  gvs[return_def, raise_def, preserves_immutables_dom_refl] >>
  Cases_on `ALOOKUP s''.immutables cx.txn.target` >>
  gvs[return_def, raise_def, preserves_immutables_dom_refl] >>
  (* success path: prove preserves_immutables_dom for the updated state *)
  simp[preserves_immutables_dom_def] >> conj_tac
  >- (rpt strip_tac >>
      Cases_on `cx.txn.target = tgt` >>
      gvs[alistTheory.ALOOKUP_ADELKEY])
  >> gen_tac >> rename1 `IS_SOME (FLOOKUP _ n)` >>
     simp[set_source_immutables_def, get_source_immutables_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `n = string_to_num id` >>
     gvs[get_source_immutables_def]
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
  simp[bind_def, check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  first_x_assum irule >> metis_tac[]
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
  simp[Once assign_target_def, bind_def, get_Value_def,
       AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >|
  [(* INL/INL case: st -> s'' -> s'³' -> s'⁴' *)
   irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >> conj_tac
   >- (irule preserves_immutables_dom_trans >> qexists_tac `s''` >> conj_tac
       >- (first_assum (qspecl_then [`st`, `INL tw`, `s''`] mp_tac) >> simp[])
       >- (irule preserves_immutables_dom_eq >> gvs[]))
   >- (first_x_assum (qspecl_then [`s'³'`, `INL ws`, `s'⁴'`] mp_tac) >> simp[]),
   (* INL/INR case: st -> s'' -> s'³' -> s'⁴' *)
   irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >> conj_tac
   >- (irule preserves_immutables_dom_trans >> qexists_tac `s''` >> conj_tac
       >- (first_assum (qspecl_then [`st`, `INL tw`, `s''`] mp_tac) >> simp[])
       >- (irule preserves_immutables_dom_eq >> gvs[]))
   >- (first_x_assum (qspecl_then [`s'³'`, `INR e`, `s'⁴'`] mp_tac) >> simp[]),
   (* INR case: st -> s'' -> s'³' *)
   irule preserves_immutables_dom_trans >> qexists_tac `s''` >> conj_tac
   >- (first_assum (qspecl_then [`st`, `INL tw`, `s''`] mp_tac) >> simp[])
   >- (irule preserves_immutables_dom_eq >> gvs[])]
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

(* ===== Helper: finally preserves immutables ===== *)

Theorem finally_preserves_imm_dom[local]:
  ∀f cleanup cx st res st'.
    finally f cleanup st = (res, st') ∧
    (∀st1 res1 st1'. f st1 = (res1, st1') ⇒ preserves_immutables_dom cx st1 st1') ∧
    (∀st1 res1 st1'. cleanup st1 = (res1, st1') ⇒ st1'.immutables = st1.immutables) ⇒
    preserves_immutables_dom cx st st'
Proof
  rw[finally_def, AllCaseEqs()] >> gvs[] >> (
    irule preserves_immutables_dom_trans >> qexists_tac `s''` >> conj_tac
    >- (first_x_assum drule >> simp[])
    >- (gvs[ignore_bind_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
        irule preserves_immutables_dom_eq >> first_x_assum drule >> simp[])
  )
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
  ∀cx src_id_opt fname body env st0 vs sevl fres sfnl es prev.
    (∀st res st'.
       eval_exprs cx es st = (res,st') ⇒ preserves_immutables_dom cx st st') ∧
    (∀cx' body' st res st'.
       eval_stmts cx' body' st = (res,st') ⇒ preserves_immutables_dom cx' st st') ∧
    eval_exprs cx es st0 = (INL vs, sevl) ∧
    finally
      (try (bind (eval_stmts (cx with stk updated_by CONS (src_id_opt,fname))
         body) (λx. return NoneV)) handle_function)
      (pop_function prev)
      (sevl with scopes := [env]) = (fres, sfnl) ⇒
    preserves_immutables_dom cx st0 sfnl
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `sevl` >> conj_tac >- gvs[] >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, AllCaseEqs(), pop_function_def, set_scopes_def,
       return_def, ignore_bind_def, bind_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_eq, preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sevl with scopes := [env]` >>
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
  imp_res_tac handle_function_immutables >> gvs[]
QED

Theorem case_IntCall_imm_dom_inner_specific[local]:
  ∀cx src_id_opt fname body env st0 vs sevl fres sfnl es prev.
    (∀st res st'.
       eval_exprs cx es st = (res,st') ⇒ preserves_immutables_dom cx st st') ∧
    (∀st res st'.
       eval_stmts (cx with stk updated_by CONS (src_id_opt,fname)) body st =
       (res,st') ⇒
       preserves_immutables_dom
         (cx with stk updated_by CONS (src_id_opt,fname)) st st') ∧
    eval_exprs cx es st0 = (INL vs, sevl) ∧
    finally
      (try (bind (eval_stmts (cx with stk updated_by CONS (src_id_opt,fname))
         body) (λx. return NoneV)) handle_function)
      (pop_function prev)
      (sevl with scopes := [env]) = (fres, sfnl) ⇒
    preserves_immutables_dom cx st0 sfnl
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `sevl` >> conj_tac >- gvs[] >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, AllCaseEqs(), pop_function_def, set_scopes_def,
       return_def, ignore_bind_def, bind_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_eq, preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sevl with scopes := [env]` >>
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
  imp_res_tac handle_function_immutables >> gvs[]
QED

Theorem case_IntCall_imm_dom_unconditional[local]:
  ∀src_id_opt fname es cx.
    (∀st res st'.
       eval_exprs cx es st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
    (∀cx' body st res st'.
       eval_stmts cx' body st = (res, st') ⇒
       preserves_immutables_dom cx' st st') ⇒
    ∀st res st'.
      eval_expr cx (Call (IntCall (src_id_opt, fname)) es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def, check_def, assert_def,
       lift_option_def, lift_sum_def, get_scopes_def, push_function_def, LET_THM] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def,
       preserves_immutables_dom_refl, preserves_immutables_dom_eq]) >>
  irule case_IntCall_imm_dom_inner >> gvs[] >> metis_tac[]
QED

(* ===== Helper lemmas for complex induction cases ===== *)

(* Helper: handle_loop_exception preserves immutables *)
Theorem handle_loop_exception_immutables[local]:
  ∀exc st res st'.
    handle_loop_exception exc st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  Cases_on `exc` >> simp[handle_loop_exception_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `b` >> gvs[handle_loop_exception_def, return_def, raise_def]
QED

(* Helper: push_scope_with_var preserves immutables *)
Theorem push_scope_with_var_immutables[local]:
  ∀nm v st res st'.
    push_scope_with_var nm v st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  simp[push_scope_with_var_def, return_def]
QED

(* Helper: pop_scope preserves immutables *)
Theorem pop_scope_immutables[local]:
  ∀st res st'.
    pop_scope st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  rpt strip_tac >> gvs[pop_scope_def, AllCaseEqs(), return_def, raise_def]
QED

(* Helper: push_scope preserves immutables *)
Theorem push_scope_immutables[local]:
  ∀st res st'.
    push_scope st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  simp[push_scope_def, return_def]
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
  imp_res_tac get_Value_immutables >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[preserves_immutables_dom_eq]
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
       lift_option_def, return_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >>
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
     simp[bind_def, AllCaseEqs(), return_def, raise_def, lift_option_def] >>
     rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
     imp_res_tac get_Value_immutables >>
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
       new_variable_def, LET_THM, get_scopes_def, check_def, assert_def,
       set_scopes_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[preserves_immutables_dom_eq] >> cheat
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
  simp[bind_def, AllCaseEqs(), return_def, raise_def, lift_option_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  Cases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac get_Value_immutables >>
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
  imp_res_tac get_Value_immutables >>
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
  simp[bind_def, AllCaseEqs(), return_def, raise_def, lift_option_def,
       lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  Cases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac get_Value_immutables >>
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
       ignore_bind_def, check_def, assert_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  (* Derive unconditional IH for eval_for from the conditional one *)
  first_x_assum (drule_then mp_tac) >>
  simp[check_def, assert_def] >> strip_tac >>
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
  imp_res_tac get_Value_immutables >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
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
  gvs[] >> cheat
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
       lift_option_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[preserves_immutables_dom_eq] >> cheat
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
  imp_res_tac get_Value_immutables >>
  first_x_assum (qspecl_then [`st`, `tv1`, `s''`, `s''`, `v1`, `t`] mp_tac) >>
  simp[] >> rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `t` >>
  gvs[preserves_immutables_dom_eq] >> cheat
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
  gvs[] >> cheat
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
       lift_option_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >>
  first_x_assum (qspecl_then [`st`, `loc`, `sbs`, `s''`] mp_tac) >> simp[] >>
  strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `t'` >>
  gvs[preserves_immutables_dom_eq] >> cheat
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
  cheat
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
  irule preserves_immutables_dom_trans >>
  qexists_tac ‘s'' with scopes updated_by CONS FEMPTY’ >>
  conj_tac >- (irule preserves_immutables_dom_eq >> simp[]) >>
  cheat
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
  cheat
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
  imp_res_tac get_Value_immutables >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[preserves_immutables_dom_eq]
  >> cheat
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
       lift_option_def, lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac (cj 1 assign_target_imm_dom_any) >>
  imp_res_tac get_Value_immutables >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `t` >>
  gvs[preserves_immutables_dom_eq]
  >> cheat
QED

(* ----- Case 41: eval_expr (Call Send es) ----- *)
Theorem case_Send_imm_dom[local]:
  ∀cx es.
    (∀s'' x t. check (LENGTH es = 2) "Send args" s'' = (INL x,t) ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Call Send es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  cheat
QED

(* ----- Case 45: eval_exprs (e::es) ----- *)
Theorem case_eval_exprs_cons_imm_dom[local]:
  ∀cx e es.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv t s'³' v t'.
       eval_expr cx e s'' = (INL tv,t) ∧ get_Value tv s'³' = (INL v,t') ⇒
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
  imp_res_tac get_Value_immutables >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `t` >>
  cheat
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
  cheat
QED

(* ----- Case: eval_base_target (NameTarget id) ----- *)
Theorem case_NameTarget_imm_dom[local]:
  ∀cx id.
    ∀st res st'.
      eval_base_target cx (NameTarget id) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  cheat
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
  cheat
QED

(* ----- Case: eval_expr (Name id) ----- *)
Theorem case_Name_imm_dom[local]:
  ∀cx id.
    ∀st res st'.
      eval_expr cx (Name id) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  cheat
QED

(* ----- Case: eval_expr (Builtin bt es) ----- *)
Theorem case_Builtin_imm_dom[local]:
  ∀cx bt es.
    (∀s'' x t.
       check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Builtin bt es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  cheat
QED

(* ----- Case: eval_expr (TypeBuiltin tb typ es) ----- *)
Theorem case_TypeBuiltin_imm_dom[local]:
  ∀cx tb typ es.
    (∀s'' x t.
       check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (TypeBuiltin tb typ es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  cheat
QED

(* ----- Case: eval_expr (Call (ExtCall ...) es) ----- *)
Theorem case_ExtCall_imm_dom[local]:
  ∀cx is_static' func_name arg_types ret_type es.
    (∀st res st'.
       eval_exprs cx es st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Call (ExtCall is_static' (func_name,arg_types,ret_type)) es)
        st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  cheat
QED

(* ----- Case: eval_expr (Call (IntCall ...) es) - updated ----- *)
Theorem case_IntCall_imm_dom[local]:
  ∀src_id_opt fn es cx.
    (∀s'' x t s'³' ts t' s'⁴' tup t'' stup args sstup ret body' s'⁵' x'
        t'³'.
       check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
       lift_option (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'³' = (INL ts,t') ∧
       lift_option (lookup_function fn Internal ts)
         "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ stup = SND tup ∧
       args = FST stup ∧ sstup = SND stup ∧ ret = FST sstup ∧
       body' = SND sstup ∧
       check (LENGTH args = LENGTH es) "IntCall args length" s'⁵' =
       (INL x',t'³') ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀s'' x t s'³' ts t' s'⁴' tup t'' stup args sstup ret ss s'⁵' x' t'³'
        s'⁶' vs t'⁴' tenv all_mods all_tenv s'⁷' env t'⁵' s'⁸' prev t'⁶'
        s'⁹' rtv t'⁷' s'¹⁰' cx' t'⁸'.
       check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
       lift_option (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'³' = (INL ts,t') ∧
       lift_option (lookup_function fn Internal ts)
         "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ stup = SND tup ∧
       args = FST stup ∧ sstup = SND stup ∧ ret = FST sstup ∧
       ss = SND sstup ∧
       check (LENGTH args = LENGTH es) "IntCall args length" s'⁵' =
       (INL x',t'³') ∧ eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
       tenv = type_env ts ∧
       all_mods =
       (case ALOOKUP cx.sources cx.txn.target of NONE => [] | SOME m => m) ∧
       all_tenv = type_env_all_modules all_mods ∧
       lift_option (bind_arguments tenv args vs) "IntCall bind_arguments"
         s'⁷' = (INL env,t'⁵') ∧ get_scopes s'⁸' = (INL prev,t'⁶') ∧
       lift_option (evaluate_type all_tenv ret) "IntCall eval ret" s'⁹' =
       (INL rtv,t'⁷') ∧
       push_function (src_id_opt,fn) env cx s'¹⁰' = (INL cx',t'⁸') ⇒
       ∀st res st'.
         eval_stmts cx' ss st = (res,st') ⇒
         preserves_immutables_dom cx' st st') ⇒
    ∀st res st'.
      eval_expr cx (Call (IntCall (src_id_opt,fn)) es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  cheat
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
            lift_option_def, lift_sum_def] >>
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
            lift_option_def, lift_sum_def, LET_THM, check_def, assert_def,
            ignore_bind_def, get_accounts_def, lift_sum_def,
            get_transient_storage_def, update_accounts_def, update_transient_def] >>
       rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
       first_x_assum irule >> first_assum (irule_at Any) >>
            simp[check_def, assert_def])
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
(* OLD PROOF of immutables_dom_mutual (before conditional IH reformulation):
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt strip_tac
  (* 1: Pass *)
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  (* 2: Continue *)
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  (* 3: Break *)
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  (* 4: Return NONE *)
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  (* 5: Return (SOME e) *)
  >- (drule_all case_Return_SOME_imm_dom >> simp[])
  (* 6: Raise e *)
  >- (drule_all case_Raise_imm_dom >> simp[])
  (* 7: Assert e se *)
  >- (irule case_Assert_imm_dom >> metis_tac[])
  (* 8: Log id es *)
  >- (drule_all case_Log_imm_dom >> simp[])
  (* 9: AnnAssign id typ e *)
  >- (drule_all case_AnnAssign_imm_dom >> simp[])
  (* 10: Append bt e *)
  >- (irule case_Append_imm_dom >> metis_tac[])
  (* 11: Assign g e *)
  >- (irule case_Assign_imm_dom >> metis_tac[])
  (* 12: AugAssign bt bop e *)
  >- (irule case_AugAssign_imm_dom >> metis_tac[])
  (* 13: If e ss1 ss2 *)
  >- (irule case_If_imm_dom >> qexistsl ['e', 'res', 'ss', 'ss''] >> rpt strip_tac >> gvs[] >> cheat)
  (* 14: For id typ it n body *)
  >- (irule case_For_imm_dom >> metis_tac[])
  (* 15: Expr e *)
  >- (drule_all case_Expr_imm_dom >> simp[])
  (* 16: eval_stmts [] *)
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  (* 17: eval_stmts (s::ss) *)
  >- (irule case_eval_stmts_cons_imm_dom >> metis_tac[])
  (* 18: eval_iterator (Array e) *)
  >- (drule_all case_Array_imm_dom >> simp[])
  (* 19: eval_iterator (Range e1 e2) *)
  >- (irule case_Range_imm_dom >> metis_tac[])
  (* 20: eval_target (BaseTarget bt) *)
  >- (qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      first_x_assum irule >> first_assum (irule_at Any))
  (* 21: eval_target (TupleTarget gs) *)
  >- (qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      first_x_assum irule >> first_assum (irule_at Any))
  (* 22: eval_targets [] *)
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  (* 23: eval_targets (g::gs) *)
  >- (irule case_eval_targets_cons_imm_dom >> metis_tac[])
  (* 24: eval_base_target (NameTarget id) *)
  >- (qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
           get_scopes_def, LET_THM, get_immutables_def, get_address_immutables_def,
           lift_option_def, lift_sum_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl])
  (* 25: eval_base_target (TopLevelNameTarget) *)
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  (* 26: eval_base_target (AttributeTarget bt id) *)
  >- (qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      first_x_assum irule >> first_assum (irule_at Any))
  (* 27: eval_base_target (SubscriptTarget bt e) *)
  >- (irule case_SubscriptTarget_imm_dom >> metis_tac[])
  (* 28: eval_for [] *)
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  (* 29: eval_for (v::vs) *)
  >- (irule case_eval_for_cons_imm_dom >> metis_tac[])
  (* 30: eval_expr (Name id) *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
           get_scopes_def, get_immutables_def, get_address_immutables_def,
           lift_option_def, lift_sum_def, LET_THM] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl])
  (* 31: eval_expr (TopLevelName) *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def] >> strip_tac >>
      imp_res_tac lookup_global_immutables >>
      irule preserves_immutables_dom_eq >> gvs[])
  (* 32: eval_expr (FlagMember) *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def] >> strip_tac >>
      imp_res_tac lookup_flag_mem_immutables >>
      irule preserves_immutables_dom_eq >> gvs[])
  (* 33: eval_expr (IfExp e e' e'') *)
  >- (irule case_IfExp_imm_dom >> metis_tac[])
  (* 34: eval_expr (Literal l) *)
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  (* 35: eval_expr (StructLit) *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
           LET_THM] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      first_x_assum irule >> first_assum (irule_at Any))
  (* 36: eval_expr (Subscript e1 e2) *)
  >- (irule case_Subscript_imm_dom >> metis_tac[])
  (* 37: eval_expr (Attribute e id) *)
  >- (drule_all case_Attribute_imm_dom >> simp[])
  (* 38: eval_expr (Builtin bt es) *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
           check_def, assert_def, ignore_bind_def, get_accounts_def,
           lift_sum_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      first_x_assum irule >> first_assum (irule_at Any) >>
      simp[check_def, assert_def])
  (* 39: eval_expr (Pop bt) *)
  >- (drule_all case_Pop_imm_dom >> simp[])
  (* 40: eval_expr (TypeBuiltin tb typ es) *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
           check_def, assert_def, ignore_bind_def, lift_sum_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      first_x_assum irule >> first_assum (irule_at Any) >>
      simp[check_def, assert_def])
  (* 41: eval_expr (Call Send es) *)
  >- (irule case_Send_imm_dom >> metis_tac[])
  (* 42: eval_expr (Call (ExtCall is_static sig) es) *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
           check_def, assert_def, ignore_bind_def, lift_option_def, lift_sum_def,
           get_accounts_def, get_transient_storage_def,
           update_accounts_def, update_transient_def, LET_THM] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      first_x_assum irule >> first_assum (irule_at Any))
  (* 43: eval_expr (Call (IntCall (src_id_opt, fn)) es) *)
  >- (irule case_IntCall_imm_dom >> metis_tac[])
  (* 44: eval_exprs [] *)
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  (* 45: eval_exprs (e::es) *)
  >- (irule case_eval_exprs_cons_imm_dom >> metis_tac[])
QED
*)

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
    ∀n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables NONE imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables NONE imms') n))
Proof
  rpt strip_tac >> drule (cj 8 immutables_dom_mutual) >>
  rw[preserves_immutables_dom_def] >> metis_tac[]
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
    ∀n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables NONE imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables NONE imms') n))
Proof
  rpt strip_tac >> drule (cj 6 immutables_dom_mutual) >>
  rw[preserves_immutables_dom_def] >> metis_tac[]
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
    ∀n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables NONE imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables NONE imms') n))
Proof
  rpt strip_tac >> drule (cj 2 immutables_dom_mutual) >>
  rw[preserves_immutables_dom_def] >> metis_tac[]
QED
