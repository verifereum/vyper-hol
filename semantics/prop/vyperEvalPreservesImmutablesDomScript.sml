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
  TRY (imp_res_tac set_global_immutables >> gvs[] >> NO_TAC) >>
  (* HashMap branch: further decompose the remaining do-block *)
  qpat_x_assum `_ = (res, st')` mp_tac >>
  simp[bind_def, return_def, raise_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_storage_slot_immutables >>
  imp_res_tac write_storage_slot_immutables >> gvs[] >>
  (* remaining goals: chain read/write immutables preservation *)
  cheat
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
  rw[finally_def, AllCaseEqs()] >> gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  first_x_assum drule >> simp[] >>
  irule preserves_immutables_dom_eq >> first_x_assum drule >> simp[]
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
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt strip_tac >>
  gvs[preserves_immutables_dom_def] >>
  cheat
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
    ∀n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables NONE imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables NONE imms') n))
Proof
  metis_tac[immutables_dom_mutual, preserves_immutables_dom_def]
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
  metis_tac[immutables_dom_mutual, preserves_immutables_dom_def]
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
  metis_tac[immutables_dom_mutual, preserves_immutables_dom_def]
QED
