(*
 * Remove Unused — OWHILE iteration correctness under wf_ssa.
 *
 * Depends on removeUnusedStructProofs for rusp_preserves_all and
 * removeUnusedSsaProofs for nop_output_not_used_as_operand.
 *
 * Key theorem:
 *   remove_unused_function_correct_ssa — full OWHILE iteration correctness
 *)

Theory removeUnusedFnProofs
Ancestors
  removeUnusedStructProofs
  removeUnusedSsaProofs
  removeUnusedProofs removeUnusedDefs
  passSimulationDefs passSimulationProps analysisSimProps
  livenessProofs livenessDefs
  dfAnalyzeDefs dfAnalyzeProps dfHelperProps
  venomInstProps venomWf venomExecProps
  stateEquiv stateEquivProps stateEquivProofs
  execEquivProps cfgTransformProps cfgDefs
  passSharedDefs passSharedProps
  venomInst venomState venomExecSemantics
  indexedLists cfgAnalysisProps pointerConfinedDefs
  worklistDefs
  list rich_list combin

(* ===== Self-contained OWHILE correctness under SSA ===== *)

(* Abbreviations for readability *)
val G_def = ``\g:ir_function. remove_unused_single_pass g <> g``;
val f_def = ``remove_unused_single_pass``;

(* Forward preservation of structural bundle through OWHILE iteration *)
Theorem owhile_preserves_bundle[local]:
  !x y.
    OWHILE ^G_def ^f_def x = SOME y ==>
    wf_function x /\ fn_inst_wf x /\ wf_ssa x /\
    ssa_form x /\ nop_outputs_empty x /\ alloca_pointer_confined x ==>
    wf_function y /\ fn_inst_wf y /\ wf_ssa y /\
    ssa_form y /\ nop_outputs_empty y /\ alloca_pointer_confined y /\
    fn_all_outputs y SUBSET fn_all_outputs x /\
    fn_entry_label y = fn_entry_label x
Proof
  ho_match_mp_tac WhileTheory.OWHILE_IND >>
  simp_tac std_ss [BETA_THM] >>
  rpt conj_tac
  >- (rpt strip_tac >> simp[pred_setTheory.SUBSET_REFL])
  >> rpt gen_tac >> strip_tac >> strip_tac >> strip_tac >>
  (* IH: bundle(f(x)) ==> bundle(y) /\ outputs(y) <= outputs(f(x)) *)
  (* Need: bundle(y) /\ outputs(y) <= outputs(x) *)
  `wf_function (remove_unused_single_pass x) /\
   fn_inst_wf (remove_unused_single_pass x) /\
   wf_ssa (remove_unused_single_pass x) /\
   ssa_form (remove_unused_single_pass x) /\
   nop_outputs_empty (remove_unused_single_pass x) /\
   alloca_pointer_confined (remove_unused_single_pass x)` by
    metis_tac[rusp_preserves_all] >>
  fs[] >>
  metis_tac[removeUnusedProofsTheory.rusp_all_outputs_subset,
            pred_setTheory.SUBSET_TRANS, rusp_preserves_entry_label]
QED


(* Helper: nop_outputs of intermediate x are subset of eliminated vars *)
Theorem nop_outputs_subset_elim[local]:
  !fn x result.
    remove_unused_single_pass x <> x ==>
    OWHILE ^G_def ^f_def x = SOME result ==>
    wf_function x /\ fn_inst_wf x /\ wf_ssa x /\
    ssa_form x /\ nop_outputs_empty x /\ alloca_pointer_confined x ==>
    fn_all_outputs x SUBSET fn_all_outputs fn ==>
    single_pass_nop_outputs x SUBSET
      (fn_all_outputs fn DIFF fn_all_outputs result)
Proof
  rpt strip_tac >>
  simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_DIFF] >>
  rpt strip_tac
  >- (
    (* x' IN fn_all_outputs fn: nop_outputs x <= fn_all_outputs x <= fn_all_outputs fn *)
    imp_res_tac (SRULE [pred_setTheory.SUBSET_DEF]
      removeUnusedProofsTheory.nop_outputs_subset_all_outputs) >>
    metis_tac[pred_setTheory.SUBSET_DEF]
  )
  >- (
    (* x' NOTIN fn_all_outputs result *)
    (* Step 1: nop_outputs x are not in fn_all_outputs(rusp x) *)
    `x' NOTIN fn_all_outputs (remove_unused_single_pass x)` by
      metis_tac[removeUnusedProofsTheory.nop_outputs_not_in_rusp] >>
    (* Step 2: OWHILE tail gives result from rusp x *)
    `OWHILE (\g. remove_unused_single_pass g <> g)
            remove_unused_single_pass (remove_unused_single_pass x) = SOME result` by (
      qpat_x_assum `OWHILE _ _ x = SOME result` mp_tac >>
      simp_tac std_ss [Once WhileTheory.OWHILE_THM, BETA_THM] >>
      simp[]) >>
    (* Step 3: bundle preserved for rusp x *)
    `wf_function (remove_unused_single_pass x) /\
     fn_inst_wf (remove_unused_single_pass x) /\
     wf_ssa (remove_unused_single_pass x) /\
     ssa_form (remove_unused_single_pass x) /\
     nop_outputs_empty (remove_unused_single_pass x) /\
     alloca_pointer_confined (remove_unused_single_pass x)` by
      metis_tac[rusp_preserves_all] >>
    (* Step 4: fn_all_outputs result <= fn_all_outputs(rusp x) by owhile_preserves_bundle *)
    `fn_all_outputs result SUBSET fn_all_outputs (remove_unused_single_pass x)` by
      metis_tac[owhile_preserves_bundle] >>
    (* Step 5: x' not in result outputs *)
    metis_tac[pred_setTheory.SUBSET_DEF]
  )
QED

(* Helper: step condition for owhile_lift_result_compose *)
Theorem rusp_step_condition[local]:
  !fuel ctx fn s result x.
    venom_wf ctx /\ s.vs_inst_idx = 0 /\
    remove_unused_iterate fn = SOME result /\
    remove_unused_single_pass x <> x /\
    OWHILE ^G_def ^f_def x = SOME result /\
    wf_function x /\ fn_inst_wf x /\ wf_ssa x /\
    ssa_form x /\ nop_outputs_empty x /\ alloca_pointer_confined x /\
    fn_entry_label x = SOME s.vs_current_bb /\
    fn_all_outputs x SUBSET fn_all_outputs fn ==>
    let elim = remove_unused_eliminated_vars fn in
    (?e. run_function fuel ctx x s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim) (execution_equiv elim)
      (run_function fuel ctx x s)
      (run_function fuel ctx (remove_unused_single_pass x) s)
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >>
  (* Apply single-pass correctness *)
  mp_tac (SIMP_RULE std_ss [LET_THM]
            removeUnusedProofsTheory.remove_unused_single_pass_correct_proof) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `x`, `s`] mp_tac) >>
  (impl_tac >- (
    rpt conj_tac >> fs[] >>
    rpt strip_tac >>
    metis_tac[nop_output_not_used_as_operand])) >>
  simp_tac std_ss [LET_THM] >>
  strip_tac
  >- metis_tac[] >>
  (* Weaken nop_outputs to elim *)
  DISJ2_TAC >>
  irule removeUnusedProofsTheory.lift_result_weaken_vars >>
  qexists_tac `single_pass_nop_outputs x` >> conj_tac
  >- (
    (* single_pass_nop_outputs x <= elim *)
    simp[remove_unused_eliminated_vars_def, LET_THM,
         GSYM fn_all_outputs_def, remove_unused_function_def] >>
    irule nop_outputs_subset_elim >>
    simp[remove_unused_iterate_def] >> fs[]
  )
  >- first_assum ACCEPT_TAC
QED

(* Helper: preservation condition for owhile_lift_result_compose *)
Theorem rusp_preservation_condition[local]:
  !fn result s x.
    OWHILE ^G_def ^f_def x = SOME result /\
    remove_unused_single_pass x <> x /\
    wf_function x /\ fn_inst_wf x /\ wf_ssa x /\
    ssa_form x /\ nop_outputs_empty x /\ alloca_pointer_confined x /\
    fn_entry_label x = SOME s.vs_current_bb /\
    fn_all_outputs x SUBSET fn_all_outputs fn ==>
    OWHILE ^G_def ^f_def (remove_unused_single_pass x) = SOME result /\
    wf_function (remove_unused_single_pass x) /\
    fn_inst_wf (remove_unused_single_pass x) /\
    wf_ssa (remove_unused_single_pass x) /\
    ssa_form (remove_unused_single_pass x) /\
    nop_outputs_empty (remove_unused_single_pass x) /\
    alloca_pointer_confined (remove_unused_single_pass x) /\
    fn_entry_label (remove_unused_single_pass x) = SOME s.vs_current_bb /\
    fn_all_outputs (remove_unused_single_pass x) SUBSET fn_all_outputs fn
Proof
  rpt strip_tac >>
  `OWHILE (\g. remove_unused_single_pass g <> g)
          remove_unused_single_pass (remove_unused_single_pass x) = SOME result` by (
    qpat_x_assum `OWHILE _ _ x = SOME result` mp_tac >>
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [WhileTheory.OWHILE_THM])) >>
    simp[]) >>
  fs[rusp_preserves_all, rusp_preserves_entry_label] >>
  metis_tac[removeUnusedProofsTheory.rusp_all_outputs_subset,
            pred_setTheory.SUBSET_TRANS]
QED

(* Self-contained function-level correctness under SSA.
   Uses owhile_lift_result_compose with the bundle as invariant P. *)
Theorem remove_unused_function_correct_ssa:
  !fuel ctx fn s.
    venom_wf ctx /\ wf_function fn /\ fn_inst_wf fn /\
    wf_ssa fn /\ ssa_form fn /\
    nop_outputs_empty fn /\ alloca_pointer_confined fn /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb ==>
    let elim = remove_unused_eliminated_vars fn in
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim) (execution_equiv elim)
      (run_function fuel ctx fn s)
      (run_function fuel ctx (remove_unused_function fn) s)
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >>
  simp[remove_unused_function_def] >>
  Cases_on `remove_unused_iterate fn`
  >- simp[removeUnusedProofsTheory.lift_result_refl_state_equiv] >>
  rename1 `remove_unused_iterate fn = SOME result` >>
  simp[] >>
  qabbrev_tac `elim = remove_unused_eliminated_vars fn` >>
  (* Apply owhile_lift_result_compose *)
  mp_tac (BETA_RULE (Q.ISPECL [
    `\g:ir_function. remove_unused_single_pass g <> g`,
    `remove_unused_single_pass`,
    `state_equiv elim`,
    `execution_equiv elim`,
    `\x. run_function fuel ctx x s`
  ] removeUnusedProofsTheory.owhile_lift_result_compose)) >>
  disch_then (qspec_then
    `\x. OWHILE ^G_def ^f_def x = SOME result /\
         wf_function x /\ fn_inst_wf x /\ wf_ssa x /\
         ssa_form x /\ nop_outputs_empty x /\ alloca_pointer_confined x /\
         fn_entry_label x = SOME s.vs_current_bb /\
         fn_all_outputs x SUBSET fn_all_outputs fn` mp_tac) >>
  simp_tac std_ss [BETA_THM] >>
  simp[stateEquivPropsTheory.state_equiv_refl,
       stateEquivPropsTheory.execution_equiv_refl] >>
  (* Discharge transitivity *)
  (SUBGOAL_THEN
    ``(!s1 s2 s3. state_equiv elim s1 s2 /\ state_equiv elim s2 s3 ==>
                  state_equiv elim s1 s3) /\
     (!s1 s2 s3. execution_equiv elim s1 s2 /\ execution_equiv elim s2 s3 ==>
                  execution_equiv elim s1 s3)``
    (fn th => REWRITE_TAC [th])
  >- metis_tac[stateEquivPropsTheory.state_equiv_trans,
               stateEquivPropsTheory.execution_equiv_trans]) >>
  (* Discharge step condition *)
  `!x. remove_unused_single_pass x <> x /\
       OWHILE (\g. remove_unused_single_pass g <> g)
              remove_unused_single_pass x = SOME result /\
       wf_function x /\ fn_inst_wf x /\ wf_ssa x /\
       ssa_form x /\ nop_outputs_empty x /\ alloca_pointer_confined x /\
       fn_entry_label x = SOME s.vs_current_bb /\
       fn_all_outputs x SUBSET fn_all_outputs fn ==>
       (?e. run_function fuel ctx x s = Error e) \/
       lift_result (state_equiv elim) (execution_equiv elim) (execution_equiv elim)
         (run_function fuel ctx x s)
         (run_function fuel ctx (remove_unused_single_pass x) s)` by (
    rpt strip_tac >>
    mp_tac (SIMP_RULE std_ss [LET_THM] rusp_step_condition) >>
    disch_then (qspecl_then [`fuel`, `ctx`, `fn`, `s`, `result`, `x`] mp_tac) >>
    (impl_tac >- (simp[remove_unused_iterate_def] >> fs[])) >>
    fs[Abbr `elim`]) >>
  (* Discharge preservation condition *)
  `!x. remove_unused_single_pass x <> x /\
       OWHILE (\g. remove_unused_single_pass g <> g)
              remove_unused_single_pass x = SOME result /\
       wf_function x /\ fn_inst_wf x /\ wf_ssa x /\
       ssa_form x /\ nop_outputs_empty x /\ alloca_pointer_confined x /\
       fn_entry_label x = SOME s.vs_current_bb /\
       fn_all_outputs x SUBSET fn_all_outputs fn ==>
       OWHILE (\g. remove_unused_single_pass g <> g)
              remove_unused_single_pass (remove_unused_single_pass x) = SOME result /\
       wf_function (remove_unused_single_pass x) /\
       fn_inst_wf (remove_unused_single_pass x) /\
       wf_ssa (remove_unused_single_pass x) /\
       ssa_form (remove_unused_single_pass x) /\
       nop_outputs_empty (remove_unused_single_pass x) /\
       alloca_pointer_confined (remove_unused_single_pass x) /\
       fn_entry_label (remove_unused_single_pass x) = SOME s.vs_current_bb /\
       fn_all_outputs (remove_unused_single_pass x) SUBSET fn_all_outputs fn` by (
    rpt strip_tac >>
    mp_tac rusp_preservation_condition >>
    disch_then (qspecl_then [`fn`, `result`, `s`, `x`] mp_tac) >>
    (impl_tac >- fs[]) >> simp[]) >>
  (* Feed to owhile_lift_result_compose *)
  (impl_tac >- (rpt strip_tac >> metis_tac[])) >>
  disch_then (qspec_then `fn` mp_tac) >>
  simp[remove_unused_iterate_def, pred_setTheory.SUBSET_REFL] >>
  fs[remove_unused_iterate_def]
QED

