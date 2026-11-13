(*
 * Remove Unused — OWHILE iteration correctness under wf_ssa.
 *
 * Depends on removeUnusedStructProofs for rusp_preserves_all and
 * removeUnusedSsaProofs for nop_output_not_used_as_operand.
 *
 * Key theorems reconstruct source GAS oracles through finite OWHILE
 * iteration, preserving nonzero budgets and low-fuel Error reflection.
 *)

Theory removeUnusedFnProofs
Ancestors
  removeUnusedStructProofs removeUnusedGasProofs
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

(* OWHILE iteration preserves wf, SSA, pointer confinement, entry label; fn_all_outputs only shrinks *)
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


(* nop_outputs of a function in the OWHILE chain is a subset of the eliminated variable set *)
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
  rpt strip_tac >| [
  (* x' IN fn_all_outputs fn: nop_outputs x <= fn_all_outputs x <= fn_all_outputs fn *)
  imp_res_tac (SRULE [pred_setTheory.SUBSET_DEF]
    removeUnusedProofsTheory.nop_outputs_subset_all_outputs) >>
  metis_tac[pred_setTheory.SUBSET_DEF],
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
  ]
QED


Theorem remove_unused_owhile_reachable_ind[local]:
  !G f P.
    (!x. ~G x ==> P x x) /\
    (!x y. G x /\ OWHILE G f (f x) = SOME y /\ P (f x) y ==> P x y) ==>
    !x y. OWHILE G f x = SOME y ==> P x y
Proof
  rpt gen_tac >> strip_tac >>
  `!x y. OWHILE G f x = SOME y ==>
    OWHILE G f x = SOME y /\ P x y` by
    (ho_match_mp_tac WhileTheory.OWHILE_IND >> conj_tac >>
     rpt strip_tac >> simp[Once WhileTheory.OWHILE_THM] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem remove_unused_owhile_permanent_error_reconstruction:
  !x y. OWHILE ^G_def ^f_def x = SOME y ==>
    !ctx s.
      wf_function x /\ fn_inst_wf x /\ wf_ssa x /\ ssa_form x /\
      nop_outputs_empty x /\ alloca_pointer_confined x /\
      s.vs_inst_idx = 0 /\
      (!fuel. ?e. run_blocks fuel ctx y s = Error e) ==>
      ?gs:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) gs) <=
          LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
        !fuel. ?e. run_blocks fuel ctx x (s with vs_gas_readings := gs) = Error e
Proof
  ho_match_mp_tac WhileTheory.OWHILE_IND >>
  simp_tac std_ss [BETA_THM] >> conj_tac
  >- (rpt strip_tac >> qexists_tac `s.vs_gas_readings` >> simp[]) >>
  rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `wf_function (remove_unused_single_pass x) /\
   fn_inst_wf (remove_unused_single_pass x) /\
   wf_ssa (remove_unused_single_pass x) /\
   ssa_form (remove_unused_single_pass x) /\
   nop_outputs_empty (remove_unused_single_pass x) /\
   alloca_pointer_confined (remove_unused_single_pass x)` by
    metis_tac[rusp_preserves_all] >>
  `?hs:(256 word) list.
     LENGTH (FILTER (\w. w <> 0w) hs) <=
       LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
     !fuel. ?e. run_blocks fuel ctx (remove_unused_single_pass x)
       (s with vs_gas_readings := hs) = Error e` by metis_tac[] >>
  `?gs:(256 word) list.
     LENGTH (FILTER (\w. w <> 0w) gs) <= LENGTH (FILTER (\w. w <> 0w) hs) /\
     !fuel. ?e. run_blocks fuel ctx x (s with vs_gas_readings := gs) = Error e` by
    (qspecl_then [`ctx`, `x`, `s`, `s with vs_gas_readings := hs`] mp_tac
       remove_unused_single_pass_permanent_error_reconstruction >>
     simp[stateEquivPropsTheory.state_equiv_refl]) >>
  qexists_tac `gs` >> simp[] >> decide_tac
QED

Theorem remove_unused_owhile_finite_reconstruction:
  !x y. OWHILE ^G_def ^f_def x = SOME y ==>
    !N ctx s.
      wf_function x /\ fn_inst_wf x /\ wf_ssa x /\ ssa_form x /\
      nop_outputs_empty x /\ alloca_pointer_confined x /\
      s.vs_inst_idx = 0 /\ ~(?e. run_blocks N ctx y s = Error e) ==>
      ?gs:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) gs) <=
          LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
        ((!fuel. ?e. run_blocks fuel ctx x (s with vs_gas_readings := gs) = Error e) \/
         lift_result (state_equiv (fn_all_outputs x DIFF fn_all_outputs y))
           (execution_equiv (fn_all_outputs x DIFF fn_all_outputs y))
           (execution_equiv (fn_all_outputs x DIFF fn_all_outputs y))
           (run_blocks N ctx x (s with vs_gas_readings := gs))
           (run_blocks N ctx y s)) /\
        (!k. k <= N /\ (?e. run_blocks k ctx y s = Error e) ==>
          ?e. run_blocks k ctx x (s with vs_gas_readings := gs) = Error e)
Proof
  ho_match_mp_tac remove_unused_owhile_reachable_ind >>
  simp_tac std_ss [BETA_THM] >> conj_tac
  >- (rpt strip_tac >> qexists_tac `s.vs_gas_readings` >>
      simp[removeUnusedProofsTheory.lift_result_refl_state_equiv]) >>
  rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `wf_function (remove_unused_single_pass x) /\
   fn_inst_wf (remove_unused_single_pass x) /\
   wf_ssa (remove_unused_single_pass x) /\
   ssa_form (remove_unused_single_pass x) /\
   nop_outputs_empty (remove_unused_single_pass x) /\
   alloca_pointer_confined (remove_unused_single_pass x)` by
    metis_tac[rusp_preserves_all] >>
  suspend "step"
QED

Resume remove_unused_owhile_finite_reconstruction[step]:
  `OWHILE ^G_def ^f_def x = SOME y` by
    (simp[Once WhileTheory.OWHILE_THM] >> first_assum ACCEPT_TAC) >>
  `single_pass_nop_outputs x SUBSET (fn_all_outputs x DIFF fn_all_outputs y)` by
    (irule nop_outputs_subset_elim >> simp[]) >>
  `fn_all_outputs (remove_unused_single_pass x) DIFF fn_all_outputs y SUBSET
      (fn_all_outputs x DIFF fn_all_outputs y)` by
    (mp_tac (Q.SPEC `x` removeUnusedProofsTheory.rusp_all_outputs_subset) >>
     pred_setLib.SET_TAC[]) >>
  qpat_x_assum `!N ctx s. _` (qspecl_then [`N`, `ctx`, `s`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `hs` strip_assume_tac)
  >- (qspecl_then [`ctx`, `x`, `s`, `s with vs_gas_readings := hs`] mp_tac
        remove_unused_single_pass_permanent_error_reconstruction >>
      simp[stateEquivPropsTheory.state_equiv_refl] >>
      disch_then (qx_choose_then `gs` strip_assume_tac) >>
      qexists_tac `gs` >> simp[] >> decide_tac) >>
  qpat_x_assum `remove_unused_single_pass x <> x` kall_tac >>
  qpat_x_assum `OWHILE _ _ x = SOME y` kall_tac >>
  qpat_x_assum `OWHILE _ _ (remove_unused_single_pass x) = SOME y` kall_tac >>
  qpat_x_assum `wf_function (remove_unused_single_pass x)` kall_tac >>
  qpat_x_assum `fn_inst_wf (remove_unused_single_pass x)` kall_tac >>
  qpat_x_assum `wf_ssa (remove_unused_single_pass x)` kall_tac >>
  qpat_x_assum `ssa_form (remove_unused_single_pass x)` kall_tac >>
  qpat_x_assum `nop_outputs_empty (remove_unused_single_pass x)` kall_tac >>
  qpat_x_assum `alloca_pointer_confined (remove_unused_single_pass x)` kall_tac >>
  suspend "tail"
QED

Resume remove_unused_owhile_finite_reconstruction[tail]:
  `~(?e. run_blocks N ctx (remove_unused_single_pass x)
       (s with vs_gas_readings := hs) = Error e)` by
    (Cases_on `run_blocks N ctx (remove_unused_single_pass x)
       (s with vs_gas_readings := hs)` >>
     Cases_on `run_blocks N ctx y s` >> gvs[lift_result_def]) >>
  gvs[] >>
  qspecl_then [`N`, `ctx`, `x`, `s`, `s with vs_gas_readings := hs`] mp_tac
    remove_unused_single_pass_finite_reconstruction >>
  simp[stateEquivPropsTheory.state_equiv_refl] >>
  disch_then (qx_choose_then `gs` strip_assume_tac)
  >- (qexists_tac `gs` >> simp[] >> decide_tac) >>
  qexists_tac `gs` >> conj_tac >- decide_tac >>
  reverse conj_tac >- metis_tac[] >>
  disj2_tac >>
  irule passSimulationProofsTheory.lift_result_trans_proof >>
  conj_tac >- metis_tac[stateEquivPropsTheory.execution_equiv_trans] >>
  conj_tac >- metis_tac[stateEquivPropsTheory.state_equiv_trans] >>
  conj_tac >- metis_tac[stateEquivPropsTheory.execution_equiv_trans] >>
  qexists_tac `run_blocks N ctx (remove_unused_single_pass x)
    (s with vs_gas_readings := hs)` >> conj_tac >>
  irule removeUnusedProofsTheory.lift_result_weaken_vars >>
  goal_assum (drule_at Any) >> simp[]
QED

Finalise remove_unused_owhile_finite_reconstruction


Theorem remove_unused_function_permanent_error_reconstruction:
  !ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\ ssa_form fn /\
    nop_outputs_empty fn /\ alloca_pointer_confined fn /\
    s.vs_inst_idx = 0 /\
    (!fuel. ?e. run_blocks fuel ctx (remove_unused_function fn) s = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
      !fuel. ?e. run_blocks fuel ctx fn (s with vs_gas_readings := gs) = Error e
Proof
  rpt gen_tac >>
  simp[remove_unused_function_def] >>
  Cases_on `remove_unused_iterate fn`
  >- (simp[] >> strip_tac >> qexists_tac `s.vs_gas_readings` >> simp[]) >>
  simp[] >> strip_tac >>
  irule remove_unused_owhile_permanent_error_reconstruction >>
  goal_assum (drule_at Any) >> simp[GSYM remove_unused_iterate_def]
QED

Theorem remove_unused_function_finite_reconstruction:
  !N ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\ ssa_form fn /\
    nop_outputs_empty fn /\ alloca_pointer_confined fn /\
    s.vs_inst_idx = 0 /\
    ~(?e. run_blocks N ctx (remove_unused_function fn) s = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
      ((!fuel. ?e. run_blocks fuel ctx fn (s with vs_gas_readings := gs) = Error e) \/
       lift_result (state_equiv (remove_unused_eliminated_vars fn))
         (execution_equiv (remove_unused_eliminated_vars fn))
         (execution_equiv (remove_unused_eliminated_vars fn))
         (run_blocks N ctx fn (s with vs_gas_readings := gs))
         (run_blocks N ctx (remove_unused_function fn) s)) /\
      (!k. k <= N /\ (?e. run_blocks k ctx (remove_unused_function fn) s = Error e) ==>
        ?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e)
Proof
  rpt gen_tac >>
  simp[remove_unused_eliminated_vars_def, remove_unused_function_def] >>
  Cases_on `remove_unused_iterate fn`
  >- (simp[] >> strip_tac >> qexists_tac `s.vs_gas_readings` >>
      simp[removeUnusedProofsTheory.lift_result_refl_state_equiv]) >>
  simp[] >> strip_tac >>
  irule remove_unused_owhile_finite_reconstruction >>
  goal_assum (drule_at Any) >> simp[GSYM remove_unused_iterate_def]
QED

Theorem remove_unused_owhile_error_reconstruction:
  !x y. OWHILE ^G_def ^f_def x = SOME y ==>
    !N ctx s.
      wf_function x /\ fn_inst_wf x /\ wf_ssa x /\ ssa_form x /\
      nop_outputs_empty x /\ alloca_pointer_confined x /\
      s.vs_inst_idx = 0 /\
      (?e. run_blocks N ctx y s = Error e) ==>
      ?gs:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) gs) <=
          LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
        ?e. run_blocks N ctx x (s with vs_gas_readings := gs) = Error e
Proof
  ho_match_mp_tac WhileTheory.OWHILE_IND >>
  simp_tac std_ss [BETA_THM] >> conj_tac
  >- (rpt strip_tac >> qexists_tac `s.vs_gas_readings` >> simp[]) >>
  rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `wf_function (remove_unused_single_pass x) /\
   fn_inst_wf (remove_unused_single_pass x) /\
   wf_ssa (remove_unused_single_pass x) /\
   ssa_form (remove_unused_single_pass x) /\
   nop_outputs_empty (remove_unused_single_pass x) /\
   alloca_pointer_confined (remove_unused_single_pass x)` by
    metis_tac[rusp_preserves_all] >>
  `?hs:(256 word) list.
     LENGTH (FILTER (\w. w <> 0w) hs) <=
       LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
     ?e. run_blocks N ctx (remove_unused_single_pass x)
       (s with vs_gas_readings := hs) = Error e` by metis_tac[] >>
  `?gs:(256 word) list.
     LENGTH (FILTER (\w. w <> 0w) gs) <= LENGTH (FILTER (\w. w <> 0w) hs) /\
     ?e. run_blocks N ctx x (s with vs_gas_readings := gs) = Error e` by
    (qspecl_then [`N`, `ctx`, `x`, `s`, `s with vs_gas_readings := hs`]
       mp_tac remove_unused_single_pass_error_reconstruction >>
     simp[stateEquivPropsTheory.state_equiv_refl]) >>
  qexists_tac `gs` >> conj_tac >- decide_tac >> metis_tac[]
QED

Theorem remove_unused_function_error_reconstruction:
  !N ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\ ssa_form fn /\
    nop_outputs_empty fn /\ alloca_pointer_confined fn /\
    s.vs_inst_idx = 0 /\
    (?e. run_blocks N ctx (remove_unused_function fn) s = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
      ?e. run_blocks N ctx fn (s with vs_gas_readings := gs) = Error e
Proof
  rpt gen_tac >> simp[remove_unused_function_def] >>
  Cases_on `remove_unused_iterate fn`
  >- (simp[] >> strip_tac >> qexists_tac `s.vs_gas_readings` >> simp[]) >>
  simp[] >> strip_tac >>
  irule remove_unused_owhile_error_reconstruction >>
  goal_assum (drule_at Any) >> simp[GSYM remove_unused_iterate_def]
QED

Theorem remove_unused_function_bounded_error_reconstruction:
  !N ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\ ssa_form fn /\
    nop_outputs_empty fn /\ alloca_pointer_confined fn /\
    s.vs_inst_idx = 0 /\
    (?e. run_blocks N ctx (remove_unused_function fn) s = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
      !k. k <= N ==> ?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`N`, `ctx`, `fn`, `s`] mp_tac
    remove_unused_function_error_reconstruction >> simp[] >>
  disch_then (qx_choose_then `gs` strip_assume_tac) >>
  qexists_tac `gs` >> simp[] >> rpt strip_tac >>
  irule remove_unused_run_blocks_error_downward >>
  qexists_tac `N` >> simp[]
QED
