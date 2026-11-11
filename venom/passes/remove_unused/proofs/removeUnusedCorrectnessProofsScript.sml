(*
 * Remove Unused Variables — Correctness proof helpers
 *
 * All intermediate lemmas used by removeUnusedCorrectnessScript.
 * Includes: monotonicity, structural helpers, cross-context equivalence.
 *)

Theory removeUnusedCorrectnessProofs
Ancestors
  removeUnusedDefs removeUnusedProofs removeUnusedFnProofs
  removeUnusedStructProofs removeUnusedCrossContextProofs
  passSharedDefs passSharedProps passSimulationDefs passSimulationProps
  venomState venomInst venomExecSemantics venomExecProps venomWf
  stateEquiv stateEquivProps
  crossBlockSimDefs crossBlockSimProps execEquivParamProps pointerConfinedDefs

(* ===== Monotonicity: larger excluded set is weaker ===== *)

Theorem execution_equiv_mono:
  !V1 V2 s1 s2. V1 SUBSET V2 /\ execution_equiv V1 s1 s2 ==>
    execution_equiv V2 s1 s2
Proof
  rw[execution_equiv_def, pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem state_equiv_mono:
  !V1 V2 s1 s2. V1 SUBSET V2 /\ state_equiv V1 s1 s2 ==>
    state_equiv V2 s1 s2
Proof
  rw[state_equiv_def, execution_equiv_def, pred_setTheory.SUBSET_DEF] >>
  metis_tac[]
QED

Theorem result_equiv_mono:
  !V1 V2 r1 r2.
    V1 SUBSET V2 /\ result_equiv V1 r1 r2 ==>
    result_equiv V2 r1 r2
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> gvs[result_equiv_def] >>
  metis_tac[state_equiv_mono, execution_equiv_mono]
QED

(* Each function's eliminated vars are a subset of the context-wide union *)
Theorem elim_subset_all_elim:
  !ctx fn. MEM fn ctx.ctx_functions ==>
    remove_unused_eliminated_vars fn SUBSET remove_unused_all_eliminated ctx
Proof
  rw[remove_unused_all_eliminated_def, pred_setTheory.SUBSET_DEF,
     pred_setTheory.IN_BIGUNION] >>
  rpt strip_tac >>
  qexists_tac `remove_unused_eliminated_vars fn` >> simp[] >>
  simp[listTheory.MEM_MAP] >> metis_tac[]
QED

(* ===== Bridge lemmas for precondition derivation ===== *)

Theorem fn_inst_wf_nop_outputs_empty:
  !fn. fn_inst_wf fn ==> nop_outputs_empty fn
Proof
  rw[fn_inst_wf_def, nop_outputs_empty_def] >>
  rpt strip_tac >> res_tac >>
  gvs[inst_wf_def]
QED

Theorem remove_unused_function_uniform_reconstruction:
  !ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    alloca_pointer_confined fn /\ s.vs_inst_idx = 0 ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
      (!fuel.
        (?e. run_blocks fuel ctx fn (s with vs_gas_readings := gs) = Error e) \/
        lift_result (state_equiv (remove_unused_eliminated_vars fn))
          (execution_equiv (remove_unused_eliminated_vars fn))
          (execution_equiv (remove_unused_eliminated_vars fn))
          (run_blocks fuel ctx fn (s with vs_gas_readings := gs))
          (run_blocks fuel ctx (remove_unused_function fn) s))
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn /\ nop_outputs_empty fn` by
    metis_tac[wf_ssa_def, fn_inst_wf_nop_outputs_empty] >>
  irule remove_unused_context_uniform_from_reconstruction >> conj_tac
  >- (rpt strip_tac >>
      irule remove_unused_function_bounded_error_reconstruction >> simp[]) >>
  rpt strip_tac >> irule remove_unused_function_finite_reconstruction >> fs[]
QED

(* ===== Function-level correctness (same context) ===== *)

(* GAS consumes vs_gas_readings, and the pass deletes dead GAS, so the
   transformed function reads fewer entries.  For every transformed initial
   state s' (with its readings) there is one original reading list gs,
   chosen before fuel, under which the runs agree.

   Intuition (may be ignored): the runs are in lockstep with equal fuel
   (fuel is spent per block; blocks and INVOKEs are kept).  Build gs from
   the transformed run: before each dead GAS the original executes, insert a
   dummy reading when the transformed run's remaining list is nonempty (an
   empty list reads 0w on both sides).  If the transformed run never
   terminates, stop inserting after its last consumed reading: from then on
   either both lists are empty or no kept GAS runs again. *)
Theorem remove_unused_function_correct_gas:
  !ctx fn s'.
    venom_wf ctx /\ wf_function fn /\ fn_inst_wf fn /\
    wf_ssa fn /\ alloca_pointer_confined fn /\
    s'.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s'.vs_current_bb ==>
    ?gs. !fuel.
      (?e. run_blocks fuel ctx fn (s' with vs_gas_readings := gs) = Error e) \/
      lift_result (state_equiv (remove_unused_eliminated_vars fn))
                  (execution_equiv (remove_unused_eliminated_vars fn))
                  (execution_equiv (remove_unused_eliminated_vars fn))
        (run_blocks fuel ctx fn (s' with vs_gas_readings := gs))
        (run_blocks fuel ctx (remove_unused_function fn) s')
Proof
  rpt strip_tac >>
  drule_all remove_unused_function_uniform_reconstruction >>
  disch_then (qspec_then `ctx` (qx_choose_then `gs` strip_assume_tac)) >>
  qexists_tac `gs` >> simp[]
QED

(* ===== Structural helpers ===== *)

Theorem rusp_fn_name:
  !fn. (remove_unused_single_pass fn).fn_name = fn.fn_name
Proof
  rw[remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def, function_map_transform_def]
QED

Theorem ru_function_fn_name:
  !fn. (remove_unused_function fn).fn_name = fn.fn_name
Proof
  rw[remove_unused_function_def] >>
  Cases_on `remove_unused_iterate fn` >> simp[] >>
  rename1 `SOME r` >>
  fs[remove_unused_iterate_def] >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`r`, `fn`] >>
  ho_match_mp_tac WhileTheory.OWHILE_IND >> rpt strip_tac >>
  gvs[rusp_fn_name]
QED

Theorem ru_function_entry_label:
  !fn. fn_entry_label (remove_unused_function fn) = fn_entry_label fn
Proof
  rw[remove_unused_function_def] >>
  Cases_on `remove_unused_iterate fn` >> simp[] >>
  rename1 `SOME r` >>
  fs[remove_unused_iterate_def] >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`r`, `fn`] >>
  ho_match_mp_tac WhileTheory.OWHILE_IND >> rpt strip_tac >>
  gvs[rusp_preserves_entry_label]
QED

Theorem lookup_function_ru_context:
  !name ctx.
    lookup_function name (remove_unused_context ctx).ctx_functions =
    OPTION_MAP remove_unused_function
      (lookup_function name ctx.ctx_functions)
Proof
  rw[remove_unused_context_def, lookup_function_def] >>
  qspec_tac (`ctx.ctx_functions`, `fns`) >>
  Induct_on `fns` >> simp[listTheory.FIND_thm] >>
  rpt strip_tac >> simp[ru_function_fn_name] >> rw[]
QED

Theorem lookup_function_ru_none:
  !name ctx.
    lookup_function name ctx.ctx_functions = NONE ==>
    lookup_function name (remove_unused_context ctx).ctx_functions = NONE
Proof
  simp[lookup_function_ru_context]
QED

(* state_equiv_empty_eq: now in stateEquivPropsTheory *)
(* step_inst_ctx_irrel: now in venomExecPropsTheory *)

(* remove_unused_function preserves setup_callee (entry label unchanged) *)
Theorem setup_callee_ru:
  !fn args s.
    setup_callee (remove_unused_function fn) args s = setup_callee fn args s
Proof
  rw[setup_callee_def, fn_entry_label_def, entry_block_def] >>
  pop_assum mp_tac >>
  `fn_entry_label (remove_unused_function fn) = fn_entry_label fn`
    by simp[ru_function_entry_label] >>
  fs[fn_entry_label_def, entry_block_def] >>
  Cases_on `NULL fn.fn_blocks` >> fs[]
QED

(* Actual-context contracts, with a single oracle for lower-fuel reflection. *)
val ru_member_error = ``\N ctx fn s.
  (?e. run_blocks N (remove_unused_context ctx) (remove_unused_function fn) s = Error e) ==>
  ?gs:(256 word) list.
    LENGTH (FILTER (\w. w <> 0w) gs) <= LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
    ?e. run_blocks N ctx fn (s with vs_gas_readings := gs) = Error e``;
val ru_member_success = ``\N ctx fn s V.
  ~(?e. run_blocks N (remove_unused_context ctx) (remove_unused_function fn) s = Error e) ==>
  ?gs:(256 word) list.
    LENGTH (FILTER (\w. w <> 0w) gs) <= LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
    ((!k. ?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e) \/
     lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
       (run_blocks N ctx fn (s with vs_gas_readings := gs))
       (run_blocks N (remove_unused_context ctx) (remove_unused_function fn) s)) /\
    (!k. k <= N /\
      (?e. run_blocks k (remove_unused_context ctx) (remove_unused_function fn) s = Error e) ==>
      ?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e)``;

Theorem remove_unused_actual_context_runner:
  !N ctx fn V.
    (!m f s. m < N /\ MEM f ctx.ctx_functions /\ s.vs_inst_idx = 0 /\
      fn_entry_label f = SOME s.vs_current_bb ==>
      ^ru_member_error m ctx f s /\ ^ru_member_success m ctx f s V) ==>
    (!s. (?e. run_blocks N (remove_unused_context ctx) fn s = Error e) ==>
      ?gs:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) gs) <= LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
        ?e. run_blocks N ctx fn (s with vs_gas_readings := gs) = Error e) /\
    (!s. ~(?e. run_blocks N (remove_unused_context ctx) fn s = Error e) ==>
      ?gs:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) gs) <= LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
        ((!k. ?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e) \/
         lift_result (state_equiv {}) (execution_equiv V) (execution_equiv V)
           (run_blocks N ctx fn (s with vs_gas_readings := gs))
           (run_blocks N (remove_unused_context ctx) fn s)) /\
        (!k. k <= N /\ (?e. run_blocks k (remove_unused_context ctx) fn s = Error e) ==>
          ?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e))
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [BETA_THM] >>
  ho_match_mp_tac (SIMP_RULE std_ss [BETA_THM] remove_unused_runner_from_callee_contracts) >>
  conj_tac
  >- (simp[lookup_function_ru_context] >> rpt strip_tac >>
      gvs[setup_callee_ru]) >>
  rpt gen_tac >> strip_tac >> conj_tac >> rpt gen_tac >> strip_tac >>
  gvs[lookup_function_ru_context] >>
  `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  imp_res_tac setup_callee_props >>
  first_x_assum (qspecl_then [`m`, `fn`, `cs`] mp_tac) >> simp[]
QED

Theorem remove_unused_actual_member_reconstruction:
  !ctx.
    venom_wf ctx /\
    (!f. MEM f ctx.ctx_functions ==> wf_ssa f /\ alloca_pointer_confined f) ==>
    !N fn s. MEM fn ctx.ctx_functions /\ s.vs_inst_idx = 0 /\
      fn_entry_label fn = SOME s.vs_current_bb ==>
      ^ru_member_error N ctx fn s /\
      ^ru_member_success N ctx fn s (remove_unused_all_eliminated ctx)
Proof
  gen_tac >> strip_tac >> completeInduct_on `N` >>
  rpt gen_tac >> strip_tac >>
  `wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\ ssa_form fn /\
   nop_outputs_empty fn /\ alloca_pointer_confined fn` by
    (fs[venom_wf_def] >> metis_tac[wf_ssa_def, fn_inst_wf_nop_outputs_empty]) >>
  qspecl_then [`N`, `ctx`, `remove_unused_function fn`, `remove_unused_all_eliminated ctx`]
    mp_tac remove_unused_actual_context_runner >>
  (impl_tac >- (rpt strip_tac >> first_x_assum drule >> simp[])) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "runner_error") (mk_asm "runner_success")) >>
  conj_tac
  >- suspend "error"
  >> suspend "success"
QED

Resume remove_unused_actual_member_reconstruction[error]:
  simp_tac std_ss [BETA_THM] >> strip_tac >>
  asm "runner_error" (qspec_then `s` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `hs` strip_assume_tac) >>
  qspecl_then [`N`, `ctx`, `fn`, `s with vs_gas_readings := hs`]
    mp_tac remove_unused_function_error_reconstruction >> simp[] >>
  disch_then (qx_choose_then `gs` strip_assume_tac) >>
  qexists_tac `gs` >> simp[] >> decide_tac
QED

Resume remove_unused_actual_member_reconstruction[success]:
  qpat_x_assum `!m. _` kall_tac >>
  asm_x "runner_error" kall_tac >>
  qpat_x_assum `venom_wf ctx` kall_tac >>
  qpat_x_assum `!f. MEM f _ ==> _` kall_tac >>
  simp_tac std_ss [BETA_THM] >> strip_tac >>
  asm_x "runner_success" (qspec_then `s` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `hs`
    (CONJUNCTS_THEN2 (mk_asm "budget_B")
      (CONJUNCTS_THEN2 (mk_asm "result_B") (mk_asm "reflect_B")))) >>
  asm_x "result_B" strip_assume_tac
  >- (qspecl_then [`ctx`, `fn`, `s with vs_gas_readings := hs`]
        mp_tac remove_unused_function_permanent_error_reconstruction >> simp[] >>
      disch_then (qx_choose_then `gs` strip_assume_tac) >>
      qexists_tac `gs` >> simp[] >>
      asm "budget_B" mp_tac >> decide_tac) >>
  `!e. run_blocks N ctx (remove_unused_function fn)
     (s with vs_gas_readings := hs) <> Error e` by
    (Cases_on `run_blocks N ctx (remove_unused_function fn)
       (s with vs_gas_readings := hs)` >>
     Cases_on `run_blocks N (remove_unused_context ctx) (remove_unused_function fn) s` >>
     gvs[lift_result_def]) >>
  qspecl_then [`N`, `ctx`, `fn`, `s with vs_gas_readings := hs`]
    mp_tac remove_unused_function_finite_reconstruction >> simp[] >>
  disch_then (qx_choose_then `gs`
    (CONJUNCTS_THEN2 (mk_asm "budget_A")
      (CONJUNCTS_THEN2 (mk_asm "result_A") (mk_asm "reflect_A")))) >>
  qexists_tac `gs` >> conj_tac
  >- (asm "budget_A" mp_tac >> asm "budget_B" mp_tac >> simp[] >> decide_tac) >>
  asm_x "result_A" strip_assume_tac
  >- simp[] >>
  conj_tac
  >- suspend "compose_results" >>
  rpt gen_tac >> strip_tac >>
  asm "reflect_B" (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
  asm "reflect_A" (qspec_then `k` mp_tac) >> simp[]
QED

Resume remove_unused_actual_member_reconstruction[compose_results]:
  disj2_tac >>
  `remove_unused_eliminated_vars fn SUBSET remove_unused_all_eliminated ctx` by
    metis_tac[elim_subset_all_elim] >>
  drule_all lift_result_weaken_vars >> strip_tac >>
  Cases_on `run_blocks N ctx fn (s with vs_gas_readings := gs)` >>
  Cases_on `run_blocks N ctx (remove_unused_function fn) (s with vs_gas_readings := hs)` >>
  Cases_on `run_blocks N (remove_unused_context ctx) (remove_unused_function fn) s` >>
  gvs[lift_result_def] >> imp_res_tac state_equiv_empty_eq >> gvs[] >>
  drule_all execution_equiv_trans >> simp[]
QED

Finalise remove_unused_actual_member_reconstruction

Theorem remove_unused_actual_member_uniform:
  !ctx fn s.
    venom_wf ctx /\
    (!f. MEM f ctx.ctx_functions ==> wf_ssa f /\ alloca_pointer_confined f) /\
    MEM fn ctx.ctx_functions /\ s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
      (!fuel.
        (?e. run_blocks fuel ctx fn (s with vs_gas_readings := gs) = Error e) \/
        lift_result (state_equiv (remove_unused_all_eliminated ctx))
          (execution_equiv (remove_unused_all_eliminated ctx))
          (execution_equiv (remove_unused_all_eliminated ctx))
          (run_blocks fuel ctx fn (s with vs_gas_readings := gs))
          (run_blocks fuel (remove_unused_context ctx) (remove_unused_function fn) s))
Proof
  rpt gen_tac >> strip_tac >>
  irule remove_unused_context_uniform_from_reconstruction >> conj_tac
  >- (gen_tac >> strip_tac >>
      qspecl_then [`ctx`] mp_tac remove_unused_actual_member_reconstruction >> simp[] >>
      disch_then (qspecl_then [`N`, `fn`, `s`] mp_tac) >> simp[] >>
      simp_tac std_ss [BETA_THM] >> strip_tac >>
      qexists_tac `gs` >> simp[] >> rpt strip_tac >>
      irule removeUnusedGasProofsTheory.remove_unused_run_blocks_error_downward >> qexists_tac `N` >> simp[]) >>
  gen_tac >>
  qspecl_then [`ctx`] mp_tac remove_unused_actual_member_reconstruction >> simp[] >>
  disch_then (qspecl_then [`N`, `fn`, `s`] mp_tac) >> simp[] >>
  simp_tac std_ss [BETA_THM] >> metis_tac[]
QED

(* merge_callee_execution_equiv relocated to removeUnusedCrossContextProofs. *)


(* setup_callee_props: now in venomExecPropsTheory *)


(* ===== Pass correctness: remove_unused preserves behavior on non-eliminated vars ===== *)

(* Every function of the context is transformed, so callees' dead GAS
   shift the readings too; gs is chosen as above over the whole trace. *)
Theorem remove_unused_pass_correct_gas:
  !ctx entry.
    venom_wf ctx /\
    (!fn. MEM fn ctx.ctx_functions ==>
          wf_ssa fn /\ alloca_pointer_confined fn) /\
    lookup_function entry ctx.ctx_functions <> NONE ==>
    ?fn fn'.
      lookup_function entry ctx.ctx_functions = SOME fn /\
      lookup_function entry (remove_unused_context ctx).ctx_functions =
        SOME fn' /\
      !s'. s'.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s'.vs_current_bb ==>
        ?gs. !fuel.
          (?e. run_blocks fuel ctx fn (s' with vs_gas_readings := gs) =
               Error e) \/
          lift_result (state_equiv (remove_unused_all_eliminated ctx))
                      (execution_equiv (remove_unused_all_eliminated ctx))
                      (execution_equiv (remove_unused_all_eliminated ctx))
            (run_blocks fuel ctx fn (s' with vs_gas_readings := gs))
            (run_blocks fuel (remove_unused_context ctx) fn' s')
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_function entry ctx.ctx_functions` >> gvs[] >>
  rename1 `lookup_function entry ctx.ctx_functions = SOME fn` >>
  qexists_tac `remove_unused_function fn` >>
  simp[lookup_function_ru_context] >> rpt strip_tac >>
  `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  drule_all remove_unused_actual_member_uniform >>
  disch_then (qx_choose_then `gs` strip_assume_tac) >>
  qexists_tac `gs` >> simp[]
QED

