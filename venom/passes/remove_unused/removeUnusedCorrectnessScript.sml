(*
 * Remove Unused Variables — Correctness (API)
 *
 * Top-level theorems only. All helpers in proofs/removeUnusedCorrectnessProofs.
 *)

Theory removeUnusedCorrectness
Ancestors
  removeUnusedCorrectnessProofs removeUnusedDefs removeUnusedFnProofs
  passSimulationDefs passSimulationProps
  venomState venomExecSemantics venomExecProps venomWf
  stateEquiv stateEquivProps
  crossBlockSimProps pointerConfinedDefs

(* ===== Function-level correctness (same context) ===== *)

Theorem remove_unused_function_correct =
  removeUnusedCorrectnessProofsTheory.remove_unused_function_correct

(* ===== Context-level pass_correct ===== *)

Theorem remove_unused_pass_correct:
  !ctx entry.
    venom_wf ctx /\
    (!fn. MEM fn ctx.ctx_functions ==>
          wf_ssa fn /\ alloca_pointer_confined fn) /\
    lookup_function entry ctx.ctx_functions <> NONE ==>
    let ctx' = remove_unused_context ctx in
    let all_elim = remove_unused_all_eliminated ctx in
    ?fn fn'.
      lookup_function entry ctx.ctx_functions = SOME fn /\
      lookup_function entry ctx'.ctx_functions = SOME fn' /\
      !s. s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb /\
          (?f. terminates (run_function f ctx fn s)) ==>
          pass_correct (state_equiv all_elim) (execution_equiv all_elim)
            (\fuel. run_function fuel ctx fn s)
            (\fuel. run_function fuel ctx' fn' s)
Proof
  rpt gen_tac >> strip_tac >> simp[LET_THM] >>
  Cases_on `lookup_function entry ctx.ctx_functions` >> fs[] >>
  rename1 `_ = SOME fn` >>
  qexists_tac `remove_unused_function fn` >>
  conj_tac >- simp[lookup_function_ru_context] >>
  rpt strip_tac >>
  `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `wf_function fn /\ fn_inst_wf fn` by fs[venom_wf_def] >>
  `wf_ssa fn /\ alloca_pointer_confined fn` by metis_tac[] >>
  qabbrev_tac `all_elim = remove_unused_all_eliminated ctx` >>
  qabbrev_tac `ctx' = remove_unused_context ctx` >>
  qabbrev_tac `fn' = remove_unused_function fn` >>
  (* Get cross-ctx result at any fuel *)
  `!fuel.
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv all_elim) (execution_equiv all_elim)
      (run_function fuel ctx fn s)
      (run_function fuel ctx' fn' s)` by (
    gen_tac >>
    mp_tac remove_unused_cross_ctx_fn_equiv >>
    disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then (fn th => assume_tac (CONJUNCT1 th)) >>
    first_x_assum (qspecl_then [`fn`, `s`] mp_tac) >>
    simp_tac std_ss [LET_THM] >>
    simp[Abbr `all_elim`, Abbr `ctx'`, Abbr `fn'`]) >>
  (* At terminating fuel: lift_result holds (Error excluded) *)
  `!fuel. terminates (run_function fuel ctx fn s) ==>
    lift_result (state_equiv all_elim) (execution_equiv all_elim)
      (run_function fuel ctx fn s)
      (run_function fuel ctx' fn' s)` by (
    rpt strip_tac >>
    first_x_assum (qspec_then `fuel` strip_assume_tac) >>
    fs[terminates_def]) >>
  simp[pass_correct_def] >> rpt conj_tac
  >- (
    (* terminates iff terminates *)
    eq_tac >> strip_tac
    >- (
      first_x_assum drule >> strip_tac >>
      qexists_tac `fuel` >>
      Cases_on `run_function fuel ctx fn s` >>
      Cases_on `run_function fuel ctx' fn' s` >>
      fs[lift_result_def, terminates_def])
    >- metis_tac[])
  >- (
    (* result_equiv at terminating fuels *)
    rpt strip_tac >>
    `lift_result (state_equiv all_elim) (execution_equiv all_elim)
      (run_function fuel ctx fn s) (run_function fuel ctx' fn' s)` by
      metis_tac[] >>
    `terminates (run_function fuel ctx' fn' s)` by (
      Cases_on `run_function fuel ctx fn s` >>
      Cases_on `run_function fuel ctx' fn' s` >>
      fs[lift_result_def, terminates_def]) >>
    `run_function fuel ctx' fn' s =
     run_function fuel' ctx' fn' s` by (
      simp_tac std_ss [Abbr `ctx'`, Abbr `fn'`] >>
      irule run_function_deterministic >> simp[]) >>
    fs[])
QED
