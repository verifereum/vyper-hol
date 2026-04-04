(*
 * SCCP — Context-level Correctness (API)
 *
 * Top-level theorems only. All helpers in proofs/sccpCorrectnessProofsScript.
 *)

Theory sccpCorrectness
Ancestors
  sccpCorrectnessProofs sccpProofs sccpDefs
  passSimulationDefs passSimulationProps passSimulationProofs
  venomPipelineCorrect
  venomWf venomExecSemantics venomExecProofs venomInst venomState
  stateEquiv stateEquivProps
  finite_map list

Theorem sccp_pass_correct:
  !ctx entry.
    venom_wf ctx /\
    (!f. MEM f ctx.ctx_functions ==> wf_ssa f) /\
    lookup_function entry ctx.ctx_functions <> NONE ==>
    let ctx' = sccp_context ctx in
    ?f f'.
      lookup_function entry ctx.ctx_functions = SOME f /\
      lookup_function entry ctx'.ctx_functions = SOME f' /\
      !s. s.vs_inst_idx = 0 /\ fn_entry_label f = SOME s.vs_current_bb /\
          FDOM s.vs_vars = {} ==>
          pass_correct (state_equiv {}) (execution_equiv {})
            (\fuel. run_function fuel ctx f s)
            (\fuel. run_function fuel ctx' f' s)
Proof
  rpt gen_tac >> strip_tac >>
  simp[LET_THM] >>
  Cases_on `lookup_function entry ctx.ctx_functions` >> fs[] >>
  rename1 `lookup_function entry ctx.ctx_functions = SOME f` >>
  qexists_tac `sccp_fn f` >>
  conj_tac >- (
    simp[sccp_context_def, sccp_fn_def] >>
    metis_tac[lookup_function_sccp_context]) >>
  rpt strip_tac >>
  `MEM f ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `wf_function f /\ fn_inst_wf f` by fs[venom_wf_def] >>
  `wf_ssa f` by metis_tac[] >>
  irule lift_result_implies_pass_correct >>
  simp[] >> rpt conj_tac
  >- (
    (* fuel determinism for exec1 *)
    rpt strip_tac >>
    `!e. run_function fuel ctx f s <> Error e` by
      (Cases_on `run_function fuel ctx f s` >> fs[terminates_def]) >>
    `!e. run_function fuel' ctx f s <> Error e` by
      (Cases_on `run_function fuel' ctx f s` >> fs[terminates_def]) >>
    Cases_on `fuel <= fuel'`
    >- metis_tac[fuel_mono]
    >- (`fuel' <= fuel` by simp[] >> metis_tac[fuel_mono]))
  >- (
    (* fuel determinism for exec2 *)
    rpt strip_tac >>
    `!e. run_function fuel (sccp_context ctx) (sccp_fn f) s <> Error e` by
      (Cases_on `run_function fuel (sccp_context ctx) (sccp_fn f) s` >>
       fs[terminates_def]) >>
    `!e. run_function fuel' (sccp_context ctx) (sccp_fn f) s <> Error e` by
      (Cases_on `run_function fuel' (sccp_context ctx) (sccp_fn f) s` >>
       fs[terminates_def]) >>
    Cases_on `fuel <= fuel'`
    >- metis_tac[fuel_mono]
    >- (`fuel' <= fuel` by simp[] >> metis_tac[fuel_mono]))
  >- (
    (* result_equiv at every fuel *)
    gen_tac >>
    mp_tac (Q.SPECL [`fuel`, `ctx`] sccp_run_function_equiv) >>
    simp[] >> disch_then (qspecl_then [`f`, `s`] mp_tac) >>
    simp[] >>
    (impl_tac >- (
      rpt conj_tac
      >- metis_tac[nophi_inv_entry]
      >- (irule strict_dom_vars_defined_entry >> metis_tac[])
      >- (simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]))) >>
    simp[result_equiv_is_lift_result])
QED

(* Context-level theorem: FDOM s.vs_vars = {} is discharged by
   the calling convention — run_context preserves vs_vars from s,
   and the initial EVM-to-Venom state has empty vs_vars.
   This form is directly composable in the pass pipeline. *)
Theorem sccp_ctx_pass_correct:
  !ctx s.
    venom_wf ctx /\
    (!f. MEM f ctx.ctx_functions ==> wf_ssa f) /\
    FDOM s.vs_vars = {} ==>
    ctx_pass_correct sccp_context (state_equiv {}) (execution_equiv {}) ctx s
Proof
  rpt strip_tac >>
  simp[ctx_pass_correct_def, run_context_def] >>
  (* sccp_context preserves ctx_entry *)
  `(sccp_context ctx).ctx_entry = ctx.ctx_entry` by simp[sccp_context_def] >>
  simp[] >>
  (* Case 1: no entry function *)
  (Cases_on `ctx.ctx_entry` >- simp[pass_correct_def, terminates_def]) >>
  simp[] >> rename1 `ctx.ctx_entry = SOME entry_name` >>
  (* Case 2: entry function not found *)
  (Cases_on `lookup_function entry_name ctx.ctx_functions` >- (
    `lookup_function entry_name (sccp_context ctx).ctx_functions = NONE` by
      metis_tac[lookup_function_none_sccp_context] >>
    simp[pass_correct_def, terminates_def])) >>
  simp[] >> rename1 `_ = SOME fn` >>
  `lookup_function entry_name (sccp_context ctx).ctx_functions =
   SOME (sccp_fn fn)` by
    (simp[sccp_context_def, sccp_fn_def] >>
     irule lookup_function_sccp_context >> simp[]) >>
  simp[] >>
  (* Case 3: empty entry function *)
  (Cases_on `entry_block fn` >- (
    imp_res_tac entry_block_sccp_fn_none >>
    simp[pass_correct_def, terminates_def])) >>
  simp[] >> rename1 `entry_block fn = SOME entry_bb` >>
  (* Resolve entry_block for sccp_fn fn *)
  imp_res_tac entry_block_sccp_fn_some >>
  gvs[] >>
  (* Apply sccp_pass_correct *)
  mp_tac (Q.SPECL [`ctx`, `entry_name`] sccp_pass_correct) >>
  simp[LET_THM] >> strip_tac >> gvs[] >>
  first_x_assum irule >>
  gvs[fn_entry_label_def, entry_block_def, listTheory.NULL_EQ]
QED
