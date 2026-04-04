(*
 * SCCP — Context-level Correctness (API)
 *
 * Top-level theorems only. All helpers in proofs/sccpCorrectnessProofs.
 *)

Theory sccpCorrectness
Ancestors
  sccpCorrectnessProofs sccpDefs
  venomPipelineCorrect
  venomExecSemantics venomInst venomWf
  passSimulationDefs

Theorem sccp_pass_correct =
  sccpCorrectnessProofsTheory.sccp_pass_correct

Theorem sccp_ctx_pass_correct:
  !ctx s.
    venom_wf ctx /\
    (!f. MEM f ctx.ctx_functions ==> wf_ssa f) /\
    FDOM s.vs_vars = {} ==>
    ctx_pass_correct sccp_context (state_equiv {}) (execution_equiv {}) ctx s
Proof
  rpt strip_tac >>
  simp[ctx_pass_correct_def, run_context_def] >>
  `(sccp_context ctx).ctx_entry = ctx.ctx_entry` by simp[sccp_context_def] >>
  simp[] >>
  (Cases_on `ctx.ctx_entry` >- simp[pass_correct_def, terminates_def]) >>
  simp[] >> rename1 `ctx.ctx_entry = SOME entry_name` >>
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
  (Cases_on `entry_block fn` >- (
    imp_res_tac entry_block_sccp_fn_none >>
    simp[pass_correct_def, terminates_def])) >>
  simp[] >> rename1 `entry_block fn = SOME entry_bb` >>
  imp_res_tac entry_block_sccp_fn_some >>
  gvs[] >>
  mp_tac (Q.SPECL [`ctx`, `entry_name`] sccp_pass_correct) >>
  simp[LET_THM] >> strip_tac >> gvs[] >>
  first_x_assum irule >>
  gvs[fn_entry_label_def, entry_block_def, listTheory.NULL_EQ]
QED
