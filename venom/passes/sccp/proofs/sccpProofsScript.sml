(*
 * SCCP — Function-level correctness proof.
 *
 * Depends on sccpProofsBase for all the helper lemmas.
 *)

Theory sccpProofs
Ancestors
  sccpProofsBase
  analysisSimDefs analysisSimProps analysisSimProofsBase
  sccpDefs sccpSound sccpConvergence
  venomWf venomExecSemantics venomExecProofs venomInst
  dfAnalyzeDefs dfAnalyzeProps
  cfgAnalysisProps cfgDefs
  passSharedDefs passSharedProps venomInstProps venomExecProps
  stateEquiv stateEquivProps
  execEquivParamBase execEquivParamProps
  passSimulationDefs passSimulationProps passSimulationProofs
  finite_map worklistDefs worklistProofs venomState
  list

(* Nophi invariant predicate for the function-level proof *)
Definition nophi_inv_def:
  nophi_inv f s <=>
    MEM s.vs_current_bb (cfg_analyze f).cfg_dfs_pre /\
    (!x c.
       FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
                  s.vs_current_bb 0).sl_vals x = SOME (CL_Const c) /\
       x IN FDOM s.vs_vars /\
       ~is_phi_output_of_block f.fn_blocks s.vs_current_bb x ==>
       FLOOKUP s.vs_vars x = SOME c) /\
    (!x. x IN FDOM s.vs_vars /\
         ~is_phi_output_of_block f.fn_blocks s.vs_current_bb x ==>
       x IN FDOM (df_at sccp_bottom (sccp_df_analyze f)
                    s.vs_current_bb 0).sl_vals /\
       FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
                  s.vs_current_bb 0).sl_vals x <> SOME CL_Top)
End

(* An entry state with empty variables satisfies the nophi invariant *)
Theorem nophi_inv_entry:
  !f s.
    fn_entry_label f = SOME s.vs_current_bb /\
    FDOM s.vs_vars = {} ==>
    nophi_inv f s
Proof
  rpt strip_tac >>
  simp[nophi_inv_def] >>
  metis_tac[entry_label_in_dfs_pre]
QED

(* eval_phis_preserves_current_bb is now in venomExecProofsTheory *)
(* eval_phis preserves lookup for variables that are not PHI outputs
   of any instruction in the list. *)

(* The old sccp_function_lift_result theorem was removed after the eval_phis
   refactor. It was unused, and its original statement no longer matched the
   final SCCP correctness architecture, which is proved in
   sccpCorrectnessProofsTheory.sccp_run_blocks_equiv / sccp_pass_correct_fn. *)
