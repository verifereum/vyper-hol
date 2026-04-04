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
  venomWf venomExecSemantics venomInst
  dfAnalyzeDefs dfAnalyzeProofs
  cfgAnalysisProps cfgDefs
  passSharedDefs passSharedProps venomInstProps venomExecProps
  stateEquiv stateEquivProps
  execEquivParamBase execEquivParamProps
  passSimulationDefs passSimulationProps passSimulationProofs
  finite_map worklistDefs worklistProofs venomState
  list

(* state_equiv {} implies full equality of venom_state *)
Triviality state_equiv_empty_eq[local]:
  !s1 s2. state_equiv {} s1 s2 ==> s1 = s2
Proof
  rpt strip_tac >>
  fs[state_equiv_def, execution_equiv_def] >>
  simp[venom_state_component_equality] >>
  simp[FLOOKUP_EXT, FUN_EQ_THM] >> fs[lookup_var_def]
QED

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

(* Entry state trivially satisfies nophi invariant *)
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

(* Function-level lift_result via direct fuel induction *)
Theorem sccp_function_lift_result:
  !f.
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\
    ~sccp_has_static_assertion_failure (sccp_df_analyze f) f ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      nophi_inv f s ==>
      (?e. run_function fuel ctx f s = Error e) \/
      lift_result (state_equiv {}) (execution_equiv {})
        (run_function fuel ctx f s)
        (run_function fuel ctx
          (analysis_function_transform sccp_bottom (sccp_df_analyze f)
            (\lat inst. [sccp_inst lat.sl_vals inst]) f) s)
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `fuel`
  >- (
    (* Base: fuel = 0 => Error "out of fuel" *)
    rpt strip_tac >>
    ONCE_REWRITE_TAC[run_function_def] >> simp[])
  >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
  qabbrev_tac `fn' = analysis_function_transform sccp_bottom (sccp_df_analyze f)
    (\lat inst. [sccp_inst lat.sl_vals inst]) f` >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks`
  >- simp[]
  >>
  rename1 `_ = SOME bb` >>
  `MEM bb f.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  (* Lookup in transformed function *)
  `lookup_block s.vs_current_bb fn'.fn_blocks =
    SOME (analysis_block_transform sccp_bottom (sccp_df_analyze f)
      (\lat inst. [sccp_inst lat.sl_vals inst]) bb)` by (
    simp[Abbr `fn'`, analysis_function_transform_def,
         function_map_transform_def] >>
    `lookup_block s.vs_current_bb (MAP
       (analysis_block_transform sccp_bottom (sccp_df_analyze f)
         (\lat inst. [sccp_inst lat.sl_vals inst])) f.fn_blocks) =
     OPTION_MAP (analysis_block_transform sccp_bottom (sccp_df_analyze f)
         (\lat inst. [sccp_inst lat.sl_vals inst]))
       (lookup_block s.vs_current_bb f.fn_blocks)` suffices_by simp[] >>
    irule lookup_block_map_proof >>
    simp[abt_label]) >>
  qabbrev_tac `bt_bb = analysis_block_transform sccp_bottom (sccp_df_analyze f)
    (\lat inst. [sccp_inst lat.sl_vals inst]) bb` >>
  simp[] >>
  (* Per-block simulation *)
  `MEM bb.bb_label (cfg_analyze f).cfg_dfs_pre` by
    fs[nophi_inv_def] >>
  mp_tac (Q.SPECL [`f`, `bb`] sccp_per_block_sim_nophi) >>
  simp[] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  impl_tac >- fs[nophi_inv_def] >>
  strip_tac
  >- simp[]
  >>
  (* lift_result for run_block *)
  Cases_on `run_block fuel ctx bb s`
  >> gvs[lift_result_def]
  >- (
    (* run_block = OK v *)
    rename1 `run_block fuel ctx bb s = OK v` >>
    Cases_on `run_block fuel ctx bt_bb s`
    >> gvs[lift_result_def, Abbr `bt_bb`]
    >- (
      (* Both OK *)
      rename1 `state_equiv {} v v'` >>
      `v = v'` by metis_tac[state_equiv_empty_eq] >>
      gvs[] >>
      Cases_on `v.vs_halted`
      >- (
        simp[lift_result_def] >>
        fs[state_equiv_def])
      >>
      simp[] >>
      `v.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
      `nophi_inv f v` by (
        simp[nophi_inv_def] >>
        mp_tac (Q.SPECL [`f`, `bb`, `fuel`, `ctx`, `s`, `v`]
          sccp_cross_block_inv) >>
        simp[] >>
        impl_tac >- fs[nophi_inv_def] >>
        strip_tac >> simp[]) >>
      first_x_assum (qspecl_then [`ctx`, `v`] mp_tac) >>
      simp[]))
  >> (
    Cases_on `run_block fuel ctx bt_bb s`
    >> gvs[lift_result_def, Abbr `bt_bb`])
QED

(* Wrapper: sccp_function_lift_result with original signature *)
Theorem sccp_function_lift_result_entry[local]:
  !f.
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\
    ~sccp_has_static_assertion_failure (sccp_df_analyze f) f ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      fn_entry_label f = SOME s.vs_current_bb /\
      FDOM s.vs_vars = {} ==>
      (?e. run_function fuel ctx f s = Error e) \/
      lift_result (state_equiv {}) (execution_equiv {})
        (run_function fuel ctx f s)
        (run_function fuel ctx
          (analysis_function_transform sccp_bottom (sccp_df_analyze f)
            (\lat inst. [sccp_inst lat.sl_vals inst]) f) s)
Proof
  rpt strip_tac >>
  irule sccp_function_lift_result >> simp[] >>
  metis_tac[nophi_inv_entry]
QED

