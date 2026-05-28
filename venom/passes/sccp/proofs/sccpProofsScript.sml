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
  finite_map worklistDefs worklistProps venomState
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
(* eval_one_phi returns an output that is a member of inst.inst_outputs *)
Triviality eval_one_phi_output_mem[local]:
  !s inst out v. eval_one_phi s inst = SOME (out,v) ==> MEM out inst.inst_outputs
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[eval_one_phi_def] >>
  Cases_on `t` >> gvs[eval_one_phi_def] >>
  Cases_on `s.vs_prev_bb` >> gvs[eval_one_phi_def] >>
  gvs[AllCaseEqs()]
QED
(* eval_phis preserves lookup for variables that are not PHI outputs
   of any instruction in the list. *)
Triviality eval_phis_flookup_not_phi_output[local]:
  !s insts x s'.
    eval_phis s insts = OK s' /\
    (!inst. MEM inst insts ==> inst.inst_opcode = PHI ==> ~MEM x inst.inst_outputs) ==>
    FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x
Proof
  Induct_on `insts`
  >- (rpt strip_tac >> fs[eval_phis_def])
  >> rpt strip_tac >> fs[eval_phis_def]
  >> Cases_on `h.inst_opcode = PHI` >> fs[] >> rfs[]
  >> Cases_on `eval_one_phi s h` >> fs[]
  >> PairCases_on `x'` >> fs[]
  >> Cases_on `eval_phis s insts` >> fs[update_var_def, FLOOKUP_UPDATE]
  >> `FLOOKUP v.vs_vars x = FLOOKUP s.vs_vars x`
     by (qsuff_tac `∀s''. eval_phis s insts = OK s'' ⇒
           FLOOKUP s''.vs_vars x = FLOOKUP s.vs_vars x`
         >- metis_tac[] >> metis_tac[])
  >> `x'0 ≠ x` by (
       CCONTR_TAC >> fs[] >>
       first_x_assum (qspec_then `h` mp_tac) >> simp[] >>
       metis_tac[eval_one_phi_output_mem])
  >> `s' = v with vs_vars := v.vs_vars⟨x'0 ↦ x'1⟩` by metis_tac[]
  >> fs[FLOOKUP_UPDATE]
QED
(* eval_phis preserves FDOM for variables that are not PHI outputs *)
Triviality eval_phis_fdom_not_phi_output[local]:
  !s insts x s'.
    eval_phis s insts = OK s' /\
    x IN FDOM s.vs_vars /\
    (!inst. MEM inst insts ==> inst.inst_opcode = PHI ==> ~MEM x inst.inst_outputs) ==>
    x IN FDOM s'.vs_vars
Proof
  rpt strip_tac >>
  imp_res_tac eval_phis_flookup_not_phi_output >>
  fs[TO_FLOOKUP]
QED

(* A variable that is not a PHI output of the block is not a PHI output
   of any instruction in the block's instruction list. *)
Triviality not_phi_output_of_block_imp_not_phi_output_insts[local]:
  !bbs lbl x bb.
    lookup_block lbl bbs = SOME bb /\
    ~is_phi_output_of_block bbs lbl x ==>
    !inst. MEM inst bb.bb_instructions ==>
           inst.inst_opcode = PHI ==>
           ~MEM x inst.inst_outputs
Proof
  rpt strip_tac >>
  CCONTR_TAC >>
  fs[is_phi_output_of_block_def] >>
  metis_tac[]
QED

(* eval_phis preserves the nophi invariant when processing a block's instructions *)
Triviality eval_phis_preserves_nophi_inv[local]:
  !f s s' bb.
    nophi_inv f s /\
    eval_phis s bb.bb_instructions = OK s' /\
    s.vs_current_bb = bb.bb_label /\
    lookup_block bb.bb_label f.fn_blocks = SOME bb ==>
    nophi_inv f s'
Proof
  rpt strip_tac >>
  fs[nophi_inv_def] >>
  `s'.vs_current_bb = s.vs_current_bb` by metis_tac[eval_phis_preserves_current_bb] >>
  conj_tac >- simp[] >>
  conj_tac >- (
    rpt strip_tac >>
    `!inst. MEM inst bb.bb_instructions ==>
            inst.inst_opcode = PHI ==> ~MEM x inst.inst_outputs`
      by metis_tac[not_phi_output_of_block_imp_not_phi_output_insts] >>
    `FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x`
      by metis_tac[eval_phis_flookup_not_phi_output] >>
    `FLOOKUP s.vs_vars x = SOME c` by metis_tac[TO_FLOOKUP] >>
    simp[]) >>
  rpt strip_tac >>
  `!inst. MEM inst bb.bb_instructions ==>
          inst.inst_opcode = PHI ==> ~MEM x inst.inst_outputs`
    by metis_tac[not_phi_output_of_block_imp_not_phi_output_insts] >>
  `FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x`
    by metis_tac[eval_phis_flookup_not_phi_output] >>
  `x IN FDOM s.vs_vars` by metis_tac[TO_FLOOKUP] >>
  metis_tac[]
QED

(* The old sccp_function_lift_result theorem was removed after the eval_phis
   refactor. It was unused, and its original statement no longer matched the
   final SCCP correctness architecture, which is proved in
   sccpCorrectnessProofsTheory.sccp_run_blocks_equiv / sccp_pass_correct_fn. *)
