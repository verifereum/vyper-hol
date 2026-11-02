Theory dftFrameVars
Ancestors
  sccpCorrectnessProofs contextCodegenRel venomExecProofs venomExecProps
  venomWf cfgDefs finite_map venomInstProps venomExecSemantics list
Libs
  BasicProvers

Definition dft_frame_prefix_def:
  dft_frame_prefix f s <=>
    strict_dom_vars_defined f s /\ fn_reachable f s.vs_current_bb /\
    (!bb. MEM bb f.fn_blocks /\ bb.bb_label = s.vs_current_bb ==>
      phi_prefix_length bb.bb_instructions <= s.vs_inst_idx /\
      s.vs_inst_idx < LENGTH bb.bb_instructions /\
      (!j v. j < s.vs_inst_idx /\
        MEM v (EL j bb.bb_instructions).inst_outputs ==>
        v IN FDOM s.vs_vars))
End

Theorem dft_frame_prefix_enters:
  wf_function f /\ fn_inst_wf f /\ strict_dom_vars_defined f s /\
  fn_reachable f s.vs_current_bb /\ enters_block f s t /\
  active_inst f i t ==> dft_frame_prefix f t
Proof
  rw[enters_block_def, active_inst_def] >>
  `s_phi.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `FDOM s.vs_vars SUBSET FDOM s_phi.vs_vars` by
    metis_tac[eval_phis_vars_grow] >>
  `MEM bb f.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  fs[] >>
  `bb' = bb` by metis_tac[same_label_same_block] >>
  gvs[dft_frame_prefix_def] >>
  conj_tac
  >- (rw[strict_dom_vars_defined_def] >>
      `v IN FDOM s.vs_vars` by
        metis_tac[strict_dom_vars_defined_def] >>
      fs[pred_setTheory.SUBSET_DEF]) >>
  rpt strip_tac >>
  `bb' = bb` by metis_tac[same_label_same_block] >>
  gvs[] >>
  metis_tac[eval_phis_outputs_in_fdom_idx]
QED

Theorem dft_frame_prefix_step:
  wf_function f /\ fn_inst_wf f /\ dft_frame_prefix f s /\
  active_inst f i s /\ ~is_terminator i.inst_opcode /\
  step_inst fuel C i s = OK t /\
  active_inst f j (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
  dft_frame_prefix f (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `i.inst_opcode <> PHI` by
    (strip_tac >>
     fs[step_inst_non_invoke, step_inst_base_def]) >>
  `inst_wf i` by
    (gvs[active_inst_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[MEM_EL]) >>
  drule_all step_inst_fdom >> strip_tac >>
  fs[active_inst_def] >>
  `bb' = bb` by metis_tac[same_label_same_block] >>
  gvs[dft_frame_prefix_def] >>
  conj_tac
  >- (rw[strict_dom_vars_defined_def] >>
      `v IN FDOM s.vs_vars` by metis_tac[strict_dom_vars_defined_def] >>
      simp[]) >>
  rpt strip_tac >>
  `bb' = bb` by metis_tac[same_label_same_block] >>
  gvs[]
  >- (first_x_assum (drule_then mp_tac) >> simp[]) >>
  Cases_on `j = s.vs_inst_idx` >> gvs[] >>
  `j < s.vs_inst_idx` by decide_tac >>
  `v IN FDOM s.vs_vars` by metis_tac[] >> simp[]
QED
