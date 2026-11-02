Theory dftFrameVars
Ancestors
  sccpCorrectnessProofs contextCodegenRel venomExecProofs venomExecProps
  venomWf cfgDefs finite_map venomInstProps venomExecSemantics venomInst venomState pred_set list
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

Theorem dft_frame_prefix_edge:
  wf_function f /\ fn_inst_wf f /\ dft_frame_prefix f s /\
  active_inst f i s /\ is_terminator i.inst_opcode /\
  step_inst fuel C i s = OK t /\ ~t.vs_halted ==>
  fn_cfg_edge f s.vs_current_bb t.vs_current_bb
Proof
  rw[active_inst_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `inst_wf (EL s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[MEM_EL]) >>
  `EL s.vs_inst_idx bb.bb_instructions = LAST bb.bb_instructions` by
    (fs[bb_well_formed_def] >> metis_tac[LAST_EL]) >>
  `~is_terminator INVOKE` by EVAL_TAC >>
  `MEM t.vs_current_bb (get_successors (LAST bb.bb_instructions))` by
    (irule step_inst_base_term_succs >>
     fs[] >> qexists `s` >>
     ` (LAST bb.bb_instructions).inst_opcode <> INVOKE` by metis_tac[] >>
     fs[step_inst_non_invoke]) >>
  simp[fn_cfg_edge_def] >> qexists `bb` >>
  Cases_on `bb.bb_instructions` >>
  gvs[bb_succs_def, bb_well_formed_def, MEM_nub]
QED

Theorem dft_terminator_fdom:
  step_inst fuel C i s = OK t /\ is_terminator i.inst_opcode ==>
  FDOM t.vs_vars = FDOM s.vs_vars
Proof
  strip_tac >> drule_all step_terminator_preserves_vars >>
  simp[lookup_var_def] >> strip_tac >>
  simp[EXTENSION] >> metis_tac[flookup_thm]
QED

Theorem dft_frame_departing_outputs:
  wf_function f /\ fn_inst_wf f /\ dft_frame_prefix f s /\
  active_inst f i s /\ is_terminator i.inst_opcode /\
  MEM bb f.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs ==>
  v IN FDOM s.vs_vars
Proof
  rw[active_inst_def] >>
  `bb' = bb` by metis_tac[same_label_same_block] >> gvs[] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[bb_well_formed_def] >>
  `?k. k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst` by
    metis_tac[MEM_EL] >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `k <> s.vs_inst_idx` by
    (strip_tac >> gvs[] >>
     metis_tac[terminator_no_outputs, MEM]) >>
  `k < s.vs_inst_idx` by decide_tac >>
  fs[dft_frame_prefix_def] >> metis_tac[]
QED

Theorem dft_frame_prefix_terminator:
  wf_function f /\ fn_inst_wf f /\ dft_frame_prefix f s /\
  active_inst f i s /\ is_terminator i.inst_opcode /\
  step_inst fuel C i s = OK t /\ ~t.vs_halted /\
  enters_block f t u /\ active_inst f j u ==> dft_frame_prefix f u
Proof
  rpt strip_tac >>
  `fn_cfg_edge f s.vs_current_bb t.vs_current_bb` by
    metis_tac[dft_frame_prefix_edge] >>
  `FDOM t.vs_vars = FDOM s.vs_vars` by
    metis_tac[dft_terminator_fdom] >>
  `fn_reachable f s.vs_current_bb` by fs[dft_frame_prefix_def] >>
  `fn_reachable f t.vs_current_bb` by metis_tac[fn_reachable_step] >>
  `strict_dom_vars_defined f t` by
    (rw[strict_dom_vars_defined_def] >>
     Cases_on `d_bb.bb_label = s.vs_current_bb`
     >- (drule_all dft_frame_departing_outputs >> simp[]) >>
     `fn_dominates f d_bb.bb_label s.vs_current_bb` by
       metis_tac[fn_dominates_predecessor] >>
     fs[dft_frame_prefix_def, strict_dom_vars_defined_def] >> metis_tac[]) >>
  drule_all dft_frame_prefix_enters >> simp[]
QED
