(* Static aliases retain their allocation occurrence, independently of values. *)
Theory readonlyInvokeCopyFwdOccurrenceAlias
Ancestors
  internalReturnCopyFwdAlias o1LowerDloadOccurrence ssaAvailablePred
  ptrDisciplineControl singleUseExpansionSupplySim o1FrameLockstep
  ptrDiscipline list finite_map venomWf venomWfProps venomInst o1PassContract
  venomExecProofs venomExecSemantics rangeAnalysisProofs contextCodegenRel venomInstProps

Definition occurrence_alias_def:
  occurrence_alias fn a H v <=>
    !ai root sz. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
      ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
      ircf_alias fn root v ==> FLOOKUP H v = SOME (a,ai.inst_id)
End

Theorem occurrence_alias_other_output:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> ASSIGN /\
  MEM v inst.inst_outputs ==> occurrence_alias fn a H v
Proof
  simp[occurrence_alias_def] >> metis_tac[ircf_alias_other_output]
QED

Theorem occurrence_alias_preserves:
  ~MEM v inst.inst_outputs /\ occurrence_alias fn a H v ==>
  occurrence_alias fn a (occurrence_step a HP H inst t) v
Proof
  simp[occurrence_alias_def, occurrence_step_def, FLOOKUP_set_prov]
QED

Theorem occurrence_alias_output:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ venomWf$inst_wf inst /\
  MEM v inst.inst_outputs /\
  (!u. MEM (Var u) inst.inst_operands ==> occurrence_alias fn a H u) /\
  step_inst fuel C inst s = OK t ==>
  occurrence_alias fn a (occurrence_step a HP H inst t) v
Proof
  strip_tac >> simp[occurrence_alias_def] >> rpt strip_tac >>
  drule_all ircf_alias_output_inv >> strip_tac
  >- (gvs[] >> drule_all occurrence_alloca_metadata >> strip_tac >>
      simp[occurrence_step_def, occurrence_out_def, set_prov_def, FLOOKUP_UPDATE]) >>
  `inst.inst_operands = [Var u]` by
    (gvs[venomWfTheory.inst_wf_def, LENGTH_EQ_1] >> gvs[]) >>
  `occurrence_alias fn a H u` by metis_tac[MEM] >>
  `FLOOKUP H u = SOME (a,ai.inst_id)` by
    metis_tac[occurrence_alias_def] >>
  simp[occurrence_step_def, occurrence_out_def, out_prov_def,
       first_prov_def, op_prov_def, set_prov_def, FLOOKUP_UPDATE]
QED

Theorem occurrence_alias_boundary_step:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  MEM bb fn.fn_blocks /\ n < LENGTH bb.bb_instructions /\
  inst = EL n bb.bb_instructions /\ inst.inst_opcode <> PHI /\
  boundary_pred fn bb n (occurrence_alias fn a H) /\
  step_inst fuel C inst s = OK t ==>
  boundary_pred fn bb (SUC n)
    (occurrence_alias fn a (occurrence_step a HP H inst t))
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (gvs[fn_insts_def] >> metis_tac[o1PassContractTheory.fn_insts_blocks_MEM, EL_MEM]) >>
  `venomWf$inst_wf inst` by metis_tac[fn_inst_wf_every_bb, EVERY_MEM, EL_MEM] >>
  `ssa_form fn` by gvs[wf_ssa_def] >>
  `!u. MEM (Var u) inst.inst_operands ==> occurrence_alias fn a H u` by
    metis_tac[boundary_pred_operand] >>
  `!v. MEM v inst.inst_outputs ==>
    occurrence_alias fn a (occurrence_step a HP H inst t) v` by
    metis_tac[occurrence_alias_output] >>
  `!v. occurrence_alias fn a H v ==>
    occurrence_alias fn a (occurrence_step a HP H inst t) v` by
    (rpt strip_tac >> Cases_on `MEM v inst.inst_outputs` >>
     metis_tac[occurrence_alias_preserves]) >>
  simp[boundary_pred_def] >> conj_tac
  >- metis_tac[boundary_pred_def, dom_pred_mono] >>
  irule prefix_pred_suc >> metis_tac[boundary_pred_def, prefix_pred_mono]
QED

Theorem occurrence_alias_phis:
  !insts. ssa_form fn /\ EVERY (\i. MEM i (fn_insts fn)) insts /\
  occurrence_alias fn a H v ==>
  occurrence_alias fn a (phis_prov prev H insts) v
Proof
  Induct >> simp[phis_prov_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  `occurrence_alias fn a (phis_prov prev H insts) v` by metis_tac[EVERY_DEF] >>
  simp[occurrence_alias_def] >> rpt strip_tac >>
  `~MEM v h.inst_outputs` by
    (strip_tac >> drule_all ircf_alias_output_inv >> strip_tac >> gvs[]) >>
  simp[FLOOKUP_set_prov] >> metis_tac[occurrence_alias_def]
QED

Theorem occurrence_alias_phi_prefix:
  ssa_form fn /\ MEM bb fn.fn_blocks ==>
  prefix_pred bb (phi_prefix_length bb.bb_instructions) (occurrence_alias fn a H)
Proof
  rw[prefix_pred_def] >>
  `(EL j bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[phi_prefix_length_el_phi] >>
  irule occurrence_alias_other_output >> simp[] >>
  qexists_tac `EL j bb.bb_instructions` >> simp[] >>
  gvs[fn_insts_def] >> metis_tac[fn_insts_blocks_MEM, EL_MEM]
QED

Theorem occurrence_alias_block_entry:
  ssa_form fn /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  dom_pred fn bb.bb_label (occurrence_alias fn a H) ==>
  boundary_pred fn bb (phi_prefix_length bb.bb_instructions)
    (occurrence_alias fn a (entry_prov fn s H))
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions` by
    (simp[EVERY_MEM, fn_insts_def] >> metis_tac[fn_insts_blocks_MEM]) >>
  simp[boundary_pred_def] >> reverse conj_tac
  >- metis_tac[occurrence_alias_phi_prefix] >>
  irule dom_pred_mono >> qexists_tac `occurrence_alias fn a H` >> simp[] >>
  rpt strip_tac >> gvs[entry_prov_def] >> metis_tac[occurrence_alias_phis]
QED

Definition occurrence_alias_boundary_def:
  occurrence_alias_boundary fn s a H <=>
    fn_reachable fn s.vs_current_bb /\
    ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      boundary_pred fn bb s.vs_inst_idx (occurrence_alias fn a H)
End

Theorem occurrence_alias_entry:
  ssa_form fn /\ fn_entry_label fn = SOME s.vs_current_bb /\
  enters_block fn s t ==> occurrence_alias_boundary fn t a H
Proof
  strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by metis_tac[enters_block_current_bb] >>
  simp[occurrence_alias_boundary_def] >> conj_tac
  >- (simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]) >>
  gvs[enters_block_def] >>
  simp[boundary_pred_def] >> conj_tac
  >- metis_tac[dom_pred_entry, lookup_block_label] >>
  metis_tac[occurrence_alias_phi_prefix, lookup_block_MEM]
QED

Theorem occurrence_alias_call:
  ssa_form callee /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs t ==> occurrence_alias_boundary callee t a H
Proof
  strip_tac >> irule occurrence_alias_entry >> simp[] >>
  qexists_tac `cs` >> simp[] >>
  gvs[setup_callee_def, fn_entry_label_def, entry_block_def]
QED

Theorem occurrence_alias_next:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  occurrence_alias_boundary fn s a H /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK t ==>
  occurrence_alias_boundary fn (t with vs_inst_idx := SUC s.vs_inst_idx)
    a (occurrence_step a HP H inst t)
Proof
  strip_tac >> fs[occurrence_alias_boundary_def, active_inst_def] >>
  `bb' = bb` by metis_tac[lookup_block_MEM, lookup_block_label, same_label_same_block] >>
  gvs[] >>
  `t.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> PHI` by
    (strip_tac >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  simp[] >> irule occurrence_alias_boundary_step >> metis_tac[lookup_block_MEM]
QED

Theorem occurrence_alias_restrict:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  occurrence_alias fn a H v ==>
  occurrence_alias fn a (DRESTRICT H (COMPL (set inst.inst_outputs))) v
Proof
  strip_tac >> simp[occurrence_alias_def] >> rpt strip_tac >>
  `~MEM v inst.inst_outputs` by
    (strip_tac >> drule_all ircf_alias_output_inv >> strip_tac >> gvs[]) >>
  simp[FLOOKUP_DRESTRICT] >> metis_tac[occurrence_alias_def]
QED

Theorem occurrence_alias_boundary_return:
  ssa_form fn /\ MEM bb fn.fn_blocks /\ n < LENGTH bb.bb_instructions /\
  inst = EL n bb.bb_instructions /\ inst.inst_opcode = INVOKE /\
  boundary_pred fn bb n (occurrence_alias fn a H) ==>
  boundary_pred fn bb (SUC n)
    (occurrence_alias fn a (DRESTRICT H (COMPL (set inst.inst_outputs))))
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (gvs[fn_insts_def] >> metis_tac[fn_insts_blocks_MEM, EL_MEM]) >>
  `!v. occurrence_alias fn a H v ==>
    occurrence_alias fn a (DRESTRICT H (COMPL (set inst.inst_outputs))) v` by
    metis_tac[occurrence_alias_restrict] >>
  simp[boundary_pred_def] >> conj_tac
  >- metis_tac[boundary_pred_def, dom_pred_mono] >>
  irule prefix_pred_suc >> reverse conj_tac
  >- metis_tac[boundary_pred_def, prefix_pred_mono] >>
  rpt strip_tac >> irule occurrence_alias_other_output >> simp[] >>
  qexists_tac `inst` >> simp[]
QED

Theorem occurrence_alias_block:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  occurrence_alias_boundary fn s a H /\ active_inst fn inst s /\
  is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK t /\
  ~t.vs_halted /\ enters_block fn t s1 ==>
  occurrence_alias_boundary fn s1 a (entry_prov fn t H)
Proof
  strip_tac >> fs[occurrence_alias_boundary_def, active_inst_def] >>
  `bb' = bb` by metis_tac[lookup_block_MEM, lookup_block_label, same_label_same_block] >>
  gvs[] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  `bb_well_formed bb` by gvs[wf_function_def] >>
  `EVERY venomWf$inst_wf bb.bb_instructions` by metis_tac[fn_inst_wf_every_bb] >>
  `fn_cfg_edge fn s.vs_current_bb t.vs_current_bb` by
    metis_tac[sue_terminator_cfg_edge] >>
  `s1.vs_current_bb = t.vs_current_bb` by metis_tac[enters_block_current_bb] >>
  conj_tac >- metis_tac[fn_reachable_step] >>
  `dom_pred fn t.vs_current_bb (occurrence_alias fn a H)` by
    metis_tac[boundary_pred_exit] >>
  gvs[enters_block_def] >>
  irule occurrence_alias_block_entry >> metis_tac[wf_ssa_def, lookup_block_label]
QED

Theorem occurrence_alias_return:
  ssa_form fn /\ wf_function fn /\ occurrence_alias_boundary fn s a H /\
  active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s e)) = SOME t ==>
  occurrence_alias_boundary fn (t with vs_inst_idx := SUC s.vs_inst_idx) a
    (DRESTRICT H (COMPL (set inst.inst_outputs)))
Proof
  strip_tac >> fs[occurrence_alias_boundary_def, active_inst_def] >>
  `bb' = bb` by metis_tac[lookup_block_MEM, lookup_block_label, same_label_same_block] >>
  gvs[] >>
  `t.vs_current_bb = s.vs_current_bb` by metis_tac[bind_return_current_bb] >>
  simp[] >> irule occurrence_alias_boundary_return >> metis_tac[lookup_block_MEM]
QED

Definition occurrence_alias_saved_def:
  (occurrence_alias_saved [] stk <=> stk = []) /\
  (occurrence_alias_saved (u::U) stk <=>
    ?f fs. stk = f::fs /\ wf_ssa f.cf_fn /\ wf_function f.cf_fn /\ fn_inst_wf f.cf_fn /\
      active_inst f.cf_fn f.cf_inst f.cf_state /\ f.cf_inst.inst_opcode = INVOKE /\
      occurrence_alias_boundary f.cf_fn f.cf_state u.of_owner u.of_prov /\
      occurrence_alias_saved U fs)
End

Theorem occurrence_alias_reachable:
  !vs C stk PG G tn fn inst s n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
    EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
    EVERY fn_inst_wf C.ctx_functions ==>
    wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
    occurrence_alias_boundary fn s a H /\ occurrence_alias_saved U stk
Proof
  ho_match_mp_tac occ_frame_reachable_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> strip_tac
  >- (simp[occurrence_alias_saved_def] >>
      `wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn` by
        metis_tac[lookup_function_MEM, EVERY_MEM] >> simp[] >>
      irule occurrence_alias_entry >> conj_tac >- gvs[wf_ssa_def] >>
      goal_assum (drule_at Any) >> simp[])
  >- metis_tac[occurrence_alias_next]
  >- metis_tac[occurrence_alias_block]
  >- (fs[] >> rename1 `lookup_function nm C.ctx_functions = SOME callee` >>
      `wf_ssa callee /\ wf_function callee /\ fn_inst_wf callee` by
        metis_tac[lookup_function_MEM, EVERY_MEM] >>
      simp[occurrence_alias_saved_def] >>
      irule occurrence_alias_call >> metis_tac[wf_ssa_def])
  >> fs[occurrence_alias_saved_def] >>
  metis_tac[occurrence_alias_return, wf_ssa_def]
QED

Theorem occurrence_alias_reachable_available:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!P. boundary_pred fn bb s.vs_inst_idx P ==> P v) /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
  ircf_alias fn root v ==> FLOOKUP H v = SOME (a,ai.inst_id)
Proof
  strip_tac >> drule occurrence_alias_reachable >> simp[] >> strip_tac >>
  fs[occurrence_alias_boundary_def] >>
  `occurrence_alias fn a H v` by metis_tac[optionTheory.SOME_11] >>
  metis_tac[occurrence_alias_def]
QED

Theorem occurrence_alias_reachable_operand:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [root] /\ ai.inst_operands = [Lit sz] /\
  ircf_alias fn root v ==> FLOOKUP H v = SOME (a,ai.inst_id)
Proof
  strip_tac >> drule occurrence_alias_reachable >> simp[] >> strip_tac >>
  `active_inst fn inst s` by
    gvs[Once occ_frame_reachable_cases] >>
  fs[occurrence_alias_boundary_def, active_inst_def] >>
  `bb' = bb` by metis_tac[lookup_block_MEM, lookup_block_label, same_label_same_block] >>
  gvs[] >>
  `occurrence_alias fn a H v` by metis_tac[boundary_pred_operand, lookup_block_MEM] >>
  metis_tac[occurrence_alias_def]
QED
