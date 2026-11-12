(* Static aliases retain their allocation occurrence, independently of values. *)
Theory readonlyInvokeCopyFwdOccurrenceAlias
Ancestors
  internalReturnCopyFwdAlias o1LowerDloadOccurrence ssaAvailablePred
  ptrDisciplineControl singleUseExpansionSupplySim o1FrameLockstep
  ptrDiscipline list finite_map venomWf venomWfProps venomInst o1PassContract
  venomExecProofs venomExecSemantics rangeAnalysisProofs

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
  gvs[enters_block_def] >> goal_assum drule >>
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
  rw[occurrence_alias_boundary_def, active_inst_def] >>
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
