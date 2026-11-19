(* Recover the source point after the PHIs on a successful jump edge. *)
Theory gasFocusFmpCutSourceJump
Ancestors
  o1PassContract o1PassLift o1ContractSimplifyCfgSrcFrame
  lowerDloadPtrRawReachable o1LowerDloadEntryFetch simplifyCfgAvailability
  makeSsaCurrentLockstep makeSsaCurrentPhiBatchRuntime dfAnalyzeProofs
  contextCodegenRel analysisSimProofsBase venomExecSemantics venomExecProofs
  venomWf venomWfProps venomState venomInst finite_map list

Theorem focus_source_jump_phis[local]:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phis_cover_preds fn /\ MEM bb fn.fn_blocks /\ MEM pb fn.fn_blocks /\
  fn_cfg_edge fn pb.bb_label bb.bb_label /\ s.vs_prev_bb = SOME pb.bb_label /\
  scfg_path_defined fn path pb (LENGTH pb.bb_instructions) s ==>
  ?sp. eval_phis s bb.bb_instructions = OK sp
Proof
  strip_tac >> irule current_phi_batch_success_all >> rpt strip_tac >>
  rename1 `MEM i bb.bb_instructions` >>
  `inst_wf i` by (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `phi_well_formed i.inst_operands /\ LENGTH i.inst_outputs = 1` by
    (qpat_x_assum `inst_wf i` mp_tac >> simp[inst_wf_def]) >>
  `?v. MEM (pb.bb_label,v) (phi_pairs i.inst_operands)` by
    metis_tac[fn_phis_cover_preds_def] >>
  `?x. resolve_phi pb.bb_label i.inst_operands = SOME (Var x)` by
    metis_tac[phi_pairs_resolve_phi_some, resolve_phi_well_formed] >>
  `MEM (pb.bb_label,x) (phi_pairs i.inst_operands)` by
    metis_tac[resolve_phi_pair] >>
  `IS_SOME (lookup_var x s)` by
    (irule scfg_phi_edge_defined >> qexistsl [`bb`,`fn`,`i`,`path`,`pb`] >> simp[]) >>
  Cases_on `i.inst_outputs` >> gvs[eval_one_phi_def, eval_operand_def] >>
  Cases_on `lookup_var x s` >> gvs[]
QED

Theorem focus_fmp_cut_source_jump_entry:
  o1_ctx_shape C /\ o1_fn_row 3 fn /\ root.vs_vars = FEMPTY /\
  ~root.vs_halted /\ frame_reachable root C stk PG G tn fn bi sb /\
  active_inst fn bi sb /\ MEM bi.inst_opcode [JMP;JNZ;DJMP] /\
  step_inst k C bi sb = OK (jump_to lbl sb) /\
  MEM lbl (MAP (\bb. bb.bb_label) fn.fn_blocks) ==>
  ?s1 i. enters_block fn (jump_to lbl sb) s1 /\ active_inst fn i s1
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[frame_reachable_raw_certificate] >>
  `!f. MEM f C.ctx_functions ==> wf_function f /\ fn_inst_wf f` by
    fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
  `wf_function fn /\ fn_inst_wf fn` by simp[] >>
  `fn_defs_reach_uses fn /\ fn_phis_cover_preds fn` by
    fs[o1_fn_row_def, make_ssa_input_ok_def] >>
  `!nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f` by
    metis_tac[lookup_function_MEM] >>
  drule_all scfg_frame_reachable_entry_root >> strip_tac >>
  `is_terminator bi.inst_opcode` by gvs[is_terminator_def] >>
  `~sb.vs_halted` by
    (drule supply_frame_reach_not_halted >> fs[fn_entry_state_def]) >>
  `~(jump_to lbl sb).vs_halted` by simp[jump_to_def] >>
  drule_all lockstep_active_terminator_edge >> strip_tac >>
  drule_all scfg_frame_path_endpoint >>
  disch_then (qx_choose_then `pb` (qx_choose_then `path` strip_assume_tac)) >>
  `?bb. lookup_block lbl fn.fn_blocks = SOME bb` by
    metis_tac[lookup_block_exists] >>
  `MEM pb fn.fn_blocks /\ pb.bb_label = sb.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `?sp. eval_phis (jump_to lbl sb) bb.bb_instructions = OK sp` by
    (irule focus_source_jump_phis >> qexistsl [`fn`,`path`,`pb`] >>
     fs[jump_to_def]) >>
  `enters_block fn (jump_to lbl sb)
     (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[enters_block_def, jump_to_def] >> qexists `sp` >> fs[jump_to_def]) >>
  drule_all ld_wf_enters_block_fetch >> metis_tac[]
QED
