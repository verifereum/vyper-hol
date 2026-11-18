(* Execute a kept jump and its destination PHIs at the restored cut point.
   The two reading histories and the saved caller stacks are not changed. *)
Theory gasFocusFmpCutJumpEntry
Ancestors
  gasFocusFmpJumpPoint gasFocusFmpStagePin fmpStageBlockSimEntryAssembly
  fmpStageBlockSimEntryShape fnFrameStepsPhi fmpStageRel o1LowerDloadShared
  o1PassContract contextCodegenRel ptrDiscipline ptrStaticDiscipline
  venomWfProps venomWf venomInst venomExecProofs venomExecSemantics venomState
  finite_map passSimulationDefs

Theorem focus_fmp_cut_jump_entry:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn /\
  wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
  make_ssa_input_ok fn /\ first_block_no_preds fn /\ opaque_use_ok fn /\
  (C.ctx_entry = SOME fn.fn_name ==> entry_fn_no_params fn) /\
  active_inst fn bi sb /\ ~sb.vs_halted /\ MEM bi.inst_opcode [JMP; JNZ; DJMP] /\
  ptr_use_static_ok P (fn_pv P fn) bi /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn bi sb /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn sb lo tb ts /\
  step_inst k C bi sb = OK (jump_to lbl sb) /\
  enters_block fn (jump_to lbl sb) s1 ==>
  active_inst fn' bi tb /\
  (!k'. step_inst k' C' bi tb = OK (jump_to lbl tb)) /\
  ?t1. enters_block fn' (jump_to lbl tb) t1 /\
    fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
      (entry_prov fn (jump_to lbl sb) G)
      (entry_taint_vars fn (jump_to lbl sb) tn) fn s1 lo t1 ts
Proof
  strip_tac >>
  `terminates (OK (jump_to lbl sb))` by simp[terminates_def] >>
  drule_all focus_fmp_jump_point >> strip_tac >>
  rename1 `OK (jump_to lbl sb) = OK (jump_to dst sb)` >>
  `dst = lbl` by
    (qpat_assum `OK (jump_to lbl sb) = OK (jump_to dst sb)` mp_tac >>
     simp[jump_to_def, venom_state_component_equality]) >>
  qpat_x_assum `dst = lbl` SUBST_ALL_TAC >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  drule_all fmp_entry_jump_edge >>
  disch_then (qx_choose_then `pb` strip_assume_tac) >>
  `EL sb.vs_inst_idx pb.bb_instructions = bi` by
    (fs[active_inst_def] >>
     `lookup_block sb.vs_current_bb fn.fn_blocks = SOME bb` by
       (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >> gvs[]) >>
  `all_reachable fn` by fs[make_ssa_input_ok_def] >>
  drule_all fmp_entry_jump_dfs >> strip_tac >>
  drule_all fn_cfg_edge_succs >> strip_tac >>
  `?bb. lookup_block lbl fn.fn_blocks = SOME bb` by
    fs[enters_block_def, jump_to_def] >>
  drule_all focus_fmp_selected_root_pin >>
  disch_then (qx_choose_then `lowered` strip_assume_tac) >>
  `lowered = fn'` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `lowered = fn'` SUBST_ALL_TAC >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  drule fmp_entry_block_phis >>
  disch_then (qspec_then `bb` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `bb'` strip_assume_tac) >>
  `!u. eval_phis u bb'.bb_instructions = eval_phis u bb.bb_instructions` by
    metis_tac[phi_eval_collect] >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_stage_rel_def] >> strip_tac >> gns[] >>
  `?t1. enters_block fn' (jump_to lbl tb) t1 /\
    fmp_frame_rel sm fmp0 raw0 (fmp_frame_base raw0 stk)
      (fmp_frame_lo fmp0 ts) lo F fn fn' PG
      (entry_prov fn (jump_to lbl sb) G)
      (entry_taint_vars fn (jump_to lbl sb) tn).t_var s1 t1` by
    (irule fmpStageBlockSimEntryAssemblyTheory.fmp_entry_frame_from_geometry >>
     simp[] >> rpt gen_tac >> disch_tac >> conj_tac
     >- (rpt gen_tac >> disch_tac >>
         drule fmp_entry_root_label >> strip_tac >>
         qpat_assum `!infos ctx runner rl rp. _` (drule_all_then strip_assume_tac) >>
         simp[]) >>
     irule fmp_entry_phi_tidx >> simp[]) >>
  qexists `t1` >> simp[] >>
  qpat_x_assum `enters_block fn _ s1` mp_tac >>
  qpat_x_assum `enters_block fn' _ t1` mp_tac >>
  simp[enters_block_def, jump_to_def] >> rpt strip_tac >>
  imp_res_tac eval_phis_only_updates_vs_vars >>
  gns[jump_to_def, venom_state_component_equality, entry_taint_vars_def,
      ld_shared_agree_def]
QED
