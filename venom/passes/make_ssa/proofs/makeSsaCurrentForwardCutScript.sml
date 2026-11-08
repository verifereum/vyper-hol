Theory makeSsaCurrentForwardCut
Ancestors
  makeSsaCurrentCutInv makeSsaCurrentForwardBase makeSsaCurrentForwardInvoke
  makeSsaCurrentLockstepShape makeSsaCurrentCleanupShape makeSsaCurrentWfSsa
  o1PassLift o1FrameLockstep venomExecProps venomWf venomInst list
  makeSsaCurrentSourceCuts makeSsaCurrentDemand makeSsaCurrentCertificate
  makeSsaCurrentDemandRuntime simplifyCfgSimTools

Theorem current_cut_final_last_output_slots:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  A l = current_block_annotations old pre /\
  LENGTH (collect_phis old.bb_instructions) <= i /\
  i < LENGTH old.bb_instructions ==>
  ?bb. lookup_block l
    (simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed) = SOME bb /\
    current_last_output_slots (current_cut_sg fn A renamed H events l i)
      (EL i old.bb_instructions).inst_outputs
      (EL (LENGTH pre + i) bb.bb_instructions).inst_outputs
      (current_cut_sg fn A renamed H events l (SUC i))
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn` by fs[current_wf_phi_context_def] >>
  `?new. lookup_block l renamed = SOME new` by
    (drule current_wf_precleanup_labels >> strip_tac >>
     `ALL_DISTINCT (MAP (\bb. bb.bb_label) renamed)` by
       fs[wf_function_def, fn_labels_def] >>
     `MEM l (MAP (\bb. bb.bb_label) renamed)` by
       metis_tac[lookup_block_MEM, venomExecProofsTheory.lookup_block_label, MEM_MAP] >>
     fs[MEM_MAP] >> metis_tac[MEM_lookup_block]) >>
  `MEM new renamed /\ new.bb_label = l` by
    metis_tac[lookup_block_MEM, venomExecProofsTheory.lookup_block_label] >>
  drule_all current_wf_precleanup_block_shape >> strip_tac >>
  drule current_wf_precleanup_structural >> strip_tac >>
  `lookup_block (current_event_label ev) fn.fn_blocks = SOME old` by simp[] >>
  drule_all current_wf_certificate_actual_prefix >> strip_tac >>
  `LENGTH pre = LENGTH pre'` by
    (`LENGTH (current_block_annotations old pre) =
      LENGTH (current_block_annotations old pre')` by metis_tac[] >>
     qpat_x_assum `LENGTH (current_block_annotations _ _) = _` mp_tac >>
     simp[current_block_annotations_def, current_inserted_annotations_def]) >>
  `bb_well_formed old` by metis_tac[lookup_block_MEM, wf_function_def] >>
  `(EL i old.bb_instructions).inst_opcode <> PHI` by
    (fs[bb_well_formed_def] >>
     metis_tac[current_phi_index_before_prefix, arithmeticTheory.NOT_LESS]) >>
  drule_all current_wf_edge_shape_ordinary_index >> strip_tac >>
  suspend "final_slots"
QED

Resume current_cut_final_last_output_slots[final_slots]:
  `?rs E. current_source_cut A ev (LENGTH pre + i) rs E` by
    metis_tac[current_wf_event_source_cut_exists, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  `LENGTH pre + i < LENGTH (current_event_input_block ev).bb_instructions` by simp[] >>
  drule_all current_wf_event_source_cut_step >> strip_tac >>
  drule makeSsaCurrentRenameTraceTheory.current_inst_trace_projection >> strip_tac >>
  drule rename_current_inst_signature >> strip_tac >>
  `LENGTH (current_event_renamed_block ev).bb_instructions =
     LENGTH pre + LENGTH old.bb_instructions` by
    (`LENGTH (current_event_renamed_block ev).bb_instructions =
       LENGTH (current_event_input_block ev).bb_instructions` by
       (qpat_x_assum `current_event_trace A H ev` mp_tac >> PairCases_on `ev` >>
        simp[makeSsaCurrentTreeTraceTheory.current_event_trace_def,
          makeSsaCurrentFinalBlockTheory.current_event_renamed_block_def,
          current_event_input_block_def] >>
        metis_tac[current_local_trace_lengths]) >>
     fs[makeSsaCurrentFinalBlockTheory.current_edge_shape_def, LIST_REL_EL_EQN]) >>
  `LENGTH new.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
   (EL (LENGTH pre + i) new.bb_instructions).inst_opcode <> PHI` by
    (fs[makeSsaCurrentFinalBlockTheory.current_edge_shape_def, LIST_REL_EL_EQN] >>
     metis_tac[]) >>
  drule_all current_wf_phi_context_cleanup_split >> strip_tac >>
  qpat_x_assum `new.bb_instructions = _` (fn th => assume_tac th) >>
  rename1 `new.bb_instructions = bp ++ bt` >>
  `LENGTH bp <= LENGTH pre + i` by
    (Cases_on `LENGTH pre + i < LENGTH bp` >> simp[] >>
     `MEM (EL (LENGTH pre + i) bp) bp` by metis_tac[EL_MEM] >>
     fs[EL_APPEND_EQN, EVERY_MEM]) >>
  `bt <> [] /\ (HD bt).inst_opcode <> PHI` by
    (Cases_on `bt` >> fs[EVERY_DEF] >> gvs[]) >>
  `LENGTH pre + i - LENGTH bp < LENGTH bt` by fs[] >>
  drule_all current_cut_last_output_slots >> strip_tac >>
  `?bb. lookup_block l
     (simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed) = SOME bb /\
     LENGTH bb.bb_instructions = LENGTH new.bb_instructions /\
     current_inst_no_id (EL (LENGTH bp + (LENGTH pre + i - LENGTH bp)) bb.bb_instructions) =
     current_inst_no_id (EL (LENGTH pre + i - LENGTH bp) bt)` by
    (irule current_cleanup_if_ordinary_index >> metis_tac[]) >>
  qexists_tac `bb` >>
  gvs[current_inst_no_id_def, instruction_component_equality, EL_APPEND_EQN]
QED
Finalise current_cut_final_last_output_slots

Theorem current_cut_inv_ordinary_step_forward:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  entry_block fn = SOME eb /\
  inst_wf (EL i old.bb_instructions) /\
  lookup_block l fn.fn_blocks = SOME old /\
  A l = current_block_annotations old pre /\
  LENGTH (collect_phis old.bb_instructions) <= i /\
  i < LENGTH old.bb_instructions /\
  st.vs_current_bb = l /\
  current_cut_inv fn A renamed H events l i st st' ==>
  ?bb'. lookup_block l fn'.fn_blocks = SOME bb' /\
    LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
    inst_pair (current_cut_sg fn A renamed H events l i)
      (EL i old.bb_instructions) (EL (LENGTH pre + i) bb'.bb_instructions) /\
    (!fuel. case step_inst fuel C (EL i old.bb_instructions) st of
      OK t => ?t'. step_inst fuel C (EL (LENGTH pre + i) bb'.bb_instructions) st' = OK t' /\
        current_cut_inv fn A renamed H events l (SUC i) t t'
    | Error e => T
    | r => frame_result_rel r
        (step_inst fuel C (EL (LENGTH pre + i) bb'.bb_instructions) st'))
Proof
  strip_tac >>
  `ctx_bisim C C` by metis_tac[ctx_bisim_refl] >>
  drule_all current_cut_inv_ordinary_step >> strip_tac >>
  drule_all current_cut_final_last_output_slots >> strip_tac >>
  `bb = bb'` by gvs[] >>
  qpat_x_assum `bb = bb'` SUBST_ALL_TAC >>
  qexists_tac `bb'` >> asm_rewrite_tac [] >>
  `bb_well_formed old` by
    metis_tac[current_wf_phi_context_def, lookup_block_MEM, wf_function_def] >>
  `(EL i old.bb_instructions).inst_opcode <> PHI` by
    (fs[bb_well_formed_def] >>
     metis_tac[current_phi_index_before_prefix, arithmeticTheory.NOT_LESS]) >>
  `state_rel (current_cut_sg fn A renamed H events l i) st st'` by
    fs[current_cut_inv_def] >>
  `fn_inst_wf fn` by fs[current_wf_phi_context_def] >>
  `!v. current_demand fn v l i ==> IS_SOME (lookup_var v st)` by
    fs[current_cut_inv_def] >>
  gen_tac >> Cases_on `(EL i old.bb_instructions).inst_opcode = INVOKE`
  >- (drule_all current_exec_invoke_pair_forward >>
      disch_then (qspecl_then [`fuel`, `C`] mp_tac) >>
      Cases_on `step_inst fuel C (EL i old.bb_instructions) st` >>
      simp[arithmeticTheory.ADD_COMM] >>
      strip_tac >>
      `!w. current_demand fn w l (SUC i) ==> IS_SOME (lookup_var w v)` by
        (MATCH_MP_TAC (Q.INST [`bb` |-> `old`] current_demand_step_defined) >>
         asm_rewrite_tac[]) >>
      qexists_tac `t'` >> asm_rewrite_tac[current_cut_inv_def]) >>
  Cases_on `step_inst fuel C (EL i old.bb_instructions) st` >> simp[]
  >- (drule_all current_exec_step_noninvoke_ok_pair_forward >>
      disch_then (qspec_then `C` strip_assume_tac) >>
      qexists_tac `t'` >> simp[current_cut_inv_def] >>
      conj_tac >- fs[arithmeticTheory.ADD_COMM] >>
      MATCH_MP_TAC (Q.INST [`bb` |-> `old`] current_demand_step_defined) >>
      asm_rewrite_tac[])
  >- (drule_all current_exec_step_noninvoke_halt_pair_forward >>
      disch_then (qspec_then `C` strip_assume_tac) >> RULE_ASSUM_TAC (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]) >>
      fs[frame_result_rel_def])
  >- (drule_all current_exec_step_noninvoke_abort_pair_forward >>
      disch_then (qspec_then `C` strip_assume_tac) >> RULE_ASSUM_TAC (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]) >>
      fs[frame_result_rel_def]) >>
  drule_all current_exec_step_noninvoke_intret_pair_forward >>
  disch_then (qspec_then `C` strip_assume_tac) >> RULE_ASSUM_TAC (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]) >>
      fs[frame_result_rel_def]
QED
