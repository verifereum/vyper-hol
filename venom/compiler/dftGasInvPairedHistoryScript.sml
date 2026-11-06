Theory dftGasInvPairedHistory
Ancestors
  dftGasInvPairedSuccessor dftGasInvPairedPrefix dftGasInvReachSlice
  dftGasInvBlockInit dftLifting
  dftGasInvPrefixRun dftGasInvPrefixReach dftGasInvCallerExtract
  dftGasOracleDefs dftRunRel dftDefs dftCorrectness dftStructural
  o1PassContract unitShapeDefs venomExecSemantics venomExecProofs
  venomInst venomState venomWf contextCodegenRel list rich_list

Theorem inv_paired_function_lookup[local]:
  !fs gs name.
  LIST_REL (\fn fn'. fn' = dft_fn fn) fs gs /\ LIST_REL dft_fn_rel fs gs ==>
  OPTREL (\fn fn'. fn' = dft_fn fn /\ dft_fn_rel fn fn')
    (lookup_function name fs) (lookup_function name gs)
Proof
  Induct >> Cases_on `gs` >> simp[lookup_function_def, FIND_thm] >>
  rpt strip_tac >>
  `h'.fn_name = h.fn_name` by fs[dft_fn_rel_def] >>
  simp[] >> IF_CASES_TAC >> gvs[lookup_function_def]
QED

Theorem inv_paired_target_wf[local]:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\
  fn' = dft_fn fn /\ dft_fn_rel fn fn' ==> wf_function fn'
Proof
  gvs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> strip_tac >>
  irule dft_fn_wf_function >> gvs[dft_fn_rel_def, fn_shape_ok_def] >> metis_tac[]
QED

Theorem inv_paired_entry_data[local]:
  dft_fn_rel fn fn' /\ wf_function fn' /\ enters_block fn' before entry /\
  active_inst fn' inst entry ==>
  enters_block fn before entry /\
  ?bb bb' first.
    lookup_block entry.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block entry.vs_current_bb fn'.fn_blocks = SOME bb' /\
    get_instruction bb entry.vs_inst_idx = SOME first /\
    active_inst fn first entry /\
    entry.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
    entry.vs_inst_idx = phi_prefix_length bb'.bb_instructions /\
    get_instruction bb' entry.vs_inst_idx = SOME inst
Proof
  strip_tac >> drule_all inv_related_successor_entry >> strip_tac >>
  qpat_x_assum `enters_block fn' _ _` mp_tac >> simp[enters_block_def] >> strip_tac >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  `lookup_block entry.vs_current_bb fn'.fn_blocks = SOME bb'` by gvs[] >>
  drule_all inv_lookup_phis >> strip_tac >>
  `get_instruction bb' entry.vs_inst_idx = SOME inst` by
    (qpat_x_assum `active_inst fn' inst entry` mp_tac >> simp[active_inst_def] >> strip_tac >>
     rename1 `MEM activebb fn'.fn_blocks` >>
     `lookup_block entry.vs_current_bb fn'.fn_blocks = SOME activebb` by
       (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
     gvs[get_instruction_def]) >>
  qexists_tac `bb'` >> gvs[]
QED

Theorem inv_paired_history:
  !orc initial C' p d fn' inst t.
  ev_reachable orc initial C' p d fn' inst t ==> !C.
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_run_state_ok initial ==>
  ?fn entry sourcefirst bb bb' n.
    MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
    ev_reachable orc initial C p d fn sourcefirst entry /\
    active_inst fn sourcefirst entry /\
    lookup_block entry.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block entry.vs_current_bb fn'.fn_blocks = SOME bb' /\
    entry.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
    entry.vs_inst_idx = phi_prefix_length bb'.bb_instructions /\
    inv_ev_prefix orc p d C' bb' n entry t /\
    get_instruction bb' t.vs_inst_idx = SOME inst /\
    t.vs_current_bb = entry.vs_current_bb /\
    t.vs_inst_idx = entry.vs_inst_idx + n
Proof
  ho_match_mp_tac ev_reachable_strongind >> rpt strip_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >> suspend "callee"
QED

Resume inv_paired_history[entry]:
  `?fn. lookup_function name C.ctx_functions = SOME fn /\
     fn' = dft_fn fn /\ dft_fn_rel fn fn'` by
    (drule_all inv_paired_function_lookup >>
     disch_then (qspec_then `name` mp_tac) >>
     Cases_on `lookup_function name C.ctx_functions` >> gvs[] >>
     strip_tac >> gvs[]) >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_def, FIND_MEM] >>
  `wf_function fn'` by
    (irule inv_paired_target_wf >> goal_assum (drule_at (Pat `MEM _ C.ctx_functions`)) >> simp[]) >>
  drule_all inv_paired_entry_data >> strip_tac >>
  `ev_reachable orc initial C [] 1 fn first t` by
    (irule ev_reachable_entry >> simp[] >> metis_tac[dft_fn_rel_entry_label]) >>
  qexistsl_tac [`fn`, `t`, `first`, `bb`, `bb'`, `0`] >> simp[]
QED
Resume inv_paired_history[next]:
  first_x_assum (qspec_then `C` mp_tac) >> simp[] >> strip_tac >>
  `s'.vs_current_bb = t.vs_current_bb` by metis_tac[ev_step_nonterm_current_bb] >>
  `wf_function fn'` by
    (irule inv_paired_target_wf >> goal_assum (drule_at (Pat `MEM _ C.ctx_functions`)) >> simp[]) >>
  `get_instruction bb' (SUC t.vs_inst_idx) = SOME inst'` by
    (qpat_x_assum `active_inst _ _ t` kall_tac >>
     qpat_x_assum `active_inst fn' inst' _` mp_tac >> simp[NoAsms, active_inst_def] >> strip_tac >>
     rename1 `MEM activebb fn'.fn_blocks` >>
     `lookup_block entry.vs_current_bb fn'.fn_blocks = SOME activebb` by
       (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
     gvs[get_instruction_def]) >>
  `inv_ev_prefix orc p d C' bb' (SUC 0) t
     (s' with vs_inst_idx := SUC t.vs_inst_idx)` by
    (pure_rewrite_tac[GSYM arithmeticTheory.ONE, inv_ev_prefix_suc, inv_ev_prefix_zero] >>
     metis_tac[]) >>
  drule_all inv_ev_prefix_compose >> strip_tac >>
  qexistsl_tac [`fn`, `entry`, `sourcefirst`, `bb`, `bb'`, `n+1`] >>
  simp[] >> metis_tac[arithmeticTheory.ONE]
QED
Resume inv_paired_history[block]:
  first_x_assum (qspec_then `C` mp_tac) >> simp[] >> strip_tac >>
  `get_instruction bb entry.vs_inst_idx = SOME sourcefirst` by
    (qpat_x_assum `active_inst fn sourcefirst entry` mp_tac >>
     simp[NoAsms, active_inst_def] >> strip_tac >> rename1 `MEM activebb fn.fn_blocks` >>
     `lookup_block entry.vs_current_bb fn.fn_blocks = SOME activebb` by
       (irule MEM_lookup_block >> gvs[dft_fn_rel_def, wf_function_def, fn_labels_def]) >>
     gvs[get_instruction_def]) >>
  drule_all inv_paired_successor >> strip_tac >>
  `wf_function fn'` by
    (irule inv_paired_target_wf >> goal_assum (drule_at (Pat `MEM _ C.ctx_functions`)) >> simp[]) >>
  drule_all inv_paired_entry_data >> strip_tac >>
  goal_assum (drule_at (Pat `ev_reachable _ _ C _ (SUC d) _ _ _`)) >>
  simp[] >> metis_tac[]
QED
Resume inv_paired_history[callee]:
  first_x_assum (qspec_then `C` mp_tac) >> simp[] >> strip_tac >>
  `EVERY inst_shape_ok bb.bb_instructions` by
    (`MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
     gvs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM,
         fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  drule_all inv_paired_prefix_invoke >> strip_tac >>
  drule_all inv_invoke_observation_decode >> strip_tac >>
  `?callee. lookup_function nm C.ctx_functions = SOME callee /\
     fn'' = dft_fn callee /\ dft_fn_rel callee fn''` by
    (drule_all inv_paired_function_lookup >>
     disch_then (qspec_then `nm` mp_tac) >>
     Cases_on `lookup_function nm C.ctx_functions` >> gvs[] >> strip_tac >> gvs[]) >>
  `MEM callee C.ctx_functions` by metis_tac[lookup_function_def, FIND_MEM] >>
  `setup_callee callee args sS = SOME cs` by metis_tac[dft_fn_rel_setup_callee] >>
  `wf_function fn''` by
    (irule inv_paired_target_wf >> goal_assum (drule_at (Pat `MEM _ C.ctx_functions`)) >> simp[]) >>
  drule_all inv_paired_entry_data >> strip_tac >>
  `ev_reachable orc initial C ((d,inst.inst_id)::p) (SUC d) callee first t'` by
    (irule ev_reachable_callee >> simp[] >>
     goal_assum (drule_at (Pat `ev_reachable _ _ C _ _ _ inst sS`)) >>
     simp[] >> metis_tac[ev_reachable_cases]) >>
  goal_assum (drule_at (Pat `ev_reachable _ _ C _ (SUC d) callee _ _`)) >>
  simp[] >> metis_tac[]
QED
Finalise inv_paired_history
