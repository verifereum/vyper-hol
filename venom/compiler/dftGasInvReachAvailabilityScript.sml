Theory dftGasInvReachAvailability
Ancestors
  dftGasInvReachSlice dftGasInvPrefixRun dftGasInvPrefixReach
  dftGasInvOracleAvailability dftGasInvSSAProbe dftGasOracleDefs
  dftRunRel dftAvailability venomWfProps venomExecSemantics
  venomExecProofs venomWf venomInst venomState contextCodegenRel
  dftGasInvPseudoPrefix dftIndexedExec venomInstProofs1 venomExecProps
  dftCorrectness
  list finite_map pred_set

Theorem inv_strict_dom_mono[local]:
  strict_dom_vars_defined fn s /\ t.vs_current_bb = s.vs_current_bb /\
  FDOM s.vs_vars SUBSET FDOM t.vs_vars ==>
  strict_dom_vars_defined fn t
Proof
  rw[strict_dom_vars_defined_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem inv_enters_available[local]:
  enters_block fn s t /\ fn_reachable fn s.vs_current_bb /\
  strict_dom_vars_defined fn s ==>
  fn_reachable fn t.vs_current_bb /\ strict_dom_vars_defined fn t
Proof
  rw[enters_block_def] >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  drule eval_phis_vars_grow >> strip_tac >>
  simp[] >> irule inv_strict_dom_mono >>
  qexists_tac `s` >> simp[]
QED

Theorem inv_ev_prefix_available[local]:
  !n s t. inv_ev_prefix orc p d ctx bb n s t /\
  EVERY inst_wf bb.bb_instructions /\ fn_reachable fn s.vs_current_bb /\
  strict_dom_vars_defined fn s ==>
  fn_reachable fn t.vs_current_bb /\ strict_dom_vars_defined fn t
Proof
  Induct >> simp[inv_ev_prefix_suc] >> rpt strip_tac >>
  `inst_wf inst` by gvs[get_instruction_def, EVERY_EL] >>
  `u.vs_current_bb = s.vs_current_bb` by
    metis_tac[ev_step_nonterm_current_bb] >>
  `FDOM s.vs_vars SUBSET FDOM u.vs_vars` by
    metis_tac[inv_ev_step_fdom_mono] >>
  `strict_dom_vars_defined fn (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule inv_strict_dom_mono >> qexists_tac `s` >> simp[]) >>
  first_x_assum drule >> simp[]
QED

Theorem inv_ev_prefix_terminator_run[local]:
  inv_ev_prefix orc p d ctx bb n entry s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ ~t.vs_halted /\
  ev_step orc p d fuel ctx inst s = OK t ==>
  ?joined. ev_block orc p d joined ctx bb entry = OK t
Proof
  strip_tac >>
  `ev_block orc p d fuel ctx bb s = OK t` by
    (once_rewrite_tac[ev_block_def] >> simp[]) >>
  drule inv_ev_prefix_suffix >> disch_then drule >> simp[]
QED

Theorem inv_ev_available_history[local]:
  !orc initial ctx p d fn inst t.
  ev_reachable orc initial ctx p d fn inst t ==>
  (!f. MEM f ctx.ctx_functions ==> wf_function f /\ ssa_form f /\ fn_inst_wf f) ==>
  ?before u bb n.
    lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
    MEM bb fn.fn_blocks /\ bb.bb_label = before.vs_current_bb /\
    fn_reachable fn before.vs_current_bb /\ strict_dom_vars_defined fn before /\
    eval_phis before bb.bb_instructions = OK u /\
    inv_ev_prefix orc p d ctx bb n
      (u with vs_inst_idx := phi_prefix_length bb.bb_instructions) t /\
    t.vs_current_bb = before.vs_current_bb /\
    get_instruction bb t.vs_inst_idx = SOME inst
Proof
  ho_match_mp_tac ev_reachable_strongind >> rpt strip_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >> suspend "callee"
QED

Resume inv_ev_available_history[entry]:
  qmatch_asmsub_abbrev_tac `enters_block fn before t` >>
      `wf_function fn` by
        (gvs[lookup_function_def] >> metis_tac[FIND_MEM]) >>
      `fn_entry_label fn = SOME before.vs_current_bb` by simp[Abbr `before`] >>
      `fn_reachable fn before.vs_current_bb` by
        simp[fn_reachable_def] >>
      `strict_dom_vars_defined fn before` by
        metis_tac[strict_dom_vars_defined_entry] >>
      qpat_x_assum `enters_block _ _ _` mp_tac >>
      simp[enters_block_def] >> strip_tac >>
      rename1 `eval_phis before bb.bb_instructions = OK u` >>
      drule eval_phis_preserves_current_bb >> strip_tac >>
      qexistsl_tac [`before`, `u`, `bb`, `0`] >> simp[] >>
      `MEM bb fn.fn_blocks /\ bb.bb_label = before.vs_current_bb` by
        metis_tac[lookup_block_MEM, lookup_block_label] >> simp[] >>
      gvs[active_inst_def] >>
      `lookup_block bb.bb_label fn.fn_blocks = SOME bb'` by
        (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
      gvs[get_instruction_def]
QED

Resume inv_ev_available_history[next]:
  first_x_assum drule >> strip_tac >>
      rename1 `ev_step orc p d fuel ctx inst current = OK result` >>
      `wf_function fn` by metis_tac[inv_ev_reachable_function_mem] >>
      `result.vs_current_bb = current.vs_current_bb` by
        metis_tac[ev_step_nonterm_current_bb] >>
      `get_instruction bb (SUC current.vs_inst_idx) = SOME inst'` by
        (qpat_x_assum `active_inst _ inst _` kall_tac >>
         gvs[active_inst_def] >>
         `lookup_block bb.bb_label fn.fn_blocks = SOME bb'` by
           (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
         gvs[get_instruction_def]) >>
      `inv_ev_prefix orc p d ctx bb (SUC 0) current
        (result with vs_inst_idx := SUC current.vs_inst_idx)` by
        (pure_rewrite_tac[inv_ev_prefix_suc, inv_ev_prefix_zero] >> metis_tac[]) >>
      drule_all inv_ev_prefix_compose >> strip_tac >>
      qexistsl_tac [`before`, `u`, `bb`, `n + SUC 0`] >> simp[]
QED

Resume inv_ev_available_history[block]:
  first_x_assum drule >> strip_tac >>
      rename1 `ev_step orc p d fuel ctx inst current = OK result` >>
      `wf_function fn /\ ssa_form fn /\ fn_inst_wf fn` by
        metis_tac[inv_ev_reachable_function_mem] >>
      `EVERY inst_wf bb.bb_instructions` by
        (gvs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
      drule_all inv_ev_prefix_terminator_run >> strip_tac >>
      `fn_reachable fn result.vs_current_bb /\ strict_dom_vars_defined fn result` by
        (irule inv_ev_successor_available >>
         goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[] >>
         qexists_tac `before` >> simp[]) >>
      qpat_x_assum `enters_block _ _ _` mp_tac >>
      simp[enters_block_def] >> strip_tac >>
      rename1 `eval_phis result nextbb.bb_instructions = OK nextu` >>
      drule_at (Pat `eval_phis result _ = _`) eval_phis_preserves_current_bb >> strip_tac >>
      qexistsl_tac [`result`, `nextu`, `nextbb`, `0`] >> simp[] >>
      `MEM nextbb fn.fn_blocks /\ nextbb.bb_label = result.vs_current_bb` by
        metis_tac[lookup_block_MEM, lookup_block_label] >> simp[] >>
      qpat_x_assum `active_inst _ inst _` kall_tac >>
      gvs[active_inst_def] >>
      `lookup_block nextbb.bb_label fn.fn_blocks = SOME bb'` by
        (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
      gvs[get_instruction_def]
QED

Resume inv_ev_available_history[callee]:
  qpat_x_assum `(!f. _) ==> _` kall_tac >>
  rename1 `setup_callee callee args t = SOME cs` >>
  `wf_function callee` by
    (gvs[lookup_function_def] >> metis_tac[FIND_MEM]) >>
  `fn_entry_label callee = SOME cs.vs_current_bb` by
    metis_tac[dft_setup_callee_entry] >>
  `fn_reachable callee cs.vs_current_bb` by simp[fn_reachable_def] >>
  `strict_dom_vars_defined callee cs` by metis_tac[strict_dom_vars_defined_entry] >>
  qpat_x_assum `enters_block _ _ _` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  rename1 `eval_phis cs bb.bb_instructions = OK u` >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  qexistsl_tac [`cs`, `u`, `bb`, `0`] >> simp[] >>
  `MEM bb callee.fn_blocks /\ bb.bb_label = cs.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >> simp[] >>
  qpat_x_assum `active_inst fn _ _` kall_tac >>
  gvs[active_inst_def] >>
  `lookup_block bb.bb_label callee.fn_blocks = SOME bb'` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  gvs[get_instruction_def]
QED

Finalise inv_ev_available_history

Theorem inv_source_structural[local]:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions ==>
  !f. MEM f C.ctx_functions ==> wf_function f /\ ssa_form f /\ fn_inst_wf f /\ fn_pseudos_prefix f
Proof
  strip_tac >>
  `EVERY (\f. wf_function f /\ ssa_form f /\ fn_inst_wf f /\ fn_pseudos_prefix f) C.ctx_functions` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
     first_x_assum drule >> gvs[dft_fn_rel_def, wf_ssa_def]) >>
  gvs[EVERY_MEM]
QED

Theorem inv_ev_reachable_source_available:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ ctx_labels_bound C initial.vs_labels /\ o1_run_state_ok initial /\
  ev_reachable orc initial C p d fn inst t ==>
  fn_reachable fn t.vs_current_bb /\ strict_dom_vars_defined fn t
Proof
  strip_tac >> drule inv_source_structural >> strip_tac >>
  drule inv_ev_available_history >> (impl_tac >- metis_tac[]) >> strip_tac >>
  `fn_inst_wf fn` by metis_tac[inv_ev_reachable_function_mem] >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `fn_reachable fn (u with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_current_bb /\
   strict_dom_vars_defined fn (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (irule inv_enters_available >> qexists_tac `before` >>
     simp[enters_block_def] >> metis_tac[]) >>
  drule_all inv_ev_prefix_available >> simp[]
QED

Theorem inv_ev_step_labels[local]:
  ev_step orc p d fuel ctx inst s = OK t ==> t.vs_labels = s.vs_labels
Proof
  simp[Once ev_step_def] >> Cases_on `inst.inst_opcode = GAS`
  >- (simp[ev_gas_def] >> strip_tac >> gvs[AllCaseEqs()]) >>
  simp[] >> Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[] >> strip_tac >> gvs[AllCaseEqs()] >>
      rename1 `bind_outputs _ ret.iret_values _ = SOME _` >>
      drule inv_bind_outputs_frame >>
      Cases_on `ret.iret_adopt_fmp` >>
      simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  simp[] >> strip_tac >>
  `step_inst fuel ctx inst s = OK t` by
    simp[Once step_inst_def] >>
  metis_tac[step_inst_preserves_labels_always]
QED

Theorem inv_ev_prefix_labels[local]:
  !n s t. inv_ev_prefix orc p d ctx bb n s t ==> t.vs_labels = s.vs_labels
Proof
  Induct >> simp[inv_ev_prefix_suc] >> rpt strip_tac >>
  drule inv_ev_step_labels >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem inv_ev_reachable_labels_bound[local]:
  !orc initial ctx p d fn inst t.
  ev_reachable orc initial ctx p d fn inst t ==>
  ctx_labels_bound ctx initial.vs_labels ==> ctx_labels_bound ctx t.vs_labels
Proof
  ho_match_mp_tac ev_reachable_ind >> rpt strip_tac >>
  gvs[enters_block_def]
  >- (drule eval_phis_preserves_labels >> gvs[])
  >- (drule inv_ev_step_labels >> gvs[])
  >- (drule eval_phis_preserves_labels >> drule inv_ev_step_labels >> gvs[])
  >> drule eval_phis_preserves_labels >> strip_tac >>
  metis_tac[ctx_labels_bound_setup_callee]
QED

Theorem inv_ev_prefix_index[local]:
  !n s t. inv_ev_prefix orc p d ctx bb n s t ==>
    t.vs_inst_idx = s.vs_inst_idx + n
Proof
  Induct >> simp[inv_ev_prefix_suc] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem inv_ev_reachable_source_initialized:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ ctx_labels_bound C initial.vs_labels /\ o1_run_state_ok initial /\
  ev_reachable orc initial C p d fn inst t /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  t.vs_inst_idx = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
  dft_remaining_inv fn bb (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) t
Proof
  strip_tac >> drule inv_source_structural >> strip_tac >>
  drule inv_ev_available_history >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  gvs[] >>
  `wf_function fn /\ fn_inst_wf fn /\ fn_pseudos_prefix fn` by
    metis_tac[inv_ev_reachable_function_mem] >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `pseudos_prefix bb` by metis_tac[fn_pseudos_prefix_def] >>
  qmatch_goalsub_abbrev_tac `dft_remaining_inv fn bb normal t` >>
  qabbrev_tac `pseudos = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions` >>
  `bb.bb_instructions = pseudos ++ normal` by
    suspend "pseudo_partition" >>
  `EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
   EVERY (\i. ~is_pseudo i.inst_opcode) normal` by
    simp[Abbr `pseudos`, Abbr `normal`, EVERY_FILTER] >>
  `EVERY (\i. i.inst_opcode <> PHI) normal` by
    (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `phi_prefix_length bb.bb_instructions = phi_prefix_length pseudos` by
    metis_tac[dft_phi_prefix_append] >>
  `eval_phis before pseudos = OK u` by metis_tac[dft_eval_phis_append] >>
  `n = LENGTH pseudos - phi_prefix_length pseudos` by
    (drule inv_ev_prefix_index >> simp[] >> strip_tac >> decide_tac) >>
  `FOLDR (dft_exec_cons 0 C) OK (DROP (phi_prefix_length pseudos) pseudos)
     (u with vs_inst_idx := phi_prefix_length pseudos) = OK t` by
    (irule inv_pseudo_prefix_drop >> simp[phi_prefix_length_le] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `t.vs_labels = before.vs_labels` by
    (drule inv_ev_prefix_labels >> drule eval_phis_preserves_labels >> simp[]) >>
  `ctx_labels_bound C before.vs_labels` by
    metis_tac[inv_ev_reachable_labels_bound] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  simp[Abbr `normal`] >> irule dft_remaining_inv_initialized >> simp[] >>
  qexistsl_tac [`C`, `0`, `before`, `u`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `ctx_labels_bound C before.vs_labels` mp_tac >>
  simp[ctx_labels_bound_def] >> disch_then irule >>
  qexistsl_tac [`fn`, `i`] >> simp[] >>
  conj_tac
  >- (simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
      qexists_tac `bb` >> simp[]) >>
  metis_tac[inv_ev_reachable_function_mem]
QED

Resume inv_ev_reachable_source_initialized[pseudo_partition]:
  qpat_x_assum `pseudos_prefix bb` mp_tac >>
  simp[pseudos_prefix_def, Abbr `pseudos`, Abbr `normal`] >>
  POP_ASSUM_LIST (K all_tac) >>
  Q.SPEC_TAC (`bb.bb_instructions`, `xs`) >> Induct >> simp[] >>
  gen_tac >> Cases_on `is_pseudo h.inst_opcode` >> simp[] >> strip_tac
  >- (first_x_assum irule >> rpt strip_tac >>
      first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[])
  >> `EVERY (\i. ~is_pseudo i.inst_opcode) xs` by
       (simp[EVERY_EL] >> rpt strip_tac >>
        rename1 `k < LENGTH xs` >>
        first_x_assum (qspecl_then [`0`, `SUC k`] mp_tac) >> simp[]) >>
  gvs[EVERY_MEM] >>
  `FILTER (\i. is_pseudo i.inst_opcode) xs = []` by
    simp[FILTER_EQ_NIL, EVERY_MEM] >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) xs = xs` by
    simp[FILTER_EQ_ID, EVERY_MEM] >> simp[]
QED

Finalise inv_ev_reachable_source_initialized
