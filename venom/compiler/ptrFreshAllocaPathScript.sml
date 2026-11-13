(* Completed block paths and the allocation sites they have executed. *)
Theory ptrFreshAllocaPath
Ancestors
  ptrDiscipline ptrDisciplineControl o1LowerDloadOccurrence venomInstProofs
  venomWf venomExecSemantics venomExecProofs rangeAnalysisProofs finite_map list pred_set
  singleUseExpansionSupplySim venomWfProps simplifyCfgPhiSemantics

Definition frame_alloca_path_def:
  frame_alloca_path fn s <=>
    ?done.
      is_fn_path fn (done ++ [s.vs_current_bb]) /\
      fn_entry_label fn = SOME (HD (done ++ [s.vs_current_bb])) /\
      s.vs_prev_bb = (if done = [] then NONE else SOME (LAST done)) /\
      (!bb ai. MEM bb fn.fn_blocks /\ MEM bb.bb_label done /\
        MEM ai bb.bb_instructions /\ ai.inst_opcode = ALLOCA ==>
        ai.inst_id IN FDOM s.vs_allocas) /\
      (!bb k. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        k < s.vs_inst_idx /\ k < LENGTH bb.bb_instructions /\
        (EL k bb.bb_instructions).inst_opcode = ALLOCA ==>
        (EL k bb.bb_instructions).inst_id IN FDOM s.vs_allocas)
End

Theorem frame_alloca_path_transport:
  frame_alloca_path fn s /\ t.vs_current_bb = s.vs_current_bb /\
  t.vs_prev_bb = s.vs_prev_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
  s.vs_allocas SUBMAP t.vs_allocas ==> frame_alloca_path fn t
Proof
  rw[frame_alloca_path_def] >> qexists_tac `done` >> simp[] >>
  metis_tac[SUBMAP_FDOM_SUBSET, SUBSET_DEF]
QED

Theorem frame_alloca_path_phi_entry:
  fn_entry_label fn = SOME s.vs_current_bb /\ s.vs_prev_bb = NONE /\
  enters_block fn s t ==> frame_alloca_path fn t
Proof
  rw[frame_alloca_path_def] >> qexists_tac `[]` >>
  drule enters_block_current_bb >> strip_tac >>
  gvs[contextCodegenRelTheory.enters_block_def] >>
  drule eval_phis_only_updates_vs_vars >> strip_tac >>
  simp[is_fn_path_def] >> conj_tac
  >- (qpat_x_assum `s_phi = _` SUBST1_TAC >> simp[]) >>
  rpt strip_tac >> imp_res_tac phi_prefix_length_el_phi >> gvs[]
QED

Theorem frame_alloca_path_next:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  frame_alloca_path fn s /\ active_inst fn ai s /\
  ~is_terminator ai.inst_opcode /\ ai.inst_opcode <> INVOKE /\
  step_inst fuel C ai s = OK t ==>
  frame_alloca_path fn (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_prev_bb = s.vs_prev_bb` by
    metis_tac[step_preserves_control_flow] >>
  `s.vs_allocas SUBMAP t.vs_allocas` by
    metis_tac[step_inst_noninvoke_allocas_submap] >>
  fs[frame_alloca_path_def] >> qexists_tac `done` >> simp[] >>
  conj_tac
  >- metis_tac[SUBMAP_FDOM_SUBSET, SUBSET_DEF] >>
  rpt strip_tac >>
  Cases_on `k < s.vs_inst_idx`
  >- metis_tac[SUBMAP_FDOM_SUBSET, SUBSET_DEF] >>
  `k = s.vs_inst_idx` by decide_tac >> gvs[] >>
  fs[contextCodegenRelTheory.active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb'` by
    metis_tac[MEM_lookup_block] >>
  gvs[] >> drule_all occurrence_alloca_metadata >>
  simp[FLOOKUP_DEF] >> metis_tac[]
QED

Theorem frame_alloca_path_enter:
  frame_alloca_path fn s /\
  (!bb. MEM bb fn.fn_blocks ==> bb_well_formed bb) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn ai s /\ is_terminator ai.inst_opcode /\
  fn_cfg_edge fn s.vs_current_bb t.vs_current_bb /\
  t.vs_prev_bb = SOME s.vs_current_bb /\
  s.vs_allocas SUBMAP t.vs_allocas /\ enters_block fn t u ==>
  frame_alloca_path fn u
Proof
  strip_tac >>
  `u.vs_current_bb = t.vs_current_bb` by metis_tac[enters_block_current_bb] >>
  fs[contextCodegenRelTheory.enters_block_def] >>
  drule eval_phis_only_updates_vs_vars >> strip_tac >>
  `u.vs_prev_bb = SOME s.vs_current_bb` by
    (gvs[] >> qpat_x_assum `s_phi = _` SUBST1_TAC >> simp[]) >>
  fs[frame_alloca_path_def] >>
  qexists_tac `done ++ [s.vs_current_bb]` >>
  qpat_x_assum `s_phi = _` SUBST1_TAC >>
  simp[] >>
  conj_tac
  >- (irule is_fn_path_snoc >> simp[]) >>
  conj_tac >- (Cases_on `done` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> fs[MEM_APPEND] 
      >- metis_tac[SUBMAP_FDOM_SUBSET, SUBSET_DEF] >>
      gvs[] >>
      fs[contextCodegenRelTheory.active_inst_def] >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb'` by
        metis_tac[MEM_lookup_block] >>
      `bb'' = bb'` by metis_tac[MEM_lookup_block, optionTheory.SOME_11] >>
      gvs[] >>
      `bb_well_formed bb'` by metis_tac[] >>
      fs[bb_well_formed_def] >>
      `s.vs_inst_idx = PRE (LENGTH bb'.bb_instructions)` by metis_tac[] >>
      qpat_x_assum `MEM ai' _` mp_tac >> simp[MEM_EL] >>
      strip_tac >>
      `n < s.vs_inst_idx` by
        (Cases_on `n = s.vs_inst_idx` >> gvs[venomInstTheory.is_terminator_def] >> decide_tac) >>
      metis_tac[SUBMAP_FDOM_SUBSET, SUBSET_DEF]) >>
  rpt strip_tac >> imp_res_tac phi_prefix_length_el_phi >> gvs[]
QED

Theorem frame_alloca_path_resume:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  frame_alloca_path fn s /\ active_inst fn ai s /\
  ai.inst_opcode <> ALLOCA /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_prev_bb = s.vs_prev_bb /\
  s.vs_allocas SUBMAP t.vs_allocas ==>
  frame_alloca_path fn (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> fs[frame_alloca_path_def] >> qexists_tac `done` >> simp[] >>
  conj_tac >- metis_tac[SUBMAP_FDOM_SUBSET, SUBSET_DEF] >>
  rpt strip_tac >> Cases_on `k < s.vs_inst_idx`
  >- metis_tac[SUBMAP_FDOM_SUBSET, SUBSET_DEF] >>
  `k = s.vs_inst_idx` by decide_tac >> gvs[] >>
  fs[contextCodegenRelTheory.active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb'` by
    metis_tac[MEM_lookup_block] >> gvs[]
QED

Theorem frame_alloca_path_return:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  frame_alloca_path fn s /\ active_inst fn ai s /\ ai.inst_opcode = INVOKE /\
  bind_outputs ai.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se)) = SOME t ==>
  frame_alloca_path fn (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_prev_bb = s.vs_prev_bb /\
   t.vs_allocas = s.vs_allocas` by
    (qspec_then `\u. (u.vs_current_bb, u.vs_prev_bb, u.vs_allocas)` mp_tac
       venomInstProofs1Theory.bind_outputs_preserves >>
     simp[venomStateTheory.update_var_def] >>
     disch_then drule >>
     Cases_on `ret.iret_adopt_fmp` >>
     simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  irule frame_alloca_path_resume >> simp[] >> qexists_tac `ai` >> simp[]
QED

Theorem frame_alloca_path_block:
  wf_function fn /\ fn_inst_wf fn /\ frame_alloca_path fn s /\
  active_inst fn ai s /\ is_terminator ai.inst_opcode /\
  step_inst fuel C ai s = OK t /\ ~t.vs_halted /\ enters_block fn t u ==>
  frame_alloca_path fn u
Proof
  strip_tac >>
  `ai.inst_opcode <> INVOKE` by (strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  `s.vs_allocas SUBMAP t.vs_allocas` by
    metis_tac[step_inst_noninvoke_allocas_submap] >>
  `t.vs_prev_bb = SOME s.vs_current_bb` by
    metis_tac[step_inst_base_term_prev_bb, step_inst_non_invoke] >>
  `fn_cfg_edge fn s.vs_current_bb t.vs_current_bb` by
    (fs[contextCodegenRelTheory.active_inst_def] >>
     `bb_well_formed bb` by metis_tac[wf_function_def] >>
     `EVERY inst_wf bb.bb_instructions` by metis_tac[fn_inst_wf_every_bb] >>
     metis_tac[sue_terminator_cfg_edge]) >>
  irule frame_alloca_path_enter >>
  gvs[wf_function_def, venomInstTheory.fn_labels_def] >> metis_tac[]
QED

Theorem frame_alloca_path_callee:
  setup_callee fn args s = SOME cs /\ enters_block fn cs t ==>
  frame_alloca_path fn t
Proof
  strip_tac >> irule frame_alloca_path_phi_entry >> qexists_tac `cs` >>
  gvs[setup_callee_def, AllCaseEqs(), venomInstTheory.fn_entry_label_def,
      venomInstTheory.entry_block_def]
QED

Theorem frame_reachable_alloca_path:
  !vs C stk PG G tn fn ai s.
  frame_reachable vs C stk PG G tn fn ai s ==>
  (!f. MEM f C.ctx_functions ==> wf_function f /\ fn_inst_wf f) ==>
  MEM fn C.ctx_functions /\ frame_alloca_path fn s /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions /\
    frame_alloca_path f.cf_fn f.cf_state /\
    active_inst f.cf_fn f.cf_inst f.cf_state /\
    f.cf_inst.inst_opcode = INVOKE) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> simp[] >>
      `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
      simp[] >> irule frame_alloca_path_phi_entry >>
      qexists_tac `vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` >>
      simp[])
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
      irule frame_alloca_path_next >>
      gvs[wf_function_def, venomInstTheory.fn_labels_def] >> metis_tac[])
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
      irule frame_alloca_path_block >> metis_tac[])
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
      metis_tac[venomInstTheory.lookup_function_MEM, frame_alloca_path_callee])
  >> rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
  irule frame_alloca_path_return >>
  gvs[wf_function_def, venomInstTheory.fn_labels_def] >> metis_tac[]
QED

Theorem frame_alloca_path_fresh_phi_exclusion:
  !fn s ai out bb phi_inst pred.
  wf_ssa fn /\ frame_alloca_path fn s /\ active_inst fn ai s /\
  ai.inst_opcode = ALLOCA /\ MEM out ai.inst_outputs /\
  FLOOKUP s.vs_allocas ai.inst_id = NONE /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  MEM phi_inst bb.bb_instructions /\ phi_inst.inst_opcode = PHI /\
  s.vs_prev_bb = SOME pred ==>
  resolve_phi pred phi_inst.inst_operands <> SOME (Var out)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `phi_edge_uses_wf fn bb phi_inst` by
    metis_tac[wf_ssa_def, def_dominates_uses_def] >>
  `MEM (pred,out) (phi_pairs phi_inst.inst_operands)` by
    metis_tac[scfg_resolve_phi_pair] >>
  fs[phi_edge_uses_wf_def] >>
  first_x_assum drule >> strip_tac >>
  fs[def_available_at_def, contextCodegenRelTheory.active_inst_def] >>
  `bb' = def_bb /\ ai = def_inst` by
    metis_tac[wf_ssa_def, ssa_unique_output_block, EL_MEM] >>
  gvs[] >>
  fs[frame_alloca_path_def] >>
  Cases_on `done = []` >- gvs[] >>
  `is_fn_path fn done` by
    metis_tac[is_fn_path_init, SNOC_APPEND] >>
  `fn_entry_label fn = SOME (HD done)` by
    (Cases_on `done` >> gvs[]) >>
  `MEM s.vs_current_bb done` by
    (qpat_x_assum `fn_dominates _ _ _` mp_tac >>
     simp[fn_dominates_def] >> strip_tac >>
     first_x_assum (qspec_then `done` mp_tac) >> simp[]) >>
  `bb'.bb_instructions❲s.vs_inst_idx❳.inst_id IN FDOM s.vs_allocas` by
    metis_tac[EL_MEM] >>
  gvs[FLOOKUP_DEF]
QED

Theorem frame_reachable_fresh_alloca_phi_exclusion:
  !vs C stk PG G tn fn ai s out bb phi_inst pred.
  (!f. MEM f C.ctx_functions ==> wf_function f /\ fn_inst_wf f /\ wf_ssa f) /\
  frame_reachable vs C stk PG G tn fn ai s /\ active_inst fn ai s /\
  ai.inst_opcode = ALLOCA /\ MEM out ai.inst_outputs /\
  FLOOKUP s.vs_allocas ai.inst_id = NONE /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  MEM phi_inst bb.bb_instructions /\ phi_inst.inst_opcode = PHI /\
  s.vs_prev_bb = SOME pred ==>
  resolve_phi pred phi_inst.inst_operands <> SOME (Var out)
Proof
  rpt strip_tac >>
  `MEM fn C.ctx_functions /\ frame_alloca_path fn s` by
    metis_tac[frame_reachable_alloca_path] >>
  metis_tac[frame_alloca_path_fresh_phi_exclusion]
QED
