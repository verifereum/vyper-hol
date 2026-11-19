(* The bounded LowerDload fold starts with the actual entry ghosts. *)
Theory gasFocusLowerDloadActualEntry
Ancestors
  gasFocusLowerDloadRoot lowerDloadReachability lowerDloadPtrEntry
  lowerDloadPtrAggregate lowerDloadPtrPhase lowerDloadPtrRel
  lowerDloadSafetyEntry lowerDloadSafetyRelation lowerDloadSafetyLocations
  lowerDloadConfiguredOrigins fmpStageBlockSimCode venomInst
  o1SafeUpto unitTransformDefs lowerDloadDefs contextCodegenRel
  finite_map list words

Theorem ld_entry_control[local]:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  gn = FST (lower_dload_function_supply u fn) /\
  t.vs_inst_idx = 0 /\ ld_envelope u fn t 0 X 0 /\
  active_inst fn inst t /\ active_inst gn ti t ==>
  dload_control_match u fn gn t t inst X 0
Proof
  strip_tac >>
  `0 < LENGTH X /\ ti = EL 0 X` by
    (irule ld_envelope_active_head >> metis_tac[]) >>
  qpat_x_assum `ld_envelope _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ld_envelope_def] >> strip_tac >>
  rename1 `bi < LENGTH fn.fn_blocks` >>
  rename1 `EL bi fn.fn_blocks = bb` >>
  `active_inst fn (EL 0 bb.bb_instructions) t` by
    (simp[active_inst_def] >> qexists `bb` >> simp[] >> metis_tac[MEM_EL]) >>
  `inst = EL 0 bb.bb_instructions` by
    metis_tac[active_inst_unique, fn_labels_def] >>
  simp[dload_control_match_def] >>
  (conj_tac >- metis_tac[pairTheory.PAIR]) >>
  qexists `bi` >> fs[lower_dload_insts_supply_def] >>
  metis_tac[pairTheory.PAIR]
QED

Theorem ld_focus_actual_frame_entry:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  gn = FST (lower_dload_function_supply (Sigma fn.fn_name) fn) /\
  enters_block gn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  active_inst gn ti t /\ gas_cut n vs t ==>
  ?inst f X.
    f.lf_fn = fn /\ f.lf_supply = Sigma fn.fn_name /\ f.lf_Q = [] /\
    ld_sync lo P C vs [] [] FEMPTY entry_taint fn inst t t FEMPTY [f] 1 /\
    ld_global lo FEMPTY [f] /\
    ld_envelope (Sigma fn.fn_name) fn t t.vs_inst_idx X 0 /\
    ld_prefix C' gn X 0 0 t t /\ ti = EL 0 X /\
    t.vs_inst_idx = 0 /\ t.vs_gas_readings = vs.vs_gas_readings /\
    gn = ld_image f /\ 0 < LENGTH X /\
    dload_boundary_core (dyn_floor C vs) lo
      [<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|>]
      (set (fn_ir_vars fn) DIFF {v | retpc_var fn v}) [] [] []
      FEMPTY FEMPTY entry_taint entry_taint t t [] [] /\
    dload_control_match (Sigma fn.fn_name) fn gn t t inst X 0 /\
    dload_prefix_match 0 C' [] X 0 t FEMPTY entry_taint t FEMPTY entry_taint /\
    t.vs_allocas = FEMPTY /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH t.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) [f]
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (drule o1_ctx_shape_distinct_block_labels >> simp[EVERY_MEM] >>
     disch_then irule >> metis_tac[lookup_function_MEM]) >>
  drule_all_then (qspecl_then [`lo`, `C'`] strip_assume_tac)
    ld_focus_root_correlated >>
  drule_then strip_assume_tac ld_sync_source >>
  drule_then strip_assume_tac ld_sync_active >>
  `enters_block fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t` by
    (irule lower_dload_function_supply_enters_block_origin >>
     qexistsl [`gn`, `Sigma fn.fn_name`,
       `SND (lower_dload_function_supply (Sigma fn.fn_name) fn)`] >>
     simp[pairTheory.PAIR]) >>
  `t = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
    (irule ld_enters_entry >> simp[] >> metis_tac[]) >>
  `mem_inv dload_headroom_ok C vs /\ lo <= vs.vs_alloca_next` by
    fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >>
  drule_all_then assume_tac dload_active_entry_frontier_bound >>
  drule_all_then assume_tac dload_active_entry_dyn_floor >>
  `0 < LENGTH X` by metis_tac[ld_envelope_active_head] >>
  `dload_control_match (Sigma fn.fn_name) fn gn t t inst X 0` by
    (irule ld_entry_control >> simp[] >> metis_tac[]) >>
  qexistsl [`inst`, `f`, `X`] >>
  gvs[ld_image_def, dload_prefix_zero, o1_initial_state_ok_def] >>
  irule dload_boundary_initial_static >>
  fs[o1_initial_state_ok_def, code_layout_valid_def]
  >> (gvs[])
QED
