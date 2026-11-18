(* The post-FMP passes preserve a finite GAS prefix from the selected C4 entry. *)
Theory gasFocusPostFmpEntryEvents
Ancestors
  gasFocusMakeSsaStageEvents o1SimplifyCfgGasEventsStatic gasFocusSueContextEvents
  o1ContractSimplifyCfg o1ContractSue singleUseExpansionSupplySim
  o1PassContract o1PassLift venomPassSchedule unitTransformDefs gasEvents
  finite_map list option

Theorem focus_post_fmp_entry_events:
  ctx_pass_stage rpolicy (EL 4 o1_fn_passes) (o1_walk_view rpolicy 4)
    (stage 4) (stage 5) /\
  ctx_pass_stage rpolicy (EL 5 o1_fn_passes) (o1_walk_view rpolicy 5)
    (stage 5) (stage 6) /\
  ctx_pass_stage rpolicy (EL 6 o1_fn_passes) (o1_walk_view rpolicy 6)
    (stage 6) (stage 7) /\
  o1_ctx_shape (stage 4) /\ EVERY (o1_fn_row 4) (stage 4).ctx_functions /\
  o1_ctx_shape (stage 5) /\ EVERY (o1_fn_row 5) (stage 5).ctx_functions /\
  o1_ctx_shape (stage 6) /\ EVERY (o1_fn_row 6) (stage 6).ctx_functions /\
  o1_initial_state_ok V4 /\ V4.vs_fmp = V4.vs_initial_fmp /\ code_layout_valid V4 /\
  (stage 4).ctx_entry = SOME nm /\
  lookup_function nm (stage 4).ctx_functions = SOME fn4 /\
  fn_entry_label fn4 = SOME lbl /\
  n <= LENGTH (gas_events_blocks f4 (stage 4) fn4
    (V4 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) ==>
  ?f7 fn7.
    (stage 7).ctx_entry = SOME nm /\
    lookup_function nm (stage 7).ctx_functions = SOME fn7 /\
    fn_entry_label fn7 = SOME lbl /\
    n <= LENGTH (gas_events_blocks f7 (stage 7) fn7
      (V4 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) /\
    TAKE n (gas_events_blocks f7 (stage 7) fn7
      (V4 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) =
    TAKE n (gas_events_blocks f4 (stage 4) fn4
      (V4 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))
Proof
  simp[o1_fn_passes_def] >> strip_tac >>
  `EVERY make_ssa_input_ok (stage 4).ctx_functions` by
    fs[EVERY_MEM, o1_fn_row_def] >>
  `V4.vs_vars = FEMPTY /\ ~V4.vs_halted` by fs[o1_initial_state_ok_def] >>
  drule_all make_ssa_stage_gas_events_upto >> strip_tac >>
  rename1 `TAKE n (gas_events_blocks f5 (stage 5) fn5 _) = _` >>
  `EVERY simplify_cfg_fn_ok (stage 5).ctx_functions` by
    (fs[EVERY_MEM, o1_ctx_shape_def, o1_fn_shape_def, o1_fn_row_def] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_ssa >> metis_tac[]) >>
  drule_all simplify_cfg_stage_gas_prefix_static >>
  disch_then (qspec_then `f5` strip_assume_tac) >>
  rename1 `gas_events_blocks f6 (stage 6) fn6 _ = _ ++ _` >>
  `(stage 6).ctx_entry = SOME nm` by fs[ctx_pass_stage_def] >>
  drule sue_stage_functions >> strip_tac >>
  `?fn7. lookup_function nm (stage 7).ctx_functions = SOME fn7 /\
         fn_entry_label fn7 = SOME lbl` by
    (drule list_rel_lookup_function >>
     (impl_tac >-
       (simp[] >> rpt strip_tac >> drule sue_expand_function_supply_identity >> simp[])) >>
     disch_then (qspec_then `nm` mp_tac) >>
     simp[OPTREL_SOME] >> metis_tac[sue_expand_function_supply_identity]) >>
  `EVERY wf_ssa (stage 6).ctx_functions` by fs[EVERY_MEM, o1_fn_row_def] >>
  `fn_entry_state fn6
    (V4 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)` by
    simp[fn_entry_state_def] >>
  drule_all sue_stage_finite_gas_events >>
  disch_then (qspec_then `f6` strip_assume_tac) >>
  rename1 `gas_events_blocks f7 (stage 7) fn7 _ = _ ++ _` >>
  qexistsl [`f7`, `fn7`] >> asm_rewrite_tac[] >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >> simp[TAKE_APPEND1] >> decide_tac
QED
