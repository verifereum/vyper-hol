(*
 * DFT's stage simulation at run 7 in the gas form, from the
 * context-level simulation over its function relation (dft_ctx_sim_gas)
 * and the labels code_layout_valid binds (dft_ctx_labels_bound).
 *)
Theory o1DftStageSim
Ancestors
  o1DftStageSsa dftContractGas o1PassContract venomPassSchedule venomWf
  gasEvents gasCount

Theorem dft_stage_sim_gas:
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' /\ o1_pre 7 C C' /\
  dead_wf D /\ o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim_fuel I D C C' vs vs' /\
       (o1_lowered_inv C vs ==> o1_lowered_inv C' vs')
Proof
  strip_tac >> drule_all dft_stage_fn_rel >> strip_tac >>
  drule ctx_pass_stage_dft >> strip_tac >>
  irule dft_ctx_sim_gas >> simp[] >>
  irule dft_ctx_labels_bound >> gvs[o1_run_state_ok_def]
QED

Theorem dft_stage_gas_mask:
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' /\ o1_pre 7 C C' /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\ EVERY wf_ssa C.ctx_functions /\
  o1_run_state_ok vs' /\
  C'.ctx_entry = SOME nm /\ lookup_function nm C'.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  terminates (run_context fuel C' vs') /\
  gas_count_blocks fuel C' fn'
    (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) <=
    LENGTH vs'.vs_gas_readings ==>
  ?fn raw_slots sites unused.
    C.ctx_entry = SOME nm /\
    lookup_function nm C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl /\
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) vs'.vs_gas_readings /\
    !gobs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
      (?extra. sites =
         gas_events_blocks fuel C fn
           (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                        vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra) /\
      ((?fr. terminates
               (run_context fr C (vs' with vs_gas_readings := gobs ++ tail))) ==>
       terminates (run_context fuel C (vs' with vs_gas_readings := gobs ++ tail)) /\
       !D. ctx_sim D C C' (vs' with vs_gas_readings := gobs ++ tail) vs')
Proof
  strip_tac >> drule_all dft_stage_fn_rel >> strip_tac >>
  drule ctx_pass_stage_dft >> strip_tac >>
  `ctx_labels_bound C vs'.vs_labels` by
    (irule dft_ctx_labels_bound >> gvs[o1_run_state_ok_def]) >>
  drule_all dft_ctx_gas_mask >> strip_tac >>
  qexistsl [`fn`, `raw_slots`, `sites`, `unused`] >> gvs[]
QED

(* dft_stage_gas_mask under the DFT prefix property (dft_blocks_gas_prefix):
 * the same mask's sites cover the source events at every fuel. *)
Theorem dft_stage_gas_mask_prefix:
  dft_blocks_gas_prefix /\
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' /\ o1_pre 7 C C' /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\ EVERY wf_ssa C.ctx_functions /\
  o1_run_state_ok vs' /\
  C'.ctx_entry = SOME nm /\ lookup_function nm C'.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  terminates (run_context fuel C' vs') /\
  gas_count_blocks fuel C' fn'
    (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) <=
    LENGTH vs'.vs_gas_readings ==>
  ?fn raw_slots sites unused.
    C.ctx_entry = SOME nm /\
    lookup_function nm C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl /\
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) vs'.vs_gas_readings /\
    !gobs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
      (?extra. sites =
         gas_events_blocks fuel C fn
           (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                        vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra) /\
      ((?fr. terminates
               (run_context fr C (vs' with vs_gas_readings := gobs ++ tail))) ==>
       terminates (run_context fuel C (vs' with vs_gas_readings := gobs ++ tail)) /\
       !D. ctx_sim D C C' (vs' with vs_gas_readings := gobs ++ tail) vs') /\
      !f_src. ?extra. sites =
         gas_events_blocks f_src C fn
           (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                        vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra
Proof
  strip_tac >> drule_all dft_stage_fn_rel >> strip_tac >>
  drule ctx_pass_stage_dft >> strip_tac >>
  `ctx_labels_bound C vs'.vs_labels` by
    (irule dft_ctx_labels_bound >> gvs[o1_run_state_ok_def]) >>
  drule_all dft_ctx_gas_mask_prefix >> strip_tac >>
  qexistsl [`fn`, `raw_slots`, `sites`, `unused`] >> gvs[]
QED

