Theory lowerDloadPtrSourceInv
Ancestors
  lowerDloadPtrRawReachable unitMemInv o1PassContract lowerDloadDefs unitTransformDefs
  memSafeRun contextRawReachable codegenRel contextCodegenRel o1PassLift

Theorem mem_inv_frame_reachable:
  o1_ctx_shape ctx /\ mem_inv M ctx vs /\
  frame_reachable vs ctx stk PG G tn fn inst s ==> M ctx fn inst s
Proof
  strip_tac >> drule_all frame_reachable_raw >>
  fs[mem_inv_raw_reachable]
QED

Theorem o1_src_frame_raw_mem_ok:
  o1_ctx_shape C /\ o1_src_inv D C vs /\
  frame_reachable vs C stk PG G tn fn inst s ==> raw_mem_ok C fn inst s
Proof
  strip_tac >> irule mem_inv_frame_reachable >>
  fs[o1_src_inv_def] >> metis_tac[]
QED

Theorem o1_src_frame_dload_offset_ok:
  o1_ctx_shape C /\ o1_src_inv D C vs /\
  frame_reachable vs C stk PG G tn fn inst s ==> dload_offset_ok C fn inst s
Proof
  strip_tac >> irule mem_inv_frame_reachable >>
  fs[o1_src_inv_def] >> metis_tac[]
QED

Theorem o1_src_frame_dload_headroom_ok:
  o1_ctx_shape C /\ o1_src_inv D C vs /\
  frame_reachable vs C stk PG G tn fn inst s ==> dload_headroom_ok C fn inst s
Proof
  strip_tac >> irule mem_inv_frame_reachable >>
  fs[o1_src_inv_def] >> metis_tac[]
QED

Theorem o1_src_frame_code_layout_valid:
  o1_ctx_shape C /\ o1_src_inv D C vs /\ o1_run_state_ok vs /\
  frame_reachable vs C cs PG G tn f i s ==> code_layout_valid s
Proof
  strip_tac >>
  `raw_reachable vs C f i s` by metis_tac[frame_reachable_raw] >>
  `s.vs_labels = vs.vs_labels` by metis_tac[raw_reachable_labels] >>
  `codegen_reachability_package
    (\c f i t. t.vs_code = vs.vs_code /\ t.vs_data_section = vs.vs_data_section) C vs` by
    (fs[o1_src_inv_def, mem_inv_def, codegen_reachability_package_def] >>
     conj_tac >- simp[code_data_closed] >>
     qspecl_then [`C`,`fn''`,`vs with <|vs_prev_bb := NONE; vs_current_bb := lbl''; vs_inst_idx := 0|>`]
       mp_tac code_data_entry >> simp[]) >>
  drule_all raw_reachable_least >> simp[] >> strip_tac >>
  gvs[o1_run_state_ok_def, o1_initial_state_ok_def, code_layout_valid_def]
QED
