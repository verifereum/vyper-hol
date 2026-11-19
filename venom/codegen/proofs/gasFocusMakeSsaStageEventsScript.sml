(* Fixed-filling finite GAS-event transport through either MakeSSA stage. *)
Theory gasFocusMakeSsaStageEvents
Ancestors
  gasFocusMakeSsaSuccessor gasFocusMakeSsaFinite gasFocusMakeSsaContext
  o1ContractMakeSsaSrc o1PassLift o1PassContract list

Theorem make_ssa_stage_gas_events_upto:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  n <= LENGTH (gas_events_blocks fuel C fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) ==>
  ?fuel' fn'.
    C'.ctx_entry = SOME name /\
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\
    n <= LENGTH (gas_events_blocks fuel' C' fn'
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) /\
    TAKE n (gas_events_blocks fuel' C' fn'
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) =
    TAKE n (gas_events_blocks fuel C fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))
Proof
  mp_tac make_ssa_context_events_from_same_context >>
  (impl_tac >-
    (mp_tac current_focus_same_context_events >>
     (impl_tac >-
       (rpt gen_tac >> MATCH_ACCEPT_TAC current_focus_prepared_successor)) >>
     simp[])) >>
  disch_then (mk_asm "context") >> strip_tac >>
  drule_all make_ssa_src_stage_lookup >> strip_tac >>
  `C'.ctx_entry = SOME name` by
    fs[ctx_pass_stage_def] >>
  `fn_entry_state fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)` by
    simp[fn_entry_state_def] >>
  asm "context" drule_all >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  qexistsl [`m`, `fn'`] >> simp[TAKE_APPEND1]
QED
