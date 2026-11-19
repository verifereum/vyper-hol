Theory gasFocusLoweringBridge
Ancestors
  o1PassContract o1PassLift o1SafeUpto unitTransformDefs
  venomPassSchedule ptrDiscipline venomWf lowerDloadDefs stackPlanGen
  venomState words list
  gasEvents unitMemInv venomInst

(* Scratch statement for elaboration and independent review.
   root3 is the shared pre-FMP root at C2 and C3, with the chosen FMP,
   and root4 restores the assembly entry FMP. The room premise is the
   existing fmp_variant_room contract plus the stage EOM bound. *)
Theorem focus_lowering_cut_bridge:
  let s2 = root3 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>;
      s4 = root4 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>
  in
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C2 C3 /\
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C3 C4 /\
  o1_ctx_shape C2 /\
  o1_initial_state_ok root4 /\ root4.vs_fmp = root4.vs_initial_fmp /\
  code_layout_valid root4 /\
  w2n root4.vs_initial_fmp <= w2n fmp /\
  root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  dead_wf D /\ o1_safe_upto D lo n C2 root3 /\ alloca_frontier_upto n C2 root3 /\
  EVERY ssa_form C2.ctx_functions /\ EVERY all_reachable C2.ctx_functions /\
  EVERY fn_defs_reach_uses C2.ctx_functions /\ ctx_inst_ids_distinct C2 /\
  callee_first names C2.ctx_functions /\
  max_live_eom C3 = SOME eom /\ eom <= w2n root4.vs_initial_fmp /\
  fmp_variant_room (SOME fmp) C4 root4 /\
  C2.ctx_entry = SOME nm /\ lookup_function nm C2.ctx_functions = SOME fn2 /\
  fn_entry_label fn2 = SOME lbl /\
  n <= LENGTH (gas_events_blocks fuel2 C2 fn2 s2) ==>
  mem_inv (\ctx fn inst u. gas_cut n root4 u ==> lowered_mem_fact eom ctx fn inst u)
    C4 root4 /\
  ?fn4 fuel4.
    C4.ctx_entry = SOME nm /\ lookup_function nm C4.ctx_functions = SOME fn4 /\
    fn_entry_label fn4 = SOME lbl /\
    n <= LENGTH (gas_events_blocks fuel4 C4 fn4 s4) /\
    TAKE n (gas_events_blocks fuel4 C4 fn4 s4) =
      TAKE n (gas_events_blocks fuel2 C2 fn2 s2)
Proof
  cheat
QED
