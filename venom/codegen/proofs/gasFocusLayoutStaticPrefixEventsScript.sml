Theory gasFocusLayoutStaticPrefixEvents
Ancestors concretizeLayoutStageSimulation

(* The bounded C2-to-C3 GAS prefix is available for static as well as
   nonstatic roots, with no assumption that either run terminates. *)
Theorem focus_layout_stage_prefix_events_static:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\ dead_wf D /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  s = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  (ctx_has_dalloca C ==>
     ?eom. max_live_eom C' = SOME eom /\ eom <= w2n vs.vs_initial_fmp) /\
  o1_ptr_safe_upto D lo n C vs /\ alloca_frontier_upto n C vs /\
  n <= LENGTH (gas_events_blocks fuel C fn s) ==>
  ?fuel' fn'. C'.ctx_entry = SOME name /\ lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\
    n <= LENGTH (gas_events_blocks fuel' C' fn' s) /\
    TAKE n (gas_events_blocks fuel' C' fn' s) = TAKE n (gas_events_blocks fuel C fn s)
Proof
  strip_tac >> drule_all layout_stage_prefix_events_eventually >>
  disch_then (qx_choosel_then [`k`, `out`] strip_assume_tac) >>
  qexistsl [`k`, `out`] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED
