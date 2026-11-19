(* Compatibility interface for callers with bounded pointer discipline. *)
Theory gasFocusFmpCutEvents
Ancestors gasFocusFmpCutFieldEvents concretizeLayoutCutSafe o1SafeUpto
  ptrStaticDiscipline lowerDloadPtrRawReachable o1LowerDloadGhost
  stepWriteFootprintBase allocaFrontierBound list

Theorem focus_fmp_cut_prefix_events:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  o1_ctx_shape C3 /\ o1_ctx_shape C4 /\ o1_pre 3 C3 C4 /\
  EVERY ssa_form C3.ctx_functions /\ fmp_free_ctx C3 /\
  callee_first names C3.ctx_functions /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  o1_initial_state_ok v /\ v.vs_fmp = v.vs_initial_fmp /\ code_layout_valid v /\
  eom <= w2n v.vs_initial_fmp /\ w2n v.vs_initial_fmp <= w2n fmp /\
  vs = v with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  ptr_discipline_upto eom n C3 vs /\ taint_within_upto D n C3 vs /\
  (!f i s. raw_reachable vs C3 f i s /\ gas_cut n vs s ==> dalloca_no_wrap i s) /\
  s3 = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  s4 = v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  n <= LENGTH (gas_events_blocks fuel C3 fn s3) ==>
  ?fn4. lookup_function name C4.ctx_functions = SOME fn4 /\
    fn_entry_label fn4 = SOME lbl /\
    ?fuel4. n <= LENGTH (gas_events_blocks fuel4 C4 fn4 s4) /\
      TAKE n (gas_events_blocks fuel4 C4 fn4 s4) =
      TAKE n (gas_events_blocks fuel C3 fn s3)
Proof
  strip_tac >>
  `!stk PG G tn f i s.
    frame_reachable vs C3 stk PG G tn f i s /\ gas_cut n vs s ==>
    access_ok eom G f i s /\ taint_ok f tn i s /\
    (?P. fn_static_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
         ptr_use_static_ok P (fn_pv P f) i)` by
    (rpt gen_tac >> strip_tac >>
     drule_all ptr_discipline_upto_at >> strip_tac >> simp[] >>
     `?P. EVERY (fn_ptr_ok P) C3.ctx_functions` by
       (fs[ptr_discipline_upto_def, EVERY_MEM] >> metis_tac[]) >>
     drule frame_reachable_prov_support >>
     disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
     `fn_static_ptr_ok P f` by metis_tac[EVERY_MEM, fn_ptr_ok_static] >>
     drule_all frame_reachable_raw_certificate >> strip_tac >>
     `MEM i (fn_insts f)` by
       metis_tac[stepWriteFootprintBaseTheory.raw_reachable_active,
                 allocaFrontierBoundTheory.active_inst_mem_fn_insts] >>
     qexists `P` >> fs[fn_static_ptr_ok_def] >> metis_tac[]) >>
  drule_all focus_fmp_cut_prefix_events_fields >> simp[]
QED
