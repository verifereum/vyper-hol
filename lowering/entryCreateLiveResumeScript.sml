(* Retain the terminal visit of the same native run when moving to a
   live cursor. The suffix cannot be empty, even if its first step aborts. *)
Theory entryCreateLiveResume
Ancestors
  entryCreateTraceSplit entryCreateNativeResume fragExec venomExecProofs
  venomState dftGasFromListTraceDefs list

Theorem create_trace_from_live[local]:
  lookup_block t.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME i ==>
  create_trace_from p d k C f t <> []
Proof
  strip_tac >> simp[create_trace_from_def] >> drule trace_block_visit >> simp[]
QED

(* Preserve the full visit, including its invocation key, and rebase only
   the chronological list prefix. *)
Theorem create_terminal_hit_after_live_cursor:
  !m. gas_origin_path mem E C f s marks (OK t) /\
  (!b. MEM b f.fn_blocks ==> phi_prefix_length b.bb_instructions = 0) /\
  lookup_block t.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME i ==>
  ?bound. !k p d before hit. bound <= k /\
    create_trace_from p d k C f s = before ++ [hit] ==>
    ?left dd kk before'. m <= kk /\ kk <= k /\
      before = left ++ before' /\
      create_trace_from p dd kk C f t = before' ++ [hit]
Proof
  rpt strip_tac >>
  drule_all create_trace_from_completed_min >>
  disch_then (qspec_then `m` (qx_choose_then `bound` (mk_asm "split"))) >>
  qexists_tac `bound` >> rpt strip_tac >>
  asm "split" (qspecl_then [`k`, `p`, `d`] mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`left`, `dd`, `kk`] strip_assume_tac) >>
  `create_trace_from p dd kk C f t <> []` by metis_tac[create_trace_from_live] >>
  qspec_then `create_trace_from p dd kk C f t` mp_tac SNOC_CASES >>
  simp[SNOC_APPEND] >> disch_then (qx_choosel_then [`last`, `before'`] assume_tac) >>
  qexistsl_tac [`left`, `dd`, `kk`, `before'`] >>
  qpat_x_assum `before ++ [hit] = _` mp_tac >>
  simp[APPEND_ASSOC, GSYM SNOC_APPEND]
QED

Theorem create_terminal_hit_after_live_prefix:
  !m. C.ctx_entry = SOME nm /\
  lookup_function nm C.ctx_functions = SOME f /\
  fn_entry_label f = SOME "__entry" /\
  lookup_block "__entry" f.fn_blocks = SOME entry /\
  (!b. MEM b f.fn_blocks ==> phi_prefix_length b.bb_instructions = 0) /\
  gas_origin_path mem E C f
    (vi with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)
    marks (OK t) /\
  lookup_block t.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME i ==>
  ?bound. !k before hit. bound <= k /\
    trace_context (SUC k) C vi = before ++ [hit] ==>
    ?left dd kk before'. m <= kk /\ kk <= k /\
      before = left ++ before' /\
      create_trace_from [] dd kk C f t = before' ++ [hit]
Proof
  rpt strip_tac >>
  qabbrev_tac `s = vi with
    <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `phi_prefix_length entry.bb_instructions = 0` by metis_tac[lookup_block_MEM] >>
  `s with vs_inst_idx := 0 = s` by simp[Abbr `s`] >>
  `!k. trace_context (SUC k) C vi = create_trace_from [] 1 k C f s` by
    (gen_tac >>
     `trace_context (SUC k) C vi = trace_blocks [] 0 (SUC k) C f s` by
       simp[trace_context_def, trace_function_def, venom_state_fupdcanon, Abbr `s`] >>
     pop_assum SUBST1_TAC >>
     `lookup_block s.vs_current_bb f.fn_blocks = SOME entry /\
      eval_phis s entry.bb_instructions = OK s` by simp[Abbr `s`, eval_phis_no_phi] >>
     drule create_trace_from_enter >> disch_then drule >> simp[]) >>
  drule_all create_terminal_hit_after_live_cursor >>
  disch_then (qspec_then `m` (qx_choose_then `bound` (mk_asm "resume"))) >>
  qexists_tac `bound` >> rpt strip_tac >>
  asm "resume" (qspecl_then [`k`, `[]`, `1`, `before`, `hit`] mp_tac) >> gvs[]
QED
