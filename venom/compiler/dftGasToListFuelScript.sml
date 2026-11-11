Theory dftGasToListFuel
Ancestors
  dftGasToListTrace dftGasOracleDefs venomExecSemantics venomInst venomState
  list rich_list arithmetic

(* Mixed-log prefix preserves both event order and visit offsets. *)
Definition trace_extension_def:
  trace_extension r ts r' ts' <=>
    (?tail. ts' = ts ++ tail) /\
    ((!err. r <> Error err) ==> r' = r /\ ts' = ts)
End

Theorem trace_fuel_extension:
  (!orc p d fuel ctx inst s.
     !larger. fuel <= larger ==>
       trace_extension (ev_step orc p d fuel ctx inst s)
         (trace_step orc p d fuel ctx inst s)
         (ev_step orc p d larger ctx inst s)
         (trace_step orc p d larger ctx inst s)) /\
  (!orc p d fuel ctx fn bb s.
     !larger. fuel <= larger ==>
       trace_extension (ev_block orc p d fuel ctx bb s)
         (trace_block orc p d fuel ctx fn bb s)
         (ev_block orc p d larger ctx bb s)
         (trace_block orc p d larger ctx fn bb s)) /\
  (!orc p d fuel ctx fn s.
     !larger. fuel <= larger ==>
       trace_extension (ev_blocks orc p d fuel ctx fn s)
         (trace_blocks orc p d fuel ctx fn s)
         (ev_blocks orc p d larger ctx fn s)
         (trace_blocks orc p d larger ctx fn s))
Proof
  ho_match_mp_tac oracle_trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_fuel_extension[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = GAS`
  >- simp[ev_step_def, trace_step_eq, trace_extension_def] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke inst`
      >- simp[ev_step_def, trace_step_eq, trace_extension_def] >>
      rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
      Cases_on `lookup_function pair0 ctx.ctx_functions`
      >- simp[ev_step_def, trace_step_eq, trace_extension_def] >>
      Cases_on `eval_operands pair1 s`
      >- simp[ev_step_def, trace_step_eq, trace_extension_def] >>
      rename1 `lookup_function pair0 ctx.ctx_functions = SOME callee` >>
      rename1 `eval_operands pair1 s = SOME args` >>
      Cases_on `setup_callee callee args s`
      >- simp[ev_step_def, trace_step_eq, trace_extension_def] >>
      gvs[] >> first_x_assum drule_all >> strip_tac >>
      simp[ev_step_def, trace_step_eq] >>
      Cases_on `ev_blocks orc ((d,inst.inst_id)::p) d fuel ctx callee x` >>
      gvs[trace_extension_def]) >>
  simp[ev_step_def, trace_step_eq, trace_extension_def]
QED

Resume trace_fuel_extension[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (simp[Once ev_block_def] >> simp[Once ev_block_def] >>
      simp[Once trace_block_eq] >> simp[Once trace_block_eq] >>
      simp[trace_extension_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  gvs[] >>
  qpat_x_assum `!larger. _` (qspec_then `larger` mp_tac) >>
  simp[] >> strip_tac >>
  once_rewrite_tac[ev_block_def, trace_block_eq] >> simp[] >>
  Cases_on `ev_step orc p d fuel ctx inst s` >>
  gvs[trace_extension_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  first_x_assum (qspec_then `larger` mp_tac) >> simp[]
QED

Resume trace_fuel_extension[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  namedCases_on `fuel` ["", "small"]
  >- simp[Once ev_blocks_def, trace_blocks_zero, trace_extension_def] >>
  namedCases_on `larger` ["", "big"] >> gvs[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (once_rewrite_tac[ev_blocks_def, trace_blocks_eq] >>
      simp[trace_extension_def]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- (gvs[] >>
      qpat_x_assum `!larger. _` (qspec_then `big` mp_tac) >>
      simp[] >> strip_tac >>
      once_rewrite_tac[ev_blocks_def, trace_blocks_eq] >> simp[] >>
      rename1 `eval_phis s bb.bb_instructions = OK s_phi` >>
      qmatch_goalsub_abbrev_tac `ev_block orc p (SUC d) small ctx bb entry` >>
      Cases_on `ev_block orc p (SUC d) small ctx bb entry` >>
      gvs[trace_extension_def] >>
      rename1 `ev_block orc p (SUC d) small ctx bb entry = OK result` >>
      Cases_on `result.vs_halted` >> gvs[] >>
      first_x_assum (qspec_then `big` mp_tac) >> simp[]) >>
  once_rewrite_tac[ev_blocks_def, trace_blocks_eq] >>
  simp[trace_extension_def]
QED

Finalise trace_fuel_extension

Theorem trace_function_fuel_extension:
  fuel <= larger ==>
  trace_extension (ev_function orc fuel ctx fn s)
    (trace_function orc fuel ctx fn s)
    (ev_function orc larger ctx fn s)
    (trace_function orc larger ctx fn s)
Proof
  strip_tac >> Cases_on `fn_entry_label fn` >>
  simp[ev_function_def, trace_function_def, trace_extension_def] >>
  irule (SRULE [trace_extension_def] (cj 3 trace_fuel_extension)) >> simp[]
QED

Theorem trace_context_fuel_extension:
  fuel <= larger ==>
  trace_extension (ev_context orc fuel ctx s)
    (trace_context orc fuel ctx s)
    (ev_context orc larger ctx s)
    (trace_context orc larger ctx s)
Proof
  strip_tac >> Cases_on `ctx.ctx_entry`
  >- simp[ev_context_def, trace_context_def, trace_extension_def] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions` >>
  simp[ev_context_def, trace_context_def, trace_extension_def] >>
  irule (SRULE [trace_extension_def] trace_function_fuel_extension) >> simp[]
QED

Theorem trace_extension_events:
  trace_extension r ts r' ts' ==>
  ?tail. trace_events ts' = trace_events ts ++ tail
Proof
  simp[trace_extension_def] >> rpt strip_tac >>
  simp[trace_events_append]
QED

Theorem trace_extension_visits:
  trace_extension r ts r' ts' ==>
  !n. ?tail. trace_visits n ts' = trace_visits n ts ++ tail
Proof
  simp[trace_extension_def] >> rpt strip_tac >>
  simp[trace_visits_append]
QED

Theorem trace_extension_complete:
  trace_extension r ts r' ts' /\ (!err. r <> Error err) ==>
  r' = r /\ trace_events ts' = trace_events ts /\
  (!n. trace_visits n ts' = trace_visits n ts)
Proof
  simp[trace_extension_def] >> metis_tac[]
QED

Theorem trace_extension_visit_mem:
  trace_extension r ts r' ts' /\ MEM visit (trace_visits n ts) ==>
  MEM visit (trace_visits n ts')
Proof
  rpt strip_tac >> drule trace_extension_visits >>
  disch_then (qspec_then `n` strip_assume_tac) >> simp[MEM_APPEND]
QED

Theorem context_events_fuel_prefix:
  fuel <= larger ==>
  ?tail. trace_events (trace_context orc larger ctx s) =
    trace_events (trace_context orc fuel ctx s) ++ tail
Proof
  strip_tac >> drule trace_context_fuel_extension >>
  metis_tac[trace_extension_events]
QED

Theorem context_visits_fuel_preserved:
  fuel <= larger /\ MEM visit (trace_visits n (trace_context orc fuel ctx s)) ==>
  MEM visit (trace_visits n (trace_context orc larger ctx s))
Proof
  rpt strip_tac >> drule trace_context_fuel_extension >>
  metis_tac[trace_extension_visit_mem]
QED
