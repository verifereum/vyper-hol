Theory dftGasFromListTracePrefix
Ancestors
  dftGasFromListTraceDefs venomExecProofs venomExecSemantics list rich_list
  arithmetic

Theorem trace_stable:
  (!p d n ctx fn inst s. !m.
    n <= m /\ (!e. step_inst n ctx inst s <> Error e) ==>
    trace_step p d m ctx fn inst s = trace_step p d n ctx fn inst s) /\
  (!p d n ctx fn bb s. !m.
    n <= m /\ (!e. exec_block n ctx bb s <> Error e) ==>
    trace_block p d m ctx fn bb s = trace_block p d n ctx fn bb s) /\
  (!p d n ctx fn s. !m.
    n <= m /\ (!e. run_blocks n ctx fn s <> Error e) ==>
    trace_blocks p d m ctx fn s = trace_blocks p d n ctx fn s)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_stable[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke inst`
      >- simp[cj 1 trace_defs] >>
      rename1 `decode_invoke inst = SOME pair` >>
      PairCases_on `pair` >>
      Cases_on `lookup_function pair0 ctx.ctx_functions`
      >- simp[cj 1 trace_defs] >>
      rename1 `lookup_function _ _ = SOME callee` >>
      Cases_on `eval_operands pair1 s`
      >- simp[cj 1 trace_defs] >>
      rename1 `eval_operands _ _ = SOME args` >>
      Cases_on `setup_callee callee args s`
      >- simp[cj 1 trace_defs] >>
      rename1 `setup_callee _ _ _ = SOME cs` >>
      simp[cj 1 trace_defs] >>
      `!e. run_blocks n ctx callee cs <> Error e` by
        (gen_tac >> strip_tac >>
         qpat_x_assum `!e. step_inst _ _ _ _ <> Error e`
           (qspec_then `e` mp_tac) >> simp[Once step_inst_def]) >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[cj 1 trace_defs]
QED

Resume trace_stable[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (simp[Once trace_defs] >> simp[Once trace_defs]) >>
  rename1 `get_instruction _ _ = SOME inst` >>
  `!e. step_inst n ctx inst s <> Error e` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!e. exec_block _ _ _ _ <> Error e`
       (qspec_then `e` mp_tac) >> simp[Once exec_block_def]) >>
  `step_inst m ctx inst s = step_inst n ctx inst s` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  `trace_step p d m ctx fn inst s = trace_step p d n ctx fn inst s` by
    (first_x_assum irule >> simp[]) >>
  simp[Once trace_defs] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [cj 2 trace_defs])) >> simp[] >>
  Cases_on `step_inst n ctx inst s` >> gvs[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  first_x_assum irule >> simp[] >>
  qpat_x_assum `!e. exec_block n ctx bb s <> Error e` mp_tac >>
  simp[Once exec_block_def]
QED

Resume trace_stable[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `n`
  >- (qpat_x_assum `!e. run_blocks _ _ _ _ <> Error e` mp_tac >>
      simp[Once run_blocks_def]) >>
  rename1 `SUC k <= m` >>
  Cases_on `m` >- gvs[] >> rename1 `SUC k <= SUC j` >>
  gvs[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (simp[Once trace_defs] >> simp[Once trace_defs]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  gvs[]
  >- (rename1 `eval_phis _ _ = OK sp` >>
      qmatch_asmsub_abbrev_tac `exec_block k ctx bb start` >>
      `!e. exec_block k ctx bb start <> Error e` by
        (gen_tac >> strip_tac >>
         qpat_x_assum `!e. run_blocks _ _ _ _ <> Error e`
           (qspec_then `e` mp_tac) >>
         simp[Once run_blocks_def, Abbr `start`]) >>
      `exec_block j ctx bb start = exec_block k ctx bb start` by
        (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
      `trace_block p (SUC d) j ctx fn bb start =
       trace_block p (SUC d) k ctx fn bb start` by
        (first_x_assum irule >> simp[]) >>
      simp[Once trace_defs] >>
      CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [cj 3 trace_defs])) >>
      unabbrev_all_tac >> simp[] >>
      Cases_on `exec_block k ctx bb
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
      gvs[] >> rename1 `exec_block _ _ _ _ = OK t` >>
      Cases_on `t.vs_halted` >> simp[] >>
      first_x_assum irule >> simp[] >>
      qpat_x_assum `!e. run_blocks (SUC k) ctx fn s <> Error e` mp_tac >>
      simp[Once run_blocks_def]) >>
  (simp[Once trace_defs] >> simp[Once trace_defs])
QED

Finalise trace_stable

Theorem trace_prefix:
  (!p d n ctx fn inst s. !m. n <= m ==>
    ?suffix. trace_step p d m ctx fn inst s =
             trace_step p d n ctx fn inst s ++ suffix) /\
  (!p d n ctx fn bb s. !m. n <= m ==>
    ?suffix. trace_block p d m ctx fn bb s =
             trace_block p d n ctx fn bb s ++ suffix) /\
  (!p d n ctx fn s. !m. n <= m ==>
    ?suffix. trace_blocks p d m ctx fn s =
             trace_blocks p d n ctx fn s ++ suffix)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_prefix[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke inst`
      >- simp[cj 1 trace_defs] >>
      rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
      Cases_on `lookup_function pair0 ctx.ctx_functions`
      >- simp[cj 1 trace_defs] >>
      rename1 `lookup_function _ _ = SOME callee` >>
      Cases_on `eval_operands pair1 s`
      >- simp[cj 1 trace_defs] >>
      rename1 `eval_operands _ _ = SOME args` >>
      Cases_on `setup_callee callee args s`
      >- simp[cj 1 trace_defs] >>
      simp[cj 1 trace_defs] >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[cj 1 trace_defs]
QED

Resume trace_prefix[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (simp[Once trace_defs] >> simp[Once trace_defs]) >>
  rename1 `get_instruction _ _ = SOME inst` >>
  Cases_on `?msg. step_inst n ctx inst s = Error msg`
  >- (pop_assum strip_assume_tac >>
      `?suffix. trace_step p d m ctx fn inst s =
                trace_step p d n ctx fn inst s ++ suffix` by
        (first_x_assum irule >> simp[]) >>
      once_rewrite_tac[cj 2 trace_defs] >> simp[] >>
      qmatch_goalsub_abbrev_tac `suffix ++ rest` >>
      qexists_tac `suffix ++ rest` >> simp[APPEND_ASSOC]) >>
  `!e. step_inst n ctx inst s <> Error e` by
    (Cases_on `step_inst n ctx inst s` >> gvs[]) >>
  `step_inst m ctx inst s = step_inst n ctx inst s` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  `trace_step p d m ctx fn inst s = trace_step p d n ctx fn inst s` by
    (irule (cj 1 trace_stable) >> simp[]) >>
  once_rewrite_tac[cj 2 trace_defs] >> simp[] >>
  Cases_on `step_inst n ctx inst s` >> gvs[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  `?suffix. trace_block p d m ctx fn bb
      (v with vs_inst_idx := SUC s.vs_inst_idx) =
    trace_block p d n ctx fn bb
      (v with vs_inst_idx := SUC s.vs_inst_idx) ++ suffix` by
    (first_x_assum irule >> simp[]) >>
  qexists_tac `suffix` >> simp[APPEND_ASSOC]
QED

Resume trace_prefix[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `n` >- simp[] >> rename1 `SUC k <= m` >>
  Cases_on `m` >- gvs[] >> rename1 `SUC k <= SUC j` >> gvs[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (once_rewrite_tac[cj 3 trace_defs] >> simp[]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[]
  >- (rename1 `eval_phis _ _ = OK sp` >>
      qmatch_asmsub_abbrev_tac `exec_block k ctx bb start` >>
      Cases_on `?msg. exec_block k ctx bb start = Error msg`
      >- (pop_assum strip_assume_tac >>
          `?suffix. trace_block p (SUC d) j ctx fn bb start =
             trace_block p (SUC d) k ctx fn bb start ++ suffix` by
            (first_x_assum irule >> simp[]) >>
          once_rewrite_tac[cj 3 trace_defs] >>
          unabbrev_all_tac >> simp[] >>
          qmatch_goalsub_abbrev_tac `suffix ++ rest` >>
          qexists_tac `suffix ++ rest` >> simp[APPEND_ASSOC]) >>
      `!e. exec_block k ctx bb start <> Error e` by metis_tac[] >>
      `exec_block j ctx bb start = exec_block k ctx bb start` by
        (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
      `trace_block p (SUC d) j ctx fn bb start =
       trace_block p (SUC d) k ctx fn bb start` by
        (irule (cj 2 trace_stable) >> simp[]) >>
      once_rewrite_tac[cj 3 trace_defs] >>
      unabbrev_all_tac >> simp[] >>
      Cases_on `exec_block k ctx bb
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
      gvs[] >> rename1 `exec_block _ _ _ _ = OK t` >>
      Cases_on `t.vs_halted` >> simp[] >>
      `?suffix. trace_blocks p (SUC d) j ctx fn t =
                trace_blocks p (SUC d) k ctx fn t ++ suffix` by
        (first_x_assum irule >> simp[]) >>
      qexists_tac `suffix` >> simp[APPEND_ASSOC]) >>
  (once_rewrite_tac[cj 3 trace_defs] >> simp[])
QED

Finalise trace_prefix

Theorem trace_context_prefix:
  n <= m ==>
  ?suffix. trace_context m ctx s = trace_context n ctx s ++ suffix
Proof
  strip_tac >>
  simp[trace_context_def, trace_function_def] >>
  Cases_on `ctx.ctx_entry` >> simp[] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions` >> simp[] >>
  rename1 `lookup_function _ _ = SOME fn` >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  irule (cj 3 trace_prefix) >> simp[]
QED

Theorem trace_context_visit_preserved:
  n <= m /\ idx < LENGTH (trace_context n ctx s) ==>
  EL idx (trace_context m ctx s) = EL idx (trace_context n ctx s)
Proof
  strip_tac >> drule trace_context_prefix >>
  disch_then (qspecl_then [`s`, `ctx`] strip_assume_tac) >> simp[EL_APPEND1]
QED
