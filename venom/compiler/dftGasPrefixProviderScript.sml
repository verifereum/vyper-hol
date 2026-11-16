(* Uniform all-fillings prefix mask with entry-aligned oracle replay. *)
Theory dftGasPrefixProvider
Ancestors alist[qualified,ignore_grammar] dftHelpers[qualified,ignore_grammar]
  dftGasOracleKeyReplay dftGasToListReplay dftGasOracleDefs
  dftGasSimSwap dftGasSimLocalBoundary dftGasSimSchedule
  dftGasFromListRestore dftGasFromListReplay dftGasFromListReadings
  dftGasFromListReplayBoundary dftGasFromListTraceDefs dftGasFromListTraceNames
  dftGasToListTrace dftGasToListAgreement gasOracleReplay
  dftGasToListReachWitness dftGasToListVisitReplay
  dftGasFromListLocator dftGasFromListContextReach
  dftRunRel dftDefs o1PassContract contextRawReachable gasEvents gasCount
  venomExecSemantics venomState venomInst list sorting
  dftGasInvResidualTrace dftGasInvFixedTrace dftGasInvExtraction venomInstProps venomInstProofs stateEquivProofs
  dftBlockSim stateFrame venomEffects dftScheduleOrder
  dftGasInvSSAProbe unitShapeDefs venomWf option
  dftPermSim dftShape dftStructural dftCorrectness passSharedDefs
  dftSsaPreserve[qualified,ignore_grammar]

Definition dft_blocks_gas_prefix_def:
  dft_blocks_gas_prefix <=>
  !fuel C C' fn fn' s.
    LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    o1_ctx_shape C /\ o1_ctx_shape C' /\
    MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
    dft_fn_rel fn fn' /\ strict_dom_vars_defined fn s /\
    fn_reachable fn s.vs_current_bb /\
    ctx_labels_bound C s.vs_labels /\
    ctx_labels_bound C' s.vs_labels /\ ~s.vs_call_ctx.cc_static /\
    terminates (run_blocks fuel C' fn' s) /\
    gas_count_blocks fuel C' fn' s <= LENGTH s.vs_gas_readings
    ==>
    ?raw_slots sites unused.
      LENGTH raw_slots = LENGTH sites /\
      PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) s.vs_gas_readings /\
      (!t.
        (?ir. run_blocks fuel C' fn' s = IntRet ir t) ==>
        EVERY IS_SOME raw_slots /\ unused = t.vs_gas_readings) /\
      (!gobs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
        (?extra.
          sites = gas_events_blocks fuel C fn
            (s with vs_gas_readings := gobs ++ tail) ++ extra) /\
        ((?fuel_src. terminates
          (run_blocks fuel_src C fn (s with vs_gas_readings := gobs ++ tail)))
         ==>
        terminates
          (run_blocks fuel C fn (s with vs_gas_readings := gobs ++ tail)) /\
        dft_res_rel
          (restore_result []
            (run_blocks fuel C fn (s with vs_gas_readings := gobs ++ tail)))
          (restore_result [] (run_blocks fuel C' fn' s)) /\
        (!vs' nm lbl.
          C.ctx_entry = SOME nm /\ C'.ctx_entry = SOME nm /\
          lookup_function nm C.ctx_functions = SOME fn /\
          lookup_function nm C'.ctx_functions = SOME fn' /\
          fn_entry_label fn = SOME lbl /\ fn_entry_label fn' = SOME lbl /\
          s = vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |> /\ o1_run_state_ok vs' ==>
          ?orc.
            (!f. gas_res_rel
              (run_context f C (vs' with vs_gas_readings := gobs ++ tail))
              (ev_context orc f C vs')) /\
            (!f. gas_res_rel (run_context f C' vs')
                            (ev_context orc f C' vs')) /\
            (!p d f inst t. ev_reachable orc vs' C p d f inst t ==>
               ?ws. raw_reachable (vs' with vs_gas_readings := gobs ++ tail)
                         C f inst (t with vs_gas_readings := ws)) /\
            (!f inst t. raw_reachable vs' C' f inst t ==>
               ?p d. ev_reachable orc vs' C' p d f inst
                         (t with vs_gas_readings := vs'.vs_gas_readings))) /\
        (!t.
          (?ir. run_blocks fuel C' fn' s = IntRet ir t) ==>
          gas_events_blocks fuel C fn
            (s with vs_gas_readings := gobs ++ tail) = sites /\
          residual_result tail (run_blocks fuel C' fn' s)
            (run_blocks fuel C fn (s with vs_gas_readings := gobs ++ tail))))) /\
      (!gobs tail f_src.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
        ?extra.
          sites = gas_events_blocks f_src C fn
            (s with vs_gas_readings := gobs ++ tail) ++ extra)
End

Theorem native_trace_oracle_agreement:
  (!p d fuel ctx fn inst s. !orc gs.
    trace_agrees orc
      (((p,d,inst.inst_id),fn,inst,s)::
        dftGasFromListTraceDefs$trace_step p d fuel ctx fn inst s) ==>
    MAP FST (visit_gas ((p,d,inst.inst_id),fn,inst,s) ++
      trace_gas (dftGasFromListTraceDefs$trace_step p d fuel ctx fn inst s)) =
      trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst (s with vs_gas_readings := gs)) /\
    agrees orc s.vs_gas_readings
      (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst (s with vs_gas_readings := gs)))) /\
  (!p d fuel ctx fn bb s. !orc gs.
    trace_agrees orc
      (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb s) ==>
    MAP FST (trace_gas (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb s)) =
      trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb (s with vs_gas_readings := gs)) /\
    agrees orc s.vs_gas_readings
      (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb (s with vs_gas_readings := gs)))) /\
  (!p d fuel ctx fn s. !orc gs.
    trace_agrees orc
      (dftGasFromListTraceDefs$trace_blocks p d fuel ctx fn s) ==>
    MAP FST (trace_gas (dftGasFromListTraceDefs$trace_blocks p d fuel ctx fn s)) =
      trace_events (dftGasToListTrace$trace_blocks orc p d fuel ctx fn (s with vs_gas_readings := gs)) /\
    agrees orc s.vs_gas_readings
      (trace_events (dftGasToListTrace$trace_blocks orc p d fuel ctx fn (s with vs_gas_readings := gs))))
Proof
  ho_match_mp_tac dftGasFromListTraceDefsTheory.trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume native_trace_oracle_agreement[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[trace_agrees_cons] >> strip_tac >>
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[dftGasFromListTraceDefsTheory.trace_step_gas,
           dftGasToListTraceTheory.trace_step_gas,
           visit_gas_def, trace_events_def, agrees_cons] >>
      Cases_on `s.vs_gas_readings` >> gvs[]) >>
  simp[visit_gas_def, dftGasFromListTraceDefsTheory.trace_step_noninvoke,
       dftGasToListTraceTheory.trace_step_eq, gas_setup_callee] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[cj 1 dftGasFromListTraceDefsTheory.trace_defs] >>
      Cases_on `decode_invoke inst` >> gvs[trace_events_def] >>
      rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
      Cases_on `lookup_function pair0 ctx.ctx_functions` >> gvs[trace_events_def] >>
      rename1 `lookup_function _ _ = SOME callee` >>
      Cases_on `eval_operands pair1 s` >> gvs[trace_events_def] >>
      rename1 `eval_operands _ _ = SOME args` >>
      Cases_on `setup_callee callee args s` >> gvs[trace_events_def] >>
      metis_tac[gas_setup_callee_readings]) >>
  gvs[trace_events_def, dftGasFromListTraceDefsTheory.trace_step_noninvoke]
QED

Resume native_trace_oracle_agreement[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                        dftGasToListTraceTheory.trace_block_eq] >>
      simp[trace_events_def]) >>
  rename1 `get_instruction _ _ = SOME inst` >>
  qpat_x_assum `trace_agrees _ _` mp_tac >>
  simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs),
       trace_agrees_cons] >> strip_tac >>
  `restore_rel gs (step_inst fuel ctx inst s)
    (ev_step orc p d fuel ctx inst (s with vs_gas_readings := gs))` by
    (irule (cj 1 dftGasFromListReplayTheory.trace_replay) >>
     qexists_tac `fn` >> simp[trace_agrees_cons]) >>
  `MAP FST (visit_gas ((p,d,inst.inst_id),fn,inst,s) ++
     trace_gas (dftGasFromListTraceDefs$trace_step p d fuel ctx fn inst s)) =
     trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst
       (s with vs_gas_readings := gs)) /\
   agrees orc s.vs_gas_readings
     (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst
       (s with vs_gas_readings := gs)))` by
    (first_x_assum irule >> simp[trace_agrees_cons]) >>
  once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                   dftGasToListTraceTheory.trace_block_eq] >> simp[] >>
  Cases_on `step_inst fuel ctx inst s` >>
  gvs[restore_rel_cases, trace_events_def, trace_events_append,
      agrees_append, MAP_APPEND, APPEND_ASSOC] >>
  rename1 `step_inst _ _ _ _ = OK t` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[trace_events_def] >>
  `t.vs_gas_readings = DROP (gas_count_step fuel ctx inst s) s.vs_gas_readings` by
    (mp_tac (cj 1 gas_count_suffix) >>
     disch_then (qspecl_then [`fuel`, `ctx`, `inst`, `s`] mp_tac) >>
     simp[gas_count_suffix_def]) >>
  `LENGTH (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst
     (s with vs_gas_readings := gs))) = gas_count_step fuel ctx inst s` by
    metis_tac[cj 1 trace_gas_lengths, LENGTH_MAP, LENGTH_APPEND] >>
  first_x_assum (qspecl_then [`orc`, `gs`] mp_tac) >> gvs[]
QED

Resume native_trace_oracle_agreement[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel`
  >- simp[dftGasToListTraceTheory.trace_blocks_zero, trace_events_def] >>
  rename1 `SUC k` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (once_rewrite_tac[cj 3 dftGasFromListTraceDefsTheory.trace_defs,
                        dftGasToListTraceTheory.trace_blocks_eq] >>
      simp[trace_events_def]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- suspend "blocks_ok" >>
  `restore_rel gs (eval_phis s bb.bb_instructions)
     (eval_phis (s with vs_gas_readings := gs) bb.bb_instructions)` by
    metis_tac[eval_phis_restore] >>
  once_rewrite_tac[cj 3 dftGasFromListTraceDefsTheory.trace_defs,
                   dftGasToListTraceTheory.trace_blocks_eq] >>
  gvs[restore_rel_cases, trace_events_def]
QED

Resume native_trace_oracle_agreement[blocks_ok]:
  `restore_rel gs (eval_phis s bb.bb_instructions)
     (eval_phis (s with vs_gas_readings := gs) bb.bb_instructions)` by
    metis_tac[eval_phis_restore] >>
  gvs[restore_rel_cases] >>
  `s'.vs_gas_readings = s.vs_gas_readings` by
    metis_tac[gas_count_phis_ok] >>
  qpat_x_assum `trace_agrees _ _` mp_tac >>
  simp[Once (cj 3 dftGasFromListTraceDefsTheory.trace_defs),
       trace_agrees_append] >> strip_tac >>
  `restore_rel gs
     (exec_block k ctx bb (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions))
     (ev_block orc p (SUC d) k ctx bb
       (s' with <| vs_inst_idx := phi_prefix_length bb.bb_instructions;
                   vs_gas_readings := gs |>))` by
    (drule (cj 2 dftGasFromListReplayTheory.trace_replay) >>
     disch_then (qspec_then `gs` mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `orc` mp_tac) >>
  disch_then (qspec_then `gs` mp_tac) >> simp[] >> strip_tac >>
  once_rewrite_tac[cj 3 dftGasFromListTraceDefsTheory.trace_defs,
                   dftGasToListTraceTheory.trace_blocks_eq] >> simp[] >>
  Cases_on `exec_block k ctx bb
    (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[restore_rel_cases, trace_events_def, trace_events_append,
      agrees_append, MAP_APPEND] >>
  rename1 `run_block_non_phis _ _ _ _ = OK t` >>
  Cases_on `t.vs_halted` >> gvs[trace_events_def] >>
  `t.vs_gas_readings = DROP
     (gas_count_block k ctx bb
       (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions))
     s'.vs_gas_readings` by
    (mp_tac (cj 2 gas_count_suffix) >>
     disch_then (qspecl_then [`k`, `ctx`, `bb`,
       `s' with vs_inst_idx := phi_prefix_length bb.bb_instructions`] mp_tac) >>
     simp[gas_count_suffix_def]) >>
  `LENGTH (trace_events (dftGasToListTrace$trace_block orc p (SUC d) k ctx fn bb
      (s' with <| vs_inst_idx := phi_prefix_length bb.bb_instructions;
                  vs_gas_readings := gs |>))) =
    gas_count_block k ctx bb
      (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    metis_tac[cj 2 trace_gas_lengths, LENGTH_MAP] >>
  first_x_assum (qspecl_then [`orc`, `gs`] mp_tac) >> gvs[]
QED

Finalise native_trace_oracle_agreement

Theorem native_context_oracle_agreement:
  (!n. trace_agrees orc
    (dftGasFromListTraceDefs$trace_context n ctx s)) ==>
  !n. agrees orc s.vs_gas_readings
    (trace_events (dftGasToListTrace$trace_context orc n ctx s))
Proof
  strip_tac >> gen_tac >>
  first_x_assum (qspec_then `n` mp_tac) >>
  Cases_on `ctx.ctx_entry` >>
  simp[dftGasFromListTraceDefsTheory.trace_context_def,
       dftGasToListTraceTheory.trace_context_def, trace_events_def] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions` >> simp[trace_events_def] >>
  rename1 `lookup_function _ _ = SOME fn` >>
  Cases_on `fn_entry_label fn` >>
  simp[dftGasFromListTraceDefsTheory.trace_function_def,
       dftGasToListTraceTheory.trace_function_def, trace_events_def] >>
  strip_tac >> drule (cj 3 native_trace_oracle_agreement) >>
  disch_then (qspec_then `s.vs_gas_readings` mp_tac) >> simp[]
QED

Theorem fixed_shared_oracle_replay:
  !C C' orc readings s.
  EVERY wf_function C.ctx_functions /\ EVERY wf_function C'.ctx_functions /\
  (!n. agrees orc readings
    (trace_events (dftGasToListTrace$trace_context orc n C s))) /\
  (!n. trace_agrees orc (dftGasFromListTraceDefs$trace_context n C' s)) ==>
  (!f. gas_res_rel (run_context f C (s with vs_gas_readings := readings))
    (ev_context orc f C s)) /\
  (!f. gas_res_rel (run_context f C' s) (ev_context orc f C' s)) /\
  (!p d fn inst t. ev_reachable orc s C p d fn inst t ==>
    ?ws. raw_reachable (s with vs_gas_readings := readings) C fn inst
      (t with vs_gas_readings := ws)) /\
  (!fn inst t. raw_reachable s C' fn inst t ==>
    ?p d. ev_reachable orc s C' p d fn inst
      (t with vs_gas_readings := s.vs_gas_readings))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (gen_tac >> metis_tac[replay_context, residual_result_gas_rel]) >>
  conj_tac
  >- (gen_tac >> irule trace_context_gas_res >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> drule_all ev_reachable_trace_witness >>
      strip_tac >> qexists_tac `DROP n readings` >>
      irule replay_context_visit >> metis_tac[]) >>
  rpt strip_tac >> drule_all raw_reachable_trace >> strip_tac >>
  qexistsl_tac [`p`, `d`] >> irule trace_context_reachable >>
  metis_tac[]
QED

Theorem stopped_invoke_native_row:
  !p d fuel ctx fn bb inst s nm ops callee args cs slots keys.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\
    setup_callee callee args s = SOME cs /\
    (!g tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots g ==>
      ?k. k <= LENGTH keys /\
        trace_gas (dftGasFromListTraceDefs$trace_blocks
          ((d,inst.inst_id)::p) d fuel ctx callee
          (cs with vs_gas_readings := g ++ tail)) =
        ZIP (TAKE k keys, TAKE k g)) ==>
    !g tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots g /\
      (~?u. step_inst fuel ctx inst
        (s with vs_gas_readings := g ++ tail) = OK u) ==>
      ?k. k <= LENGTH keys /\
        trace_gas (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb
          (s with vs_gas_readings := g ++ tail)) =
        ZIP (TAKE k keys, TAKE k g)
Proof
  rpt strip_tac >>
  `get_instruction bb
     (s with vs_gas_readings := g ++ tail).vs_inst_idx = SOME inst`
    by simp[] >>
  drule dftGasFromListTraceDefsTheory.trace_block_visit >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[cj 1 dftGasFromListTraceDefsTheory.trace_defs,
       gas_eval_operands, gas_setup_callee] >>
  Cases_on `step_inst fuel ctx inst
    (s with vs_gas_readings := g ++ tail)` >>
  gvs[dftGasFromListTraceDefsTheory.trace_gas_def,
      dftGasFromListTraceDefsTheory.visit_gas_def]
QED

Theorem returning_child_packet_exhaustion:
  LENGTH keys = LENGTH g /\ LENGTH sites = LENGTH g /\
  ((?f. terminates (run_blocks f C fn
      (cs with vs_gas_readings := g ++ tail))) ==>
    terminates (run_blocks b C fn (cs with vs_gas_readings := g ++ tail)) /\
    dft_res_rel
      (restore_result [] (run_blocks b C fn (cs with vs_gas_readings := g ++ tail)))
      (restore_result [] target)) /\
  (!v t. target = IntRet v t ==>
    residual_result tail target
      (run_blocks b C fn (cs with vs_gas_readings := g ++ tail))) /\
  (!f. ?k. k <= LENGTH keys /\
    trace_gas (dftGasFromListTraceDefs$trace_blocks p d f C fn
      (cs with vs_gas_readings := g ++ tail)) =
      ZIP (TAKE k keys, TAKE k g)) /\
  (!f. ?extra. sites = gas_events_blocks f C fn
      (cs with vs_gas_readings := g ++ tail) ++ extra) /\
  run_blocks n C fn (cs with vs_gas_readings := g ++ tail) = IntRet ret u ==>
  (?t. target = IntRet ret t) /\
  run_blocks b C fn (cs with vs_gas_readings := g ++ tail) = IntRet ret u /\
  trace_gas (dftGasFromListTraceDefs$trace_blocks p d n C fn
    (cs with vs_gas_readings := g ++ tail)) = ZIP (keys,g) /\
  gas_events_blocks n C fn (cs with vs_gas_readings := g ++ tail) = sites /\
  u.vs_gas_readings = tail
Proof
  strip_tac >>
  `terminates (run_blocks b C fn (cs with vs_gas_readings := g ++ tail)) /\
   dft_res_rel
    (restore_result [] (run_blocks b C fn (cs with vs_gas_readings := g ++ tail)))
    (restore_result [] target)` by
    (first_x_assum irule >> qexists_tac `n` >> simp[passSimulationDefsTheory.terminates_def]) >>
  `run_blocks b C fn (cs with vs_gas_readings := g ++ tail) = IntRet ret u` by
    (mp_tac (cj 3 venomExecProofsTheory.fuel_mono) >>
     disch_then (qspecl_then [`b`, `MAX b n`, `C`, `fn`,
       `cs with vs_gas_readings := g ++ tail`,
       `run_blocks b C fn (cs with vs_gas_readings := g ++ tail)`] mp_tac) >>
     simp[] >>
     `(!e. run_blocks b C fn (cs with vs_gas_readings := g ++ tail) <> Error e)` by
       (Cases_on `run_blocks b C fn (cs with vs_gas_readings := g ++ tail)` >>
        gvs[passSimulationDefsTheory.terminates_def]) >>
     simp[] >> strip_tac >>
     mp_tac (cj 3 venomExecProofsTheory.fuel_mono) >>
     disch_then (qspecl_then [`n`, `MAX b n`, `C`, `fn`,
       `cs with vs_gas_readings := g ++ tail`, `IntRet ret u`] mp_tac) >>
     simp[]) >>
  Cases_on `target` >>
  gvs[restore_result_def, dft_res_rel_def] >>
  fs[residual_result_def, stateEquivTheory.lift_result_def] >>
  qpat_x_assum `!f. ?k. _ /\ trace_gas _ = _`
    (qspec_then `n` strip_assume_tac) >>
  `gas_count_blocks n C fn (cs with vs_gas_readings := g ++ tail) = k` by
    (mp_tac (cj 3 trace_gas_lengths) >>
     disch_then (qspecl_then [`p`, `d`, `n`, `C`, `fn`,
       `cs with vs_gas_readings := g ++ tail`] mp_tac) >>
     simp[LENGTH_ZIP, LENGTH_TAKE]) >>
  `tail = DROP k (g ++ tail)` by
    (mp_tac (cj 3 gas_count_suffix) >>
     disch_then (qspecl_then [`n`, `C`, `fn`,
       `cs with vs_gas_readings := g ++ tail`] mp_tac) >>
     simp[gas_count_suffix_def]) >>
  `k = LENGTH g` by
    (qpat_x_assum `tail = DROP _ _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  gvs[] >>
  qpat_x_assum `!f. ?extra. _` (qspec_then `n` strip_assume_tac) >>
  `extra = []` by
    (mp_tac (cj 3 gas_events_length) >>
     disch_then (qspecl_then [`n`, `C`, `fn`,
       `cs with vs_gas_readings := g ++ tail`] mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  gvs[TAKE_LENGTH_TOO_LONG]
QED

Theorem ambient_region_mask:
  EVERY R keys ==>
  MAP (ALOOKUP (FILTER (\kw. R (FST kw)) obs)) keys =
  MAP (ALOOKUP obs) keys
Proof
  strip_tac >> irule MAP_CONG >> simp[] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  `R x` by metis_tac[] >>
  simp[pairTheory.LAMBDA_PROD, alistTheory.ALOOKUP_FILTER]
QED

Theorem native_blocks_gas_region:
  EVERY (\kw. later_region p d (FST kw))
    (trace_gas (dftGasFromListTraceDefs$trace_blocks p d fuel C fn s))
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM (FST kw) (MAP FST
    (dftGasFromListTraceDefs$trace_blocks p d fuel C fn s))` by
    (irule trace_gas_name_mem >> simp[MEM_MAP] >> metis_tac[]) >>
  gvs[MEM_MAP] >> drule trace_blocks_region >> simp[]
QED

Theorem crossed_schedule_probe[local]:
  dft_block ["g"]
      <| bb_label := "entry"; bb_instructions :=
        [mk_inst 2 GAS [] ["g"];
         mk_inst 1 INVOKE [Label "child"] ["x"];
         mk_inst 3 RET [Var "x"; Var "g"; Lit 0w] []] |> =
      <| bb_label := "entry"; bb_instructions :=
        [mk_inst 1 INVOKE [Label "child"] ["x"];
         mk_inst 2 GAS [] ["g"];
         mk_inst 3 RET [Var "x"; Var "g"; Lit 0w] []] |>
Proof
  EVAL_TAC
QED

Theorem crossed_target_stopped_probe[local]:
  s.vs_inst_idx = 0 /\
  lookup_function "child" C.ctx_functions = SOME callee /\
  setup_callee callee [] s = SOME cs /\
  run_blocks b C callee cs = Halt t ==>
  exec_block b C
    (dft_block ["g"]
      <| bb_label := "entry"; bb_instructions :=
        [mk_inst 2 GAS [] ["g"];
         mk_inst 1 INVOKE [Label "child"] ["x"];
         mk_inst 3 RET [Var "x"; Var "g"; Lit 0w] []] |>) s = Halt t /\
  trace_gas (dftGasFromListTraceDefs$trace_block p d b C fn
    (dft_block ["g"]
      <| bb_label := "entry"; bb_instructions :=
        [mk_inst 2 GAS [] ["g"];
         mk_inst 1 INVOKE [Label "child"] ["x"];
         mk_inst 3 RET [Var "x"; Var "g"; Lit 0w] []] |>) s) =
  trace_gas (dftGasFromListTraceDefs$trace_blocks ((d,1)::p) d b C callee cs)
Proof
  strip_tac >>
  simp[crossed_schedule_probe, Once exec_block_def,
       get_instruction_def, Once step_inst_def, decode_invoke_def,
       eval_operands_def, mk_inst_def,
       Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs),
       cj 1 dftGasFromListTraceDefsTheory.trace_defs,
       trace_gas_def, visit_gas_def] >>
  simp[Once step_inst_def, decode_invoke_def, eval_operands_def]
QED

(* The return boundary is aligned only after exec_block has performed both
   increments.  In particular the raw caller states need not coincide. *)
Theorem crossed_returning_caller_boundary[local]:
  ~MEM out outs /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state a rt)) = SOME qt ==>
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret
      (merge_callee_state
        ((update_var out w (a with vs_gas_readings := readings)) with
          vs_inst_idx := SUC j)
        (rt with vs_gas_readings := tail))) =
    SOME ((update_var out w qt) with
      <| vs_inst_idx := SUC j; vs_gas_readings := tail |>) /\
  (((update_var out w qt) with
      <| vs_inst_idx := SUC j; vs_gas_readings := tail |>) with
        vs_inst_idx := SUC (SUC j)) =
  (((update_var out w ((qt with vs_inst_idx := SUC j) with
        vs_gas_readings := rest_readings)) with
          vs_inst_idx := SUC (SUC j)) with vs_gas_readings := tail)
Proof
  strip_tac >> conj_tac
  >- (`adopt_return_fmp ret
        (merge_callee_state
          ((update_var out w (a with vs_gas_readings := readings)) with
            vs_inst_idx := SUC j)
          (rt with vs_gas_readings := tail)) =
        ((update_var out w
          (adopt_return_fmp ret (merge_callee_state a rt))) with
            <|vs_inst_idx := SUC j; vs_gas_readings := tail|>)` by
        (Cases_on `ret.iret_adopt_fmp` >>
         simp[adopt_return_fmp_def, merge_callee_state_def, update_var_def,
              venom_state_component_equality]) >>
      simp[venomExecProofsTheory.bind_outputs_idx, gas_bind_outputs,
           dftCommutationTheory.bind_outputs_update_var]) >>
  simp[update_var_def]
QED

Theorem native_trace_block_suffix_cong[local]:
  !xs s bb bb'.
    DROP s.vs_inst_idx bb.bb_instructions = xs /\
    DROP s.vs_inst_idx bb'.bb_instructions = xs ==>
    dftGasFromListTraceDefs$trace_block p d fuel C fn bb s =
    dftGasFromListTraceDefs$trace_block p d fuel C fn bb' s
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (`LENGTH bb.bb_instructions <= s.vs_inst_idx /\
       LENGTH bb'.bb_instructions <= s.vs_inst_idx` by
        gvs[DROP_EQ_NIL] >>
      simp[Once dftGasFromListTraceDefsTheory.trace_defs, get_instruction_def] >>
      simp[Once dftGasFromListTraceDefsTheory.trace_defs, get_instruction_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   s.vs_inst_idx < LENGTH bb'.bb_instructions` by
    (qpat_x_assum `DROP _ bb.bb_instructions = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     qpat_x_assum `DROP _ bb'.bb_instructions = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   EL s.vs_inst_idx bb'.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = xs /\
   DROP (SUC s.vs_inst_idx) bb'.bb_instructions = xs` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  once_rewrite_tac[dftGasFromListTraceDefsTheory.trace_defs] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel C h s` >> simp[] >>
  Cases_on `is_terminator h.inst_opcode` >> simp[] >>
  first_x_assum irule >> simp[]
QED

Theorem crossed_returning_target_decomposition[local]:
  let q = (d,call.inst_id)::p;
      e = (p,d,gas.inst_id);
      bt = bb with bb_instructions := REPLICATE j pad ++ call::gas::rest;
      br = bb with bb_instructions := REPLICATE (SUC (SUC j)) pad ++ rest;
      aI = qt with vs_inst_idx := SUC j;
      aR = (update_var out w0 (aI with vs_gas_readings := r0)) with
        vs_inst_idx := SUC (SUC j)
  in
  a.vs_inst_idx = j /\ gas.inst_opcode = GAS /\
  gas.inst_outputs = [out] /\ inst_wf gas /\ call.inst_opcode = INVOKE /\
  decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME callee' /\
  eval_operands ops a = SOME args /\
  setup_callee callee' args a = SOME ct /\
  run_blocks b C' callee' ct = IntRet ret rt /\
  bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state a rt)) = SOME qt /\
  aI.vs_gas_readings = w0::r0 ==>
  exec_block b C' bt a = exec_block b C' br aR /\
  trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt a) =
    trace_gas (dftGasFromListTraceDefs$trace_blocks q d b C' callee' ct) ++
    [(e,w0)] ++
    trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' br aR)
Proof
  simp_tac pure_ss [LET_THM] >>
  qabbrev_tac `q = (d,call.inst_id)::p` >>
  qabbrev_tac `e = (p,d,gas.inst_id)` >>
  qabbrev_tac `bt = bb with bb_instructions := REPLICATE j pad ++ call::gas::rest` >>
  qabbrev_tac `br = bb with bb_instructions := REPLICATE (SUC (SUC j)) pad ++ rest` >>
  qabbrev_tac `aI = qt with vs_inst_idx := SUC j` >>
  qabbrev_tac `aR = (update_var out w0 (aI with vs_gas_readings := r0)) with
    vs_inst_idx := SUC (SUC j)` >> strip_tac >>
  `step_inst b C' call a = OK qt` by
    (simp[Once step_inst_def] >> gvs[]) >>
  `step_inst b C' gas aI = OK (update_var out w0 (aI with vs_gas_readings := r0))` by
    (drule_all dftBlockSimTheory.step_inst_gas_single >>
     disch_then (qspecl_then [`aI`, `b`, `C'`] mp_tac) >> simp[]) >>
  `get_instruction bt j = SOME call /\
   get_instruction bt (SUC j) = SOME gas` by
    simp[Abbr `bt`, get_instruction_def, EL_APPEND_EQN] >>
  `aI.vs_inst_idx = SUC j` by simp[Abbr `aI`] >>
  conj_tac
  >- (simp[Once exec_block_def] >> simp[is_terminator_def] >>
      `qt with vs_inst_idx := SUC j = aI` by simp[Abbr `aI`] >>
      asm_rewrite_tac[] >> simp[Once exec_block_def] >>
      simp[is_terminator_def] >>
      `((update_var out w0 (aI with vs_gas_readings := r0)) with
         vs_inst_idx := SUC aI.vs_inst_idx) = aR` by simp[Abbr `aI`, Abbr `aR`] >>
      asm_rewrite_tac[] >> simp[Abbr `aR`] >>
      irule venomExecProofsTheory.exec_block_same_suffix >>
      `j - SUC (SUC j) = 0 /\ SUC (SUC j) - (j + 2) = 0` by decide_tac >>
      simp[Abbr `bt`, Abbr `br`, DROP_APPEND]) >>
  simp[Once dftGasFromListTraceDefsTheory.trace_defs] >>
  simp[trace_gas_def, visit_gas_def, is_terminator_def] >>
  `dftGasFromListTraceDefs$trace_step p d b C' fn' call a =
    dftGasFromListTraceDefs$trace_blocks q d b C' callee' ct` by
    (simp[Once dftGasFromListTraceDefsTheory.trace_defs, Abbr `q`] >> gvs[]) >>
  asm_rewrite_tac[] >> simp[GSYM trace_gas_def] >>
  simp[Once dftGasFromListTraceDefsTheory.trace_defs] >>
  simp[dftGasFromListTraceDefsTheory.trace_step_gas,
    trace_gas_def, visit_gas_def, is_terminator_def] >>
  simp[GSYM trace_gas_def, Abbr `e`, Abbr `aR`] >> AP_TERM_TAC >>
  irule native_trace_block_suffix_cong >>
  `j - SUC (SUC j) = 0 /\ SUC (SUC j) - (j + 2) = 0` by decide_tac >>
  simp[Abbr `bt`, Abbr `br`, DROP_APPEND]
QED

Theorem crossed_region_lookup_split[local]:
  ALOOKUP Oc e = NONE /\
  (!x. MEM x Kc ==> ALOOKUP obsr x = NONE /\ x <> e) /\
  (!x. MEM x Kr ==> ALOOKUP Oc x = NONE /\ x <> e) ==>
  MAP (ALOOKUP (Oc ++ [(e,w)] ++ obsr)) (e::(Kc ++ Kr)) =
    SOME w::(MAP (ALOOKUP Oc) Kc ++ MAP (ALOOKUP obsr) Kr)
Proof
  strip_tac >> simp[alistTheory.ALOOKUP_APPEND] >> BINOP_TAC
  >- (irule MAP_CONG >> simp[] >> rpt strip_tac >>
      Cases_on `ALOOKUP Oc x` >> simp[alistTheory.ALOOKUP_APPEND]) >>
  irule MAP_CONG >> simp[alistTheory.ALOOKUP_APPEND]
QED

Theorem crossed_returning_source_expansion[local]:
  let bs = bb with bb_instructions := REPLICATE j pad ++ gas::call::rest;
      br = bb with bb_instructions := REPLICATE (SUC (SUC j)) pad ++ rest;
      aG = (update_var out w (a with vs_gas_readings := hc ++ tail)) with
        vs_inst_idx := SUC j;
      aR = (update_var out w ((qt with vs_inst_idx := SUC j) with
        vs_gas_readings := r0)) with vs_inst_idx := SUC (SUC j)
  in
  a.vs_inst_idx = j /\ gas.inst_opcode = GAS /\ gas.inst_outputs = [out] /\
  inst_wf gas /\ call.inst_opcode = INVOKE /\ ~MEM out call.inst_outputs /\
  decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops aG = SOME args /\
  setup_callee callee args aG = SOME (cs with vs_gas_readings := hc ++ tail) /\
  run_blocks n C callee (cs with vs_gas_readings := hc ++ tail) =
    IntRet ret (rt with vs_gas_readings := tail) /\
  bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state a rt)) = SOME qt ==>
  exec_block n C bs (a with vs_gas_readings := w::(hc ++ tail)) =
    exec_block n C br (aR with vs_gas_readings := tail) /\
  trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bs
    (a with vs_gas_readings := w::(hc ++ tail))) =
    ((p,d,gas.inst_id),w)::
      (trace_gas (dftGasFromListTraceDefs$trace_blocks ((d,call.inst_id)::p) d n C callee
        (cs with vs_gas_readings := hc ++ tail)) ++
       trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn br
        (aR with vs_gas_readings := tail))) /\
  gas_events_block n C fn.fn_name bs (a with vs_gas_readings := w::(hc ++ tail)) =
    (fn.fn_name,gas.inst_id)::
      (gas_events_blocks n C callee (cs with vs_gas_readings := hc ++ tail) ++
       gas_events_block n C fn.fn_name br (aR with vs_gas_readings := tail))
Proof
  simp_tac pure_ss [LET_THM] >>
  qabbrev_tac `bs = bb with bb_instructions := REPLICATE j pad ++ gas::call::rest` >>
  qabbrev_tac `br = bb with bb_instructions := REPLICATE (SUC (SUC j)) pad ++ rest` >>
  qabbrev_tac `aG = (update_var out w (a with vs_gas_readings := hc ++ tail)) with
    vs_inst_idx := SUC j` >>
  qabbrev_tac `aR = (update_var out w ((qt with vs_inst_idx := SUC j) with
    vs_gas_readings := r0)) with vs_inst_idx := SUC (SUC j)` >>
  strip_tac >>
  drule_all crossed_returning_caller_boundary >>
  disch_then (qspecl_then [`w`, `tail`, `r0`, `hc ++ tail`, `j`] strip_assume_tac) >>
  `step_inst n C gas (a with vs_gas_readings := w::(hc ++ tail)) =
    OK (update_var out w (a with vs_gas_readings := hc ++ tail))` by
    simp[Once step_inst_def, step_inst_base_def, exec_gas_def] >>
  `step_inst n C call aG = OK ((update_var out w qt) with
    <|vs_inst_idx := SUC j; vs_gas_readings := tail|>)` by
    (simp[Once step_inst_def] >> gvs[Abbr `aG`]) >>
  `get_instruction bs j = SOME gas /\
   get_instruction bs (SUC j) = SOME call` by
    simp[Abbr `bs`, get_instruction_def, EL_APPEND_EQN] >>
  `((update_var out w qt with
    <|vs_inst_idx := SUC j; vs_gas_readings := tail|>) with
    vs_inst_idx := SUC aG.vs_inst_idx) = (aR with vs_gas_readings := tail)` by
    simp[Abbr `aG`, Abbr `aR`, update_var_def] >>
  `j - SUC (SUC j) = 0 /\ SUC (SUC j) - (j + 2) = 0` by decide_tac >>
  `DROP (SUC (SUC j)) bs.bb_instructions = rest /\
   DROP (SUC (SUC j)) br.bb_instructions = rest` by
    simp[Abbr `bs`, Abbr `br`, DROP_APPEND] >>
  `aG.vs_inst_idx = SUC j` by simp[Abbr `aG`] >>
  `((update_var out w (a with vs_gas_readings := hc ++ tail)) with
     vs_inst_idx := SUC a.vs_inst_idx) = aG` by simp[Abbr `aG`] >>
  fs[] >>
  conj_tac
  >- (simp[Once exec_block_def, is_terminator_def] >>
      asm_rewrite_tac[] >> simp[Once exec_block_def, is_terminator_def] >>
      fs[] >>
      irule venomExecProofsTheory.exec_block_same_suffix >> simp[Abbr `aR`, update_var_def]) >>
  conj_tac
  >- (simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs),
           cj 1 dftGasFromListTraceDefsTheory.trace_defs, is_terminator_def] >>
      fs[] >>
      simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs),
           cj 1 dftGasFromListTraceDefsTheory.trace_defs, is_terminator_def] >>
      fs[trace_gas_def, visit_gas_def] >>
      simp[GSYM trace_gas_def] >> AP_TERM_TAC >>
      irule native_trace_block_suffix_cong >> simp[Abbr `aR`, update_var_def]) >>
  simp[Once gas_events_block_def, gas_events_step_def, is_terminator_def] >>
  fs[] >>
  simp[Once gas_events_block_def, gas_events_step_def, is_terminator_def] >>
  fs[] >>
  irule gas_events_block_suffix_cong >> simp[Abbr `aR`, update_var_def]
QED

Theorem crossed_nonreturning_source_expansion[local]:
  let bs = bb with bb_instructions := REPLICATE j pad ++ gas::call::rest;
      aG = (update_var out w (a with vs_gas_readings := readings)) with
        vs_inst_idx := SUC j
  in
  a.vs_inst_idx = j /\ gas.inst_opcode = GAS /\ gas.inst_outputs = [out] /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops aG = SOME args /\
  setup_callee callee args aG = SOME cs /\
  (!v u. run_blocks n C callee cs <> IntRet v u) ==>
  exec_block n C bs (a with vs_gas_readings := w::readings) =
    run_blocks n C callee cs /\
  trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bs
    (a with vs_gas_readings := w::readings)) =
    ((p,d,gas.inst_id),w)::
      trace_gas (dftGasFromListTraceDefs$trace_blocks ((d,call.inst_id)::p) d n C callee cs) /\
  gas_events_block n C fn.fn_name bs (a with vs_gas_readings := w::readings) =
    (fn.fn_name,gas.inst_id)::gas_events_blocks n C callee cs
Proof
  simp_tac pure_ss [LET_THM] >>
  qabbrev_tac `bs = bb with bb_instructions := REPLICATE j pad ++ gas::call::rest` >>
  qabbrev_tac `aG = (update_var out w (a with vs_gas_readings := readings)) with
    vs_inst_idx := SUC j` >> strip_tac >>
  `!n s u. run_blocks n C callee s <> OK u` by
    metis_tac[o1PassLiftTheory.run_blocks_not_OK] >>
  `step_inst n C gas (a with vs_gas_readings := w::readings) =
    OK (update_var out w (a with vs_gas_readings := readings))` by
    simp[Once step_inst_def, step_inst_base_def, exec_gas_def] >>
  `step_inst n C call aG = run_blocks n C callee cs` by
    (simp[Once step_inst_def] >> Cases_on `run_blocks n C callee cs` >> fs[] >> metis_tac[]) >>
  `get_instruction bs j = SOME gas /\ get_instruction bs (SUC j) = SOME call` by
    simp[Abbr `bs`, get_instruction_def, EL_APPEND_EQN] >>
  `aG.vs_inst_idx = SUC j /\
   ((update_var out w (a with vs_gas_readings := readings)) with
     vs_inst_idx := SUC a.vs_inst_idx) = aG` by simp[Abbr `aG`] >>
  fs[] >> conj_tac
  >- (simp[Once exec_block_def, is_terminator_def] >> fs[] >>
      simp[Once exec_block_def, is_terminator_def] >>
      Cases_on `run_blocks n C callee cs` >> fs[] >> metis_tac[]) >>
  conj_tac
  >- (simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs),
           cj 1 dftGasFromListTraceDefsTheory.trace_defs, is_terminator_def] >> fs[] >>
      simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs),
           cj 1 dftGasFromListTraceDefsTheory.trace_defs, is_terminator_def] >>
      Cases_on `run_blocks n C callee cs` >> fs[trace_gas_def, visit_gas_def] >> metis_tac[]) >>
  simp[Once gas_events_block_def, gas_events_step_def, is_terminator_def] >> fs[] >>
  simp[Once gas_events_block_def, gas_events_step_def, is_terminator_def] >>
  Cases_on `run_blocks n C callee cs` >> fs[] >> metis_tac[]
QED

Theorem crossed_returning_packet_constructor:
  let q = (d,call.inst_id)::p;
      e = (p,d,gas.inst_id);
      bc = bb with bb_instructions := REPLICATE j pad ++ gas::call::rest;
      bt = bb with bb_instructions := REPLICATE j pad ++ call::gas::rest;
      br = bb with bb_instructions := REPLICATE (SUC (SUC j)) pad ++ rest;
      aI = qt with vs_inst_idx := SUC j;
      aR = (update_var out w0 (aI with vs_gas_readings := r0)) with
        vs_inst_idx := SUC (SUC j);
      Tc = run_blocks b C' callee' ct;
      Oc = trace_gas (dftGasFromListTraceDefs$trace_blocks q d b C' callee' ct);
      Tr = exec_block b C' br aR;
      Or = trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' br aR);
      Mc = MAP (ALOOKUP Oc) Kc;
      Mr = MAP (ALOOKUP Or) Kr;
      T = exec_block b C' bt a;
      obs = trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt a);
      K = e::(Kc ++ Kr);
      S = (fn.fn_name,gas.inst_id)::(Sc ++ Sr);
      M = MAP (ALOOKUP obs) K
  in
  a.vs_inst_idx = j /\ gas.inst_opcode = GAS /\
  gas.inst_outputs = [out] /\ inst_wf gas /\
  call.inst_opcode = INVOKE /\ inst_wf call /\
  dft_gas_swap_pair gas call /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (gas::call::rest)) /\
  fn.fn_name = fn'.fn_name /\
  decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  lookup_function nm C'.ctx_functions = SOME callee' /\
  callee' = dft_fn callee /\ dft_fn_rel callee callee' /\
  eval_operands ops a = SOME args /\
  setup_callee callee args a = SOME cs /\
  setup_callee callee' args a = SOME ct /\
  (cs with vs_gas_readings := []) = (ct with vs_gas_readings := []) /\
  Tc = IntRet ret rt /\
  bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state a rt)) = SOME qt /\
  aI.vs_gas_readings = w0::r0 /\
  terminates T /\ gas_count_block b C' bt a <= LENGTH a.vs_gas_readings /\
  ALL_DISTINCT Kc /\ EVERY (later_region q d) Kc /\
  LENGTH Kc = LENGTH Sc /\
  PERM (MAP THE (FILTER IS_SOME Mc) ++ Uc) ct.vs_gas_readings /\
  (!v u. Tc = IntRet v u ==> EVERY IS_SOME Mc /\ Uc = u.vs_gas_readings) /\
  (!hc tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mc hc ==>
    (!n. ?k. k <= LENGTH Kc /\
      trace_gas (dftGasFromListTraceDefs$trace_blocks q d n C callee
        (cs with vs_gas_readings := hc ++ tail)) = ZIP (TAKE k Kc,TAKE k hc) /\
      gas_events_blocks n C callee (cs with vs_gas_readings := hc ++ tail) =
        TAKE k Sc) /\
    ((?n. terminates (run_blocks n C callee
        (cs with vs_gas_readings := hc ++ tail))) ==>
      terminates (run_blocks b C callee (cs with vs_gas_readings := hc ++ tail)) /\
      dft_res_rel
        (restore_result [] (run_blocks b C callee
          (cs with vs_gas_readings := hc ++ tail))) (restore_result [] Tc) /\
      (!v u. Tc = IntRet v u ==>
        gas_events_blocks b C callee (cs with vs_gas_readings := hc ++ tail) = Sc /\
        residual_result tail Tc
          (run_blocks b C callee (cs with vs_gas_readings := hc ++ tail))))) /\
  ALL_DISTINCT Kr /\
  EVERY (block_region p d (MAP (\i. i.inst_id) rest)) Kr /\
  LENGTH Kr = LENGTH Sr /\
  PERM (MAP THE (FILTER IS_SOME Mr) ++ Ur) aR.vs_gas_readings /\
  (!u. Tr = OK u ==> EVERY IS_SOME Mr /\ Ur = u.vs_gas_readings) /\
  (!v u. Tr = IntRet v u ==> EVERY IS_SOME Mr /\ Ur = u.vs_gas_readings) /\
  (!hr tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mr hr ==>
    (!n. ?k. k <= LENGTH Kr /\
      trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn br
        (aR with vs_gas_readings := hr ++ tail)) = ZIP (TAKE k Kr,TAKE k hr) /\
      gas_events_block n C fn.fn_name br (aR with vs_gas_readings := hr ++ tail) =
        TAKE k Sr) /\
    ((?n. terminates (exec_block n C br
        (aR with vs_gas_readings := hr ++ tail))) ==>
      terminates (exec_block b C br (aR with vs_gas_readings := hr ++ tail)) /\
      dft_res_rel
        (restore_result [] (exec_block b C br
          (aR with vs_gas_readings := hr ++ tail))) (restore_result [] Tr) /\
      (!u. Tr = OK u ==>
        gas_events_block b C fn.fn_name br (aR with vs_gas_readings := hr ++ tail) = Sr /\
        residual_result tail Tr
          (exec_block b C br (aR with vs_gas_readings := hr ++ tail))) /\
      (!v u. Tr = IntRet v u ==>
        gas_events_block b C fn.fn_name br (aR with vs_gas_readings := hr ++ tail) = Sr /\
        residual_result tail Tr
          (exec_block b C br (aR with vs_gas_readings := hr ++ tail))))) ==>
  ALL_DISTINCT K /\
  EVERY (block_region p d (MAP (\i. i.inst_id) (gas::call::rest))) K /\
  LENGTH K = LENGTH S /\
  PERM (MAP THE (FILTER IS_SOME M) ++ Ur) a.vs_gas_readings /\
  (!u. T = OK u ==> EVERY IS_SOME M /\ Ur = u.vs_gas_readings) /\
  (!v u. T = IntRet v u ==> EVERY IS_SOME M /\ Ur = u.vs_gas_readings) /\
  (!g tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M g ==>
    (!n. ?k. k <= LENGTH K /\
      trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bc
        (a with vs_gas_readings := g ++ tail)) = ZIP (TAKE k K,TAKE k g) /\
      gas_events_block n C fn.fn_name bc (a with vs_gas_readings := g ++ tail) =
        TAKE k S) /\
    ((?n. terminates (exec_block n C bc
        (a with vs_gas_readings := g ++ tail))) ==>
      terminates (exec_block b C bc (a with vs_gas_readings := g ++ tail)) /\
      dft_res_rel
        (restore_result [] (exec_block b C bc
          (a with vs_gas_readings := g ++ tail))) (restore_result [] T) /\
      (!u. T = OK u ==>
        gas_events_block b C fn.fn_name bc (a with vs_gas_readings := g ++ tail) = S /\
        residual_result tail T
          (exec_block b C bc (a with vs_gas_readings := g ++ tail))) /\
      (!v u. T = IntRet v u ==>
        gas_events_block b C fn.fn_name bc (a with vs_gas_readings := g ++ tail) = S /\
        residual_result tail T
          (exec_block b C bc (a with vs_gas_readings := g ++ tail)))))
Proof
  simp_tac pure_ss [LET_THM] >>
  qabbrev_tac `q = (d,call.inst_id)::p` >>
  qabbrev_tac `e = (p,d,gas.inst_id)` >>
  qabbrev_tac `bc = bb with bb_instructions := REPLICATE j pad ++ gas::call::rest` >>
  qabbrev_tac `bt = bb with bb_instructions := REPLICATE j pad ++ call::gas::rest` >>
  qabbrev_tac `br = bb with bb_instructions := REPLICATE (SUC (SUC j)) pad ++ rest` >>
  qabbrev_tac `aI = qt with vs_inst_idx := SUC j` >>
  qabbrev_tac `aR = (update_var out w0 (aI with vs_gas_readings := r0)) with
    vs_inst_idx := SUC (SUC j)` >>
  qabbrev_tac `Tc = run_blocks b C' callee' ct` >>
  qabbrev_tac `Oc = trace_gas (dftGasFromListTraceDefs$trace_blocks q d b C' callee' ct)` >>
  qabbrev_tac `Tr = exec_block b C' br aR` >>
  qabbrev_tac `obsr = trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' br aR)` >>
  qabbrev_tac `Mc = MAP (ALOOKUP Oc) Kc` >>
  qabbrev_tac `Mr = MAP (ALOOKUP obsr) Kr` >>
  qabbrev_tac `target = exec_block b C' bt a` >>
  qabbrev_tac `obs = trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt a)` >>
  qabbrev_tac `keys = e::(Kc ++ Kr)` >>
  qabbrev_tac `sites = (fn.fn_name,gas.inst_id)::(Sc ++ Sr)` >>
  qabbrev_tac `slots = MAP (ALOOKUP obs) keys` >>
  strip_tac >>
  `target = Tr /\ obs = Oc ++ [(e,w0)] ++ obsr` by
    (simp[Abbr `target`, Abbr `Tr`, Abbr `obs`, Abbr `Oc`, Abbr `obsr`,
          Abbr `q`, Abbr `e`, Abbr `bt`, Abbr `br`, Abbr `aR`, Abbr `aI`] >>
     irule (SRULE [LET_THM] crossed_returning_target_decomposition) >>
     fs[Abbr `Tc`] >> metis_tac[]) >>
  `EVERY (\kw. block_region p d [call.inst_id] (FST kw)) Oc` by
    (simp[Abbr `Oc`, EVERY_MEM] >> rpt strip_tac >>
     `MEM (FST kw) (MAP FST (dftGasFromListTraceDefs$trace_blocks q d b C' callee' ct))` by
       (irule trace_gas_name_mem >> simp[MEM_MAP] >> metis_tac[]) >>
     gvs[MEM_MAP] >> drule trace_blocks_region >>
     strip_tac >> PairCases_on `y` >> gvs[] >>
     drule later_region_frame >>
     simp[Abbr `q`] >> metis_tac[below_call_region, MEM]) >>
  `EVERY (\kw. block_region p d (MAP (\i. i.inst_id) rest) (FST kw)) obsr` by
    (simp[Abbr `obsr`, EVERY_MEM] >> rpt strip_tac >>
     `MEM (FST kw) (MAP FST (dftGasFromListTraceDefs$trace_block p d b C' fn' br aR))` by
       (irule trace_gas_name_mem >> simp[MEM_MAP] >> metis_tac[]) >>
     gvs[MEM_MAP] >> drule trace_block_region >>
     `j - SUC (SUC j) = 0` by decide_tac >>
     simp[Abbr `br`, Abbr `aR`, DROP_APPEND]) >>
  `EVERY (block_region p d [call.inst_id]) Kc` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     PairCases_on `e'` >>
     metis_tac[later_region_frame, below_call_region, MEM]) >>
  `!x. block_region p d [gas.inst_id] x ==>
     ~block_region p d [call.inst_id] x /\
     ~block_region p d (MAP (\i. i.inst_id) rest) x` by
    (gen_tac >> disch_tac >> conj_tac >>
     irule block_regions_disjoint >> qexists_tac `[gas.inst_id]` >>
     gvs[MEM_MAP] >> metis_tac[]) >>
  `!x. block_region p d [call.inst_id] x ==>
     ~block_region p d (MAP (\i. i.inst_id) rest) x` by
    (gen_tac >> disch_tac >>
     irule block_regions_disjoint >> qexists_tac `[call.inst_id]` >>
     gvs[MEM_MAP] >> metis_tac[]) >>
  `block_region p d [gas.inst_id] e` by simp[Abbr `e`, block_region_def] >>
  `ALOOKUP Oc e = NONE` by
    (simp[alistTheory.ALOOKUP_NONE, MEM_MAP] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `!x. MEM x Kr ==> ALOOKUP Oc x = NONE /\ x <> e` by
    (simp[alistTheory.ALOOKUP_NONE, MEM_MAP] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `!x. MEM x Kc ==> ALOOKUP obsr x = NONE /\ x <> e` by
    (simp[alistTheory.ALOOKUP_NONE, MEM_MAP] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `slots = SOME w0::(Mc ++ Mr)` by
    (simp_tac pure_ss [Abbr `slots`, Abbr `keys`, Abbr `Mc`, Abbr `Mr`] >>
     pure_asm_rewrite_tac [] >> irule crossed_region_lookup_split >> simp[]) >>
  `EVERY IS_SOME Mc /\ Uc = rt.vs_gas_readings` by metis_tac[] >>
  `ct.vs_gas_readings = a.vs_gas_readings` by
    (fs[setup_callee_def] >> gvs[]) >>
  `qt.vs_gas_readings = rt.vs_gas_readings` by
    (drule gas_bind_outputs_readings >>
     simp[adopt_return_fmp_def, merge_callee_state_def] >>
     Cases_on `ret.iret_adopt_fmp` >> simp[]) >>
  `Uc = w0::r0 /\ aR.vs_gas_readings = r0` by
    gvs[Abbr `aI`, Abbr `aR`, update_var_def] >>
  `ALL_DISTINCT keys` by
    (simp[Abbr `keys`, ALL_DISTINCT_APPEND] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (block_region p d (MAP (\i. i.inst_id) (gas::call::rest))) keys` by
    (simp[Abbr `keys`, EVERY_MEM] >> conj_tac
     >- simp[Abbr `e`, block_region_def] >>
     fs[EVERY_MEM] >> rpt strip_tac >>
     metis_tac[block_region_mono, MEM]) >>
  `LENGTH keys = LENGTH sites` by simp[Abbr `keys`, Abbr `sites`] >>
  `PERM (MAP THE (FILTER IS_SOME slots) ++ Ur) a.vs_gas_readings` by
    (simp[FILTER_APPEND_DISTRIB, MAP_APPEND, APPEND_ASSOC] >>
     irule PERM_TRANS >>
     qexists_tac `MAP THE (FILTER IS_SOME Mc) ++ w0::r0` >>
     reverse conj_tac >- metis_tac[] >>
     pure_rewrite_tac[PERM_TO_APPEND_SIMPS, PERM_APPEND_IFF] >>
     metis_tac[]) >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `g` >- fs[] >>
  fs[LIST_REL_CONS1] >>
  rename1 `LIST_REL _ (Mc ++ Mr) hs` >>
  qabbrev_tac `hc = TAKE (LENGTH Mc) hs` >>
  qabbrev_tac `hr = DROP (LENGTH Mc) hs` >>
  `hs = hc ++ hr` by simp[Abbr `hc`, Abbr `hr`] >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mc hc /\
   LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mr hr` by
    (simp[Abbr `hc`, Abbr `hr`] >> conj_tac
     >- (drule rich_listTheory.EVERY2_TAKE >>
         disch_then (qspec_then `LENGTH Mc` mp_tac) >> simp[rich_listTheory.TAKE_APPEND]) >>
     drule rich_listTheory.EVERY2_DROP >>
     disch_then (qspec_then `LENGTH Mc` mp_tac) >> simp[DROP_APPEND]) >>
  `LENGTH hc = LENGTH Kc /\ LENGTH hr = LENGTH Kr` by
    (imp_res_tac LIST_REL_LENGTH >> fs[Abbr `Mc`, Abbr `Mr`]) >>
  qpat_x_assum `!hc tail. LIST_REL _ Mc hc ==> _`
    (qspecl_then [`hc`, `hr ++ tail`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!hr tail. LIST_REL _ Mr hr ==> _`
    (qspecl_then [`hr`, `tail`] mp_tac) >> simp[] >> strip_tac >>
  `(!y. MEM (Var y) ops ==> out <> y) /\ ~MEM out call.inst_outputs` by
    (drule_all dft_independent_gas_output >>
     `call.inst_operands = Label nm::ops` by
       (fs[decode_invoke_def, AllCaseEqs()] >> gvs[]) >> simp[]) >>
  qabbrev_tac `aG = (update_var out w0 (a with vs_gas_readings := hc ++ (hr ++ tail))) with vs_inst_idx := SUC j` >>
  `eval_operands ops aG = SOME args` by
    (`eval_operands ops (update_var out w0 (a with vs_gas_readings := hc ++ (hr ++ tail))) = SOME args` by
       metis_tac[dftCommutationTheory.eval_operands_update_var, gas_eval_operands] >>
     `eval_operands ops aG = eval_operands ops (update_var out w0 (a with vs_gas_readings := hc ++ (hr ++ tail)))` by
       (irule eval_operands_agree >> rpt strip_tac >> Cases_on `op` >>
        simp[Abbr `aG`, eval_operand_def, lookup_var_def]) >> metis_tac[]) >>
  `setup_callee callee args aG = SOME (cs with vs_gas_readings := hc ++ (hr ++ tail))` by
    (fs[Abbr `aG`, setup_callee_def, update_var_def] >> gvs[]) >>
  `!n v u. run_blocks n C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)) = IntRet v u ==>
    run_blocks n C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)) =
      IntRet ret (rt with vs_gas_readings := hr ++ tail) /\
    trace_gas (dftGasFromListTraceDefs$trace_blocks q d n C callee
      (cs with vs_gas_readings := hc ++ (hr ++ tail))) = ZIP(Kc,hc) /\
    gas_events_blocks n C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)) = Sc` by
    (rpt strip_tac >>
     `(?t. Tc = IntRet v t) /\
      run_blocks b C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)) = IntRet v u /\
      trace_gas (dftGasFromListTraceDefs$trace_blocks q d n C callee
        (cs with vs_gas_readings := hc ++ (hr ++ tail))) = ZIP(Kc,hc) /\
      gas_events_blocks n C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)) = Sc /\
      u.vs_gas_readings = hr ++ tail` by
       (irule returning_child_packet_exhaustion >> simp[] >>
        `?n. terminates (run_blocks n C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)))` by
          (qexists_tac `n` >> simp[passSimulationDefsTheory.terminates_def]) >>
        conj_tac >- metis_tac[APPEND_ASSOC] >>
        conj_tac
        >- (gen_tac >> qpat_x_assum `!n. ?k. _ /\ trace_gas (dftGasFromListTraceDefs$trace_blocks _ _ _ _ _ _) = _ /\ _`
              (qspec_then `f` strip_assume_tac) >>
            qexists_tac `DROP k Sc` >> simp[]) >>
        metis_tac[]) >>
     `?n. terminates (run_blocks n C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)))` by
       (qexists_tac `n` >> simp[passSimulationDefsTheory.terminates_def]) >>
     `residual_result (hr ++ tail) Tc
       (run_blocks b C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)))` by
       metis_tac[APPEND_ASSOC] >>
     gvs[residual_result_def, stateEquivTheory.lift_result_def]) >>
  `!n. (?v u. run_blocks n C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)) = IntRet v u) ==>
    exec_block n C bc (a with vs_gas_readings := w0::(hc ++ (hr ++ tail))) =
      exec_block n C br (aR with vs_gas_readings := hr ++ tail) /\
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bc
      (a with vs_gas_readings := w0::(hc ++ (hr ++ tail)))) =
      (e,w0)::(ZIP(Kc,hc) ++ trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn br
        (aR with vs_gas_readings := hr ++ tail))) /\
    gas_events_block n C fn.fn_name bc (a with vs_gas_readings := w0::(hc ++ (hr ++ tail))) =
      (fn.fn_name,gas.inst_id)::(Sc ++ gas_events_block n C fn.fn_name br
        (aR with vs_gas_readings := hr ++ tail))` by
    (gen_tac >> disch_then strip_assume_tac >>
     `run_blocks n C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)) =
        IntRet ret (rt with vs_gas_readings := hr ++ tail) /\
      trace_gas (dftGasFromListTraceDefs$trace_blocks q d n C callee
        (cs with vs_gas_readings := hc ++ (hr ++ tail))) = ZIP(Kc,hc) /\
      gas_events_blocks n C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)) = Sc` by metis_tac[] >>
     qpat_assum `trace_gas (dftGasFromListTraceDefs$trace_blocks q d n _ _ _) = ZIP(Kc,hc)`
       (fn th => rewrite_tac[GSYM th]) >>
     qpat_assum `gas_events_blocks n _ _ _ = Sc` (fn th => rewrite_tac[GSYM th]) >>
     simp_tac (srw_ss()) [Abbr `bc`, Abbr `br`, Abbr `aR`, Abbr `aI`, Abbr `e`, Abbr `q`] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC] >>
     irule (REWRITE_RULE [GSYM APPEND_ASSOC]
       (SRULE [LET_THM] crossed_returning_source_expansion)) >>
     simp[] >> conj_tac
     >- (qexists_tac `rt` >> simp[]) >>
     qexists_tac `args` >>
     qpat_x_assum `eval_operands ops aG = SOME args` mp_tac >>
     qpat_x_assum `setup_callee callee args aG = _` mp_tac >>
     simp[Abbr `aG`, update_var_def, APPEND_ASSOC]) >>
  `!n. ~(?v u. run_blocks n C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)) = IntRet v u) ==>
    exec_block n C bc (a with vs_gas_readings := w0::(hc ++ (hr ++ tail))) =
      run_blocks n C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)) /\
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bc
      (a with vs_gas_readings := w0::(hc ++ (hr ++ tail)))) =
      (e,w0)::trace_gas (dftGasFromListTraceDefs$trace_blocks q d n C callee
        (cs with vs_gas_readings := hc ++ (hr ++ tail))) /\
    gas_events_block n C fn.fn_name bc (a with vs_gas_readings := w0::(hc ++ (hr ++ tail))) =
      (fn.fn_name,gas.inst_id)::gas_events_blocks n C callee
        (cs with vs_gas_readings := hc ++ (hr ++ tail))` by
    (gen_tac >> strip_tac >>
     simp_tac (srw_ss()) [Abbr `bc`, Abbr `e`, Abbr `q`] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC] >>
     irule (REWRITE_RULE [GSYM APPEND_ASSOC]
       (SRULE [LET_THM] crossed_nonreturning_source_expansion)) >>
     simp[] >> conj_tac >- metis_tac[APPEND_ASSOC] >>
     qexists_tac `args` >>
     qpat_x_assum `eval_operands ops aG = SOME args` mp_tac >>
     qpat_x_assum `setup_callee callee args aG = _` mp_tac >>
     simp[Abbr `aG`, update_var_def, APPEND_ASSOC]) >>
  conj_tac
  >- (gen_tac >>
      Cases_on `?v u. run_blocks n C callee (cs with vs_gas_readings := hc ++ (hr ++ tail)) = IntRet v u`
      >- (qpat_assum `!n. (?v u. run_blocks n _ _ _ = IntRet v u) ==> _`
            (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
          qpat_x_assum `!n. ?k. _ /\ trace_gas (dftGasFromListTraceDefs$trace_block _ _ _ _ _ _ _) = _ /\ _`
            (qspec_then `n` strip_assume_tac) >>
          qexists_tac `SUC (LENGTH Kc + k)` >>
          simp[Abbr `keys`, Abbr `sites`, APPEND_ASSOC,
            rich_listTheory.TAKE_APPEND, rich_listTheory.ZIP_APPEND,
            TAKE_LENGTH_TOO_LONG]) >>
      qpat_assum `!n. ~(?v u. run_blocks n _ _ _ = IntRet v u) ==> _`
        (qspec_then `n` mp_tac) >>
      (impl_tac >- metis_tac[]) >> strip_tac >>
      qpat_x_assum `!n. ?k. _ /\ trace_gas (dftGasFromListTraceDefs$trace_blocks _ _ _ _ _ _) = _ /\ _`
        (qspec_then `n` strip_assume_tac) >>
      qexists_tac `SUC k` >>
      fs[Abbr `keys`, Abbr `sites`, APPEND_ASSOC, listTheory.TAKE_APPEND1] >>
      metis_tac[]) >>
  strip_tac >> fs[APPEND_ASSOC] >>
  `terminates (run_blocks n C callee (cs with vs_gas_readings := hc ++ hr ++ tail))` by
    (Cases_on `?v u. run_blocks n C callee (cs with vs_gas_readings := hc ++ hr ++ tail) = IntRet v u`
     >- (pop_assum strip_assume_tac >> simp[passSimulationDefsTheory.terminates_def]) >>
     qpat_assum `!n. (!v u. run_blocks n _ _ _ <> IntRet v u) ==> _`
       (qspec_then `n` mp_tac) >>
     (impl_tac >- metis_tac[]) >> strip_tac >> gvs[]) >>
  qpat_x_assum `(?n. terminates (run_blocks n _ _ _)) ==> _` mp_tac >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `run_blocks b C callee (cs with vs_gas_readings := hc ++ hr ++ tail) =
    IntRet ret (rt with vs_gas_readings := hr ++ tail)` by
    (qpat_x_assum `residual_result _ (IntRet ret rt) _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `run_blocks b C callee (cs with vs_gas_readings := hc ++ hr ++ tail)` >>
     simp[residual_result_def, stateEquivTheory.lift_result_def]) >>
  `run_blocks n C callee (cs with vs_gas_readings := hc ++ hr ++ tail) =
    IntRet ret (rt with vs_gas_readings := hr ++ tail)` by
    metis_tac[crossBlockSimPropsTheory.run_blocks_deterministic] >>
  qpat_assum `!n. (?v u. run_blocks n _ _ _ = IntRet v u) ==> _`
    (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `(?n. terminates (exec_block n _ br _)) ==> _` mp_tac >>
  (impl_tac >- (qexists_tac `n` >> metis_tac[])) >> strip_tac >>
  qpat_assum `!n. (?v u. run_blocks n _ _ _ = IntRet v u) ==> _`
    (qspec_then `b` mp_tac) >> simp[] >> strip_tac >>
  simp[Abbr `sites`] >> metis_tac[]
QED

Theorem crossed_stopped_packet_constructor:
  let q = (d,call.inst_id)::p;
      e = (p,d,gas.inst_id);
      bs = bb with bb_instructions := REPLICATE j pad ++ gas::call::rest;
      bt = bb with bb_instructions := REPLICATE j pad ++ call::gas::rest;
      Tc = run_blocks b C' callee' ct;
      Oc = trace_gas (dftGasFromListTraceDefs$trace_blocks q d b C' callee' ct);
      Mc = MAP (ALOOKUP Oc) Kc;
      T = exec_block b C' bt a;
      Ob = trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt a);
      M = MAP (ALOOKUP Ob) (e::Kc)
  in
  j = a.vs_inst_idx /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [out] /\
  call.inst_opcode = INVOKE /\ inst_wf gas /\ inst_wf call /\
  dft_gas_swap_pair gas call /\ ~MEM out call.inst_outputs /\
  ~MEM (Var out) ops /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (gas::call::rest)) /\
  fn.fn_name = fn'.fn_name /\
  decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  lookup_function nm C'.ctx_functions = SOME callee' /\
  callee' = dft_fn callee /\ dft_fn_rel callee callee' /\
  eval_operands ops a = SOME args /\
  setup_callee callee args a = SOME cs /\
  setup_callee callee' args a = SOME ct /\
  ((?rt. Tc = Halt rt) \/ (?at rt. Tc = Abort at rt)) /\
  terminates T /\ gas_count_block b C' bt a <= LENGTH a.vs_gas_readings /\
  ALL_DISTINCT Kc /\ EVERY (later_region q d) Kc /\
  LENGTH Kc = LENGTH Sc /\
  PERM (MAP THE (FILTER IS_SOME Mc) ++ Uc) ct.vs_gas_readings /\
  (!v u. Tc = IntRet v u ==> EVERY IS_SOME Mc /\ Uc = u.vs_gas_readings) /\
  (!g tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mc g ==>
    (!n. ?k. k <= LENGTH Kc /\
      trace_gas (dftGasFromListTraceDefs$trace_blocks q d n C callee
        (cs with vs_gas_readings := g ++ tail)) = ZIP (TAKE k Kc,TAKE k g) /\
      gas_events_blocks n C callee (cs with vs_gas_readings := g ++ tail) = TAKE k Sc) /\
    ((?n. terminates (run_blocks n C callee (cs with vs_gas_readings := g ++ tail))) ==>
      terminates (run_blocks b C callee (cs with vs_gas_readings := g ++ tail)) /\
      dft_res_rel
        (restore_result [] (run_blocks b C callee (cs with vs_gas_readings := g ++ tail)))
        (restore_result [] Tc) /\
      (!v u. Tc = IntRet v u ==>
        gas_events_blocks b C callee (cs with vs_gas_readings := g ++ tail) = Sc /\
        residual_result tail Tc (run_blocks b C callee (cs with vs_gas_readings := g ++ tail)))))
  ==>
  ALL_DISTINCT (e::Kc) /\
  EVERY (block_region p d (MAP (\i. i.inst_id) (gas::call::rest))) (e::Kc) /\
  LENGTH (e::Kc) = LENGTH ((fn.fn_name,gas.inst_id)::Sc) /\
  PERM (MAP THE (FILTER IS_SOME M) ++ Uc) a.vs_gas_readings /\
  (!u. T = OK u ==> EVERY IS_SOME M /\ Uc = u.vs_gas_readings) /\
  (!v u. T = IntRet v u ==> EVERY IS_SOME M /\ Uc = u.vs_gas_readings) /\
  (!g tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M g ==>
    (!n. ?k. k <= LENGTH (e::Kc) /\
      trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bs
        (a with vs_gas_readings := g ++ tail)) = ZIP (TAKE k (e::Kc),TAKE k g) /\
      gas_events_block n C fn.fn_name bs (a with vs_gas_readings := g ++ tail) =
        TAKE k ((fn.fn_name,gas.inst_id)::Sc)) /\
    ((?n. terminates (exec_block n C bs (a with vs_gas_readings := g ++ tail))) ==>
      terminates (exec_block b C bs (a with vs_gas_readings := g ++ tail)) /\
      dft_res_rel
        (restore_result [] (exec_block b C bs (a with vs_gas_readings := g ++ tail)))
        (restore_result [] T) /\
      (!u. T = OK u ==>
        gas_events_block b C fn.fn_name bs (a with vs_gas_readings := g ++ tail) =
          (fn.fn_name,gas.inst_id)::Sc /\
        residual_result tail T (exec_block b C bs (a with vs_gas_readings := g ++ tail))) /\
      (!v u. T = IntRet v u ==>
        gas_events_block b C fn.fn_name bs (a with vs_gas_readings := g ++ tail) =
          (fn.fn_name,gas.inst_id)::Sc /\
        residual_result tail T (exec_block b C bs (a with vs_gas_readings := g ++ tail)))))
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `callee' = dft_fn callee` kall_tac >>
  qmatch_asmsub_abbrev_tac `MAP (ALOOKUP obs) Kc` >>
  qmatch_goalsub_abbrev_tac `trace_block p d b C' fn' bt a` >>
  qabbrev_tac `bs = bb with bb_instructions := REPLICATE j pad ++ gas::call::rest` >>
  `get_instruction bt a.vs_inst_idx = SOME call` by
    simp[Abbr `bt`, get_instruction_def, EL_APPEND_EQN] >>
  `exec_block b C' bt a = run_blocks b C' callee' ct` by
    simp[Once exec_block_def, Once step_inst_def] >>
  `trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt a) = obs` by
    (drule dftGasFromListTraceDefsTheory.trace_block_visit >>
     disch_then (fn th => rewrite_tac [th]) >>
     simp[cj 1 dftGasFromListTraceDefsTheory.trace_defs, Once step_inst_def,
          trace_gas_def, visit_gas_def, Abbr `obs`]) >>
  `~later_region ((d,call.inst_id)::p) d (p,d,gas.inst_id)` by
    simp[later_region_def, frame_below_def] >>
  `~MEM (p,d,gas.inst_id) Kc` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `ALOOKUP obs (p,d,gas.inst_id) = NONE` by
    (`EVERY (\kw. later_region ((d,call.inst_id)::p) d (FST kw)) obs` by
       simp[Abbr `obs`, native_blocks_gas_region] >>
     fs[alistTheory.ALOOKUP_NONE, EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `ct.vs_gas_readings = a.vs_gas_readings` by
    (fs[setup_callee_def] >> gvs[]) >>
  `PERM (MAP THE (FILTER IS_SOME (MAP (ALOOKUP obs) Kc)) ++ Uc) a.vs_gas_readings` by metis_tac[] >>
  `EVERY (block_region p d (MAP (\i. i.inst_id) (gas::call::rest))) Kc` by
    (fs[EVERY_MEM, later_region_def, frame_below_def, block_region_def] >>
     rpt strip_tac >> first_x_assum drule >> strip_tac >>
     PairCases_on `e` >> irule below_call_region >>
     qexists_tac `call.inst_id` >> simp[] >>
     irule later_region_frame >> metis_tac[]) >>
  simp[block_region_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `g` >- fs[] >>
  fs[listTheory.LIST_REL_CONS1] >>
  rename1 `LIST_REL _ _ hs` >>
  qpat_x_assum `!g tail. LIST_REL _ _ g ==> _`
    (qspecl_then [`hs`, `tail`] mp_tac) >> simp[] >> strip_tac >>
  rename1 `a with vs_gas_readings := w::(hs ++ tail)` >>
  `!n v u. run_blocks n C callee (cs with vs_gas_readings := hs ++ tail) <> IntRet v u` by
    (rpt strip_tac >>
     `terminates (run_blocks b C callee (cs with vs_gas_readings := hs ++ tail)) /\
      dft_res_rel (restore_result [] (run_blocks b C callee (cs with vs_gas_readings := hs ++ tail)))
        (restore_result [] (run_blocks b C' callee' ct))` by
       (asm_rewrite_tac [] >> first_x_assum irule >> qexists_tac `n` >>
        simp[passSimulationDefsTheory.terminates_def]) >>
     `!err. run_blocks b C callee (cs with vs_gas_readings := hs ++ tail) <> Error err` by
       (Cases_on `run_blocks b C callee (cs with vs_gas_readings := hs ++ tail)` >>
        gvs[passSimulationDefsTheory.terminates_def]) >>
     `run_blocks (MAX b n) C callee (cs with vs_gas_readings := hs ++ tail) =
        run_blocks b C callee (cs with vs_gas_readings := hs ++ tail)` by
       (irule (cj 3 venomExecProofsTheory.fuel_mono) >> simp[] >> qexists_tac `b` >> simp[]) >>
     `run_blocks (MAX b n) C callee (cs with vs_gas_readings := hs ++ tail) = IntRet v u` by
       (irule (cj 3 venomExecProofsTheory.fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
     Cases_on `run_blocks b C callee (cs with vs_gas_readings := hs ++ tail)` >>
     gvs[restore_result_def, dft_res_rel_def]) >>
  qabbrev_tac `aG = (update_var out w (a with vs_gas_readings := hs ++ tail)) with vs_inst_idx := SUC j` >>
  `eval_operands ops aG = SOME args` by
    (`eval_operands ops (update_var out w (a with vs_gas_readings := hs ++ tail)) = SOME args` by
       (`!y. MEM (Var y) ops ==> out <> y` by metis_tac[] >>
        simp[dftCommutationTheory.eval_operands_update_var, gas_eval_operands]) >>
     `eval_operands ops aG = eval_operands ops (update_var out w (a with vs_gas_readings := hs ++ tail))` by
       (irule eval_operands_agree >> rpt strip_tac >> Cases_on `op` >>
        simp[Abbr `aG`, eval_operand_def, lookup_var_def]) >> metis_tac[]) >>
  `setup_callee callee args aG = SOME (cs with vs_gas_readings := hs ++ tail)` by
    (fs[Abbr `aG`, setup_callee_def, update_var_def] >> gvs[]) >>
  `get_instruction bs a.vs_inst_idx = SOME gas /\ get_instruction bs aG.vs_inst_idx = SOME call` by
    simp[Abbr `bs`, Abbr `aG`, get_instruction_def, EL_APPEND_EQN, update_var_def] >>
  `!n. step_inst n C gas (a with vs_gas_readings := w::(hs ++ tail)) =
     OK (update_var out w (a with vs_gas_readings := hs ++ tail))` by
    simp[Once step_inst_def, step_inst_base_def, exec_gas_def] >>
  `!n s u. run_blocks n C callee s <> OK u` by
    (Induct >- simp[Once run_blocks_def] >>
     simp[run_blocks_unfold] >> rpt gen_tac >> rpt (CASE_TAC >> fs[])) >>
  `!n. step_inst n C call aG = run_blocks n C callee (cs with vs_gas_readings := hs ++ tail)` by
    (gen_tac >> simp[Once step_inst_def] >>
     Cases_on `run_blocks n C callee (cs with vs_gas_readings := hs ++ tail)` >> fs[] >> metis_tac[]) >>
  `!n. exec_block n C bs (a with vs_gas_readings := w::(hs ++ tail)) =
       run_blocks n C callee (cs with vs_gas_readings := hs ++ tail)` by
    (gen_tac >> simp[Once exec_block_def, is_terminator_def] >>
     `((update_var out w (a with vs_gas_readings := hs ++ tail)) with vs_inst_idx := SUC a.vs_inst_idx) = aG` by simp[Abbr `aG`] >>
     `get_instruction bs (SUC a.vs_inst_idx) = SOME call` by
       simp[Abbr `bs`, get_instruction_def, EL_APPEND_EQN] >>
     asm_rewrite_tac [] >> simp[Once exec_block_def] >>
     Cases_on `run_blocks n C callee (cs with vs_gas_readings := hs ++ tail)` >> gvs[] >> metis_tac[]) >>
  `!n. trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bs
          (a with vs_gas_readings := w::(hs ++ tail))) =
       ((p,d,gas.inst_id),w)::trace_gas
         (dftGasFromListTraceDefs$trace_blocks ((d,call.inst_id)::p) d n C callee
           (cs with vs_gas_readings := hs ++ tail))` by
    (gen_tac >>
     simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs),
          cj 1 dftGasFromListTraceDefsTheory.trace_defs, is_terminator_def] >>
     `((update_var out w (a with vs_gas_readings := hs ++ tail)) with vs_inst_idx := SUC a.vs_inst_idx) = aG` by simp[Abbr `aG`] >>
     asm_rewrite_tac [] >>
     simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs),
          cj 1 dftGasFromListTraceDefsTheory.trace_defs] >>
     Cases_on `run_blocks n C callee (cs with vs_gas_readings := hs ++ tail)` >>
     gvs[trace_gas_def, visit_gas_def] >> metis_tac[]) >>
  `!n. gas_events_block n C fn'.fn_name bs
          (a with vs_gas_readings := w::(hs ++ tail)) =
       (fn'.fn_name,gas.inst_id)::gas_events_blocks n C callee
           (cs with vs_gas_readings := hs ++ tail)` by
    (gen_tac >> simp[Once gas_events_block_def, gas_events_step_def, is_terminator_def] >>
     `((update_var out w (a with vs_gas_readings := hs ++ tail)) with vs_inst_idx := SUC a.vs_inst_idx) = aG` by simp[Abbr `aG`] >>
     asm_rewrite_tac [] >> simp[Once gas_events_block_def, gas_events_step_def] >>
     Cases_on `run_blocks n C callee (cs with vs_gas_readings := hs ++ tail)` >> gvs[] >> metis_tac[]) >>
  (conj_tac >-
    (gen_tac >> qpat_x_assum `!n. ?k. _` (qspec_then `n` strip_assume_tac) >>
     qexists_tac `SUC k` >> simp[]) >>
   asm_rewrite_tac [])
QED

Theorem native_invoke_crossed_prefix:
  !pre s.
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\x. ~is_alloca_op x.inst_opcode) bb.bb_instructions /\
  dft_remaining_inv fn bb (pre ++ call::post) s /\
  ~s.vs_call_ctx.cc_static /\ call.inst_opcode = INVOKE /\
  EVERY (\x. inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
    ~dft_must_order x call) pre /\
  LENGTH (FILTER (\x. x.inst_opcode = GAS) pre) <= LENGTH s.vs_gas_readings ==>
  !n C. ?t.
    FOLDR (dft_exec_cons n C) OK pre s = OK t /\
    dft_remaining_inv fn bb (call::post) t /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH pre /\
    t.vs_gas_readings = DROP (LENGTH (FILTER (\x. x.inst_opcode = GAS) pre)) s.vs_gas_readings /\
    (!op. MEM op call.inst_operands ==> eval_operand op t = eval_operand op s) /\
    (!callee args cs. setup_callee callee args s = SOME cs ==>
      setup_callee callee args t = SOME (cs with vs_gas_readings :=
        DROP (LENGTH (FILTER (\x. x.inst_opcode = GAS) pre)) s.vs_gas_readings))
Proof
  Induct
  >- (simp[] >> rpt strip_tac >> fs[setup_callee_def] >>
      gvs[venom_state_component_equality]) >>
  simp[] >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  `MEM h bb.bb_instructions /\ ~is_pseudo h.inst_opcode` by
    fs[dft_remaining_inv_def] >>
  `inst_wf h /\ ~is_alloca_op h.inst_opcode` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `h.inst_opcode <> INVOKE /\ h.inst_opcode <> CODECOPY /\
   (h.inst_opcode = GAS \/ is_effect_free_op h.inst_opcode)` by
    (qpat_x_assum `~dft_must_order h call` mp_tac >>
     qpat_x_assum `~is_alloca_op h.inst_opcode` mp_tac >>
     qpat_x_assum `~is_terminator h.inst_opcode` mp_tac >>
     qpat_x_assum `inst_wf h` mp_tac >>
     qpat_x_assum `inst_shape_ok h` mp_tac >>
     qpat_x_assum `call.inst_opcode = INVOKE` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `h.inst_opcode` >>
     gvs[is_effect_free_op_def] >>
     gvs[dft_must_order_def, read_effects_def, write_effects_def,
         all_effects_def, empty_effects_def,
         is_terminator_def, is_alloca_op_def, inst_shape_ok_def, inst_wf_def]) >>
  `!op. MEM op h.inst_operands ==> IS_SOME (eval_operand op s)` by
    metis_tac[inv_remaining_head_operands] >>
  `?u. step_inst n C h s = OK u` by
    (Cases_on `h.inst_opcode = GAS`
     >- (fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
         metis_tac[step_inst_gas_single]) >> gvs[] >>
     `h.inst_opcode <> PHI /\ h.inst_opcode <> PARAM /\ h.inst_opcode <> FMP_PARAM` by
       (Cases_on `h.inst_opcode` >> gvs[is_pseudo_def]) >>
     simp[step_inst_non_invoke] >>
     irule effect_free_step_inst_base_ok >> simp[] >>
     rpt strip_tac >> first_x_assum drule >>
     Cases_on `eval_operand op s` >> gvs[]) >>
  `dft_remaining_inv fn bb (pre ++ call::post)
     (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (SRULE [] (Q.INST [`pre` |-> `[]`] dft_remaining_inv_step)) >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `u.vs_gas_readings = DROP (if h.inst_opcode = GAS then 1 else 0) s.vs_gas_readings /\
   u.vs_call_ctx = s.vs_call_ctx` by
    (Cases_on `h.inst_opcode = GAS`
     >- (drule_all step_inst_ok_gas >> strip_tac >> gvs[update_var_def]) >>
     `is_effect_free_op h.inst_opcode` by gvs[] >>
     drule_all step_effect_free_state_equiv >>
     gvs[stateEquivTheory.state_equiv_def, stateEquivTheory.execution_equiv_def,
          execution_frame_def, venom_state_component_equality]) >>
  `!op. MEM op call.inst_operands ==>
      eval_operand op (u with vs_inst_idx := SUC s.vs_inst_idx) = eval_operand op s` by
    (rpt strip_tac >>
     `eval_operand op (u with vs_inst_idx := SUC s.vs_inst_idx) = eval_operand op u` by
       (Cases_on `op` >> simp[eval_operand_def, lookup_var_def]) >>
     asm_rewrite_tac [] >> irule eval_operand_step_pres >>
     goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
     fs[dft_must_order_def, inst_defs_def, inst_uses_def,
        MEM_operand_vars_eq_Var, pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
     metis_tac[]) >>
  `!callee args cs. setup_callee callee args s = SOME cs ==>
     setup_callee callee args (u with vs_inst_idx := SUC s.vs_inst_idx) =
       SOME (cs with vs_gas_readings := u.vs_gas_readings)` by
    (Cases_on `h.inst_opcode = GAS`
     >- (drule_all step_inst_ok_gas >> strip_tac >>
         rpt strip_tac >> gvs[setup_callee_def, update_var_def]) >>
     `is_effect_free_op h.inst_opcode` by gvs[] >>
     drule_all step_effect_free_state_equiv >>
     simp[stateEquivTheory.state_equiv_def, stateEquivTheory.execution_equiv_def,
          execution_frame_def, venom_state_component_equality] >>
     rpt strip_tac >> fs[setup_callee_def] >>
     gvs[venom_state_component_equality]) >>
  qpat_x_assum `!s. _ ==> !n C. _`
    (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- (simp[] >> Cases_on `h.inst_opcode = GAS` >>
    gvs[DROP_LENGTH_TOO_LONG, LENGTH_DROP])) >>
  disch_then (qspecl_then [`n`, `C`] strip_assume_tac) >>
  qexists_tac `t` >>
  simp[dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `h.inst_opcode = GAS` >>
  gvs[rich_listTheory.DROP_DROP_T, arithmeticTheory.ADD1] >>
  rpt strip_tac >>
  qpat_x_assum `!callee args cs. setup_callee callee args s = SOME cs ==> _` drule >>
  strip_tac >> first_x_assum drule >> simp[]
QED

Theorem native_pseudo_fold_readings[local]:
  !xs s t.
    EVERY (\i. is_pseudo i.inst_opcode) xs /\
    FOLDR (dft_exec_cons b C) OK xs s = OK t ==>
    t.vs_gas_readings = s.vs_gas_readings /\
    !n D W. FOLDR (dft_exec_cons n D) OK xs
      (s with vs_gas_readings := W) = OK (t with vs_gas_readings := W)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `h.inst_opcode <> INVOKE /\ h.inst_opcode <> GAS /\
   ~is_terminator h.inst_opcode` by
    (Cases_on `h.inst_opcode` >> gvs[is_pseudo_def, is_terminator_def]) >>
  gvs[dftIndexedExecTheory.dft_exec_cons_def, AllCaseEqs()] >>
  drule_all dftBlockSimTheory.step_inst_ok_non_gas_oracle >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  simp[dftIndexedExecTheory.dft_exec_cons_def, step_inst_non_invoke] >>
  metis_tac[step_inst_non_invoke, venom_state_component_equality]
QED

Theorem native_pseudo_phase_readings:
  EVERY (\i. is_pseudo i.inst_opcode) pre /\
  eval_phis s pre = OK u /\
  FOLDR (dft_exec_cons b C) OK (DROP (phi_prefix_length pre) pre)
    (u with vs_inst_idx := phi_prefix_length pre) = OK t ==>
  t.vs_gas_readings = s.vs_gas_readings /\
  !n D W.
    eval_phis (s with vs_gas_readings := W) pre =
      OK (u with vs_gas_readings := W) /\
    FOLDR (dft_exec_cons n D) OK (DROP (phi_prefix_length pre) pre)
      ((u with vs_gas_readings := W) with vs_inst_idx := phi_prefix_length pre) =
      OK (t with vs_gas_readings := W)
Proof
  strip_tac >>
  `EVERY (\i. is_pseudo i.inst_opcode)
    (DROP (phi_prefix_length pre) pre)` by metis_tac[rich_listTheory.EVERY_DROP] >>
  drule_all native_pseudo_fold_readings >> strip_tac >>
  qspecl_then [`pre`, `s`] mp_tac gas_eval_phis >>
  simp[gas_replay_at_def] >>
  disch_then (qspec_then `s.vs_gas_readings` mp_tac) >>
  simp[stateEquivTheory.lift_result_def] >> strip_tac >>
  simp[] >> rpt gen_tac >> conj_tac
  >- metis_tac[eval_phis_restore, restore_rel_cases] >>
  (bossLib.gvs [])
QED

Theorem native_silent_swap_observations:
  let bx = bb with bb_instructions := REPLICATE j pad ++ x::y::rest;
      by = bb with bb_instructions := REPLICATE j pad ++ y::x::rest in
  a.vs_inst_idx = j /\ dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  x.inst_opcode <> GAS /\ y.inst_opcode <> GAS /\
  x.inst_opcode <> INVOKE /\ y.inst_opcode <> INVOKE ==>
  !n C fn p d.
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bx a) =
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn by a) /\
    gas_events_block n C fn.fn_name bx a =
    gas_events_block n C fn.fn_name by a
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >> rpt gen_tac >>
  qabbrev_tac `bx = bb with bb_instructions := REPLICATE j pad ++ x::y::rest` >>
  qabbrev_tac `by = bb with bb_instructions := REPLICATE j pad ++ y::x::rest` >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   dft_gas_swap_pair y x` by
    metis_tac[dft_gas_swap_pair_def, dft_gas_swap_pair_sym] >>
  `get_instruction bx j = SOME x /\ get_instruction bx (SUC j) = SOME y /\
   get_instruction by j = SOME y /\ get_instruction by (SUC j) = SOME x` by
    simp[Abbr `bx`, Abbr `by`, get_instruction_def, EL_APPEND_EQN] >>
  `!u v. step_inst n C x a = OK u /\
    step_inst n C y (u with vs_inst_idx := SUC j) = OK v ==>
    ?w z. step_inst n C y a = OK w /\
      step_inst n C x (w with vs_inst_idx := SUC j) = OK z /\
      (z with vs_inst_idx := SUC (SUC j)) =
      (v with vs_inst_idx := SUC (SUC j))` by
    (rpt strip_tac >>
     `ev_step (\e. 0w) p d n C x a = OK u /\
      ev_step (\e. 0w) p d n C y (u with vs_inst_idx := SUC a.vs_inst_idx) = OK v` by
       simp[ev_step_ordinary] >>
     drule_all ev_indexed_pair_success >> simp[ev_step_ordinary]) >>
  Cases_on `?u v. step_inst n C x a = OK u /\
    step_inst n C y (u with vs_inst_idx := SUC j) = OK v`
  >- suspend "success"
  >> suspend "stopped"
QED

Resume native_silent_swap_observations[success]:
  qpat_x_assum `?u v. _` strip_assume_tac >>
  qpat_x_assum `!u v. _` drule_all >> strip_tac >>
  once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                   gas_events_block_def] >>
  simp[dftGasFromListTraceDefsTheory.trace_step_noninvoke, visit_gas_def,
       gas_events_step_def] >>
  once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                   gas_events_block_def] >>
  simp[dftGasFromListTraceDefsTheory.trace_step_noninvoke, visit_gas_def,
       gas_events_step_def] >>
  conj_tac
  >- (AP_TERM_TAC >> irule native_trace_block_suffix_cong >>
      simp[Abbr `bx`, Abbr `by`, DROP_APPEND]) >>
  irule gas_events_block_suffix_cong >>
  simp[Abbr `bx`, Abbr `by`, DROP_APPEND]
QED

Resume native_silent_swap_observations[stopped]:
  `~?w z. step_inst n C y a = OK w /\
    step_inst n C x (w with vs_inst_idx := SUC j) = OK z` by
    (strip_tac >>
     `ev_step (\e. 0w) p d n C y a = OK w /\
      ev_step (\e. 0w) p d n C x (w with vs_inst_idx := SUC a.vs_inst_idx) = OK z` by
       simp[ev_step_ordinary] >>
     drule_all ev_indexed_pair_success >> simp[ev_step_ordinary] >>
     metis_tac[]) >>
  `!b i k. get_instruction b j = SOME i /\
    get_instruction b (SUC j) = SOME k /\
    i.inst_opcode <> GAS /\ k.inst_opcode <> GAS /\
    i.inst_opcode <> INVOKE /\ k.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\
    (~?u v. step_inst n C i a = OK u /\
       step_inst n C k (u with vs_inst_idx := SUC j) = OK v) ==>
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn b a) = [] /\
    gas_events_block n C fn.fn_name b a = []` by
    (rpt strip_tac >>
     once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                      gas_events_block_def] >>
     simp[dftGasFromListTraceDefsTheory.trace_step_noninvoke, visit_gas_def,
          gas_events_step_def] >>
     Cases_on `step_inst n C i a` >> gvs[] >>
     rename1 `step_inst n C i a = OK u` >>
     once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                      gas_events_block_def] >>
     simp[dftGasFromListTraceDefsTheory.trace_step_noninvoke, visit_gas_def,
          gas_events_step_def] >>
     Cases_on `step_inst n C k (u with vs_inst_idx := SUC a.vs_inst_idx)` >> gvs[]) >>
  gvs[]
QED

Finalise native_silent_swap_observations

Theorem native_gas_ordinary_success:
  let bgx = bb with bb_instructions := REPLICATE j pad ++ g::x::rest;
      bxg = bb with bb_instructions := REPLICATE j pad ++ x::g::rest in
  a.vs_inst_idx = j /\ g.inst_opcode = GAS /\ g.inst_outputs = [out] /\
  inst_wf g /\ inst_wf x /\ dft_gas_swap_pair g x /\
  x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
  step_inst 0 C x a = OK u ==>
  !n w ws.
    exec_block n C bgx (a with vs_gas_readings := w::ws) =
    exec_block n C bxg (a with vs_gas_readings := w::ws) /\
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bgx
      (a with vs_gas_readings := w::ws)) =
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bxg
      (a with vs_gas_readings := w::ws)) /\
    gas_events_block n C fn.fn_name bgx (a with vs_gas_readings := w::ws) =
    gas_events_block n C fn.fn_name bxg (a with vs_gas_readings := w::ws)
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >> rpt gen_tac >>
  qabbrev_tac `bgx = bb with bb_instructions := REPLICATE j pad ++ g::x::rest` >>
  qabbrev_tac `bxg = bb with bb_instructions := REPLICATE j pad ++ x::g::rest` >>
  `~is_terminator g.inst_opcode /\ ~is_terminator x.inst_opcode` by
    fs[dft_gas_swap_pair_def] >>
  `step_inst n C x a = OK u` by metis_tac[step_inst_non_invoke] >>
  `step_inst n C x (a with vs_gas_readings := w::ws) =
    OK (u with vs_gas_readings := w::ws)` by
    metis_tac[dft_nonconsuming_ok_oracle] >>
  drule_all dft_gas_noninvoke_ok_diamond >> strip_tac >>
  `step_inst n C x (sg with vs_inst_idx := SUC j) =
      OK (st with vs_inst_idx := SUC j) /\
   step_inst n C g ((u with vs_gas_readings := w::ws) with vs_inst_idx := SUC j) =
      OK (st with vs_inst_idx := SUC j)` by
    metis_tac[dftIndexedExecTheory.dft_step_ok_idx] >>
  `get_instruction bgx j = SOME g /\ get_instruction bgx (SUC j) = SOME x /\
   get_instruction bxg j = SOME x /\ get_instruction bxg (SUC j) = SOME g` by
    simp[Abbr `bgx`, Abbr `bxg`, get_instruction_def, EL_APPEND_EQN] >>
  `u.vs_gas_readings = a.vs_gas_readings` by metis_tac[dft_nonconsuming_ok_readings] >>
  once_rewrite_tac[exec_block_def, cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                   gas_events_block_def] >>
  simp[dftGasFromListTraceDefsTheory.trace_step_noninvoke, visit_gas_def,
       gas_events_step_def, trace_gas_def] >>
  once_rewrite_tac[exec_block_def, cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                   gas_events_block_def] >>
  simp[dftGasFromListTraceDefsTheory.trace_step_noninvoke, visit_gas_def,
       gas_events_step_def, trace_gas_def] >>
  rpt conj_tac
  >- (irule venomExecProofsTheory.exec_block_same_suffix >>
      simp[Abbr `bgx`, Abbr `bxg`, DROP_APPEND])
  >- (AP_TERM_TAC >> AP_TERM_TAC >> irule native_trace_block_suffix_cong >>
      simp[Abbr `bgx`, Abbr `bxg`, DROP_APPEND]) >>
  irule gas_events_block_suffix_cong >>
  simp[Abbr `bgx`, Abbr `bxg`, DROP_APPEND]
QED

Theorem native_gas_ordinary_stopped_packets:
  let bgx = bb with bb_instructions := REPLICATE j pad ++ g::x::rest;
      bxg = bb with bb_instructions := REPLICATE j pad ++ x::g::rest;
      e = (p,d,g.inst_id);
      site = (fn.fn_name,g.inst_id);
      O1 = trace_gas (dftGasFromListTraceDefs$trace_block p d b C fn bxg a);
      O2 = trace_gas (dftGasFromListTraceDefs$trace_block p d b C fn bgx a);
      M1 = MAP (ALOOKUP O1) [e];
      M2 = MAP (ALOOKUP O2) [] in
  a.vs_inst_idx = j /\ g.inst_opcode = GAS /\ g.inst_outputs = [out] /\
  inst_wf g /\ inst_wf x /\ dft_gas_swap_pair g x /\
  x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
  ~(?u. step_inst 0 C x a = OK u) ==>
  (terminates (exec_block b C bxg a) /\
   gas_count_block b C bxg a <= LENGTH a.vs_gas_readings ==>
   ALL_DISTINCT [e] /\
   EVERY (block_region p d (MAP (\i. i.inst_id) (g::x::rest))) [e] /\
   LENGTH [e] = LENGTH [site] /\
   PERM (MAP THE (FILTER IS_SOME M1) ++ a.vs_gas_readings) a.vs_gas_readings /\
   (!u. exec_block b C bxg a = OK u ==> EVERY IS_SOME M1 /\ a.vs_gas_readings = u.vs_gas_readings) /\
   (!v u. exec_block b C bxg a = IntRet v u ==> EVERY IS_SOME M1 /\ a.vs_gas_readings = u.vs_gas_readings) /\
   (!gobs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M1 gobs ==>
     (!n. ?k. k <= LENGTH [e] /\
       trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bgx
         (a with vs_gas_readings := gobs ++ tail)) = ZIP (TAKE k [e],TAKE k gobs) /\
       gas_events_block n C fn.fn_name bgx (a with vs_gas_readings := gobs ++ tail) = TAKE k [site]) /\
     ((?n. terminates (exec_block n C bgx (a with vs_gas_readings := gobs ++ tail))) ==>
       terminates (exec_block b C bgx (a with vs_gas_readings := gobs ++ tail)) /\
       dft_res_rel (restore_result [] (exec_block b C bgx (a with vs_gas_readings := gobs ++ tail)))
                   (restore_result [] (exec_block b C bxg a)) /\
       (!u. exec_block b C bxg a = OK u ==>
         gas_events_block b C fn.fn_name bgx (a with vs_gas_readings := gobs ++ tail) = [site] /\
         residual_result tail (exec_block b C bxg a) (exec_block b C bgx (a with vs_gas_readings := gobs ++ tail))) /\
       (!v u. exec_block b C bxg a = IntRet v u ==>
         gas_events_block b C fn.fn_name bgx (a with vs_gas_readings := gobs ++ tail) = [site] /\
         residual_result tail (exec_block b C bxg a) (exec_block b C bgx (a with vs_gas_readings := gobs ++ tail)))))) /\
  (terminates (exec_block b C bgx a) /\
   gas_count_block b C bgx a <= LENGTH a.vs_gas_readings ==>
   ALL_DISTINCT ([]:gas_event list) /\
   EVERY (block_region p d (MAP (\i. i.inst_id) (x::g::rest))) [] /\
   LENGTH ([]:gas_event list) = LENGTH ([]:(string # num) list) /\
   PERM (MAP THE (FILTER IS_SOME M2) ++ a.vs_gas_readings) a.vs_gas_readings /\
   (!u. exec_block b C bgx a = OK u ==> EVERY IS_SOME M2 /\ a.vs_gas_readings = u.vs_gas_readings) /\
   (!v u. exec_block b C bgx a = IntRet v u ==> EVERY IS_SOME M2 /\ a.vs_gas_readings = u.vs_gas_readings) /\
   (!gobs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M2 gobs ==>
     (!n. ?k. k <= LENGTH ([]:gas_event list) /\
       trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bxg
         (a with vs_gas_readings := gobs ++ tail)) = ZIP (TAKE k ([]:gas_event list),TAKE k gobs) /\
       gas_events_block n C fn.fn_name bxg (a with vs_gas_readings := gobs ++ tail) = TAKE k ([]:(string # num) list)) /\
     ((?n. terminates (exec_block n C bxg (a with vs_gas_readings := gobs ++ tail))) ==>
       terminates (exec_block b C bxg (a with vs_gas_readings := gobs ++ tail)) /\
       dft_res_rel (restore_result [] (exec_block b C bxg (a with vs_gas_readings := gobs ++ tail)))
                   (restore_result [] (exec_block b C bgx a)) /\
       (!u. exec_block b C bgx a = OK u ==>
         gas_events_block b C fn.fn_name bxg (a with vs_gas_readings := gobs ++ tail) = [] /\
         residual_result tail (exec_block b C bgx a) (exec_block b C bxg (a with vs_gas_readings := gobs ++ tail))) /\
       (!v u. exec_block b C bgx a = IntRet v u ==>
         gas_events_block b C fn.fn_name bxg (a with vs_gas_readings := gobs ++ tail) = [] /\
         residual_result tail (exec_block b C bgx a) (exec_block b C bxg (a with vs_gas_readings := gobs ++ tail))))))
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `bgx = bb with bb_instructions := REPLICATE j pad ++ g::x::rest` >>
  qabbrev_tac `bxg = bb with bb_instructions := REPLICATE j pad ++ x::g::rest` >>
  `~is_terminator g.inst_opcode /\ ~is_terminator x.inst_opcode` by
    fs[dft_gas_swap_pair_def] >>
  drule_all dft_independent_gas_output >> strip_tac >>
  `get_instruction bgx j = SOME g /\ get_instruction bgx (SUC j) = SOME x /\
   get_instruction bxg j = SOME x /\ get_instruction bxg (SUC j) = SOME g` by
    simp[Abbr `bgx`, Abbr `bxg`, get_instruction_def, EL_APPEND_EQN] >>
  `(!t. step_inst 0 C x a <> Halt t) /\
   (!v t. step_inst 0 C x a <> IntRet v t)` by
    metis_tac[dft_swap_nonterminator_no_intret, dft_swap_nonterminator_halt_invoke] >>
  `!n s. step_inst n C g s = OK (update_var out
      (case s.vs_gas_readings of [] => 0w | w::_ => w)
      (s with vs_gas_readings := DROP 1 s.vs_gas_readings))` by
    metis_tac[step_inst_gas_single] >>
  Cases_on `step_inst 0 C x a` >> gvs[]
  >- suspend "abort"
  >> suspend "error"
QED

Resume native_gas_ordinary_stopped_packets[abort]:
  rename1 `step_inst 0 C x a = Abort ab t` >>
  `!n. step_inst n C x a = Abort ab t` by
    metis_tac[step_inst_non_invoke] >>
  `!n readings. step_inst n C x (a with vs_gas_readings := readings) =
      Abort ab (t with vs_gas_readings := readings)` by
    (rpt gen_tac >> drule_all dft_nonconsuming_oracle_frame >>
     disch_then (qspecl_then [`a`, `readings`, `n`, `C`] mp_tac) >>
     simp[stateEquivTheory.lift_result_def] >>
     Cases_on `step_inst n C x (a with vs_gas_readings := readings)` >>
     simp[stateEquivTheory.lift_result_def]) >>
  `!n readings value idx. step_inst n C x
      ((update_var out value (a with vs_gas_readings := readings)) with vs_inst_idx := idx) =
      Abort ab ((update_var out value (t with vs_gas_readings := readings)) with vs_inst_idx := idx)` by
    (rpt gen_tac >>
     simp[runInstsPropsTheory.step_inst_idx_indep,
          dftCommutationTheory.step_inst_frame,
          dftCommutationTheory.map_result_state_def,
          instIdxIndepTheory.exec_result_map_def]) >>
  fs[] >>
  `!n readings. exec_block n C bgx (a with vs_gas_readings := readings) =
      Abort ab ((update_var out (case readings of [] => 0w | w::_ => w)
        (t with vs_gas_readings := DROP 1 readings)) with vs_inst_idx := SUC a.vs_inst_idx)` by
    (rpt gen_tac >> simp[Once exec_block_def] >>
     once_rewrite_tac[exec_block_def] >> simp[]) >>
  `!n readings. exec_block n C bxg (a with vs_gas_readings := readings) =
      Abort ab (t with vs_gas_readings := readings)` by simp[Once exec_block_def] >>
  `exec_block b C bxg a = Abort ab t` by simp[Once exec_block_def] >>
  `?z. exec_block b C bgx a = Abort ab z` by
    (qpat_assum `!n readings. exec_block n C bgx _ = _`
       (qspecl_then [`b`, `a.vs_gas_readings`] (mp_tac o SRULE [])) >>
     strip_tac >> goal_assum (drule_at Any)) >>
  `!n readings. trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bxg
      (a with vs_gas_readings := readings)) = [] /\
    gas_events_block n C fn.fn_name bxg (a with vs_gas_readings := readings) = []` by
    (rpt gen_tac >>
     simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs),
          dftGasFromListTraceDefsTheory.trace_step_noninvoke,
          Once gas_events_block_def, gas_events_step_def, trace_gas_def, visit_gas_def]) >>
  `!n readings. trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bgx
      (a with vs_gas_readings := readings)) =
      [((p,d,g.inst_id),case readings of [] => 0w | w::_ => w)] /\
    gas_events_block n C fn.fn_name bgx (a with vs_gas_readings := readings) =
      [(fn.fn_name,g.inst_id)]` by
    (rpt gen_tac >>
     once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs, gas_events_block_def] >>
     simp[dftGasFromListTraceDefsTheory.trace_step_noninvoke, gas_events_step_def,
          trace_gas_def, visit_gas_def] >>
     once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs, gas_events_block_def] >>
     simp[dftGasFromListTraceDefsTheory.trace_step_noninvoke, gas_events_step_def,
          trace_gas_def, visit_gas_def]) >>
  `trace_gas (dftGasFromListTraceDefs$trace_block p d b C fn bxg a) = []` by
    (qpat_assum `!n readings. trace_gas _ = [] /\ _`
       (qspecl_then [`b`, `a.vs_gas_readings`] (mp_tac o SRULE [])) >> metis_tac[]) >>
  simp[block_region_def, passSimulationDefsTheory.terminates_def,
       restore_result_def, dft_res_rel_def] >>
  rpt strip_tac >> gvs[] >> qexists_tac `1` >> simp[]
QED

Resume native_gas_ordinary_stopped_packets[error]:
  rename1 `step_inst 0 C x a = Error err` >>
  `!n. step_inst n C x a = Error err` by
    metis_tac[step_inst_non_invoke] >>
  `!n readings. ?err'. step_inst n C x (a with vs_gas_readings := readings) = Error err'` by
    (rpt gen_tac >> drule_all dft_nonconsuming_oracle_frame >>
     disch_then (qspecl_then [`a`, `readings`, `n`, `C`] mp_tac) >>
     simp[stateEquivTheory.lift_result_def] >>
     Cases_on `step_inst n C x (a with vs_gas_readings := readings)` >>
     simp[stateEquivTheory.lift_result_def]) >>
  `!n readings value idx. ?err'. step_inst n C x
      ((update_var out value (a with vs_gas_readings := readings)) with vs_inst_idx := idx) =
      Error err'` by
    (rpt gen_tac >>
     qpat_x_assum `!n readings. ?err'. _`
       (qspecl_then [`n`, `readings`] strip_assume_tac) >>
     simp[runInstsPropsTheory.step_inst_idx_indep,
          dftCommutationTheory.step_inst_frame,
          dftCommutationTheory.map_result_state_def,
          instIdxIndepTheory.exec_result_map_def]) >>
  fs[] >>
  `exec_block b C bxg a = Error err` by simp[Once exec_block_def] >>
  `!n readings. ?err'. exec_block n C bgx (a with vs_gas_readings := readings) = Error err'` by
    (rpt gen_tac >> simp[Once exec_block_def] >>
     once_rewrite_tac[exec_block_def] >> simp[] >>
     qpat_x_assum `!n readings value idx. ?err'. _`
       (qspecl_then [`n`, `DROP 1 readings`,
                     `case readings of [] => 0w | w::_ => w`, `SUC a.vs_inst_idx`]
         strip_assume_tac) >> simp[]) >>
  `?err'. exec_block b C bgx a = Error err'` by
    (qpat_assum `!n readings. ?err'. exec_block _ _ _ _ = _`
       (qspecl_then [`b`, `a.vs_gas_readings`] (mp_tac o SRULE [])) >> simp[]) >>
  simp[passSimulationDefsTheory.terminates_def]
QED

Finalise native_gas_ordinary_stopped_packets

Theorem native_invoke_row_updates[local]:
  !pairs s. call.inst_opcode = INVOKE /\
    EVERY (\q. ~MEM (Var (FST q)) call.inst_operands) pairs ==>
    !k.
      dftGasFromListTraceDefs$trace_step p d n C fn call
        ((FOLDL (\st (out,w). update_var out w st) s pairs) with vs_inst_idx := k) =
      dftGasFromListTraceDefs$trace_step p d n C fn call s /\
      gas_events_step n C owner call
        ((FOLDL (\st (out,w). update_var out w st) s pairs) with vs_inst_idx := k) =
      gas_events_step n C owner call s
Proof
  `!s k. call.inst_opcode = INVOKE ==>
    dftGasFromListTraceDefs$trace_step p d n C fn call (s with vs_inst_idx := k) =
      dftGasFromListTraceDefs$trace_step p d n C fn call s /\
    gas_events_step n C owner call (s with vs_inst_idx := k) =
      gas_events_step n C owner call s` by
    (rpt strip_tac >>
     simp[cj 1 dftGasFromListTraceDefsTheory.trace_defs, gas_events_step_def,
          instIdxIndepTheory.eval_ops_inst_idx, setup_callee_def]) >>
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `h` >> gvs[] >>
  simp[cj 1 dftGasFromListTraceDefsTheory.trace_defs, gas_events_step_def] >>
  Cases_on `decode_invoke call` >> simp[] >> rename1 `SOME dec` >>
  PairCases_on `dec` >> simp[] >>
  `call.inst_operands = Label dec0 :: dec1` by
    (gvs[decode_invoke_def, AllCaseEqs()]) >>
  `eval_operands dec1 (update_var q r s) = eval_operands dec1 s` by
    (irule dftCommutationTheory.eval_operands_update_var >> gvs[] >> metis_tac[]) >>
  simp[dftCommutationTheory.setup_callee_update_var]
QED

Theorem native_invoke_ordinary_crossing:
  let bxc = bb with bb_instructions := REPLICATE j pad ++ x::call::rest;
      bcx = bb with bb_instructions := REPLICATE j pad ++ call::x::rest in
  a.vs_inst_idx = j /\ call.inst_opcode = INVOKE /\
  inst_wf call /\ inst_wf x /\ dft_gas_swap_pair x call /\
  x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
  ~is_alloca_op x.inst_opcode /\ step_inst 0 C x a = OK u ==>
  !n W.
    let aW = a with vs_gas_readings := W;
        uW = (u with vs_gas_readings := W) with vs_inst_idx := SUC j in
    dftGasFromListTraceDefs$trace_step p d n C fn call aW =
      dftGasFromListTraceDefs$trace_step p d n C fn call uW /\
    exec_block n C bxc aW = exec_block n C bcx aW /\
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bxc aW) =
      trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bcx aW) /\
    gas_events_block n C fn.fn_name bxc aW =
      gas_events_block n C fn.fn_name bcx aW
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  map_every qx_gen_tac [`n`, `ws`] >>
  `dft_gas_swap_pair call x` by metis_tac[dft_gas_swap_pair_sym] >>
  `~is_terminator x.inst_opcode /\ ~is_terminator call.inst_opcode /\
   ~is_ext_call_op x.inst_opcode /\
   read_effects x.inst_opcode = {} /\ write_effects x.inst_opcode = {}` by
    (drule_all dftGasInvCallPartnerTheory.inv_call_partner_class >> simp[is_terminator_def]) >>
  `step_inst_base x a = OK u` by gvs[step_inst_non_invoke] >>
  drule_all pure_step_structure >> strip_tac >>
  `EVERY (\q. ~MEM (Var (FST q)) call.inst_operands /\
      ~MEM (FST q) call.inst_outputs) pairs` by
    (gvs[EVERY_MEM] >> metis_tac[dft_swap_output_frame, MEM_MAP]) >>
  qabbrev_tac `aW = a with vs_gas_readings := ws` >>
  qabbrev_tac `uW = (u with vs_gas_readings := ws) with vs_inst_idx := SUC j` >>
  qabbrev_tac `bxc = bb with bb_instructions := REPLICATE j pad ++ x::call::rest` >>
  qabbrev_tac `bcx = bb with bb_instructions := REPLICATE j pad ++ call::x::rest` >>
  `step_inst n C x aW = OK (u with vs_gas_readings := ws)` by
    (metis_tac[Abbr `aW`, step_inst_non_invoke, step_inst_ok_non_gas_oracle]) >>
  `uW = (FOLDL (\st (out,w). update_var out w st) aW pairs)
      with vs_inst_idx := SUC j` by
    (simp[Abbr `uW`, Abbr `aW`, gas_fold_updates]) >>
  `dftGasFromListTraceDefs$trace_step p d n C fn call uW =
      dftGasFromListTraceDefs$trace_step p d n C fn call aW /\
   gas_events_step n C fn.fn_name call uW = gas_events_step n C fn.fn_name call aW` by
    (simp[] >> irule native_invoke_row_updates >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  `aW.vs_inst_idx = j /\
   get_instruction bxc j = SOME x /\ get_instruction bxc (SUC j) = SOME call /\
   get_instruction bcx j = SOME call /\ get_instruction bcx (SUC j) = SOME x` by
    simp[Abbr `aW`, Abbr `bxc`, Abbr `bcx`, get_instruction_def, EL_APPEND_EQN] >>
  Cases_on `?v. step_inst n C call uW = OK v`
  >- suspend "success"
  >> suspend "stopped"
QED

Resume native_invoke_ordinary_crossing[success]:
  qpat_x_assum `?v. _` strip_assume_tac >>
  qpat_x_assum `u = _` kall_tac >>
  qpat_x_assum `uW = _` kall_tac >>
  fs[Abbr `uW`] >>
  `~gas_pair call.inst_opcode x.inst_opcode` by simp[gas_pair_def] >>
  `step_inst n C call
      ((u with vs_gas_readings := ws) with vs_inst_idx := SUC aW.vs_inst_idx) = OK v` by
    metis_tac[] >>
  drule_all dft_indexed_nongas_pair_ok >> strip_tac >>
  gvs[] >>
  `!s. gas_events_step n C fn.fn_name x s = []` by simp[gas_events_step_def] >>
  once_rewrite_tac[exec_block_def, cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                   gas_events_block_def] >>
  simp[dftGasFromListTraceDefsTheory.trace_step_noninvoke, visit_gas_def] >>
  once_rewrite_tac[exec_block_def, cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                   gas_events_block_def] >>
  simp[dftGasFromListTraceDefsTheory.trace_step_noninvoke, visit_gas_def] >>
  conj_tac
  >- (rewrite_tac[GSYM exec_block_def] >>
      irule venomExecProofsTheory.exec_block_same_suffix >>
      simp[Abbr `bxc`, Abbr `bcx`, DROP_APPEND]) >>
  conj_tac
  >- (AP_TERM_TAC >> irule native_trace_block_suffix_cong >>
      simp[Abbr `bxc`, Abbr `bcx`, DROP_APPEND]) >>
  irule gas_events_block_suffix_cong >>
  simp[Abbr `bxc`, Abbr `bcx`, DROP_APPEND]
QED

Resume native_invoke_ordinary_crossing[stopped]:
  `!r. (!t. r <> OK t) ==>
    (step_inst n C call uW = r <=> step_inst n C call aW = r)` by
    (rpt strip_tac >>
     qpat_x_assum `uW = _` (fn th => rewrite_tac[th]) >>
     simp[dft_invoke_stopping_idx] >>
     `((\st (out,w). update_var out w st) =
        (\st q. update_var (FST q) (SND q) st))` by
       (simp[FUN_EQ_THM, pairTheory.FORALL_PROD]) >>
     simp[] >> irule dft_swap_invoke_stopping_fold >> simp[]) >>
  `step_inst n C call uW = step_inst n C call aW` by metis_tac[] >>
  qpat_x_assum `u = _` kall_tac >>
  qpat_x_assum `uW = _` kall_tac >>
  gvs[Abbr `uW`] >>
  `!s. gas_events_step n C fn.fn_name x s = []` by simp[gas_events_step_def] >>
  once_rewrite_tac[exec_block_def, cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                   gas_events_block_def] >>
  simp[dftGasFromListTraceDefsTheory.trace_step_noninvoke, visit_gas_def] >>
  Cases_on `step_inst n C call aW` >> gvs[] >>
  once_rewrite_tac[exec_block_def, cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                   gas_events_block_def] >>
  simp[visit_gas_def]
QED

Finalise native_invoke_ordinary_crossing

Theorem native_from_block_observations[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM h bi /\
  from_block bi i /\ h.inst_id = i.inst_id ==>
  step_inst n C h a = step_inst n C i a /\
  is_terminator h.inst_opcode = is_terminator i.inst_opcode /\
  visit_gas ((p,d,h.inst_id),fn,h,a) ++
    trace_gas (dftGasFromListTraceDefs$trace_step p d n C fn h a) =
  visit_gas ((p,d,i.inst_id),fn,i,a) ++
    trace_gas (dftGasFromListTraceDefs$trace_step p d n C fn i a) /\
  gas_events_step n C fn.fn_name h a = gas_events_step n C fn.fn_name i a
Proof
  strip_tac >> fs[from_block_def]
  >- (`h = i` by metis_tac[all_distinct_map_mem_inj] >> simp[]) >>
  rename1 `i = flip_operands original` >>
  `h = original` by
    metis_tac[all_distinct_map_mem_inj, flip_operands_inst_id] >>
  qpat_x_assum `h = original` SUBST_ALL_TAC >>
  `original.inst_opcode <> GAS /\ original.inst_opcode <> INVOKE` by
    (Cases_on `original.inst_opcode` >>
     gvs[is_flippable_def, is_commutative_def, is_comparator_def]) >>
  `(flip_operands original).inst_opcode <> GAS /\
   (flip_operands original).inst_opcode <> INVOKE` by
    metis_tac[flip_operands_special_opcode, MEM] >>
  gvs[flip_operands_step_inst, flip_operands_is_terminator, visit_gas_def,
      dftGasFromListTraceDefsTheory.trace_step_noninvoke, gas_events_step_def]
QED

Theorem native_normalized_suffix_observations[local]:
  !norm scheduled a bn bt.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    EVERY (\i. MEM i bi) norm /\ EVERY (from_block bi) scheduled /\
    LIST_REL (\h i. h.inst_id = i.inst_id) norm scheduled /\
    DROP a.vs_inst_idx bn.bb_instructions = norm /\
    DROP a.vs_inst_idx bt.bb_instructions = scheduled ==>
    exec_block n C bn a = exec_block n C bt a /\
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bn a) =
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bt a) /\
    gas_events_block n C fn.fn_name bn a = gas_events_block n C fn.fn_name bt a
Proof
  Induct >> Cases_on `scheduled` >> simp[] >> rpt gen_tac >> strip_tac
  >- (gvs[DROP_EQ_NIL] >>
      once_rewrite_tac[exec_block_def, cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                       gas_events_block_def] >> simp[get_instruction_def]) >>
  rename1 `MEM source bi` >> rename1 `from_block bi target` >>
  `a.vs_inst_idx < LENGTH bn.bb_instructions /\
   a.vs_inst_idx < LENGTH bt.bb_instructions` by
    (qpat_x_assum `DROP _ bn.bb_instructions = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     qpat_x_assum `DROP _ bt.bb_instructions = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `EL a.vs_inst_idx bn.bb_instructions = source /\
   EL a.vs_inst_idx bt.bb_instructions = target /\
   DROP (SUC a.vs_inst_idx) bn.bb_instructions = norm /\
   DROP (SUC a.vs_inst_idx) bt.bb_instructions = t` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  drule_all native_from_block_observations >>
  disch_then (qspecl_then [`p`, `n`, `fn`, `d`, `a`, `C`] strip_assume_tac) >>
  once_rewrite_tac[exec_block_def, cj 2 dftGasFromListTraceDefsTheory.trace_defs,
                   gas_events_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst n C target a` >> gs[] >>
  Cases_on `is_terminator target.inst_opcode` >> gs[] >>
  first_x_assum (qspecl_then
    [`t`, `v with vs_inst_idx := SUC a.vs_inst_idx`, `bn`, `bt`] mp_tac) >>
  simp[] >> strip_tac >> gvs[APPEND_ASSOC]
QED

Theorem native_normalized_block_observations:
  !norm scheduled a.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    EVERY (\i. MEM i bi) norm /\ EVERY (from_block bi) scheduled /\
    LIST_REL (\h i. h.inst_id = i.inst_id) norm scheduled /\
    a.vs_inst_idx = j ==>
    !n C fn p d.
      let bn = bb with bb_instructions := REPLICATE j pad ++ norm;
          bt = bb with bb_instructions := REPLICATE j pad ++ scheduled in
      exec_block n C bn a = exec_block n C bt a /\
      trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bn a) =
      trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bt a) /\
      gas_events_block n C fn.fn_name bn a = gas_events_block n C fn.fn_name bt a
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> simp_tac pure_ss [LET_THM] >>
  irule native_normalized_suffix_observations >>
  qexists_tac `bi` >> simp[DROP_APPEND]
QED

Theorem native_prefix_cut:
  !pre a j.
    a.vs_inst_idx = j /\ EVERY (\i. ~is_terminator i.inst_opcode) pre ==>
    !n C fn p d rest bb pad.
    let bp = bb with bb_instructions := REPLICATE j pad ++ pre;
        bw = bb with bb_instructions := REPLICATE j pad ++ (pre ++ rest);
        br = bb with bb_instructions := REPLICATE (j + LENGTH pre) pad ++ rest;
        R = FOLDR (dft_exec_cons n C) OK pre a
    in
    exec_block n C bw a = (case R of OK t => exec_block n C br t | other => other) /\
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bw a) =
      trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bp a) ++
      (case R of OK t => trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn br t) | _ => []) /\
    gas_events_block n C fn.fn_name bw a = gas_events_block n C fn.fn_name bp a ++
      (case R of OK t => gas_events_block n C fn.fn_name br t | _ => []) /\
    (!t. R = OK t ==> t.vs_inst_idx = j + LENGTH pre)
Proof
  Induct >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp_tac pure_ss [LET_THM]
  >- (gvs[] >> simp[Once dftGasFromListTraceDefsTheory.trace_defs,
        Once gas_events_block_def, get_instruction_def]) >>
  gvs[EVERY_DEF] >>
  `!xs.
    exec_block n C (bb with bb_instructions := REPLICATE a.vs_inst_idx pad ++ h::xs) a =
      (case step_inst n C h a of OK u => exec_block n C
        (bb with bb_instructions := REPLICATE a.vs_inst_idx pad ++ h::xs)
        (u with vs_inst_idx := SUC a.vs_inst_idx) | other => other) /\
    dftGasFromListTraceDefs$trace_block p d n C fn
      (bb with bb_instructions := REPLICATE a.vs_inst_idx pad ++ h::xs) a =
      ((p,d,h.inst_id),fn,h,a)::(dftGasFromListTraceDefs$trace_step p d n C fn h a ++
        case step_inst n C h a of OK u => dftGasFromListTraceDefs$trace_block p d n C fn
          (bb with bb_instructions := REPLICATE a.vs_inst_idx pad ++ h::xs)
          (u with vs_inst_idx := SUC a.vs_inst_idx) | _ => []) /\
    gas_events_block n C fn.fn_name
      (bb with bb_instructions := REPLICATE a.vs_inst_idx pad ++ h::xs) a =
      gas_events_step n C fn.fn_name h a ++
        (case step_inst n C h a of OK u => gas_events_block n C fn.fn_name
          (bb with bb_instructions := REPLICATE a.vs_inst_idx pad ++ h::xs)
          (u with vs_inst_idx := SUC a.vs_inst_idx) | _ => [])` by
    (gen_tac >> conj_tac
     >- (CONV_TAC (LAND_CONV (REWR_CONV exec_block_def)) >>
         simp[get_instruction_def, EL_APPEND_EQN]) >>
     conj_tac
     >- (CONV_TAC (LAND_CONV (REWR_CONV (cj 2 dftGasFromListTraceDefsTheory.trace_defs))) >>
         simp[get_instruction_def, EL_APPEND_EQN]) >>
     CONV_TAC (LAND_CONV (REWR_CONV gas_events_block_def)) >>
     simp[get_instruction_def, EL_APPEND_EQN]) >>
  simp_tac pure_ss [GSYM APPEND_ASSOC, APPEND] >>
  qpat_x_assum `!xs. exec_block _ _ _ _ = _ /\ _`
    (fn th => rewrite_tac[cj 1 th, cj 2 th, cj 3 th]) >>
  simp[dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst n C h a` >> simp[] >>
  rename1 `step_inst n C h a = OK u` >>
  `a.vs_inst_idx - SUC a.vs_inst_idx = 0 /\
   SUC a.vs_inst_idx - (a.vs_inst_idx + 1) = 0` by decide_tac >>
  `!xs.
    exec_block n C (bb with bb_instructions := REPLICATE a.vs_inst_idx pad ++ h::xs)
      (u with vs_inst_idx := SUC a.vs_inst_idx) =
    exec_block n C (bb with bb_instructions := REPLICATE (SUC a.vs_inst_idx) pad ++ xs)
      (u with vs_inst_idx := SUC a.vs_inst_idx) /\
    dftGasFromListTraceDefs$trace_block p d n C fn
      (bb with bb_instructions := REPLICATE a.vs_inst_idx pad ++ h::xs)
      (u with vs_inst_idx := SUC a.vs_inst_idx) =
    dftGasFromListTraceDefs$trace_block p d n C fn
      (bb with bb_instructions := REPLICATE (SUC a.vs_inst_idx) pad ++ xs)
      (u with vs_inst_idx := SUC a.vs_inst_idx) /\
    gas_events_block n C fn.fn_name
      (bb with bb_instructions := REPLICATE a.vs_inst_idx pad ++ h::xs)
      (u with vs_inst_idx := SUC a.vs_inst_idx) =
    gas_events_block n C fn.fn_name
      (bb with bb_instructions := REPLICATE (SUC a.vs_inst_idx) pad ++ xs)
      (u with vs_inst_idx := SUC a.vs_inst_idx)` by
    (gen_tac >> conj_tac
     >- (irule venomExecProofsTheory.exec_block_same_suffix >> simp[DROP_APPEND]) >>
     conj_tac
     >- (irule native_trace_block_suffix_cong >> simp[DROP_APPEND]) >>
     irule gas_events_block_suffix_cong >> simp[DROP_APPEND]) >>
  simp_tac pure_ss [GSYM APPEND_ASSOC, APPEND] >>
  qpat_x_assum `!xs. exec_block _ _ _ _ = _ /\ _`
    (fn th => rewrite_tac[cj 1 th, cj 2 th, cj 3 th]) >>
  first_x_assum (qspec_then `u with vs_inst_idx := SUC a.vs_inst_idx` mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >> disch_then (mp_tac o cj 4) >> metis_tac[]
QED

Theorem native_inventory_root_visit[local]:
  !s. ctx_labels_bound C s.vs_labels /\
    ctx_labels_bound C' s.vs_labels /\ ~s.vs_call_ctx.cc_static /\
    terminates (exec_block b C' bb s) /\
    gas_count_block b C' bb s <= LENGTH s.vs_gas_readings ==>
    !i a. MEM ((p,d,i.inst_id),fn',i,a)
      (dftGasFromListTraceDefs$trace_block p d b C' fn' bb s) ==>
      ctx_labels_bound C a.vs_labels /\ ctx_labels_bound C' a.vs_labels /\
      ~a.vs_call_ctx.cc_static /\ terminates (step_inst b C' i a) /\
      gas_count_step b C' i a <= LENGTH a.vs_gas_readings
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> disch_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `MEM _ _` mp_tac >>
      simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs)]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `~MEM ((p,d,i.inst_id),fn',i,a)
      (dftGasFromListTraceDefs$trace_step p d b C' fn' inst s)` by
    (spose_not_then assume_tac >>
     `MEM (p,d,i.inst_id) (MAP FST
        (dftGasFromListTraceDefs$trace_step p d b C' fn' inst s))` by
       (simp[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
     metis_tac[trace_step_not_root]) >>
  qpat_x_assum `MEM _ (dftGasFromListTraceDefs$trace_block _ _ _ _ _ _ _)` mp_tac >>
  simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs), MEM_APPEND] >>
  strip_tac
  >- (gvs[] >> conj_tac
      >- (qpat_x_assum `terminates _` mp_tac >>
          simp[Once run_block_non_phis_def] >>
          Cases_on `step_inst b C' i a` >>
          simp[passSimulationDefsTheory.terminates_def]) >>
      qpat_x_assum `gas_count_block _ _ _ _ <= _` mp_tac >>
      simp[Once gas_count_block_def] >>
      Cases_on `step_inst b C' i a` >> simp[] >>
      Cases_on `is_terminator i.inst_opcode` >> simp[]) >>
  Cases_on `step_inst b C' inst s` >> gvs[] >>
  rename1 `step_inst b C' inst s = OK u` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by gvs[get_instruction_def] >>
  `u.vs_gas_readings = DROP (gas_count_step b C' inst s) s.vs_gas_readings` by
    (mp_tac (cj 1 gas_count_suffix) >>
     disch_then (qspecl_then [`b`, `C'`, `inst`, `s`] mp_tac) >>
     simp[gas_count_suffix_def]) >>
  `ctx_labels_bound C u.vs_labels /\ ctx_labels_bound C' u.vs_labels` by
    metis_tac[ctx_labels_bound_step] >>
  `~u.vs_call_ctx.cc_static` by metis_tac[venomExecProofsTheory.step_inst_ok_preserves_call_ctx] >>
  `terminates (exec_block b C' bb (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (qpat_x_assum `terminates _` mp_tac >> simp[Once run_block_non_phis_def]) >>
  `gas_count_block b C' bb (u with vs_inst_idx := SUC s.vs_inst_idx) <=
     LENGTH u.vs_gas_readings` by
    (qpat_x_assum `gas_count_block b C' bb s <= _` mp_tac >>
     simp[Once gas_count_block_def, LENGTH_DROP]) >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  simp[] >>
  disch_then (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  gvs[LENGTH_DROP] >> metis_tac[]
QED

Theorem native_inventory_call_admissible[local]:
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
  ~t.vs_call_ctx.cc_static /\ terminates (exec_block b C' bt t) /\
  gas_count_block b C' bt t <= LENGTH t.vs_gas_readings /\
  i.inst_opcode = INVOKE /\
  MEM ((p,d,i.inst_id),fn',i,a)
    (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) ==>
  ?nm ops args cf cf' cs ct.
    i.inst_opcode = INVOKE /\
    MEM ((p,d,i.inst_id),fn',i,a)
      (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) /\
    decode_invoke i = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME cf /\
    lookup_function nm C'.ctx_functions = SOME cf' /\
    MEM cf C.ctx_functions /\ MEM cf' C'.ctx_functions /\
    cf' = dft_fn cf /\ dft_fn_rel cf cf' /\
    eval_operands ops a = SOME args /\
    setup_callee cf args a = SOME cs /\
    setup_callee cf' args a = SOME ct /\ cs = ct /\
    fn_entry_label cf = SOME cs.vs_current_bb /\
    strict_dom_vars_defined cf cs /\ fn_reachable cf cs.vs_current_bb /\
    ctx_labels_bound C cs.vs_labels /\ ctx_labels_bound C' cs.vs_labels /\
    ~cs.vs_call_ctx.cc_static /\ terminates (run_blocks b C' cf' ct) /\
    gas_count_blocks b C' cf' ct <= LENGTH ct.vs_gas_readings
Proof
  strip_tac >>
  `ctx_labels_bound C a.vs_labels /\ ctx_labels_bound C' a.vs_labels /\
   ~a.vs_call_ctx.cc_static /\ terminates (step_inst b C' i a) /\
   gas_count_step b C' i a <= LENGTH a.vs_gas_readings` by
    (irule native_inventory_root_visit >> metis_tac[]) >>
  qpat_x_assum `terminates (step_inst _ _ _ _)` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `decode_invoke i` >> simp[passSimulationDefsTheory.terminates_def] >>
  rename1 `decode_invoke i = SOME dec` >> PairCases_on `dec` >>
  Cases_on `lookup_function dec0 C'.ctx_functions` >>
  simp[passSimulationDefsTheory.terminates_def] >>
  rename1 `lookup_function dec0 C'.ctx_functions = SOME cf'` >>
  Cases_on `eval_operands dec1 a` >> simp[passSimulationDefsTheory.terminates_def] >>
  rename1 `eval_operands dec1 a = SOME args` >>
  Cases_on `setup_callee cf' args a` >> simp[passSimulationDefsTheory.terminates_def] >>
  rename1 `setup_callee cf' args a = SOME ct` >>
  strip_tac >>
  `terminates (run_blocks b C' cf' ct)` by
    (Cases_on `run_blocks b C' cf' ct` >> gvs[passSimulationDefsTheory.terminates_def]) >>
  drule dft_fn_rel_lookup_function >>
  disch_then (qspec_then `dec0` mp_tac) >>
  Cases_on `lookup_function dec0 C.ctx_functions` >> simp[] >> strip_tac >>
  rename1 `lookup_function dec0 C.ctx_functions = SOME cf` >>
  `OPTREL (\f g. g = dft_fn f)
    (lookup_function dec0 C.ctx_functions)
    (lookup_function dec0 C'.ctx_functions)` by
    (irule o1PassLiftTheory.list_rel_lookup_function >> simp[] >>
     gen_tac >> simp[dftDefsTheory.dft_fn_def] >> pairarg_tac >> simp[]) >>
  `cf' = dft_fn cf` by gvs[] >>
  `setup_callee cf args a = SOME ct` by
    metis_tac[dft_fn_rel_setup_callee] >>
  `ct.vs_gas_readings = a.vs_gas_readings` by gvs[setup_callee_def] >>
  `gas_count_blocks b C' cf' ct <= LENGTH ct.vs_gas_readings` by
    (gvs[gas_count_step_def]) >>
  qexists_tac `ct` >>
  simp[GSYM passSimulationDefsTheory.terminates_def] >>
  `fn_entry_label cf = SOME ct.vs_current_bb` by metis_tac[dft_setup_callee_entry] >>
  `fn_reachable cf ct.vs_current_bb` by simp[fn_reachable_def] >>
  metis_tac[venomInstTheory.lookup_function_MEM,
    dftGasSimInvariantTheory.ev_setup_callee_dominators,
    ctx_labels_bound_setup_callee, dftGasSimInvariantTheory.ev_setup_callee_nonstatic]
QED

Theorem native_inventory_gas_excludes[local]:
  ~MEM id ids /\
  EVERY (\v. block_region p d ids (FST v)) visits ==>
  FILTER (\kw. frame_below ((d,id)::p) (FST (FST kw)))
    (trace_gas visits) = []
Proof
  simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
  `MEM (FST kw) (MAP FST visits)` by
    (irule trace_gas_name_mem >> simp[MEM_MAP] >> metis_tac[]) >>
  gvs[MEM_MAP] >>
  first_x_assum drule >> strip_tac >>
  PairCases_on `y` >> gvs[] >>
  `block_region p d [id] (y0,y1,y2)` by
    (irule below_call_region >> simp[]) >>
  `~block_region p d [id] (y0,y1,y2)` by
    (irule block_regions_disjoint >> qexists_tac `ids` >> simp[]) >>
  metis_tac[]
QED

Theorem native_inventory_root_subtree[local]:
  !s. ALL_DISTINCT (MAP (\i. i.inst_id)
      (DROP s.vs_inst_idx bb.bb_instructions)) ==>
  !i a. MEM ((p,d,i.inst_id),fn',i,a)
    (dftGasFromListTraceDefs$trace_block p d b C' fn' bb s) ==>
  FILTER (\kw. frame_below ((d,i.inst_id)::p) (FST (FST kw)))
    (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bb s)) =
  trace_gas (dftGasFromListTraceDefs$trace_step p d b C' fn' i a)
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> disch_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `MEM _ _` mp_tac >>
      simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs)]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `~MEM ((p,d,i.inst_id),fn',i,a)
      (dftGasFromListTraceDefs$trace_step p d b C' fn' inst s)` by
    (spose_not_then assume_tac >>
     `MEM (p,d,i.inst_id) (MAP FST
        (dftGasFromListTraceDefs$trace_step p d b C' fn' inst s))` by
       (simp[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
     metis_tac[trace_step_not_root]) >>
  drule remaining_ids_step >> strip_tac >> gvs[] >>
  qpat_x_assum `MEM _ (dftGasFromListTraceDefs$trace_block _ _ _ _ _ _ _)` mp_tac >>
  simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs), MEM_APPEND] >>
  strip_tac
  >- (gvs[] >>
      `FILTER (\kw. frame_below ((d,i.inst_id)::p) (FST (FST kw)))
         (trace_gas (dftGasFromListTraceDefs$trace_step p d b C' fn' i a)) =
       trace_gas (dftGasFromListTraceDefs$trace_step p d b C' fn' i a)` by
        (simp[FILTER_EQ_ID, EVERY_MEM] >> rpt strip_tac >>
         `MEM (FST kw) (MAP FST
           (dftGasFromListTraceDefs$trace_step p d b C' fn' i a))` by
           (irule trace_gas_name_mem >> simp[MEM_MAP] >> metis_tac[]) >>
         gvs[MEM_MAP] >>
         mp_tac (cj 1 trace_regions) >> simp[EVERY_MEM] >> metis_tac[]) >>
      CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV
        (REWR_CONV (cj 2 dftGasFromListTraceDefsTheory.trace_defs))))) >>
      Cases_on `i.inst_opcode = GAS` >>
      simp[FILTER_APPEND_DISTRIB, visit_gas_def, frame_not_below_self] >>
      Cases_on `step_inst b C' i a` >> simp[] >>
      Cases_on `is_terminator i.inst_opcode` >> simp[] >>
      irule native_inventory_gas_excludes >>
      qexists_tac `MAP (\i. i.inst_id) (DROP (SUC a.vs_inst_idx) bb.bb_instructions)` >>
      gvs[] >>
      qspecl_then [`p`, `d`, `b`, `C'`, `fn'`, `bb`,
        `v with vs_inst_idx := SUC a.vs_inst_idx`] mp_tac (cj 2 trace_regions) >>
      simp[]) >>
  Cases_on `step_inst b C' inst s` >> gvs[] >>
  rename1 `step_inst b C' inst s = OK u` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  `MEM i.inst_id (MAP (\i. i.inst_id)
    (DROP (SUC s.vs_inst_idx) bb.bb_instructions))` by
    (drule trace_block_region >> simp[block_region_def] >>
     strip_tac >> gvs[] >>
     `frame_below ((d,call_id)::p) p` by
       (simp[frame_below_def] >> metis_tac[]) >>
     metis_tac[frame_not_below_self]) >>
  `i.inst_id <> inst.inst_id` by metis_tac[] >>
  `FILTER (\kw. frame_below ((d,i.inst_id)::p) (FST (FST kw)))
     (trace_gas (dftGasFromListTraceDefs$trace_step p d b C' fn' inst s)) = []` by
    (irule native_inventory_gas_excludes >> qexists_tac `[inst.inst_id]` >>
     simp[EVERY_MEM] >> rpt strip_tac >> irule trace_step_region >> metis_tac[]) >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV
    (REWR_CONV (cj 2 dftGasFromListTraceDefsTheory.trace_defs))))) >>
  simp[FILTER_APPEND_DISTRIB, visit_gas_def, frame_not_below_self] >>
  Cases_on `inst.inst_opcode = GAS` >> gvs[frame_not_below_self] >>
  qpat_x_assum `!y. _` (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- gvs[get_instruction_def]) >>
  disch_then (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem native_inventory_child_lookup[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) (DROP t.vs_inst_idx bt.bb_instructions)) /\
  MEM ((p,d,i.inst_id),fn',i,a)
    (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) /\
  i.inst_opcode = INVOKE /\ decode_invoke i = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME cf' /\
  eval_operands ops a = SOME args /\ setup_callee cf' args a = SOME ct /\
  EVERY (later_region ((d,i.inst_id)::p) d) keys ==>
  MAP (ALOOKUP (trace_gas (dftGasFromListTraceDefs$trace_blocks
    ((d,i.inst_id)::p) d b C' cf' ct))) keys =
  MAP (ALOOKUP (trace_gas
    (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))) keys
Proof
  strip_tac >>
  `FILTER (\kw. frame_below ((d,i.inst_id)::p) (FST (FST kw)))
    (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)) =
    trace_gas (dftGasFromListTraceDefs$trace_blocks ((d,i.inst_id)::p) d b C' cf' ct)` by
    (drule_all native_inventory_root_subtree >>
     drule_all dftGasFromListTraceDefsTheory.trace_step_invoke >> simp[]) >>
  pop_assum (SUBST1_TAC o SYM) >> ho_match_mp_tac ambient_region_mask >>
  gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
  rename1 `later_region _ _ key` >> PairCases_on `key` >>
  simp[] >> metis_tac[later_region_frame]
QED

Theorem native_inventory_suffix_distinct[local]:
  !s. EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
      f.fn_blocks) ctx.ctx_functions /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (DROP s.vs_inst_idx bb.bb_instructions)) ==>
    ALL_DISTINCT (MAP FST
      (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb s))
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs)] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  drule remaining_ids_step >> strip_tac >> gvs[] >>
  `ALL_DISTINCT (MAP FST
    (dftGasFromListTraceDefs$trace_step p d fuel ctx fn inst s))` by
    metis_tac[cj 1 trace_names_distinct] >>
  simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs), MAP_APPEND,
       ALL_DISTINCT_APPEND] >>
  conj_tac
  >- (simp[trace_step_not_root] >>
      Cases_on `step_inst fuel ctx inst s` >> simp[] >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
      irule trace_block_excludes >> simp[]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK t` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  `ALL_DISTINCT (MAP FST (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb
    (t with vs_inst_idx := SUC s.vs_inst_idx)))` by
    (qpat_x_assum `!y. _` (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
     (impl_tac >- gvs[get_instruction_def]) >>
     disch_then (qspec_then `t with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `~MEM inst.inst_id (MAP (\i. i.inst_id)
    (DROP (t with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx bb.bb_instructions))` by simp[] >>
  drule trace_step_block_disjoint >> metis_tac[]
QED

Theorem native_lookup_fill_subtrace_agreement:
  !obs keys vals target source.
    ALL_DISTINCT (MAP FST obs) ==>
    (EVERY (\kw. MEM kw obs) (trace_gas target) ==>
      trace_agrees
        (\key. case ALOOKUP (obs ++ ZIP (keys,vals)) key of
          NONE => 0w | SOME w => w) target) /\
    (ALL_DISTINCT keys /\ LENGTH keys = LENGTH vals /\
     LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
       (MAP (ALOOKUP obs) keys) vals /\
     EVERY (\kw. MEM kw (ZIP (keys,vals))) (trace_gas source) ==>
      trace_agrees
        (\key. case ALOOKUP (obs ++ ZIP (keys,vals)) key of
          NONE => 0w | SOME w => w) source)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[trace_agrees_def, EVERY_MEM] >> strip_tac >>
      qx_gen_tac `kw` >> Cases_on `kw` >> simp[] >> strip_tac >>
      rename1 `MEM (key,w) (trace_gas target)` >>
      `MEM (key,w) obs` by metis_tac[] >>
      `ALOOKUP obs key = SOME w` by
        metis_tac[alistTheory.ALOOKUP_ALL_DISTINCT_MEM] >>
      simp[alistTheory.ALOOKUP_APPEND]) >>
  strip_tac >>
  `EVERY (\(key,w). ALOOKUP obs key = NONE \/ ALOOKUP obs key = SOME w)
     (ZIP (keys,vals))` by
    (gvs[LIST_REL_MAP1, LIST_REL_EVERY_ZIP, combinTheory.o_DEF]) >>
  `ALL_DISTINCT (MAP FST (ZIP (keys,vals)))` by simp[MAP_ZIP] >>
  fs[EVERY_MEM] >> simp[trace_agrees_def, EVERY_MEM] >>
  qx_gen_tac `kw` >> Cases_on `kw` >> simp[] >> strip_tac >>
  rename1 `MEM (key,w) (trace_gas source)` >>
  `MEM (key,w) (ZIP (keys,vals))` by metis_tac[] >>
  `ALOOKUP (ZIP (keys,vals)) key = SOME w` by
    metis_tac[alistTheory.ALOOKUP_ALL_DISTINCT_MEM] >>
  qpat_x_assum `!kw. MEM kw (ZIP _) ==> _`
    (qspec_then `(key,w)` mp_tac) >> simp[] >> strip_tac >>
  simp[alistTheory.ALOOKUP_APPEND]
QED

Theorem native_inventory_child_agreement:
  ctx_inst_ids_distinct C' /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (DROP t.vs_inst_idx bt.bb_instructions)) /\
  MEM ((p,d,i.inst_id),fn',i,a)
    (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) /\
  i.inst_opcode = INVOKE /\ decode_invoke i = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME cf' /\
  eval_operands ops a = SOME args /\ setup_callee cf' args a = SOME ct ==>
  let obs = trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t);
      child = dftGasFromListTraceDefs$trace_blocks ((d,i.inst_id)::p) d b C' cf' ct
  in ALL_DISTINCT (MAP FST obs) /\
     EVERY (\kw. MEM kw obs) (trace_gas child) /\
     trace_agrees
       (\key. case ALOOKUP (obs ++ ZIP (keys,vals)) key of
         NONE => 0w | SOME w => w) child
Proof
  strip_tac >> simp_tac pure_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `ALL_DISTINCT (MAP FST obs)` >>
  qmatch_goalsub_abbrev_tac `trace_gas child` >>
  conj_asm1_tac
  >- (simp_tac pure_ss [Abbr `obs`] >> irule trace_gas_names_distinct >>
      irule native_inventory_suffix_distinct >> simp[] >>
      qpat_x_assum `ctx_inst_ids_distinct C'` mp_tac >>
      simp_tac bool_ss [ctx_inst_ids_distinct_def] >> strip_tac >>
      simp[EVERY_MEM] >> rpt strip_tac >>
      drule_all venomWfPropsTheory.all_distinct_flat_map_member >>
      BETA_TAC >> strip_tac >>
      drule_all venomWfPropsTheory.all_distinct_flat_map_member >> simp[]) >>
  conj_asm1_tac
  >- (`FILTER (\kw. frame_below ((d,i.inst_id)::p) (FST (FST kw))) obs =
       trace_gas child` by
        (simp_tac pure_ss [Abbr `obs`, Abbr `child`] >>
         drule_all native_inventory_root_subtree >>
         drule_all dftGasFromListTraceDefsTheory.trace_step_invoke >> simp[]) >>
      pop_assum (SUBST1_TAC o SYM) >> simp[EVERY_MEM, MEM_FILTER]) >>
  irule (cj 1 native_lookup_fill_subtrace_agreement) >> simp[]
QED

Theorem native_inventory_lookup_rows[local]:
  !keys obs. ALL_DISTINCT keys /\ ALL_DISTINCT (MAP FST obs) ==>
  PERM
    (MAP (\k. (k,THE (ALOOKUP obs k)))
      (FILTER (\k. IS_SOME (ALOOKUP obs k)) keys))
    (FILTER (\kw. MEM (FST kw) keys) obs)
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP (\k. (k,THE (ALOOKUP obs k)))
      (FILTER (\k. IS_SOME (ALOOKUP obs k)) keys))` by
    (irule ALL_DISTINCT_MAP_INJ >> simp[FILTER_ALL_DISTINCT]) >>
  `ALL_DISTINCT (FILTER (\kw. MEM (FST kw) keys) obs)` by
    (irule FILTER_ALL_DISTINCT >> metis_tac[listTheory.ALL_DISTINCT_MAP]) >>
  irule PERM_ALL_DISTINCT >> simp[] >>
  Cases >> simp[MEM_MAP, MEM_FILTER] >>
  eq_tac
  >- (rpt strip_tac >> gvs[] >>
      Cases_on `ALOOKUP obs q` >> gvs[] >>
      metis_tac[alistTheory.ALOOKUP_MEM]) >>
  strip_tac >> drule_all alistTheory.ALOOKUP_ALL_DISTINCT_MEM >> simp[]
QED

Theorem native_inventory_lookup_values[local]:
  !keys obs.
    MAP THE (FILTER IS_SOME (MAP (ALOOKUP obs) keys)) =
    MAP (\k. THE (ALOOKUP obs k))
      (FILTER (\k. IS_SOME (ALOOKUP obs k)) keys)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `ALOOKUP obs h` >> simp[]
QED

Theorem native_inventory_lookup_partition[local]:
  ALL_DISTINCT keys /\ ALL_DISTINCT (MAP FST obs) ==>
  PERM
    (MAP THE (FILTER IS_SOME (MAP (ALOOKUP obs) keys)) ++
      MAP SND (FILTER (\kw. ~MEM (FST kw) keys) obs))
    (MAP SND obs)
Proof
  strip_tac >>
  qspecl_then [`keys`, `obs`] mp_tac native_inventory_lookup_rows >>
  simp[] >> disch_then (mp_tac o MATCH_MP PERM_MAP) >>
  disch_then (qspec_then `SND` mp_tac) >>
  simp[MAP_MAP_o, combinTheory.o_DEF, GSYM native_inventory_lookup_values] >>
  strip_tac >>
  irule PERM_TRANS >>
  qexists_tac `MAP SND (FILTER (\kw. MEM (FST kw) keys) obs) ++
    MAP SND (FILTER (\kw. ~MEM (FST kw) keys) obs)` >>
  conj_tac >- simp[PERM_APPEND_IFF] >>
  rewrite_tac[GSYM MAP_APPEND] >> irule PERM_MAP >>
  qspecl_then [`\kw. MEM (FST kw) keys`, `obs`] mp_tac PERM_SPLIT >>
  simp[combinTheory.o_DEF, PERM_SYM]
QED

Theorem native_inventory_return_saturation[local]:
  ALL_DISTINCT keys /\ ALL_DISTINCT (MAP FST obs) /\
  PERM (MAP THE (FILTER IS_SOME (MAP (ALOOKUP obs) keys)) ++ residual) input /\
  residual = DROP (LENGTH obs) input /\ LENGTH obs <= LENGTH input ==>
  FILTER (\kw. ~MEM (FST kw) keys) obs = []
Proof
  strip_tac >>
  `PERM (MAP THE (FILTER IS_SOME (MAP (ALOOKUP obs) keys)) ++
      MAP SND (FILTER (\kw. ~MEM (FST kw) keys) obs)) (MAP SND obs)` by
    (irule native_inventory_lookup_partition >> simp[]) >>
  pop_assum (assume_tac o MATCH_MP PERM_LENGTH) >>
  qpat_x_assum `PERM _ input` (assume_tac o MATCH_MP PERM_LENGTH) >>
  gvs[LENGTH_APPEND, LENGTH_MAP, LENGTH_DROP] >>
  `LENGTH (FILTER (\kw. ~MEM (FST kw) keys) obs) = 0` by decide_tac >>
  metis_tac[LENGTH_NIL]
QED

Theorem native_stopping_call_partner[local]:
  inst_wf z /\ inst_shape_ok z /\ dft_gas_swap_pair z call /\
  call.inst_opcode = INVOKE /\
  (!op. MEM op z.inst_operands ==> IS_SOME (eval_operand op s)) /\
  (is_terminator z.inst_opcode \/ ~(?u. step_inst b C z s = OK u)) ==> F
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `dft_gas_swap_pair call z` by metis_tac[dft_gas_swap_pair_sym] >>
  drule_all dftGasInvCallPartnerTheory.inv_call_partner_class >> strip_tac >>
  `z.inst_opcode = GAS \/ is_effect_free_op z.inst_opcode` by
    (qpat_x_assum `dft_gas_swap_pair z call` mp_tac >>
     simp[dft_gas_swap_pair_def] >> strip_tac >>
     Cases_on `z.inst_opcode` >>
     gvs[is_effect_free_op_def, read_effects_def, write_effects_def,
         is_terminator_def, is_alloca_op_def, is_ext_call_op_def, is_pseudo_def,
         dft_abort_compatible_def, dft_abort_kind_def, empty_effects_def]) >>
  Cases_on `z.inst_opcode = GAS`
  >- (fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      metis_tac[step_inst_gas_single]) >>
  `is_effect_free_op z.inst_opcode` by metis_tac[] >>
  `z.inst_opcode <> PHI /\ z.inst_opcode <> PARAM /\ z.inst_opcode <> FMP_PARAM` by
    (Cases_on `z.inst_opcode` >> gvs[is_pseudo_def]) >>
  `?u. step_inst_base z s = OK u` by
    (irule effect_free_step_inst_base_ok >>
     simp[] >> metis_tac[optionTheory.IS_SOME_EQ_NOT_NONE]) >>
  metis_tac[step_inst_non_invoke]
QED

Theorem native_selected_operands[local]:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  dft_remaining_inv fn bb (pre ++ z::post) s /\
  EVERY (\x. ~dft_must_order x z) pre /\
  ~is_terminator z.inst_opcode /\ z.inst_opcode <> INVOKE /\
  z.inst_opcode <> CODECOPY ==>
  !op. MEM op z.inst_operands ==> IS_SOME (eval_operand op s)
Proof
  strip_tac >> Cases_on `pre = []`
  >- (gvs[] >> metis_tac[inv_remaining_head_operands]) >>
  drule_all dft_remaining_inv_ready >> strip_tac >>
  Cases >> simp[eval_operand_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]
QED

Theorem native_selected_stopping_no_call_swap[local]:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  dft_remaining_inv fn bb (pre ++ z::post) s /\
  EVERY (\x. ~dft_must_order x z) pre /\ inst_wf z /\ inst_shape_ok z /\
  (is_terminator z.inst_opcode \/ ~(?u. step_inst b C z s = OK u)) ==>
  !call. call.inst_opcode = INVOKE ==> ~dft_gas_swap_pair z call
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt strip_tac >>
  `dft_gas_swap_pair call z` by metis_tac[dft_gas_swap_pair_sym] >>
  drule_all dftGasInvCallPartnerTheory.inv_call_partner_class >> strip_tac >>
  `z.inst_opcode <> CODECOPY` by
    (Cases_on `z.inst_opcode = CODECOPY` >>
     gvs[write_effects_def, empty_effects_def]) >>
  `!op. MEM op z.inst_operands ==> IS_SOME (eval_operand op s)` by
    metis_tac[native_selected_operands] >>
  metis_tac[native_stopping_call_partner]
QED

Theorem native_bubbles_perm[local]:
  !src dst. dft_head_bubbles A src dst ==> PERM src dst
Proof
  ho_match_mp_tac dft_head_bubbles_ind >> simp[] >>
  rpt strip_tac >> (simp[sortingTheory.PERM_FUN_APPEND_CONS])
QED

Theorem native_bubbles_inversion[local]:
  !src dst. dft_head_bubbles R src dst ==>
    ALL_DISTINCT src ==>
    !x z. id_before src x z /\ id_before dst z x ==> R x z
Proof
  ho_match_mp_tac dft_head_bubbles_strongind >> conj_tac
  >- simp[id_before_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `dft_head_bubbles R (pre ++ post) rest` >>
  `PERM (pre ++ post) rest` by metis_tac[native_bubbles_perm] >>
  `ALL_DISTINCT (pre ++ post) /\ ~MEM y pre /\ ~MEM y post` by
    (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  Cases_on `z = y`
  >- (gvs[dftSsaPreserveTheory.id_before_append, id_before_cons,
          EVERY_MEM] >> metis_tac[id_before_mem]) >>
  `~MEM y rest` by metis_tac[PERM_MEM_EQ, MEM_APPEND] >>
  `x <> y` by
    (gvs[id_before_cons] >> metis_tac[id_before_mem]) >>
  first_x_assum irule >> simp[] >>
  gvs[dftSsaPreserveTheory.id_before_append, id_before_cons] >>
  metis_tac[]
QED

Theorem native_bubbles_filter[local]:
  (!x y. A x y ==> ~(P x /\ P y)) ==>
  !src dst. dft_head_bubbles A src dst ==> FILTER P src = FILTER P dst
Proof
  strip_tac >> ho_match_mp_tac dft_head_bubbles_ind >> simp[] >>
  rpt strip_tac >> Cases_on `P y` >> gvs[FILTER_APPEND_DISTRIB] >>
  `FILTER P pre = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM] >> metis_tac[]) >> gvs[]
QED

Theorem native_bubbles_prefix_remaining[local]:
  !done todo rest s t.
    wf_function fn /\ EVERY inst_wf bb.bb_instructions /\
    dft_remaining_inv fn bb todo s /\ ~s.vs_call_ctx.cc_static /\
    dft_head_bubbles A todo (done ++ rest) /\
    EVERY (\i. ~is_terminator i.inst_opcode) done /\
    FOLDR (dft_exec_cons b C) OK done s = OK t ==>
    ?residual. dft_remaining_inv fn bb residual t /\
      ~t.vs_call_ctx.cc_static /\ dft_head_bubbles A residual rest
Proof
  Induct >- (simp[] >> metis_tac[]) >>
  rpt gen_tac >> simp[] >> strip_tac >>
  qpat_x_assum `dft_head_bubbles _ _ _` mp_tac >>
  simp[Once dft_head_bubbles_cases] >> strip_tac >> gvs[] >>
  gvs[dftIndexedExecTheory.dft_exec_cons_def, AllCaseEqs()] >>
  rename1 `step_inst b C h s = OK u` >>
  `dft_remaining_inv fn bb (pre ++ post)
     (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule dft_remaining_inv_step >> simp[] >>
     qexistsl_tac [`C`, `b`, `h`] >> simp[] >>
     qpat_x_assum `dft_remaining_inv fn bb _ s` mp_tac >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  `~u.vs_call_ctx.cc_static` by
    metis_tac[venomInstProofsTheory.step_preserves_call_ctx] >>
  first_x_assum (qspecl_then [`pre ++ post`, `rest`,
    `u with vs_inst_idx := SUC s.vs_inst_idx`, `t`] mp_tac) >> simp[]
QED

Theorem native_selected_maximal_cut:
  !P n C s. ?A rest q.
    P = A ++ rest /\
    EVERY (\i. ~is_terminator i.inst_opcode) A /\
    FOLDR (dft_exec_cons n C) OK A s = OK q /\
    (rest = [] \/ ?i more. rest = i::more /\
       (is_terminator i.inst_opcode \/ ~(?u. step_inst n C i q = OK u)))
Proof
  Induct >> rpt gen_tac
  >- (qexistsl_tac [`[]`, `[]`, `s`] >> simp[]) >>
  Cases_on `is_terminator h.inst_opcode \/ ~(?u. step_inst n C h s = OK u)`
  >- (qexistsl_tac [`[]`, `h::P`, `s`] >> gvs[]) >>
  gvs[] >>
  rename1 `step_inst n C h s = OK u` >>
  qpat_x_assum `!n C s. _` (qspecl_then
    [`n`, `C`, `u with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  strip_tac >>
  qexistsl_tac [`h::A`, `rest`, `q`] >>
  simp[dftIndexedExecTheory.dft_exec_cons_def]
QED

Theorem native_suffix_stopping_decomposition:
  !xs b C t. terminates (dft_exec_suffix b C xs t) ==>
  ?done z later tz.
    xs = done ++ z::later /\
    EVERY (\i. ~is_terminator i.inst_opcode) done /\
    FOLDR (dft_exec_cons b C) OK done t = OK tz /\
    tz.vs_inst_idx = t.vs_inst_idx + LENGTH done /\
    dft_exec_suffix b C xs t = dft_exec_suffix b C [z] tz /\
    (is_terminator z.inst_opcode \/ ~(?u. step_inst b C z tz = OK u))
Proof
  Induct >> rpt gen_tac
  >- simp[dftIndexedExecTheory.dft_exec_suffix_def, passSimulationDefsTheory.terminates_def] >>
  strip_tac >>
  Cases_on `is_terminator h.inst_opcode \/ ~(?u. step_inst b C h t = OK u)`
  >- (qexistsl_tac [`[]`, `h`, `xs`, `t`] >> simp[] >>
      Cases_on `step_inst b C h t` >>
      gvs[dftIndexedExecTheory.dft_exec_suffix_def]) >>
  gvs[] >>
  rename1 `step_inst b C h t = OK u` >>
  qpat_x_assum `!b C t. _` (qspecl_then
    [`b`, `C`, `u with vs_inst_idx := SUC t.vs_inst_idx`] mp_tac) >>
  impl_tac
  >- gvs[dftIndexedExecTheory.dft_exec_suffix_def] >>
  strip_tac >>
  qexistsl_tac [`h::done`, `z`, `later`, `tz`] >>
  gvs[dftIndexedExecTheory.dft_exec_cons_def] >>
  simp[Once dftIndexedExecTheory.dft_exec_suffix_def] >>
  decide_tac
QED

Theorem native_remaining_frontier_cut[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\ dft_remaining_inv fn bb todo t /\
  PERM todo (done ++ z::later) /\
  FILTER (\i. i.inst_opcode = INVOKE \/ i = z) todo =
    FILTER (\i. i.inst_opcode = INVOKE \/ i = z) (done ++ z::later) ==>
  ?before after. todo = before ++ z::after /\
    EVERY (\i. ~is_terminator i.inst_opcode) before /\
    FILTER (\i. i.inst_opcode = INVOKE) (before ++ [z]) =
      FILTER (\i. i.inst_opcode = INVOKE) (done ++ [z]) /\
    (is_terminator z.inst_opcode ==> after = [])
Proof
  strip_tac >>
  `MEM z todo` by metis_tac[sortingTheory.PERM_MEM_EQ, MEM_APPEND, MEM] >>
  `?before after. todo = before ++ z::after` by metis_tac[MEM_SPLIT] >>
  pop_assum strip_assume_tac >>
  `ALL_DISTINCT todo` by
    (qpat_x_assum `dft_remaining_inv fn bb todo t` mp_tac >>
     simp[dft_remaining_inv_def]) >>
  `ALL_DISTINCT (before ++ z::after) /\
   ALL_DISTINCT (done ++ z::later)` by
    metis_tac[sortingTheory.ALL_DISTINCT_PERM] >>
  `~MEM z before /\ ~MEM z after /\ ~MEM z done` by
    (fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = INVOKE \/ i = z) before =
   FILTER (\i. i.inst_opcode = INVOKE \/ i = z) done` by
    (qpat_x_assum `FILTER _ todo = _` mp_tac >>
     simp[FILTER_APPEND_DISTRIB] >> strip_tac >>
     drule MEM_APPEND_lemma >> simp[MEM_FILTER]) >>
  `FILTER (\i. i.inst_opcode = INVOKE) before =
   FILTER (\i. i.inst_opcode = INVOKE) done` by
    (qpat_x_assum `FILTER _ before = FILTER _ done`
       (mp_tac o Q.AP_TERM `FILTER (\i. i.inst_opcode = INVOKE)`) >>
     simp[rich_listTheory.FILTER_FILTER, SF CONJ_ss]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) before` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     `id_before todo i z` by
       (simp[] >> irule id_before_append_member >> simp[]) >>
     irule dft_wf_order_nonterminator >>
     qexistsl_tac [`bb`, `fn`, `z`] >>
     fs[dft_remaining_inv_def, EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  qexistsl_tac [`before`, `after`] >> simp[FILTER_APPEND_DISTRIB] >>
  disch_tac >>
  `MEM z bb.bb_instructions /\
   (!x. MEM x after ==>
      id_before (MAP (\i. i.inst_id) bb.bb_instructions) z.inst_id x.inst_id)` by
    (qpat_x_assum `dft_remaining_inv fn bb todo t` mp_tac >>
     simp[] >> metis_tac[dft_remaining_inv_head_order]) >>
  Cases_on `after` >> simp[] >>
  metis_tac[dft_wf_order_nonterminator, MEM]
QED

Theorem native_schedule_frontier_calls:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv fn bb todo t /\ ~t.vs_call_ctx.cc_static /\
  dft_head_bubbles (\x y.
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo (done ++ z::later) /\
  EVERY (\i. ~is_terminator i.inst_opcode) done /\
  FOLDR (dft_exec_cons b C') OK done t = OK tz /\
  terminates (dft_exec_suffix b C' [z] tz) /\
  (is_terminator z.inst_opcode \/ ~(?u. step_inst b C' z tz = OK u)) ==>
  ?before after. todo = before ++ z::after /\
    EVERY (\i. ~is_terminator i.inst_opcode) before /\
    FILTER (\i. i.inst_opcode = INVOKE) (before ++ [z]) =
      FILTER (\i. i.inst_opcode = INVOKE) (done ++ [z]) /\
    (((?u. dft_exec_suffix b C' [z] tz = OK u) \/
      (?v u. dft_exec_suffix b C' [z] tz = IntRet v u)) ==> after = [])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_asmsub_abbrev_tac `dft_head_bubbles A todo (done ++ z::later)` >>
  `?residual. dft_remaining_inv fn bb residual tz /\
     ~tz.vs_call_ctx.cc_static /\ dft_head_bubbles A residual (z::later)` by
    metis_tac[native_bubbles_prefix_remaining] >>
  qpat_x_assum `dft_head_bubbles A residual _` mp_tac >>
  simp[Once dft_head_bubbles_cases] >> strip_tac >> gvs[] >>
  qpat_x_assum `dft_remaining_inv fn bb _ tz` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> disch_tac >>
  `inst_wf z /\ inst_shape_ok z` by
    (fs[dft_remaining_inv_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\x. ~dft_must_order x z) pre` by
    (fs[EVERY_MEM, Abbr `A`] >> metis_tac[]) >>
  `!call. call.inst_opcode = INVOKE ==> ~dft_gas_swap_pair z call` by
    metis_tac[native_selected_stopping_no_call_swap] >>
  `!x y. A x y ==> dft_gas_swap_pair x y` by
    (simp[Abbr `A`] >> metis_tac[dft_crossing_swap_pair]) >>
  `!x y. A x y ==> ~((x.inst_opcode = INVOKE \/ x = z) /\
                              (y.inst_opcode = INVOKE \/ y = z))` by
    (rpt strip_tac >>
     `dft_gas_swap_pair x y` by metis_tac[] >>
     fs[Abbr `A`] >>
     metis_tac[dft_gas_swap_pair_sym,
               dftGasInvCallPartnerTheory.inv_call_partner_class,
               id_before_distinct_endpoints, dftWfTheory.wf_fn_block_inst_ids_distinct]) >>
  `FILTER (\i. i.inst_opcode = INVOKE \/ i = z) todo =
   FILTER (\i. i.inst_opcode = INVOKE \/ i = z) (done ++ z::later)` by
    (irule native_bubbles_filter >> qexists_tac `A` >> simp[] >> metis_tac[]) >>
  `PERM todo (done ++ z::later)` by metis_tac[native_bubbles_perm] >>
  drule_all native_remaining_frontier_cut >> strip_tac >>
  qexistsl_tac [`before`, `after`] >> simp[] >> disch_tac >>
  `is_terminator z.inst_opcode` by
    (Cases_on `is_terminator z.inst_opcode` >> simp[] >>
     qpat_x_assum `(?u. dft_exec_suffix _ _ _ _ = OK u) \/ _` mp_tac >>
     Cases_on `step_inst b C' z tz` >>
     simp[dftIndexedExecTheory.dft_exec_suffix_def] >>
     metis_tac[dft_swap_nonterminator_no_intret]) >>
  metis_tac[]
QED

Theorem native_schedule_stopping_frontier:
  !body.
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv fn bb todo t /\ ~t.vs_call_ctx.cc_static /\
  dft_head_bubbles (\x y.
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo scheduled /\
  EVERY (from_block bb.bb_instructions) body /\
  LIST_REL (\h i. h.inst_id = i.inst_id) scheduled body /\
  t.vs_inst_idx = j /\
  terminates (exec_block b C' (bb with bb_instructions := REPLICATE j pad ++ body) t) ==>
  ?done z later before after tz.
    scheduled = done ++ z::later /\ todo = before ++ z::after /\
    EVERY (\i. ~is_terminator i.inst_opcode) done /\
    FOLDR (dft_exec_cons b C') OK done t = OK tz /\
    tz.vs_inst_idx = j + LENGTH done /\
    exec_block b C' (bb with bb_instructions := REPLICATE j pad ++ body) t =
      dft_exec_suffix b C' [z] tz /\
    (is_terminator z.inst_opcode \/ ~(?u. step_inst b C' z tz = OK u)) /\
    EVERY (\i. ~is_terminator i.inst_opcode) before /\
    FILTER (\i. i.inst_opcode = INVOKE) (before ++ [z]) =
      FILTER (\i. i.inst_opcode = INVOKE) (done ++ [z]) /\
    (((?u. exec_block b C' (bb with bb_instructions := REPLICATE j pad ++ body) t = OK u) \/
      (?v u. exec_block b C' (bb with bb_instructions := REPLICATE j pad ++ body) t = IntRet v u)) ==>
      after = [])
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `LIST_REL _ scheduled actual_body` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  `EVERY (\i. MEM i bb.bb_instructions) scheduled` by
    (drule native_bubbles_perm >> strip_tac >>
     fs[dft_remaining_inv_def, EVERY_MEM] >>
     metis_tac[sortingTheory.PERM_MEM_EQ]) >>
  `exec_block b C' (bb with bb_instructions := REPLICATE j pad ++ scheduled) t =
   exec_block b C' (bb with bb_instructions := REPLICATE j pad ++ actual_body) t` by
    (irule (cj 1 (SIMP_RULE pure_ss [LET_THM] native_normalized_block_observations)) >>
     simp[] >> qexists_tac `bb.bb_instructions` >> simp[]) >>
  `exec_block b C' (bb with bb_instructions := REPLICATE j pad ++ scheduled) t =
   dft_exec_suffix b C' scheduled t` by
    (irule dftIndexedExecTheory.dft_exec_suffix_boundary >> simp[DROP_APPEND]) >>
  `terminates (dft_exec_suffix b C' scheduled t)` by metis_tac[] >>
  drule native_suffix_stopping_decomposition >> strip_tac >>
  `?before after. todo = before ++ z::after /\
    EVERY (\i. ~is_terminator i.inst_opcode) before /\
    FILTER (\i. i.inst_opcode = INVOKE) (before ++ [z]) =
      FILTER (\i. i.inst_opcode = INVOKE) (done ++ [z]) /\
    (((?u. dft_exec_suffix b C' [z] tz = OK u) \/
      (?v u. dft_exec_suffix b C' [z] tz = IntRet v u)) ==> after = [])` by
    (irule native_schedule_frontier_calls >> metis_tac[]) >>
  qexistsl_tac [`done`, `z`, `later`, `before`, `after`, `tz`] >> metis_tac[]
QED

Theorem native_step_root_calls_nil[local]:
  FILTER (\(e,f,i,a). e = (p,d,i.inst_id) /\ i.inst_opcode = INVOKE)
    (dftGasFromListTraceDefs$trace_step p d b C fn inst s) = []
Proof
  simp[FILTER_EQ_NIL, EVERY_MEM, pairTheory.FORALL_PROD] >>
  rpt strip_tac >> rename1 `MEM ((p,d,call.inst_id),owner,call,a) _` >>
  `MEM (p,d,call.inst_id) (MAP FST
    (dftGasFromListTraceDefs$trace_step p d b C fn inst s))` by
    (simp[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
  metis_tac[trace_step_not_root]
QED

Theorem native_from_block_calls[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM h bi /\
  from_block bi i /\ h.inst_id = i.inst_id ==>
  FILTER (\i. i.inst_opcode = INVOKE) [h] =
    FILTER (\i. i.inst_opcode = INVOKE) [i]
Proof
  strip_tac >> fs[from_block_def]
  >- (`h = i` by metis_tac[all_distinct_map_mem_inj] >> simp[]) >>
  rename1 `i = flip_operands original` >>
  `h = original` by
    metis_tac[all_distinct_map_mem_inj, flip_operands_inst_id] >>
  `original.inst_opcode <> INVOKE` by
    (Cases_on `original.inst_opcode` >>
     gvs[is_flippable_def, is_commutative_def, is_comparator_def]) >>
  `(flip_operands original).inst_opcode <> INVOKE` by
    metis_tac[flip_operands_special_opcode, MEM] >>
  simp[]
QED

Theorem native_frontier_suffix_root_calls[local]:
  !done t body tz.
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  EVERY (\i. MEM i bi) (done ++ z::later) /\
  EVERY (from_block bi) body /\
  LIST_REL (\h i. h.inst_id = i.inst_id) (done ++ z::later) body /\
  DROP t.vs_inst_idx bt.bb_instructions = body /\
  EVERY (\i. ~is_terminator i.inst_opcode) done /\
  FOLDR (dft_exec_cons b C') OK done t = OK tz /\
  (is_terminator z.inst_opcode \/ ~(?u. step_inst b C' z tz = OK u)) ==>
  MAP FST (MAP (\(e,f,i,a). (i,a))
    (FILTER (\(e,f,i,a). e = (p,d,i.inst_id) /\ i.inst_opcode = INVOKE)
      (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))) =
    FILTER (\i. i.inst_opcode = INVOKE) (done ++ [z])
Proof
  Induct >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS)
  >- suspend "stop"
  >> suspend "next"
QED

Resume native_frontier_suffix_root_calls[stop]:
  rename1 `LIST_REL _ _ actual_body` >>
  Cases_on `actual_body` >> gvs[] >>
  rename1 `from_block bi actual` >>
  rename1 `DROP a.vs_inst_idx bt.bb_instructions = _` >>
  `a.vs_inst_idx < LENGTH bt.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `EL a.vs_inst_idx bt.bb_instructions = actual` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  drule_all native_from_block_observations >>
  disch_then (qspecl_then [`p`, `b`, `fn'`, `d`, `a`, `C'`] strip_assume_tac) >>
  drule_all native_from_block_calls >> disch_tac >>
  once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst b C' actual a` >> gs[] >>
  Cases_on `actual.inst_opcode = INVOKE` >>
  gs[native_step_root_calls_nil]
QED

Resume native_frontier_suffix_root_calls[next]:
  rename1 `LIST_REL _ _ actual_body` >>
  Cases_on `actual_body` >> fs[] >>
  rename1 `~is_terminator source.inst_opcode` >>
  rename1 `from_block bi actual` >>
  `t.vs_inst_idx < LENGTH bt.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `EL t.vs_inst_idx bt.bb_instructions = actual /\
   DROP (SUC t.vs_inst_idx) bt.bb_instructions = t'` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  drule_all native_from_block_observations >>
  disch_then (qspecl_then [`p`, `b`, `fn'`, `d`, `t`, `C'`] strip_assume_tac) >>
  drule_all native_from_block_calls >> disch_tac >>
  qpat_x_assum `dft_exec_cons _ _ _ _ _ = _` mp_tac >>
  Cases_on `step_inst b C' actual t` >>
  gs[dftIndexedExecTheory.dft_exec_cons_def] >> strip_tac >>
  rename1 `step_inst b C' actual t = OK mid` >>
  first_x_assum (qspecl_then
    [`mid with vs_inst_idx := SUC t.vs_inst_idx`, `tz`] mp_tac) >>
  (impl_tac >-
    (simp[] >> qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[])) >> disch_tac >>
  once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs] >>
  simp[get_instruction_def] >>
  Cases_on `actual.inst_opcode = INVOKE` >>
  gs[FILTER_APPEND_DISTRIB, native_step_root_calls_nil] >>
  Cases_on `source.inst_opcode = INVOKE` >> gs[]
QED

Finalise native_frontier_suffix_root_calls

Theorem native_frontier_root_calls:
  !body.
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  EVERY (\i. MEM i bi) (done ++ z::later) /\
  EVERY (from_block bi) body /\
  LIST_REL (\h i. h.inst_id = i.inst_id) (done ++ z::later) body /\
  bt = bb with bb_instructions := REPLICATE j pad ++ body /\
  t.vs_inst_idx = j /\
  EVERY (\i. ~is_terminator i.inst_opcode) done /\
  FOLDR (dft_exec_cons b C') OK done t = OK tz /\
  (is_terminator z.inst_opcode \/ ~(?u. step_inst b C' z tz = OK u)) /\
  FILTER (\i. i.inst_opcode = INVOKE) (before ++ [z]) =
    FILTER (\i. i.inst_opcode = INVOKE) (done ++ [z]) ==>
  MAP FST (MAP (\(e,f,i,a). (i,a))
    (FILTER (\(e,f,i,a). e = (p,d,i.inst_id) /\ i.inst_opcode = INVOKE)
      (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))) =
    FILTER (\i. i.inst_opcode = INVOKE) (before ++ [z])
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `LIST_REL _ _ actual_body` >>
  `DROP t.vs_inst_idx bt.bb_instructions = actual_body` by simp[DROP_APPEND] >>
  drule_all native_frontier_suffix_root_calls >> simp[]
QED

Theorem native_bubbles_terminator_last[local]:
  (!x y. A x y ==> ~is_terminator y.inst_opcode) ==>
  !src dst. dft_head_bubbles A src dst ==>
    (!x y. id_before src x y ==> ~is_terminator x.inst_opcode) ==>
    !x y. id_before dst x y ==> ~is_terminator x.inst_opcode
Proof
  strip_tac >> ho_match_mp_tac dft_head_bubbles_strongind >>
  simp[id_before_cons] >> rpt gen_tac >> strip_tac >> strip_tac >>
  rename1 `dft_head_bubbles A (pre ++ post) rest` >>
  `!x z. id_before (pre ++ post) x z ==> ~is_terminator x.inst_opcode` by
    (gvs[dftSsaPreserveTheory.id_before_append, id_before_cons] >> metis_tac[]) >>
  `!x z. id_before rest x z ==> ~is_terminator x.inst_opcode` by metis_tac[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `pre` >> gvs[EVERY_MEM]
  >- (drule native_bubbles_perm >>
      disch_then (assume_tac o MATCH_MP sortingTheory.PERM_MEM_EQ) >>
      metis_tac[id_before_cons]) >>
  metis_tac[]
QED

Theorem native_success_suffix_gas_coverage[local]:
  !xs s bt.
    DROP s.vs_inst_idx bt.bb_instructions = xs /\
    (!x y. id_before xs x y ==> ~is_terminator x.inst_opcode) /\
    ((?u. exec_block b C bt s = OK u) \/
     (?v u. exec_block b C bt s = IntRet v u)) ==>
    !i. MEM i xs /\ i.inst_opcode = GAS ==>
      MEM (p,d,i.inst_id) (MAP FST (trace_gas
        (dftGasFromListTraceDefs$trace_block p d b C fn bt s)))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_inst_idx < LENGTH bt.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]) >>
  `EL s.vs_inst_idx bt.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bt.bb_instructions = xs` by
    metis_tac[rich_listTheory.DROP_CONS_EL, CONS_11] >>
  `get_instruction bt s.vs_inst_idx = SOME h` by simp[get_instruction_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule dftGasFromListTraceDefsTheory.trace_block_visit >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[trace_gas_def, MAP_FLAT, MAP_APPEND] >>
  Cases_on `i = h`
  >- gvs[visit_gas_def] >>
  `MEM i xs /\ ~is_terminator h.inst_opcode` by
    metis_tac[MEM, id_before_cons] >>
  `?u. step_inst b C h s = OK u /\
    ((?t. exec_block b C bt (u with vs_inst_idx := SUC s.vs_inst_idx) = OK t) \/
     (?v t. exec_block b C bt (u with vs_inst_idx := SUC s.vs_inst_idx) = IntRet v t))` by
    (qpat_x_assum `(?u. exec_block _ _ _ _ = OK u) \/ _`
       (mp_tac o PURE_ONCE_REWRITE_RULE [exec_block_def]) >> simp[] >>
     Cases_on `step_inst b C h s` >> simp[] >>
     metis_tac[dft_swap_nonterminator_no_intret]) >>
  simp[] >>
  `MEM (p,d,i.inst_id) (MAP FST (trace_gas
      (dftGasFromListTraceDefs$trace_block p d b C fn bt
        (u with vs_inst_idx := SUC s.vs_inst_idx))))` by
    (first_x_assum irule >> simp[] >> metis_tac[id_before_cons]) >>
  gvs[trace_gas_def, MAP_FLAT]
QED

Theorem native_inventory_success_gas_coverage:
  !body.
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv fn bb todo t /\
  dft_head_bubbles (\x y.
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo scheduled /\
  EVERY (from_block bb.bb_instructions) body /\
  LIST_REL (\h i. h.inst_id = i.inst_id) scheduled body /\
  bt = bb with bb_instructions := REPLICATE j pad ++ body /\
  t.vs_inst_idx = j /\
  ((?u. exec_block b C' bt t = OK u) \/
   (?v u. exec_block b C' bt t = IntRet v u)) ==>
  !i. MEM i todo /\ i.inst_opcode = GAS ==>
    MEM (p,d,i.inst_id) (MAP FST (trace_gas
      (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)))
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `LIST_REL _ scheduled actual_body` >>
  `PERM todo scheduled` by metis_tac[native_bubbles_perm] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  `EVERY (\i. MEM i bb.bb_instructions) scheduled` by
    (fs[dft_remaining_inv_def, EVERY_MEM] >>
     metis_tac[sortingTheory.PERM_MEM_EQ]) >>
  `!x y. id_before todo x y ==> ~is_terminator x.inst_opcode` by
    (rpt strip_tac >>
     `MEM x bb.bb_instructions /\
      id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id` by
       (fs[dft_remaining_inv_def, EVERY_MEM] >> metis_tac[id_before_mem]) >>
     metis_tac[dft_wf_order_nonterminator]) >>
  `!x y. id_before scheduled x y ==> ~is_terminator x.inst_opcode` by
    (drule_at (Pat `dft_head_bubbles _ _ _`) native_bubbles_terminator_last >>
     simp[dft_must_order_def] >> metis_tac[]) >>
  `exec_block b C' (bb with bb_instructions := REPLICATE j pad ++ scheduled) t =
     exec_block b C' bt t /\
   trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn'
     (bb with bb_instructions := REPLICATE j pad ++ scheduled) t) =
     trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)` by
    (qpat_x_assum `bt = _` SUBST_ALL_TAC >>
     mp_tac (Q.INST [`bi` |-> `bb.bb_instructions`]
       (SIMP_RULE pure_ss [LET_THM] native_normalized_block_observations)) >>
     disch_then (qspecl_then [`scheduled`, `actual_body`, `t`] mp_tac) >>
     simp[] >> disch_then (qspecl_then [`b`, `C'`, `fn'`, `p`, `d`] mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `MEM i scheduled` by metis_tac[sortingTheory.PERM_MEM_EQ] >>
  qpat_x_assum `trace_gas _ = trace_gas _` (fn th => rewrite_tac[GSYM th]) >>
  irule native_success_suffix_gas_coverage >> simp[DROP_APPEND] >> metis_tac[]
QED

Theorem native_inventory_observation_origin:
  !s kw.
    MEM kw (trace_gas
      (dftGasFromListTraceDefs$trace_block p d b C' fn' bt s)) ==>
    ?i a.
      MEM i (DROP s.vs_inst_idx bt.bb_instructions) /\
      MEM ((p,d,i.inst_id),fn',i,a)
        (dftGasFromListTraceDefs$trace_block p d b C' fn' bt s) /\
      ((i.inst_opcode = GAS /\ FST kw = (p,d,i.inst_id)) \/
       (i.inst_opcode = INVOKE /\
        MEM kw (trace_gas
          (dftGasFromListTraceDefs$trace_step p d b C' fn' i a))))
Proof
  measureInduct_on `LENGTH bt.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> disch_tac >> gvs[] >> gen_tac >>
  Cases_on `get_instruction bt s.vs_inst_idx`
  >- simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs)] >>
  rename1 `get_instruction bt s.vs_inst_idx = SOME inst` >>
  `s.vs_inst_idx < LENGTH bt.bb_instructions /\
   EL s.vs_inst_idx bt.bb_instructions = inst` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `DROP s.vs_inst_idx bt.bb_instructions =
     inst :: DROP (SUC s.vs_inst_idx) bt.bb_instructions` by
    metis_tac[rich_listTheory.DROP_CONS_EL] >>
  drule dftGasFromListTraceDefsTheory.trace_block_visit >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[] >> strip_tac
  >- (qexistsl_tac [`inst`, `s`] >>
      Cases_on `inst.inst_opcode = GAS` >> gvs[visit_gas_def])
  >- (qexistsl_tac [`inst`, `s`] >> simp[] >>
      Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
      gvs[dftGasFromListTraceDefsTheory.trace_step_noninvoke]) >>
  Cases_on `step_inst b C' inst s` >> gvs[] >>
  rename1 `step_inst b C' inst s = OK u` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  simp[] >>
  disch_then (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then drule >> strip_tac >> metis_tac[]
QED

Theorem native_inventory_root_success[local]:
  !s i a.
    ((?u. exec_block b C' bt s = OK u) \/
     (?v u. exec_block b C' bt s = IntRet v u)) /\
    MEM ((p,d,i.inst_id),fn',i,a)
      (dftGasFromListTraceDefs$trace_block p d b C' fn' bt s) ==>
    ((?u. step_inst b C' i a = OK u) \/
     (?v u. step_inst b C' i a = IntRet v u))
Proof
  measureInduct_on `LENGTH bt.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `get_instruction bt s.vs_inst_idx`
  >- (qpat_x_assum `MEM _ _` mp_tac >>
      simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs)]) >>
  rename1 `get_instruction bt s.vs_inst_idx = SOME inst` >>
  `~MEM ((p,d,i.inst_id),fn',i,a)
      (dftGasFromListTraceDefs$trace_step p d b C' fn' inst s)` by
    (spose_not_then assume_tac >>
     `MEM (p,d,i.inst_id) (MAP FST
       (dftGasFromListTraceDefs$trace_step p d b C' fn' inst s))` by
       (simp[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
     metis_tac[trace_step_not_root]) >>
  qpat_x_assum `MEM _ (dftGasFromListTraceDefs$trace_block _ _ _ _ _ _ _)` mp_tac >>
  pure_once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs] >>
  simp[MEM_APPEND] >> strip_tac
  >- (gvs[] >>
      qpat_x_assum `exec_block b C' bt _ = _` mp_tac >>
      simp[Once run_block_non_phis_def] >>
      Cases_on `step_inst b C' i a` >> simp[]) >>
  Cases_on `step_inst b C' inst s` >> gvs[] >>
  rename1 `step_inst b C' inst s = OK mid` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  qpat_x_assum `!y. _` (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- gvs[get_instruction_def]) >>
  disch_then (qspec_then `mid with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp_tac bool_ss [venom_state_accfupds, combinTheory.K_THM] >>
  disch_then (qspecl_then [`i`, `a`] mp_tac) >>
  (impl_tac >- (conj_tac >- (qpat_x_assum `exec_block b C' bt s = _` mp_tac >>
    simp[Once run_block_non_phis_def] >> metis_tac[]) >> simp[])) >>
  simp[]
QED

Theorem native_inventory_root_owner[local]:
  !s f i a. MEM ((p,d,i.inst_id),f,i,a)
    (dftGasFromListTraceDefs$trace_block p d b C' fn' bt s) ==> f = fn'
Proof
  measureInduct_on `LENGTH bt.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  Cases_on `get_instruction bt s.vs_inst_idx`
  >- (qpat_x_assum `MEM _ _` mp_tac >>
      pure_once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs] >> simp[]) >>
  rename1 `get_instruction bt s.vs_inst_idx = SOME inst` >>
  `~MEM ((p,d,i.inst_id),f,i,a)
      (dftGasFromListTraceDefs$trace_step p d b C' fn' inst s)` by
    (spose_not_then assume_tac >>
     `MEM (p,d,i.inst_id) (MAP FST
       (dftGasFromListTraceDefs$trace_step p d b C' fn' inst s))` by
       (simp[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
     metis_tac[trace_step_not_root]) >>
  qpat_x_assum `MEM _ (dftGasFromListTraceDefs$trace_block _ _ _ _ _ _ _)` mp_tac >>
  pure_once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs] >>
  simp[MEM_APPEND] >> strip_tac >>
  Cases_on `step_inst b C' inst s` >> gvs[] >>
  rename1 `step_inst b C' inst s = OK u` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- gvs[get_instruction_def]) >>
  disch_then (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> metis_tac[]
QED

(* Quotation macros only: these introduce no logical constants or selectors. *)
val native_inventory_Dq = ``\q r f f' cs ct K S U.
  let Ochild = trace_gas (dftGasFromListTraceDefs$trace_blocks q r b C' f' ct);
      Tchild = run_blocks b C' f' ct
  in let Mchild = MAP (ALOOKUP Ochild) K in
    ALL_DISTINCT K /\ EVERY (later_region q r) K /\ LENGTH K = LENGTH S /\
    PERM (MAP THE (FILTER IS_SOME Mchild) ++ U) ct.vs_gas_readings /\
    (!v u. Tchild = IntRet v u ==> EVERY IS_SOME Mchild /\ U = u.vs_gas_readings) /\
    (!g tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mchild g ==>
      (!n. ?k. k <= LENGTH K /\
        trace_gas (dftGasFromListTraceDefs$trace_blocks q r n C f
          (cs with vs_gas_readings := g ++ tail)) = ZIP (TAKE k K, TAKE k g) /\
        gas_events_blocks n C f (cs with vs_gas_readings := g ++ tail) = TAKE k S) /\
      ((?n. terminates (run_blocks n C f (cs with vs_gas_readings := g ++ tail))) ==>
       terminates (run_blocks b C f (cs with vs_gas_readings := g ++ tail)) /\
       dft_res_rel
         (restore_result [] (run_blocks b C f (cs with vs_gas_readings := g ++ tail)))
         (restore_result [] Tchild) /\
       (!v u. Tchild = IntRet v u ==>
         gas_events_blocks b C f (cs with vs_gas_readings := g ++ tail) = S /\
         residual_result tail Tchild
           (run_blocks b C f (cs with vs_gas_readings := g ++ tail)))))``;

val native_inventory_IHq = ``!f f' x q r.
  LIST_REL (\h h'. h' = dft_fn h) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  MEM f C.ctx_functions /\ f' = dft_fn f /\ dft_fn_rel f f' /\
  strict_dom_vars_defined f x /\ fn_reachable f x.vs_current_bb /\
  ctx_labels_bound C x.vs_labels /\ ctx_labels_bound C' x.vs_labels /\
  ~x.vs_call_ctx.cc_static /\ terminates (run_blocks b C' f' x) /\
  gas_count_blocks b C' f' x <= LENGTH x.vs_gas_readings ==>
  ?K S U. ^native_inventory_Dq q r f f' x x K S U``;

val native_inventory_Aq = ``\i a nm ops args cf cf' cs ct.
  i.inst_opcode = INVOKE /\
  MEM ((p,d,i.inst_id),fn',i,a)
    (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) /\
  decode_invoke i = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME cf /\
  lookup_function nm C'.ctx_functions = SOME cf' /\
  MEM cf C.ctx_functions /\ MEM cf' C'.ctx_functions /\
  cf' = dft_fn cf /\ dft_fn_rel cf cf' /\
  eval_operands ops a = SOME args /\ setup_callee cf args a = SOME cs /\
  setup_callee cf' args a = SOME ct /\ cs = ct /\
  fn_entry_label cf = SOME cs.vs_current_bb /\
  strict_dom_vars_defined cf cs /\ fn_reachable cf cs.vs_current_bb /\
  ctx_labels_bound C cs.vs_labels /\ ctx_labels_bound C' cs.vs_labels /\
  ~cs.vs_call_ctx.cc_static /\ terminates (run_blocks b C' cf' ct) /\
  gas_count_blocks b C' cf' ct <= LENGTH ct.vs_gas_readings``;

val native_inventory_Rq = ``\obs i Kc Sc cert.
  if i.inst_opcode = INVOKE then
    ?a nm ops args cf cf' cs ct Uc.
      cert = SOME (a,nm,ops,args,cf,cf',cs,ct,Uc) /\
      ^native_inventory_Aq i a nm ops args cf cf' cs ct /\
      ^native_inventory_Dq ((d,i.inst_id)::p) d cf cf' cs ct Kc Sc Uc /\
      MAP (ALOOKUP (trace_gas (dftGasFromListTraceDefs$trace_blocks
        ((d,i.inst_id)::p) d b C' cf' ct))) Kc = MAP (ALOOKUP obs) Kc
  else cert = NONE /\
    (if i.inst_opcode = GAS then
       Kc = [(p,d,i.inst_id)] /\ Sc = [(fn.fn_name,i.inst_id)]
     else Kc = [] /\ Sc = [])``;

Theorem native_selected_child_return_replay:
  !K.
  ^native_inventory_Rq
    (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))
    i Kc Sc (SOME (a,nm,ops,args,cf,cf',cs,ct,Uc)) /\
  i.inst_opcode = INVOKE /\ ctx_inst_ids_distinct C' /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (DROP t.vs_inst_idx bt.bb_instructions)) /\
  K = Kpre ++ Kc ++ Kpost /\ g = gpre ++ gc ++ gpost /\
  LENGTH Kpre = LENGTH gpre /\ LENGTH Kc = LENGTH gc /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (MAP (ALOOKUP (trace_gas
      (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))) K) g /\
  run_blocks n C cf (cs with vs_gas_readings := gc ++ tailc) = IntRet ret u ==>
  ?v.
    run_blocks b C' cf' ct = IntRet ret v /\
    run_blocks b C cf (cs with vs_gas_readings := gc ++ tailc) = IntRet ret u /\
    trace_gas (dftGasFromListTraceDefs$trace_blocks ((d,i.inst_id)::p) d n C cf
      (cs with vs_gas_readings := gc ++ tailc)) = ZIP (Kc,gc) /\
    gas_events_blocks n C cf (cs with vs_gas_readings := gc ++ tailc) = Sc /\
    u.vs_gas_readings = tailc /\
    (u with vs_gas_readings := []) = (v with vs_gas_readings := []) /\
    ev_blocks
      (\key. case ALOOKUP
        (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) ++
          ZIP (K,g)) key of NONE => 0w | SOME w => w)
      ((d,i.inst_id)::p) d b C' cf' (ct with vs_gas_readings := []) =
      IntRet ret (u with vs_gas_readings := [])
Proof
  gen_tac >> BETA_TAC >> strip_tac >>
  qpat_x_assum `(if _ then _ else _)` mp_tac >>
  asm_simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  gvs[MAP_APPEND, LIST_REL_APPEND_EQ] >>
  qpat_x_assum `!g' tail. LIST_REL _ _ g' ==> _`
    (qspecl_then [`gc`, `tailc`] mp_tac) >>
  simp[] >> strip_tac >>
  `?n. terminates (run_blocks n C cf (cs with vs_gas_readings := gc ++ tailc))` by
    (qexists_tac `n` >> simp[passSimulationDefsTheory.terminates_def]) >>
  `(?v. run_blocks b C' (dft_fn cf) cs = IntRet ret v) /\
   run_blocks b C cf (cs with vs_gas_readings := gc ++ tailc) = IntRet ret u /\
   trace_gas (dftGasFromListTraceDefs$trace_blocks ((d,i.inst_id)::p) d n C cf
     (cs with vs_gas_readings := gc ++ tailc)) = ZIP (Kc,gc) /\
   gas_events_blocks n C cf (cs with vs_gas_readings := gc ++ tailc) = Sc /\
   u.vs_gas_readings = tailc` by
    (irule returning_child_packet_exhaustion >> simp[] >>
     conj_tac >- metis_tac[] >>
     reverse conj_tac >- metis_tac[] >>
     gen_tac >> qpat_x_assum `!n'. ?k. _ /\ _ /\ _`
       (qspec_then `f` strip_assume_tac) >>
     qexists_tac `DROP k Sc` >> simp[]) >>
  `u with vs_gas_readings := [] = v with vs_gas_readings := []` by
    (qpat_x_assum `(?n. terminates _) ==> _` mp_tac >>
     simp[restore_result_def, dft_res_rel_def] >> metis_tac[]) >>
  qexists_tac `v` >> simp[] >>
  qmatch_goalsub_abbrev_tac `ev_blocks orc` >>
  `trace_agrees orc (dftGasFromListTraceDefs$trace_blocks
     ((d,i.inst_id)::p) d b C' (dft_fn cf) cs)` by
    (simp_tac pure_ss [Abbr `orc`] >>
     drule_all native_inventory_child_agreement >>
     simp_tac pure_ss [LET_THM] >> metis_tac[]) >>
  drule (cj 3 dftGasFromListReplayTheory.trace_replay) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[restore_rel_cases]
QED

Theorem native_frontier_mask_inventory:
  !body.
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv fn bb todo t /\
  dft_head_bubbles (\x y.
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo scheduled /\
  EVERY (from_block bb.bb_instructions) body /\
  LIST_REL (\h i. h.inst_id = i.inst_id) scheduled body /\
  bt = bb with bb_instructions := REPLICATE j pad ++ body /\ t.vs_inst_idx = j /\
  ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
  ~t.vs_call_ctx.cc_static /\ terminates (exec_block b C' bt t) /\
  gas_count_block b C' bt t <= LENGTH t.vs_gas_readings /\
  (?rest. todo = P ++ rest) /\
  MAP FST (MAP (\(e,f,i,a). (i,a))
    (FILTER (\(e,f,i,a). e = (p,d,i.inst_id) /\ i.inst_opcode = INVOKE)
      (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))) =
      FILTER (\i. i.inst_opcode = INVOKE) P /\
  (((?u. exec_block b C' bt t = OK u) \/ (?v u. exec_block b C' bt t = IntRet v u)) ==>
      P = todo) /\
  ^native_inventory_IHq ==>
  let V = dftGasFromListTraceDefs$trace_block p d b C' fn' bt t in
  let obs = trace_gas V in
  ?key_rows site_rows certs.
    LENGTH key_rows = LENGTH P /\ LENGTH site_rows = LENGTH P /\ LENGTH certs = LENGTH P /\
    (!h. h < LENGTH P ==>
      ^native_inventory_Rq obs (EL h P) (EL h key_rows) (EL h site_rows) (EL h certs)) /\
    (let K = FLAT key_rows; S = FLAT site_rows in
     let M = MAP (ALOOKUP obs) K;
         U = MAP SND (FILTER (\kw. ~MEM (FST kw) K) obs) ++ DROP (LENGTH obs) t.vs_gas_readings
     in ALL_DISTINCT K /\
        EVERY (block_region p d (MAP (\i. i.inst_id) todo)) K /\ LENGTH K = LENGTH S /\
        PERM (MAP THE (FILTER IS_SOME M) ++ U) t.vs_gas_readings /\
        (!u. exec_block b C' bt t = OK u ==> EVERY IS_SOME M /\ U = u.vs_gas_readings) /\
        (!v u. exec_block b C' bt t = IntRet v u ==>
           EVERY IS_SOME M /\ U = u.vs_gas_readings))
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp_tac pure_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `trace_gas V` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (DROP t.vs_inst_idx bt.bb_instructions))` by
    suspend "suffix_ids" >>
  `!i. MEM i P ==> ?Kc Sc cert. ^native_inventory_Rq (trace_gas V) i Kc Sc cert` by
    suspend "pointwise" >>
  qpat_x_assum `!i. MEM i P ==> ?Kc Sc cert. _` mp_tac >>
  CONV_TAC (LAND_CONV (SIMP_CONV pure_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM])) >>
  disch_then (qx_choose_then `kr` (qx_choose_then `sr` (qx_choose_then `cr` assume_tac))) >>
  qexistsl_tac [`MAP kr P`, `MAP sr P`, `MAP cr P`] >>
  simp_tac bool_ss [LENGTH_MAP] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. MEM i P ==> _` (qspec_then `EL h P` mp_tac) >>
      simp[EL_MEM, EL_MAP, SKOLEM_THM]) >>
  suspend "accounting"
QED

Resume native_frontier_mask_inventory[suffix_ids]:
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) todo)` by
    (irule ALL_DISTINCT_MAP_INJ >>
     fs[dft_remaining_inv_def, EVERY_MEM] >>
     rpt strip_tac >>
     drule dftCorrectnessTheory.all_distinct_map_mem_inj >>
     disch_then irule >> metis_tac[MEM_APPEND]) >>
  `PERM todo scheduled` by metis_tac[native_bubbles_perm] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) scheduled)` by
    metis_tac[PERM_MAP, ALL_DISTINCT_PERM] >>
  rename1 `LIST_REL _ scheduled actual_body` >>
  `MAP (\i. i.inst_id) scheduled = MAP (\i. i.inst_id) actual_body` by
    (irule LIST_EQ >> fs[LIST_REL_EL_EQN, EL_MAP]) >>
  gvs[DROP_APPEND]
QED
Resume native_frontier_mask_inventory[pointwise]:
  rpt gen_tac >> strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (`?f a. MEM ((p,d,i.inst_id),f,i,a) V` by
        (qpat_x_assum `MAP FST _ = _` mp_tac >>
         disch_then (mp_tac o Q.AP_TERM `MEM i`) >>
         simp[MEM_FILTER, MEM_MAP] >>
         disch_then (qx_choose_then `v` strip_assume_tac) >>
         PairCases_on `v` >> gvs[] >>
         rename1 `MEM visit V` >> PairCases_on `visit` >> gvs[] >> metis_tac[]) >>
      `f = fn'` by
        (irule native_inventory_root_owner >> metis_tac[markerTheory.Abbrev_def]) >>
      qpat_x_assum `f = fn'` SUBST_ALL_TAC >>
      `?nm ops args cf cf' cs ct. ^native_inventory_Aq i a nm ops args cf cf' cs ct` by
        (BETA_TAC >> irule native_inventory_call_admissible >>
         gvs[markerTheory.Abbrev_def] >> metis_tac[]) >>
      pop_assum (strip_assume_tac o BETA_RULE) >>
      `?Kc Sc Uc. ^native_inventory_Dq ((d,i.inst_id)::p) d cf cf' cs ct Kc Sc Uc` by
        (BETA_TAC >>
         qpat_x_assum `!f f' x q r. _`
           (qspecl_then [`cf`, `cf'`, `cs`] mp_tac) >>
         disch_then (qspecl_then [`((d,i.inst_id)::p)`, `d`] mp_tac) >>
         impl_tac >- gvs[] >> simp[]) >>
      pop_assum (fn th => assume_tac th >>
        strip_assume_tac (SIMP_RULE std_ss [LET_THM] (BETA_RULE th))) >>
      `MAP (ALOOKUP (trace_gas (dftGasFromListTraceDefs$trace_blocks
          ((d,i.inst_id)::p) d b C' cf' ct))) Kc =
       MAP (ALOOKUP (trace_gas V)) Kc` by
        (simp_tac pure_ss [Abbr `V`] >>
         irule native_inventory_child_lookup >> metis_tac[]) >>
      qexistsl_tac [`Kc`, `Sc`, `SOME (a,nm,ops,args,cf,cf',cs,ct,Uc)`] >>
      BETA_TAC >> gvs[]) >>
  simp_tac pure_ss [] >>
  Cases_on `i.inst_opcode = GAS` >>
  simp[] >> metis_tac[]
QED
Resume native_frontier_mask_inventory[accounting]:
  qpat_x_assum `!f f' x q r. _` kall_tac >>
  simp_tac pure_ss [LET_THM] >>
  `!i. MEM i P ==> ALL_DISTINCT (kr i) /\
     EVERY (block_region p d [i.inst_id]) (kr i) /\
     LENGTH (kr i) = LENGTH (sr i)` by suspend "row_shape" >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) P)` by suspend "prefix_ids" >>
  `ALL_DISTINCT (FLAT (MAP kr P)) /\
   EVERY (block_region p d (MAP (\i. i.inst_id) P)) (FLAT (MAP kr P)) /\
   LENGTH (FLAT (MAP kr P)) = LENGTH (FLAT (MAP sr P))` by
    suspend "flat_shape" >>
  `ALL_DISTINCT (MAP FST (trace_gas V))` by suspend "obs_distinct" >>
  `LENGTH (trace_gas V) = gas_count_block b C' bt t /\
   MAP SND (trace_gas V) ++ DROP (LENGTH (trace_gas V)) t.vs_gas_readings =
     t.vs_gas_readings` by suspend "obs_readings" >>
  simp[] >> conj_tac
  >- (fs[EVERY_MEM] >> rpt strip_tac >> irule block_region_mono >>
      qexists_tac `MAP (\i. i.inst_id) P` >>
      simp[] >> metis_tac[MEM_MAP, MEM_APPEND]) >>
  conj_tac
  >- (`PERM
         (MAP THE (FILTER IS_SOME (MAP (ALOOKUP (trace_gas V)) (FLAT (MAP kr P)))) ++
          MAP SND (FILTER (\kw. ~MEM (FST kw) (FLAT (MAP kr P))) (trace_gas V)))
         (MAP SND (trace_gas V))` by
        (irule native_inventory_lookup_partition >> simp[]) >>
      qpat_x_assum `_ ++ DROP _ _ = t.vs_gas_readings`
        (fn th => CONV_TAC (RAND_CONV (REWR_CONV (GSYM th)))) >>
      simp[APPEND_ASSOC, PERM_APPEND_IFF]) >>
  suspend "success_accounting"
QED
Resume native_frontier_mask_inventory[row_shape]:
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!i. MEM i P ==> _` (qspec_then `i` mp_tac) >>
  simp_tac bool_ss [LET_THM] >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (simp[] >> strip_tac >> gvs[] >>
      fs[EVERY_MEM] >> rpt strip_tac >>
      first_x_assum drule >>
      rename1 `later_region _ _ key` >> PairCases_on `key` >>
      metis_tac[later_region_frame, below_call_region, MEM]) >>
  Cases_on `i.inst_opcode = GAS` >> simp[block_region_def]
QED
Resume native_frontier_mask_inventory[prefix_ids]:
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) todo)` by
    (irule ALL_DISTINCT_MAP_INJ >>
     fs[dft_remaining_inv_def, EVERY_MEM] >>
     rpt strip_tac >>
     drule dftCorrectnessTheory.all_distinct_map_mem_inj >>
     disch_then irule >> metis_tac[MEM_APPEND]) >>
  qpat_x_assum `?rest. todo = P ++ rest` strip_assume_tac >>
  gvs[MAP_APPEND, ALL_DISTINCT_APPEND]
QED
Resume native_frontier_mask_inventory[flat_shape]:
  qpat_x_assum `!i. MEM i P ==> ALL_DISTINCT _ /\ _` mp_tac >>
  qpat_x_assum `ALL_DISTINCT (MAP (\i. i.inst_id) P)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `P` >> Induct >> simp[] >>
  rpt gen_tac >> strip_tac >> disch_tac >>
  `ALL_DISTINCT (kr h) /\ EVERY (block_region p d [h.inst_id]) (kr h) /\
   LENGTH (kr h) = LENGTH (sr h)` by metis_tac[] >>
  `ALL_DISTINCT (FLAT (MAP kr P)) /\
   EVERY (block_region p d (MAP (\i. i.inst_id) P)) (FLAT (MAP kr P)) /\
   LENGTH (FLAT (MAP kr P)) = LENGTH (FLAT (MAP sr P))` by
    (first_x_assum irule >> metis_tac[]) >>
  simp[ALL_DISTINCT_APPEND, EVERY_APPEND] >>
  rpt conj_tac >- (rpt strip_tac >>
    `block_region p d [h.inst_id] e` by metis_tac[EVERY_MEM] >>
    `block_region p d (MAP (\i. i.inst_id) P) e` by metis_tac[EVERY_MEM] >>
    metis_tac[block_regions_disjoint, MEM]) >>
  fs[EVERY_MEM] >> rpt strip_tac >> irule block_region_mono >>
  first_x_assum drule >> strip_tac >> goal_assum (drule_at Any) >> simp[]
QED
Resume native_frontier_mask_inventory[obs_distinct]:
  simp_tac pure_ss [Abbr `V`] >> irule trace_gas_names_distinct >>
  irule native_inventory_suffix_distinct >> simp[] >>
  qpat_x_assum `o1_ctx_shape C'` mp_tac >>
  simp_tac bool_ss [o1_ctx_shape_def, ctx_inst_ids_distinct_def] >>
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all venomWfPropsTheory.all_distinct_flat_map_member >>
  BETA_TAC >> strip_tac >>
  drule_all venomWfPropsTheory.all_distinct_flat_map_member >> simp[]
QED
Resume native_frontier_mask_inventory[obs_readings]:
  simp_tac pure_ss [Abbr `V`, cj 2 trace_gas_lengths] >>
  simp_tac pure_ss [cj 2 trace_gas_readings, gas_prefix_def] >>
  simp[TAKE_APPEND1]
QED
Resume native_frontier_mask_inventory[success_accounting]:
  `!u. (exec_block b C' bt t = OK u \/
        (?v. exec_block b C' bt t = IntRet v u)) ==>
    EVERY IS_SOME (MAP (ALOOKUP (trace_gas V)) (FLAT (MAP kr P))) /\
    MAP SND (FILTER (\kw. ~MEM (FST kw) (FLAT (MAP kr P))) (trace_gas V)) ++
      DROP (LENGTH (trace_gas V)) t.vs_gas_readings = u.vs_gas_readings`
    suffices_by metis_tac[] >>
  gen_tac >> disch_tac >>
  `P = todo` by metis_tac[] >>
  `!i a nm ops args cf cs Uc.
    MEM i P /\ i.inst_opcode = INVOKE /\
    cr i = SOME (a,nm,ops,args,cf,dft_fn cf,cs,cs,Uc) ==>
    EVERY IS_SOME (MAP (ALOOKUP (trace_gas V)) (kr i)) /\
    FILTER (\kw. ~MEM (FST kw) (kr i))
      (trace_gas (dftGasFromListTraceDefs$trace_blocks
        ((d,i.inst_id)::p) d b C' (dft_fn cf) cs)) = []` by
    suspend "success_children" >>
  `EVERY IS_SOME (MAP (ALOOKUP (trace_gas V)) (FLAT (MAP kr P)))` by
    suspend "selected_coverage" >>
  `FILTER (\kw. ~MEM (FST kw) (FLAT (MAP kr P))) (trace_gas V) = []` by
    suspend "actual_coverage" >>
  qpat_x_assum `bt = _` kall_tac >>
  simp[] >>
  mp_tac (cj 2 gas_count_suffix) >>
  disch_then (qspecl_then [`b`, `C'`, `bt`, `t`] mp_tac) >>
  Cases_on `exec_block b C' bt t` >> gvs[gas_count_suffix_def]
QED
Resume native_frontier_mask_inventory[selected_coverage]:
  qpat_x_assum `!i. MEM i P ==> ALL_DISTINCT _ /\ _` kall_tac >>
  pure_rewrite_tac[EVERY_MAP, EVERY_FLAT, EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM i P` >>
  qpat_assum `!i. MEM i P ==> _` (qspec_then `i` mp_tac) >>
  simp_tac bool_ss [LET_THM] >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (simp[] >> strip_tac >> gvs[] >>
      qpat_assum `!i a nm ops args cf cs Uc. _` drule_all >>
      simp_tac pure_ss [EVERY_MAP, EVERY_MEM] >> strip_tac >>
      first_assum MATCH_ACCEPT_TAC) >>
  Cases_on `i.inst_opcode = GAS` >> simp[] >> strip_tac >> gvs[] >>
  `MEM (p,d,i.inst_id) (MAP FST (trace_gas V))` by
    (simp_tac pure_ss [Abbr `V`] >>
     irule native_inventory_success_gas_coverage >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  metis_tac[alistTheory.ALOOKUP_NONE, optionTheory.NOT_IS_SOME_EQ_NONE]
QED
Resume native_frontier_mask_inventory[actual_coverage]:
  simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
  `?i a. MEM i (DROP t.vs_inst_idx bt.bb_instructions) /\
    MEM ((p,d,i.inst_id),fn',i,a) V /\
    ((i.inst_opcode = GAS /\ FST kw = (p,d,i.inst_id)) \/
     (i.inst_opcode = INVOKE /\ MEM kw (trace_gas
       (dftGasFromListTraceDefs$trace_step p d b C' fn' i a))))` by
    (simp_tac pure_ss [Abbr `V`] >>
     irule native_inventory_observation_origin >> metis_tac[markerTheory.Abbrev_def])
  >- suspend "actual_gas"
  >> suspend "actual_call"
QED
Resume native_frontier_mask_inventory[success_children]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i. MEM i P ==> ALL_DISTINCT _ /\ _` kall_tac >>
  qpat_x_assum `!i. MEM i P ==> _` (qspec_then `i` mp_tac) >>
  simp_tac bool_ss [LET_THM] >> simp[] >> strip_tac >> gvs[] >>
  `(?u. step_inst b C' i a = OK u) \/
   (?v u. step_inst b C' i a = IntRet v u)` by
    (irule native_inventory_root_success >>
     gvs[markerTheory.Abbrev_def] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `?v u. run_blocks b C' (dft_fn cf) cs = IntRet v u` by
    (qpat_x_assum `step_inst b C' i a = _` mp_tac >>
     simp[Once step_inst_def] >>
     Cases_on `run_blocks b C' (dft_fn cf) cs` >> simp[]) >>
  (conj_tac >- metis_tac[]) >>
  `ALL_DISTINCT (MAP FST (trace_gas (dftGasFromListTraceDefs$trace_blocks
      ((d,i.inst_id)::p) d b C' (dft_fn cf) cs)))` by
    suspend "success_child_distinct" >>
  irule native_inventory_return_saturation >> simp[] >>
  qexists_tac `cs.vs_gas_readings` >>
  simp_tac pure_ss [cj 3 trace_gas_lengths] >>
  `Uc = DROP (gas_count_blocks b C' (dft_fn cf) cs) cs.vs_gas_readings` by
    (mp_tac (cj 3 gas_count_suffix) >>
     disch_then (qspecl_then [`b`, `C'`, `dft_fn cf`, `cs`] mp_tac) >>
     simp[gas_count_suffix_def] >> metis_tac[]) >>
  metis_tac[]
QED
Resume native_frontier_mask_inventory[success_child_distinct]:
  markerLib.RESUME_TAC >>
  irule trace_gas_names_distinct >>
  irule (cj 3 trace_names_distinct) >>
  qpat_x_assum `o1_ctx_shape C'` mp_tac >>
  simp_tac bool_ss [o1_ctx_shape_def, ctx_inst_ids_distinct_def] >>
  strip_tac >>
  `EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
      f.fn_blocks) C'.ctx_functions` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     drule_all venomWfPropsTheory.all_distinct_flat_map_member >>
     BETA_TAC >> strip_tac >>
     drule_all venomWfPropsTheory.all_distinct_flat_map_member >> simp[]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED
Resume native_frontier_mask_inventory[actual_gas]:
  `MEM i body'` by
    (qpat_x_assum `MEM i (DROP _ _)` mp_tac >> simp[DROP_APPEND]) >>
  `?h. MEM h scheduled /\ h.inst_id = i.inst_id` by
    (drule_all LIST_REL_MEM_IMP_R >> simp[]) >>
  `PERM todo scheduled` by metis_tac[native_bubbles_perm] >>
  `MEM h todo` by metis_tac[sortingTheory.PERM_MEM_EQ] >>
  `MEM h bb.bb_instructions` by
    (fs[dft_remaining_inv_def, EVERY_MEM] >> metis_tac[]) >>
  `from_block bb.bb_instructions i` by metis_tac[EVERY_MEM] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  `i = h \/ i = flip_operands h` by
    metis_tac[dftScheduleOrderTheory.from_block_id_cases] >>
  `h.inst_opcode = GAS` by
    (qpat_x_assum `i = _` mp_tac >>
     qpat_x_assum `i.inst_opcode = GAS` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `h.inst_opcode` >>
     simp[flip_operands_def, is_comparator_def, flip_comparison_opcode_def,
          AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `!i. MEM i P ==> ALL_DISTINCT _ /\ _` kall_tac >>
  qpat_assum `!i. MEM i P ==> _` (qspec_then `h` mp_tac) >>
  simp_tac bool_ss [LET_THM] >>
  `MEM h P` by metis_tac[] >>
  qpat_assum `h.inst_opcode = GAS`
    (fn th => simp_tac (srw_ss()) [th]) >>
  qpat_assum `MEM h P` (fn th => simp_tac bool_ss [th]) >> strip_tac >>
  simp_tac pure_ss [MEM_FLAT, MEM_MAP] >> qexists_tac `kr h` >>
  metis_tac[MEM]
QED
Resume native_frontier_mask_inventory[actual_call]:
  `MEM i P` by
    (`MEM i (MAP FST (MAP (\(e,f,i,a). (i,a))
       (FILTER (\(e,f,i,a). e = (p,d,i.inst_id) /\ i.inst_opcode = INVOKE) V)))` by
       (simp[MEM_MAP, MEM_FILTER] >>
        qexists_tac `(i,a)` >> simp[] >>
        qexists_tac `((p,d,i.inst_id),fn',i,a)` >> simp[]) >>
     qpat_x_assum `MAP FST _ = FILTER _ P` mp_tac >>
     metis_tac[MEM_FILTER]) >>
  qpat_x_assum `!i. MEM i P ==> ALL_DISTINCT _ /\ _` kall_tac >>
  qpat_assum `!i. MEM i P ==> _` (qspec_then `i` mp_tac) >>
  simp_tac bool_ss [LET_THM] >> simp[] >> strip_tac >>
  rename1 `cr i = SOME (a0,nm,ops,args,cf,dft_fn cf,cs,cs,Uc)` >>
  `trace_gas (dftGasFromListTraceDefs$trace_step p d b C' fn' i a) =
   trace_gas (dftGasFromListTraceDefs$trace_step p d b C' fn' i a0)` by
    (`!x. MEM ((p,d,i.inst_id),fn',i,x) V ==>
       FILTER (\kw. frame_below ((d,i.inst_id)::p) (FST (FST kw)))
         (trace_gas V) =
       trace_gas (dftGasFromListTraceDefs$trace_step p d b C' fn' i x)` by
       (rpt strip_tac >> simp_tac pure_ss [Abbr `V`] >>
        irule native_inventory_root_subtree >> simp[] >>
        gvs[markerTheory.Abbrev_def]) >>
     metis_tac[markerTheory.Abbrev_def]) >>
  `MEM kw (trace_gas (dftGasFromListTraceDefs$trace_blocks
     ((d,i.inst_id)::p) d b C' (dft_fn cf) cs))` by
    (drule_all dftGasFromListTraceDefsTheory.trace_step_invoke >>
     metis_tac[]) >>
  `FILTER (\kw. ~MEM (FST kw) (kr i))
     (trace_gas (dftGasFromListTraceDefs$trace_blocks
       ((d,i.inst_id)::p) d b C' (dft_fn cf) cs)) = []` by
    (qpat_assum `!i a nm ops args cf cs Uc. _` drule_all >> simp[]) >>
  `MEM (FST kw) (kr i)` by
    (qpat_x_assum `FILTER _ _ = []` mp_tac >>
     simp_tac bool_ss [FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  simp_tac pure_ss [MEM_FLAT, MEM_MAP] >> metis_tac[]
QED
Finalise native_frontier_mask_inventory

Theorem native_successful_trace_pull_enabled[local]:
  !X s u v.
    ALL_DISTINCT X /\ EVERY (\x. MEM x universe) X /\ MEM y universe /\
    (!x. id_before X x y \/ (MEM x X /\ ~MEM y X) ==> indep x y) /\
    (!x y q r t. MEM x universe /\ MEM y universe /\ x <> y /\ indep x y /\
      inv_ev_trace orc p d b C [x] q r /\
      inv_ev_trace orc p d b C [y] q t ==>
      ?w. inv_ev_trace orc p d b C [y] r w /\
          inv_ev_trace orc p d b C [x] t w) /\
    inv_ev_trace orc p d b C X s u /\
    inv_ev_trace orc p d b C [y] s v ==>
    ?w. inv_ev_trace orc p d b C (if MEM y X then [] else [y]) u w /\
        inv_ev_trace orc p d b C (FILTER (\x. x <> y) X) v w
Proof
  Induct
  >- (simp[inv_ev_trace_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h = y`
  >- (gvs[] >>
      `FILTER (\x. x <> h) X = X` by simp[FILTER_EQ_ID, EVERY_MEM] >>
      gvs[inv_ev_trace_def]) >>
  `indep h y` by
    (first_x_assum irule >> simp[id_before_cons] >> metis_tac[MEM]) >>
  qpat_x_assum `inv_ev_trace _ _ _ _ _ (h::X) _ _` mp_tac >>
  simp[Once inv_ev_trace_def] >> strip_tac >>
  rename1 `ev_step orc p d b C h s = OK r` >>
  `?w. inv_ev_trace orc p d b C [y]
          (r with vs_inst_idx := SUC s.vs_inst_idx) w /\
        inv_ev_trace orc p d b C [h] v w` by
    (first_x_assum irule >> simp[] >> conj_tac
     >- gvs[] >>
     qexists_tac `s` >> simp[inv_ev_trace_def] >>
     metis_tac[inv_ev_trace_def]) >>
  first_x_assum (qspecl_then
    [`r with vs_inst_idx := SUC s.vs_inst_idx`, `u`, `w`] mp_tac) >>
  impl_tac
  >- (gvs[id_before_cons] >> metis_tac[]) >>
  strip_tac >> goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `inv_ev_trace _ _ _ _ _ [h] v w` mp_tac >>
  simp[inv_ev_trace_def] >> metis_tac[]
QED

Theorem native_successful_prefix_union_core[local]:
  !Y X Xrest Yrest.
    ALL_DISTINCT (X ++ Xrest) /\ ALL_DISTINCT (Y ++ Yrest) /\
    PERM (X ++ Xrest) (Y ++ Yrest) /\
    (!x y. id_before (X ++ Xrest) x y /\
       id_before (Y ++ Yrest) y x ==> indep x y) /\
    (!x y q r t. MEM x (X ++ Xrest) /\ MEM y (X ++ Xrest) /\
      x <> y /\ indep x y /\
      inv_ev_trace orc p d b C [x] q r /\
      inv_ev_trace orc p d b C [y] q t ==>
      ?w. inv_ev_trace orc p d b C [y] r w /\
          inv_ev_trace orc p d b C [x] t w) ==>
    !s u v. inv_ev_trace orc p d b C X s u /\
      inv_ev_trace orc p d b C Y s v ==>
      ?w. inv_ev_trace orc p d b C (FILTER (\i. ~MEM i X) Y) u w /\
          inv_ev_trace orc p d b C (FILTER (\i. ~MEM i Y) X) v w
Proof
  Induct
  >- (simp[inv_ev_trace_def, FILTER_EQ_ID] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT X /\ ~MEM h Y /\ ~MEM h Yrest` by gvs[ALL_DISTINCT_APPEND] >>
  `MEM h (X ++ Xrest)` by metis_tac[PERM_MEM_EQ, MEM, MEM_APPEND] >>
  `!x. id_before X x h \/ (MEM x X /\ ~MEM h X) ==> indep x h` by
    (qpat_x_assum `!A B D. ALL_DISTINCT _ /\ _ ==> _` kall_tac >>
     qpat_x_assum `!x y q r t. _` kall_tac >>
     qpat_x_assum `inv_ev_trace _ _ _ _ _ X s u` kall_tac >>
     qpat_x_assum `inv_ev_trace _ _ _ _ _ (h::Y) s v` kall_tac >>
     drule PERM_MEM_EQ >> simp[] >> strip_tac >>
     `!x. MEM x X /\ x <> h ==> MEM x Y \/ MEM x Yrest` by
       (rpt strip_tac >> first_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
     rpt strip_tac >> first_x_assum irule >>
     simp[dftSsaPreserveTheory.id_before_append, id_before_cons] >>
     metis_tac[id_before_mem, id_before_distinct_endpoints, MEM_APPEND]) >>
  `?a. inv_ev_trace orc p d b C [h] s a /\
       inv_ev_trace orc p d b C Y a v` by
    (qpat_x_assum `inv_ev_trace _ _ _ _ _ (h::Y) _ _` mp_tac >>
     simp[inv_ev_trace_def] >> metis_tac[]) >>
  `?z. inv_ev_trace orc p d b C (if MEM h X then [] else [h]) u z /\
       inv_ev_trace orc p d b C (FILTER (\i. i <> h) X) a z` by
    (irule native_successful_trace_pull_enabled >> simp[] >>
     conj_tac
     >- (qexistsl_tac [`indep`, `X ++ Xrest`] >>
         asm_rewrite_tac[EVERY_MEM] >> simp[]) >>
     qexists_tac `s` >> simp[]) >>
  first_x_assum (qspecl_then
    [`FILTER (\i. i <> h) X`, `FILTER (\i. i <> h) Xrest`, `Yrest`] mp_tac) >>
  impl_tac
  >- suspend "deleted_orders" >>
  disch_then drule_all >> strip_tac >>
  qexists_tac `w` >>
  conj_tac
  >- suspend "left_extension" >>
  suspend "right_extension"
QED
Resume native_successful_prefix_union_core[deleted_orders]:
  `FILTER (\i. i <> h) (Y ++ Yrest) = Y ++ Yrest` by
    simp[FILTER_EQ_ID, EVERY_MEM] >>
  `PERM (FILTER (\i. i <> h) (X ++ Xrest)) (Y ++ Yrest)` by
    (drule PERM_FILTER >>
     disch_then (qspec_then `\i. i <> h` mp_tac) >> simp[]) >>
  pure_rewrite_tac[GSYM FILTER_APPEND_DISTRIB] >>
  conj_tac >- (irule FILTER_ALL_DISTINCT >> simp[]) >>
  conj_tac >- gvs[] >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> conj_tac
      >- metis_tac[dftGasInvExtractionTheory.inv_id_before_filter_reflect] >>
      simp_tac (srw_ss()) [APPEND, id_before_cons] >> simp[]) >>
  simp_tac (srw_ss()) [MEM_FILTER] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> qexists_tac `q` >> simp[]
QED
Resume native_successful_prefix_union_core[left_extension]:
  `FILTER (\i. ~MEM i (FILTER (\i. i <> h) X)) Y =
   FILTER (\i. ~MEM i X) Y` by
    (simp[rich_listTheory.FILTER_EQ, MEM_FILTER] >> metis_tac[]) >>
  Cases_on `MEM h X`
  >- (qpat_x_assum `inv_ev_trace _ _ _ _ _ (if _ then _ else _) u z` mp_tac >>
      simp[inv_ev_trace_def] >> strip_tac >>
      qpat_x_assum `inv_ev_trace _ _ _ _ _ (FILTER _ Y) z w` mp_tac >>
      simp[]) >>
  qpat_x_assum `inv_ev_trace _ _ _ _ _ (if _ then _ else _) u z` mp_tac >>
  simp[inv_ev_trace_def] >> strip_tac >>
  simp[Once inv_ev_trace_def] >> (gvs[])
QED
Resume native_successful_prefix_union_core[right_extension]:
  qpat_x_assum `inv_ev_trace _ _ _ _ _ (FILTER _ (FILTER _ X)) _ _` mp_tac >>
  simp[rich_listTheory.FILTER_FILTER, MEM_FILTER] >>
  ` (\i. ~MEM i Y /\ i <> h) = (\i. ~MEM i (h::Y))` by
    (simp[FUN_EQ_THM] >> metis_tac[]) >> simp[]
QED
Finalise native_successful_prefix_union_core

Theorem native_successful_prefix_union:
  !L L' X Xrest Y Yrest indep orc p d b C s u v.
    ALL_DISTINCT L /\ ALL_DISTINCT L' /\ PERM L L' /\
    L = X ++ Xrest /\ L' = Y ++ Yrest /\
    (!x y. indep x y ==> indep y x) /\
    (!x y. id_before L x y /\ id_before L' y x ==> indep x y) /\
    (!x q r t. MEM x L /\ ev_step orc p d b C x q = OK r /\
       ev_step orc p d b C x q = OK t ==>
       (r with vs_inst_idx := SUC q.vs_inst_idx) =
       (t with vs_inst_idx := SUC q.vs_inst_idx)) /\
    (!x y q r t. MEM x L /\ MEM y L /\ x <> y /\ indep x y /\
       ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
       ev_step orc p d b C x q = OK r /\
       ev_step orc p d b C y q = OK t ==>
       ?r' t'.
         ev_step orc p d b C y (r with vs_inst_idx := SUC q.vs_inst_idx) = OK r' /\
         ev_step orc p d b C x (t with vs_inst_idx := SUC q.vs_inst_idx) = OK t' /\
         (r' with vs_inst_idx := SUC (SUC q.vs_inst_idx)) =
         (t' with vs_inst_idx := SUC (SUC q.vs_inst_idx))) /\
    inv_ev_trace orc p d b C X s u /\ inv_ev_trace orc p d b C Y s v ==>
    ?w.
      inv_ev_trace orc p d b C (X ++ FILTER (\i. ~MEM i X) Y) s w /\
      inv_ev_trace orc p d b C (Y ++ FILTER (\i. ~MEM i Y) X) s w /\
      inv_ev_trace orc p d b C (FILTER (\i. ~MEM i X) Y) u w /\
      inv_ev_trace orc p d b C (FILTER (\i. ~MEM i Y) X) v w
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `L = _` SUBST_ALL_TAC >>
  qpat_x_assum `L' = _` SUBST_ALL_TAC >>
  `!x y q r t. MEM x (X ++ Xrest) /\ MEM y (X ++ Xrest) /\
      x <> y /\ indep x y /\
      inv_ev_trace orc p d b C [x] q r /\
      inv_ev_trace orc p d b C [y] q t ==>
      ?w. inv_ev_trace orc p d b C [y] r w /\
          inv_ev_trace orc p d b C [x] t w` by suspend "square" >>
  qspecl_then [`Y`, `X`, `Xrest`, `Yrest`] mp_tac native_successful_prefix_union_core >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then drule_all >> strip_tac >> qexists_tac `w` >>
  simp[inv_ev_trace_append] >> conj_tac
  >- (qexists_tac `u` >> simp[]) >>
  qexists_tac `v` >> simp[]
QED
Resume native_successful_prefix_union[square]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `inv_ev_trace _ _ _ _ _ [x] q r` mp_tac >>
  qpat_x_assum `inv_ev_trace _ _ _ _ _ [y] q t` mp_tac >>
  simp[inv_ev_trace_def] >> rpt strip_tac >>
  qpat_x_assum `!x y q r t. _` drule_all >> strip_tac >>
  gvs[inv_ev_trace_def]
QED
Finalise native_successful_prefix_union

Theorem native_residual_completion_sort:
  ALL_DISTINCT (A ++ i::srcpost) /\
  dft_head_bubbles R (A ++ i::srcpost) (consumed ++ i::later) /\
  (!x y. R x y ==> dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y) /\
  inv_ev_ftrace orc p d ctx
    (consumed ++ FILTER (\x. ~MEM x consumed) A) s t ==>
  inv_ev_ftrace orc p d ctx
    (A ++ FILTER (\x. MEM x consumed) srcpost) s t
Proof
  strip_tac >>
  `PERM (A ++ i::srcpost) (consumed ++ i::later)` by
    metis_tac[native_bubbles_perm] >>
  `ALL_DISTINCT (consumed ++ i::later)` by metis_tac[ALL_DISTINCT_PERM] >>
  `EVERY (\x. MEM x (A ++ srcpost)) consumed` by
    (gvs[ALL_DISTINCT_APPEND, EVERY_MEM] >> rpt strip_tac >>
     drule PERM_MEM_EQ >> disch_then (qspec_then `x` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (A ++ srcpost)` by gvs[ALL_DISTINCT_APPEND] >>
  `PERM (consumed ++ FILTER (\x. ~MEM x consumed) A)
        (A ++ FILTER (\x. MEM x consumed) srcpost)` by
    (irule dftGasInvExtractionTheory.inv_completed_prefix_perm >>
     gvs[ALL_DISTINCT_APPEND]) >>
  irule dftGasInvExtractionTheory.inv_ftrace_source_sort >> conj_tac
  >- (gvs[ALL_DISTINCT_APPEND] >>
      simp[ALL_DISTINCT_APPEND, FILTER_ALL_DISTINCT, MEM_FILTER] >> metis_tac[]) >>
  qexists_tac `consumed ++ FILTER (\x. ~MEM x consumed) A` >>
  simp[] >> ntac 2 gen_tac >> strip_tac >>
  `id_before (A ++ i::srcpost) x z` by
    metis_tac[dftGasInvExtractionTheory.inv_completed_order_source] >>
  `id_before (consumed ++ i::later) z x` by
    metis_tac[dftGasInvExtractionTheory.inv_completion_inversion, PERM_SYM] >>
  `R x z` by metis_tac[native_bubbles_inversion] >>
  metis_tac[]
QED

(* Coinitial success: first construct a forward extension, then exchange it. *)
Theorem native_coenabled_gas[local]:
  dft_gas_swap_pair g i /\ g.inst_opcode = GAS /\
  inst_wf g /\ inst_wf i /\
  ev_step orc p d b C g s = OK sg /\
  ev_step orc p d b C i s = OK si ==>
  ?u. ev_step orc p d b C i sg = OK u
Proof
  strip_tac >>
  `?out. g.inst_outputs = [out]` by metis_tac[ev_step_gas_shape] >>
  `sg = update_var out (orc (p,d,g.inst_id)) s` by
    (gvs[ev_step_def, ev_gas_def]) >>
  drule_all dft_independent_gas_output >> strip_tac >>
  drule_all dftGasSimSwapSuccessTheory.ev_step_independent_update_ok_iff >> metis_tac[]
QED

Theorem native_coenabled_invoke[local]:
  dft_gas_swap_pair c i /\ c.inst_opcode = INVOKE /\
  i.inst_opcode <> GAS /\ inst_wf c /\ inst_wf i /\
  ev_step orc p d b C c s = OK sc /\
  ev_step orc p d b C i s = OK si ==>
  ?u. ev_step orc p d b C i sc = OK u
Proof
  strip_tac >>
  drule dftGasSimInvokePartnerTheory.ev_invoke_partner_updates >>
  simp[] >> metis_tac[]
QED

Theorem native_coenabled_ordinary[local]:
  dft_gas_swap_pair a b /\ inst_wf a /\ inst_wf b /\
  a.inst_opcode <> GAS /\ a.inst_opcode <> INVOKE /\
  b.inst_opcode <> GAS /\ b.inst_opcode <> INVOKE /\
  ~is_ext_call_op a.inst_opcode /\ ~is_ext_call_op b.inst_opcode /\
  ev_step orc p d fuel C a s = OK sa /\
  ev_step orc p d fuel C b s = OK sb ==>
  ?u. ev_step orc p d fuel C b sa = OK u
Proof
  strip_tac >> gvs[ev_step_ordinary] >>
  `~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
   ~is_alloca_op a.inst_opcode /\ ~is_alloca_op b.inst_opcode /\
   effects_independent a.inst_opcode b.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  `step_inst_base b s = OK sb` by gvs[step_inst_non_invoke] >>
  simp[step_inst_non_invoke] >>
  irule passSharedTransferTheory.step_inst_base_ok_transfer >> simp[] >>
  qexistsl_tac [`s`, `sb`] >> simp[] >>
  `sa.vs_call_ctx = s.vs_call_ctx /\ sa.vs_prev_bb = s.vs_prev_bb /\
   sa.vs_params = s.vs_params /\
   (Eff_RETURNDATA NOTIN write_effects a.inst_opcode ==>
      sa.vs_returndata = s.vs_returndata)` by
    metis_tac[step_inst_preserves_eligible_fields] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> sym_tac >> irule eval_operand_step_pres >>
      qexistsl_tac [`C`, `fuel`, `a`] >> simp[] >>
      metis_tac[dft_swap_output_frame]) >>
  strip_tac >>
  `Eff_RETURNDATA IN read_effects RETURNDATACOPY` by EVAL_TAC >>
  gvs[effects_independent_def] >> metis_tac[pred_setTheory.IN_DISJOINT]
QED

Theorem native_coenabled_external[local]:
  dft_gas_swap_pair a b /\ inst_wf a /\ inst_wf b /\
  a.inst_opcode <> GAS /\ a.inst_opcode <> INVOKE /\
  b.inst_opcode <> GAS /\ b.inst_opcode <> INVOKE /\
  is_ext_call_op a.inst_opcode /\ ~is_ext_call_op b.inst_opcode /\
  ev_step orc p d fuel C a s = OK sa /\
  ev_step orc p d fuel C b s = OK sb ==>
  ?u. ev_step orc p d fuel C b sa = OK u
Proof
  strip_tac >> gvs[ev_step_ordinary] >>
  `~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
   ~is_alloca_op b.inst_opcode /\
   effects_independent a.inst_opcode b.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  `b.inst_opcode <> RETURNDATACOPY` by
    (strip_tac >> gvs[] >> Cases_on `a.inst_opcode` >>
     gvs[is_ext_call_op_def, effects_independent_def,
         read_effects_def, write_effects_def, all_effects_def,
         empty_effects_def, pred_setTheory.DISJOINT_DEF,
         pred_setTheory.EXTENSION]) >>
  `step_inst_base b s = OK sb` by gvs[step_inst_non_invoke] >>
  drule_all venomInstProofsTheory.step_ext_call_preserves >> strip_tac >>
  simp[step_inst_non_invoke] >>
  irule passSharedTransferTheory.step_inst_base_ok_transfer >> simp[] >>
  qexistsl_tac [`s`, `sb`] >> simp[] >>
  rpt strip_tac >> sym_tac >> irule eval_operand_step_pres >>
  qexistsl_tac [`C`, `fuel`, `a`] >> simp[] >>
  metis_tac[dft_swap_output_frame]
QED

Theorem native_coenabled_step_square:
  dft_gas_swap_pair a b /\ inst_wf a /\ inst_wf b /\
  ev_step orc p d fuel C a s = OK sa /\
  ev_step orc p d fuel C b s = OK sb ==>
  ?u. ev_step orc p d fuel C b sa = OK u /\
      ev_step orc p d fuel C a sb = OK u
Proof
  strip_tac >>
  `dft_gas_swap_pair b a` by metis_tac[dft_gas_swap_pair_sym] >>
  `(?u. ev_step orc p d fuel C b sa = OK u) \/
   (?u. ev_step orc p d fuel C a sb = OK u)` by
    (Cases_on `a.inst_opcode = GAS`
     >- (disj1_tac >> irule native_coenabled_gas >> metis_tac[]) >>
     Cases_on `b.inst_opcode = GAS`
     >- (disj2_tac >> irule native_coenabled_gas >> metis_tac[]) >>
     Cases_on `a.inst_opcode = INVOKE`
     >- (disj1_tac >> irule native_coenabled_invoke >> metis_tac[]) >>
     Cases_on `b.inst_opcode = INVOKE`
     >- (disj2_tac >> irule native_coenabled_invoke >> metis_tac[]) >>
     `~(is_ext_call_op a.inst_opcode /\ is_ext_call_op b.inst_opcode)` by
       (strip_tac >>
        `effects_independent a.inst_opcode b.inst_opcode` by
          gvs[dft_gas_swap_pair_def] >>
        qpat_x_assum `effects_independent _ _` mp_tac >>
        qpat_x_assum `is_ext_call_op a.inst_opcode` mp_tac >>
        qpat_x_assum `is_ext_call_op b.inst_opcode` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        Cases_on `a.inst_opcode` >> simp[is_ext_call_op_def] >>
        Cases_on `b.inst_opcode` >> simp[is_ext_call_op_def] >>
        EVAL_TAC) >>
     Cases_on `is_ext_call_op a.inst_opcode`
     >- (disj1_tac >> irule native_coenabled_external >> metis_tac[]) >>
     Cases_on `is_ext_call_op b.inst_opcode`
     >- (disj2_tac >> irule native_coenabled_external >> metis_tac[]) >>
     disj1_tac >> irule native_coenabled_ordinary >> metis_tac[]) >>
  first_x_assum strip_assume_tac >>
  drule_all dftGasSimSwapSuccessTheory.ev_pair_success >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem native_coenabled_indexed_square:
  dft_gas_swap_pair a b /\ inst_wf a /\ inst_wf b /\
  ev_step orc p d fuel C a s = OK sa /\
  ev_step orc p d fuel C b s = OK sb ==>
  ?u v.
    ev_step orc p d fuel C b (sa with vs_inst_idx := SUC s.vs_inst_idx) = OK u /\
    ev_step orc p d fuel C a (sb with vs_inst_idx := SUC s.vs_inst_idx) = OK v /\
    (u with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
    (v with vs_inst_idx := SUC (SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all native_coenabled_step_square >> strip_tac >>
  `~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  metis_tac[dftGasSimLocalBoundaryTheory.ev_step_nonterminator_ok_idx]
QED

Theorem native_successful_cut_call_inputs:
  ALL_DISTINCT (A ++ i::srcpost) /\
  dft_head_bubbles R (A ++ i::srcpost) (consumed ++ i::later) /\
  (!x y. R x y ==> dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y) /\
  i.inst_opcode = INVOKE /\
  inv_ev_trace orc p d b C' A s0 u /\
  inv_ev_trace orc p d b C' consumed s0 v
  ==>
  (!op. MEM op i.inst_operands ==> eval_operand op u = eval_operand op v) /\
  (!callee args. setup_callee callee args u = setup_callee callee args v)
Proof
  strip_tac >>
  `PERM (A ++ i::srcpost) (consumed ++ i::later)` by
    metis_tac[native_bubbles_perm] >>
  `ALL_DISTINCT (consumed ++ i::later)` by metis_tac[ALL_DISTINCT_PERM] >>
  `?w.
    inv_ev_trace orc p d b C' (A ++ FILTER (\x. ~MEM x A) consumed) s0 w /\
    inv_ev_trace orc p d b C' (consumed ++ FILTER (\x. ~MEM x consumed) A) s0 w /\
    inv_ev_trace orc p d b C' (FILTER (\x. ~MEM x A) consumed) u w /\
    inv_ev_trace orc p d b C' (FILTER (\x. ~MEM x consumed) A) v w` by
    (irule native_successful_prefix_union >> reverse conj_tac >- simp[] >>
     qexistsl_tac [`A ++ i::srcpost`, `consumed ++ i::later`,
       `i::srcpost`, `i::later`,
       `\x y. dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y`] >>
     simp[] >> suspend "union") >>
  `EVERY (\x. dft_gas_swap_pair i x /\ inst_wf x)
     (FILTER (\x. ~MEM x A) consumed) /\
   EVERY (\x. dft_gas_swap_pair i x /\ inst_wf x)
     (FILTER (\x. ~MEM x consumed) A)` by suspend "partners" >>
  `inv_ev_ftrace orc p d C' (FILTER (\x. ~MEM x A) consumed) u w /\
   inv_ev_ftrace orc p d C' (FILTER (\x. ~MEM x consumed) A) v w` by
    metis_tac[dftGasInvFlexibleTraceTheory.inv_ev_trace_ftrace] >>
  metis_tac[dftGasInvInversionTheory.inv_ev_trailing_trace_frame,
    dftGasInvCallerInputTheory.inv_ev_invoke_trace_setup]
QED
Resume native_successful_cut_call_inputs[union]:
  conj_tac
  >- (rpt strip_tac >> irule native_coenabled_indexed_square >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- metis_tac[dft_gas_swap_pair_sym] >>
  conj_tac >- metis_tac[native_bubbles_inversion] >>
  rpt strip_tac >> gvs[]
QED
Resume native_successful_cut_call_inputs[partners]:
  simp[EVERY_MEM, MEM_FILTER] >> conj_tac
  >- (rpt strip_tac >>
      `~MEM x (i::later)` by gvs[ALL_DISTINCT_APPEND] >>
      `MEM x srcpost` by
        (drule PERM_MEM_EQ >> disch_then (qspec_then `x` mp_tac) >>
         simp[] >> metis_tac[MEM]) >>
      `id_before (A ++ i::srcpost) i x /\
       id_before (consumed ++ i::later) x i` by
        (simp[dftSsaPreserveTheory.id_before_append, id_before_cons]) >>
      `R i x` by metis_tac[native_bubbles_inversion] >> metis_tac[]) >>
  rpt strip_tac >>
  `~MEM x (i::srcpost)` by gvs[ALL_DISTINCT_APPEND] >>
  `MEM x later` by
    (drule PERM_MEM_EQ >> disch_then (qspec_then `x` mp_tac) >>
     simp[] >> metis_tac[MEM]) >>
  `id_before (A ++ i::srcpost) x i /\
   id_before (consumed ++ i::later) i x` by
    (simp[dftSsaPreserveTheory.id_before_append, id_before_cons]) >>
  `R x i` by metis_tac[native_bubbles_inversion] >>
  metis_tac[dft_gas_swap_pair_sym]
QED
Finalise native_successful_cut_call_inputs

Theorem native_successful_cut_frontier_step:
  ALL_DISTINCT (before ++ z::after) /\
  dft_head_bubbles R (before ++ z::after) (done ++ z::later) /\
  (!x y. R x y ==> dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y) /\
  inv_ev_trace orc p d b C' (before ++ [z]) s0 u /\
  inv_ev_trace orc p d b C' done s0 v
  ==> ?w. ev_step orc p d b C' z v = OK w
Proof
  strip_tac >>
  `PERM (before ++ z::after) (done ++ z::later)` by
    metis_tac[native_bubbles_perm] >>
  `ALL_DISTINCT (done ++ z::later)` by metis_tac[ALL_DISTINCT_PERM] >>
  `~MEM z done` by (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `?w.
    inv_ev_trace orc p d b C'
      ((before ++ [z]) ++ FILTER (\i. ~MEM i (before ++ [z])) done) s0 w /\
    inv_ev_trace orc p d b C'
      (done ++ FILTER (\i. ~MEM i done) (before ++ [z])) s0 w /\
    inv_ev_trace orc p d b C'
      (FILTER (\i. ~MEM i (before ++ [z])) done) u w /\
    inv_ev_trace orc p d b C'
      (FILTER (\i. ~MEM i done) (before ++ [z])) v w` by
    (irule native_successful_prefix_union >> simp[] >>
     qexistsl_tac [`after`, `z::later`,
       `\x y. dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y`] >>
     simp[] >> rpt conj_tac
     >- (rpt strip_tac >> irule native_coenabled_indexed_square >> simp[])
     >- metis_tac[dft_gas_swap_pair_sym]
     >- (rpt strip_tac >>
         `R x y` by
           (qpat_x_assum `id_before (before ++ [z] ++ after) _ _` mp_tac >>
            pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> strip_tac >>
            drule_all native_bubbles_inversion >> simp[]) >> metis_tac[])
     >- (rpt strip_tac >> gvs[]) >>
     pure_asm_rewrite_tac[GSYM APPEND_ASSOC, APPEND]) >>
  `EVERY (\x. dft_gas_swap_pair z x /\ inst_wf z /\ inst_wf x)
    (FILTER (\i. ~MEM i done) before)` by suspend "crossings" >>
  `inv_ev_trace orc p d b C'
    (z::FILTER (\i. ~MEM i done) before) v w` by
    (drule inv_trace_pull >>
     disch_then (qspec_then `[]` mp_tac) >>
     simp[] >> disch_then irule >>
     qpat_x_assum `inv_ev_trace _ _ _ _ _ (FILTER _ (before ++ [z])) _ _` mp_tac >>
     gvs[ALL_DISTINCT_APPEND, FILTER_APPEND_DISTRIB]) >>
  gvs[Once inv_ev_trace_def] >> metis_tac[]
QED
Resume native_successful_cut_frontier_step[crossings]:
  simp[EVERY_MEM, MEM_FILTER] >> rpt strip_tac >>
  `R x z` by
    (drule native_bubbles_inversion >> disch_then drule >>
     disch_then irule >>
     simp[dftSsaPreserveTheory.id_before_append, id_before_cons] >>
     drule PERM_MEM_EQ >> disch_then (qspec_then `x` mp_tac) >>
     gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  metis_tac[dft_gas_swap_pair_sym]
QED
Finalise native_successful_cut_frontier_step

Theorem native_target_cut[local]:
  !pre s a rest.
  ALL_DISTINCT (MAP (\x. x.inst_id) (pre ++ i::rest)) /\
  DROP s.vs_inst_idx bt.bb_instructions = pre ++ i::rest /\
  MEM ((p,d,i.inst_id),fn',i,a)
    (dftGasFromListTraceDefs$trace_block p d b C' fn' bt s) ==>
  EVERY (\x. ~is_terminator x.inst_opcode) pre /\
  FOLDR (dft_exec_cons b C') OK pre s = OK a
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (`get_instruction bt s.vs_inst_idx = SOME i` by
        (`s.vs_inst_idx < LENGTH bt.bb_instructions` by
          (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[LENGTH_DROP]) >>
         simp[get_instruction_def] >>
         qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `HD`) >> simp[HD_DROP]) >>
      `~MEM (p,d,i.inst_id) (MAP FST
         (dftGasFromListTraceDefs$trace_step p d b C' fn' i s))` by
        simp[trace_step_not_root] >>
      `!u. ~MEM (p,d,i.inst_id) (MAP FST
         (dftGasFromListTraceDefs$trace_block p d b C' fn' bt
           (u with vs_inst_idx := SUC s.vs_inst_idx)))` by
        (gen_tac >> irule trace_block_excludes >>
         `DROP (SUC s.vs_inst_idx) bt.bb_instructions = rest` by
           (gvs[get_instruction_def] >> qpat_x_assum `DROP _ _ = _` mp_tac >>
            simp[Once rich_listTheory.DROP_CONS_EL]) >> gvs[]) >>
      `a = s` by
        (qpat_x_assum `MEM _ (dftGasFromListTraceDefs$trace_block _ _ _ _ _ _ _)` mp_tac >>
         simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs)] >>
         Cases_on `step_inst b C' i s` >> simp[] >>
         Cases_on `is_terminator i.inst_opcode` >> simp[] >>
         metis_tac[MEM_MAP, pairTheory.FST]) >> simp[]) >>
  `get_instruction bt s.vs_inst_idx = SOME h` by
    (`s.vs_inst_idx < LENGTH bt.bb_instructions` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[LENGTH_DROP]) >>
     simp[get_instruction_def] >>
     qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `HD`) >> simp[HD_DROP]) >>
  `h.inst_id <> i.inst_id` by gvs[ALL_DISTINCT_APPEND] >>
  `~MEM ((p,d,i.inst_id),fn',i,a)
    (dftGasFromListTraceDefs$trace_step p d b C' fn' h s)` by
    (strip_tac >>
     `MEM (p,d,i.inst_id) (MAP FST
       (dftGasFromListTraceDefs$trace_step p d b C' fn' h s))` by
       (simp[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
     metis_tac[trace_step_not_root]) >>
  qpat_x_assum `MEM _ (dftGasFromListTraceDefs$trace_block _ _ _ _ _ _ _)` mp_tac >>
  simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs)] >>
  Cases_on `step_inst b C' h s` >> simp[] >>
  Cases_on `is_terminator h.inst_opcode` >> simp[] >> strip_tac >>
  rename1 `step_inst b C' h s = OK u` >>
  `DROP (SUC s.vs_inst_idx) bt.bb_instructions = pre ++ i::rest` by
    (gvs[get_instruction_def] >> qpat_x_assum `DROP _ _ = _` mp_tac >>
     simp[Once rich_listTheory.DROP_CONS_EL]) >>
  first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`, `a`, `rest`] mp_tac) >>
  simp[dftIndexedExecTheory.dft_exec_cons_def] >> gvs[]
QED

Theorem native_fixed_native_prefix[local]:
  !pre s u rest.
  DROP s.vs_inst_idx bt.bb_instructions = pre ++ rest /\
  EVERY (\x. ~is_terminator x.inst_opcode) pre /\
  FOLDR (dft_exec_cons b C') OK pre s = OK u /\
  trace_agrees orc (dftGasFromListTraceDefs$trace_block p d b C' fn' bt s) ==>
  inv_ev_trace orc p d b C' pre
    (s with vs_gas_readings := []) (u with vs_gas_readings := [])
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[inv_ev_trace_def] >>
  `get_instruction bt s.vs_inst_idx = SOME h` by
    (`s.vs_inst_idx < LENGTH bt.bb_instructions` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[LENGTH_DROP]) >>
     simp[get_instruction_def] >>
     qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `HD`) >> simp[HD_DROP]) >>
  qpat_x_assum `trace_agrees _ _` mp_tac >>
  simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs), trace_agrees_cons,
       trace_agrees_append] >> strip_tac >>
  qpat_x_assum `FOLDR _ _ _ _ = _` mp_tac >>
  simp[dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst b C' h s` >> simp[] >> strip_tac >>
  rename1 `step_inst b C' h s = OK mid` >>
  `ev_step orc p d b C' h (s with vs_gas_readings := []) =
     OK (mid with vs_gas_readings := [])` by
    (mp_tac (cj 1 dftGasFromListReplayTheory.trace_replay) >>
     disch_then (qspecl_then [`p`, `d`, `b`, `C'`, `fn'`, `h`, `s`, `orc`, `[]`] mp_tac) >>
     simp[trace_agrees_cons, restore_rel_cases]) >>
  gvs[EVERY_DEF] >> simp[Once inv_ev_trace_def] >>
  `DROP (SUC s.vs_inst_idx) bt.bb_instructions = pre ++ rest` by
    (gvs[get_instruction_def] >> qpat_x_assum `DROP _ _ = _` mp_tac >>
     simp[Once rich_listTheory.DROP_CONS_EL]) >>
  first_x_assum (qspecl_then [`mid with vs_inst_idx := SUC s.vs_inst_idx`, `u`, `rest`] mp_tac) >>
  gvs[]
QED

Theorem native_selected_target_event_cut:
  !keys vals body.
  ALL_DISTINCT (MAP (\x. x.inst_id) bi) /\
  ALL_DISTINCT (MAP (\x. x.inst_id) (consumed ++ i::later)) /\
  EVERY (\x. MEM x bi) (consumed ++ i::later) /\
  EVERY (from_block bi) body /\
  LIST_REL (\h x. h.inst_id = x.inst_id) (consumed ++ i::later) body /\
  DROP t.vs_inst_idx bt.bb_instructions = body /\
  ctx_inst_ids_distinct C' /\ i.inst_opcode = INVOKE /\
  MEM ((p,d,i.inst_id),fn',i,a)
    (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) ==>
  inv_ev_trace
    (\key. case ALOOKUP
      (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) ++
       ZIP (keys,vals)) key of NONE => 0w | SOME w => w)
    p d b C' consumed (t with vs_gas_readings := []) (a with vs_gas_readings := [])
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `EVERY (from_block bi) actual_body` >>
  `?actualpre actualcall actualpost.
    actual_body = actualpre ++ actualcall::actualpost /\
    LIST_REL (\h x. h.inst_id = x.inst_id) consumed actualpre /\
    i.inst_id = actualcall.inst_id /\
    LIST_REL (\h x. h.inst_id = x.inst_id) later actualpost` by
    (gvs[LIST_REL_SPLIT1, LIST_REL_CONS1] >> metis_tac[]) >>
  `MEM i bi /\ from_block bi actualcall` by gvs[EVERY_APPEND] >>
  `actualcall = i` by
    (fs[from_block_def] >- metis_tac[all_distinct_map_mem_inj] >>
     rename1 `actualcall = flip_operands original` >>
     `i = original` by metis_tac[all_distinct_map_mem_inj, flip_operands_inst_id] >>
     Cases_on `i.inst_opcode` >>
     gvs[is_flippable_def, is_commutative_def, is_comparator_def,
         flip_operands_special_opcode]) >>
  qpat_x_assum `actualcall = i` SUBST_ALL_TAC >>
  qpat_x_assum `actual_body = _` SUBST_ALL_TAC >>
  `MAP (\x. x.inst_id) (actualpre ++ i::actualpost) =
     MAP (\x. x.inst_id) (consumed ++ i::later)` by
    (sym_tac >> simp[MAP_EQ_EVERY2] >> metis_tac[LIST_REL_LENGTH]) >>
  `EVERY (\x. ~is_terminator x.inst_opcode) actualpre /\
   FOLDR (dft_exec_cons b C') OK actualpre t = OK a` by
    (irule native_target_cut >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[MAP_APPEND, MAP]) >>
  qmatch_goalsub_abbrev_tac `inv_ev_trace orc` >>
  `trace_agrees orc (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)` by
    (simp_tac pure_ss [Abbr `orc`] >>
     irule (cj 1 native_lookup_fill_subtrace_agreement) >>
     simp[EVERY_MEM] >> irule trace_gas_names_distinct >>
     irule native_inventory_suffix_distinct >> conj_tac
     >- (qpat_x_assum `DROP _ _ = _` (fn th => rewrite_tac[th]) >>
         simp_tac pure_ss [GSYM MAP_APPEND, GSYM MAP] >> metis_tac[]) >>
     qpat_x_assum `ctx_inst_ids_distinct C'` mp_tac >>
     simp_tac bool_ss [ctx_inst_ids_distinct_def] >> strip_tac >>
     simp[EVERY_MEM] >> rpt strip_tac >>
     drule_all venomWfPropsTheory.all_distinct_flat_map_member >>
     BETA_TAC >> strip_tac >>
     drule_all venomWfPropsTheory.all_distinct_flat_map_member >> simp[]) >>
  `inv_ev_trace orc p d b C' actualpre
     (t with vs_gas_readings := []) (a with vs_gas_readings := [])` by
    (irule native_fixed_native_prefix >> metis_tac[]) >>
  `?originals. MAP (\x. x.inst_id) originals = MAP (\x. x.inst_id) actualpre /\
    EVERY (\x. MEM x bi /\ ~is_pseudo x.inst_opcode) originals /\
    inv_ev_trace orc p d b C' originals
      (t with vs_gas_readings := []) (a with vs_gas_readings := [])` by
    (irule inv_trace_original_representatives >> simp[] >> gvs[EVERY_APPEND]) >>
  `originals = consumed` by
    (`LENGTH originals = LENGTH actualpre` by
       (qpat_x_assum `MAP _ originals = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
     simp_tac pure_ss [LIST_EQ_REWRITE] >> conj_tac >- metis_tac[LIST_REL_LENGTH] >>
     rpt strip_tac >> irule (Q.ISPEC `\x:instruction. x.inst_id` all_distinct_map_mem_inj) >>
     conj_tac >- (fs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP] >> metis_tac[]) >>
     qexists_tac `bi` >> fs[EVERY_EL, LIST_REL_EL_EQN] >> metis_tac[]) >> metis_tac[]
QED

Theorem native_cut_invoke_extension[local]:
  !body K.
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv fn bb todo t /\ todo = A ++ i::srcpost /\
  dft_remaining_inv fn bb (i::srcpost) q /\
  dft_head_bubbles (\x y.
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo (consumed ++ i::later) /\
  EVERY (from_block bb.bb_instructions) body /\
  LIST_REL (\h x. h.inst_id = x.inst_id) (consumed ++ i::later) body /\
  bt = bb with bb_instructions := REPLICATE j pad ++ body /\ t.vs_inst_idx = j /\
  ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
  ~t.vs_call_ctx.cc_static /\ terminates (exec_block b C' bt t) /\
  gas_count_block b C' bt t <= LENGTH t.vs_gas_readings /\
  ^native_inventory_Rq
    (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))
    i Kc Sc (SOME (a,nm,ops,args,cf,cf',cs,ct,Uc)) /\
  i.inst_opcode = INVOKE /\
  K = Kpre ++ Kc ++ Kpost /\ g = gpre ++ gc ++ gpost /\
  LENGTH Kpre = LENGTH gpre /\ LENGTH Kc = LENGTH gc /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (MAP (ALOOKUP (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))) K) g /\
  q.vs_gas_readings = DROP (LENGTH Kpre) (g ++ tail) /\
  FOLDR (dft_exec_cons n C) OK A (s with vs_gas_readings := g ++ tail) = OK q /\
  inv_ev_trace
    (\key. case ALOOKUP
      (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) ++ ZIP (K,g)) key of
       NONE => 0w | SOME w => w)
    p d b C' A (t with vs_gas_readings := []) (q with vs_gas_readings := []) /\
  step_inst n C i q = OK r ==>
  ev_step
    (\key. case ALOOKUP
      (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) ++ ZIP (K,g)) key of
       NONE => 0w | SOME w => w)
    p d b C' i (q with vs_gas_readings := []) = OK (r with vs_gas_readings := []) /\
  r.vs_gas_readings = gpost ++ tail /\
  trace_gas (dftGasFromListTraceDefs$trace_step p d n C fn i q) = ZIP (Kc,gc) /\
  gas_events_step n C fn.fn_name i q = Sc
Proof
  rpt gen_tac >> BETA_TAC >> strip_tac >> rename1 `EVERY (from_block bb.bb_instructions) actual_body` >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT todo /\ EVERY (\x. MEM x bb.bb_instructions) todo` by
    (qpat_x_assum `dft_remaining_inv fn bb todo t` mp_tac >>
     simp_tac bool_ss [dft_remaining_inv_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) todo)` by
    (irule ALL_DISTINCT_MAP_INJ >> simp[] >> rpt strip_tac >>
     drule dftCorrectnessTheory.all_distinct_map_mem_inj >>
     disch_then irule >> fs[EVERY_MEM] >> metis_tac[]) >>
  `PERM todo (consumed ++ i::later)` by metis_tac[native_bubbles_perm] >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) (consumed ++ i::later)) /\
   EVERY (\x. MEM x bb.bb_instructions) (consumed ++ i::later)` by
    metis_tac[PERM_MAP, ALL_DISTINCT_PERM, PERM_EVERY] >>
  `DROP t.vs_inst_idx bt.bb_instructions = actual_body` by simp[DROP_APPEND] >>
  `ctx_inst_ids_distinct C'` by fs[o1_ctx_shape_def] >>
  qmatch_goalsub_abbrev_tac `ev_step orc` >>
  `inv_ev_trace orc p d b C' consumed (t with vs_gas_readings := [])
     (a with vs_gas_readings := [])` by suspend "targetcut" >>
  `(!op. MEM op i.inst_operands ==>
      eval_operand op (q with vs_gas_readings := []) = eval_operand op (a with vs_gas_readings := [])) /\
   (!callee vals. setup_callee callee vals (q with vs_gas_readings := []) =
      setup_callee callee vals (a with vs_gas_readings := []))` by suspend "inputs" >>
  `eval_operands ops q = SOME args /\
   setup_callee cf args q = SOME (cs with vs_gas_readings := gc ++ (gpost ++ tail)) /\
   setup_callee cf' args (q with vs_gas_readings := []) = SOME (ct with vs_gas_readings := [])` by
    suspend "setup" >>
  suspend "child_and_merge"
QED
Resume native_cut_invoke_extension[targetcut]:
  simp_tac pure_ss [Abbr `orc`] >> irule native_selected_target_event_cut >> simp[] >>
  qexistsl_tac [`bb.bb_instructions`, `i`, `later`] >> simp[] >>
  qpat_x_assum `(if _ then _ else _)` mp_tac >> simp[] >> strip_tac >> fs[]
QED
Resume native_cut_invoke_extension[inputs]:
  qpat_x_assum `todo = _` SUBST_ALL_TAC >>
  drule_at (Pat `dft_head_bubbles _ _ _`) native_successful_cut_call_inputs >>
  disch_then irule >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> metis_tac[dft_crossing_swap_pair]
QED
Resume native_cut_invoke_extension[setup]:
  qpat_x_assum `(if _ then _ else _)` mp_tac >> simp[] >> strip_tac >>
  `!op. MEM op ops ==> MEM op i.inst_operands` by
    (fs[decode_invoke_def, AllCaseEqs()] >> metis_tac[MEM]) >>
  `eval_operands ops q = eval_operands ops a` by
    (irule eval_operands_agree >> rpt strip_tac >> metis_tac[gas_eval_operand]) >>
  simp[] >> reverse conj_tac >- simp[gas_setup_callee] >>
  qpat_x_assum `!callee vals. _` (qspecl_then [`cf`, `args`] mp_tac) >>
  simp[gas_setup_callee] >>
  Cases_on `setup_callee cf args q` >> simp[] >> strip_tac >>
  drule gas_setup_callee_readings >> strip_tac >>
  `q.vs_gas_readings = gc ++ gpost ++ tail` by
    (qpat_x_assum `q.vs_gas_readings = _` mp_tac >> asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >> simp[]) >>
  qpat_x_assum `_ with vs_gas_readings := [] = _`
    (mp_tac o Q.AP_TERM `\z. z with vs_gas_readings := x.vs_gas_readings`) >>
  simp[venom_state_component_equality]
QED
Resume native_cut_invoke_extension[child_and_merge]:
  `ALL_DISTINCT (MAP (\x. x.inst_id) (DROP t.vs_inst_idx bt.bb_instructions))` by
    (`MAP (\x. x.inst_id) (consumed ++ i::later) = MAP (\x. x.inst_id) actual_body` by
       (simp_tac pure_ss [MAP_EQ_EVERY2] >> metis_tac[LIST_REL_LENGTH]) >> metis_tac[]) >>
  `decode_invoke i = SOME (nm,ops) /\
   lookup_function nm C.ctx_functions = SOME cf /\
   lookup_function nm C'.ctx_functions = SOME cf'` by
    (qpat_x_assum `(if _ then _ else _)` mp_tac >> simp[] >> metis_tac[]) >>
  qpat_x_assum `step_inst n C i q = OK r` mp_tac >>
  simp[Once step_inst_def] >> simp[AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `run_blocks n C cf _ = IntRet _ _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> strip_tac >>
  drule_all (BETA_RULE native_selected_child_return_replay) >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `callee_s' with vs_gas_readings := [] = _` kall_tac >>
      qpat_x_assum `!callee vals. _` kall_tac >> qpat_x_assum `fn' = _` kall_tac >>
      qpat_x_assum `bt = _` kall_tac >> qpat_x_assum `K' = _` kall_tac >>
      qpat_x_assum `g = _` kall_tac >>
      simp[Once ev_step_def, gas_eval_operands] >> simp_tac pure_ss [Abbr `orc`] >>
      simp[gas_merge_callee, gas_adopt_return, gas_bind_outputs]) >>
  conj_tac >- (drule gas_bind_outputs_readings >> simp[]) >>
  simp[Once (cj 1 dftGasFromListTraceDefsTheory.trace_defs), Once gas_events_step_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> asm_rewrite_tac[]
QED
Finalise native_cut_invoke_extension

Theorem native_cut_fold_continuation[local]:
  !xs s k.
  EVERY (\i. ~is_terminator i.inst_opcode) xs ==>
  FOLDR (dft_exec_cons n C) k xs s =
    case FOLDR (dft_exec_cons n C) OK xs s of OK u => k u | other => other
Proof
  Induct >- simp[] >>
  rpt gen_tac >> simp_tac bool_ss [EVERY_DEF, FOLDR] >> strip_tac >>
  simp_tac bool_ss [dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst n C h s` >>
  qpat_x_assum `!s k. _` (qspecl_then [`v with vs_inst_idx := SUC s.vs_inst_idx`, `k`] mp_tac) >> simp[]
QED

Theorem native_successful_cut_inventory:
  !body key_rows site_rows certs.
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv fn bb todo t /\
  (s with vs_gas_readings := []) = (t with vs_gas_readings := []) /\
  dft_head_bubbles (\x y.
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo scheduled /\
  EVERY (from_block bb.bb_instructions) body /\
  LIST_REL (\h x. h.inst_id = x.inst_id) scheduled body /\
  bt = bb with bb_instructions := REPLICATE j pad ++ body /\ t.vs_inst_idx = j /\
  ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
  ~t.vs_call_ctx.cc_static /\ terminates (exec_block b C' bt t) /\
  gas_count_block b C' bt t <= LENGTH t.vs_gas_readings /\
  (?post. todo = P ++ post) /\
  LENGTH key_rows = LENGTH P /\ LENGTH site_rows = LENGTH P /\ LENGTH certs = LENGTH P /\
  (!h. h < LENGTH P ==>
    ^native_inventory_Rq
      (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))
      (EL h P) (EL h key_rows) (EL h site_rows) (EL h certs)) /\
  ALL_DISTINCT (FLAT key_rows) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (MAP (ALOOKUP (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)))
      (FLAT key_rows)) g ==>
  !A n rest frontpost q.
    todo = A ++ rest /\ P = A ++ frontpost /\
    EVERY (\i. ~is_terminator i.inst_opcode) A /\
    FOLDR (dft_exec_cons n C) OK A (s with vs_gas_readings := g ++ tail) = OK q ==>
    let KA = FLAT (TAKE (LENGTH A) key_rows);
        SA = FLAT (TAKE (LENGTH A) site_rows) in
    let m = LENGTH KA;
        orc = (\key. case ALOOKUP
          (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) ++
           ZIP (FLAT key_rows,g)) key of NONE => 0w | SOME w => w) in
    inv_ev_trace orc p d b C' A (t with vs_gas_readings := []) (q with vs_gas_readings := []) /\
    q.vs_gas_readings = DROP m (g ++ tail) /\
    q.vs_inst_idx = s.vs_inst_idx + LENGTH A /\
    dft_remaining_inv fn bb rest q /\
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn
      (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ A)
      (s with vs_gas_readings := g ++ tail)) = ZIP (KA,TAKE m g) /\
    gas_events_block n C fn.fn_name
      (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ A)
      (s with vs_gas_readings := g ++ tail) = SA
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac rich_listTheory.SNOC_INDUCT >> conj_tac
  >- (rpt gen_tac >> simp[] >> strip_tac >> gvs[] >>
      simp[inv_ev_trace_def, Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs),
           Once gas_events_block_def, get_instruction_def] >>
      irule dft_remaining_inv_gas_variant >>
      qexists_tac `t` >> simp[] >>
      qpat_x_assum `s with vs_gas_readings := [] = _`
        (mp_tac o Q.AP_TERM `\x. x with vs_gas_readings := t.vs_gas_readings`) >> simp[]) >>
  qx_gen_tac `A` >> strip_tac >> qx_gen_tac `i` >>
  rpt gen_tac >> rewrite_tac[rich_listTheory.SNOC_APPEND] >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) A /\ ~is_terminator i.inst_opcode` by
    gvs[EVERY_APPEND] >>
  `?u r. FOLDR (dft_exec_cons n C) OK A (s with vs_gas_readings := g ++ tail) = OK u /\
     step_inst n C i u = OK r /\ q = r with vs_inst_idx := SUC u.vs_inst_idx` by
    (qpat_x_assum `FOLDR _ _ _ _ = OK q` mp_tac >>
     simp[rich_listTheory.FOLDR_APPEND] >>
     asm_simp_tac bool_ss [Once native_cut_fold_continuation] >>
     Cases_on `FOLDR (dft_exec_cons n C) OK A (s with vs_gas_readings := g ++ tail)` >>
     simp[dftIndexedExecTheory.dft_exec_cons_def] >>
     Cases_on `step_inst n C i v` >> simp[]) >>
  `todo = A ++ i::rest /\ P = A ++ i::frontpost` by gvs[APPEND_ASSOC] >>
  first_x_assum (qspecl_then [`n`, `i::rest`, `i::frontpost`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  suspend "extension"
QED
Resume native_successful_cut_inventory[extension]:
  `LENGTH A < LENGTH P` by simp[] >>
  `LENGTH A < LENGTH key_rows /\ LENGTH A < LENGTH site_rows` by metis_tac[] >>
  qmatch_asmsub_abbrev_tac `ALL_DISTINCT keys_all` >>
  qabbrev_tac `Kpre = FLAT (TAKE (LENGTH A) key_rows)` >>
  qabbrev_tac `Kc = EL (LENGTH A) key_rows` >>
  qabbrev_tac `Kpost = FLAT (DROP (SUC (LENGTH A)) key_rows)` >>
  qabbrev_tac `Sc = EL (LENGTH A) site_rows` >>
  `keys_all = Kpre ++ Kc ++ Kpost` by
    (simp_tac pure_ss [Abbr `keys_all`, Abbr `Kpre`, Abbr `Kc`, Abbr `Kpost`] >>
     qspecl_then [`LENGTH A`, `key_rows`] mp_tac rich_listTheory.TAKE_DROP_SUC >>
     simp[] >> disch_then (mp_tac o Q.AP_TERM `FLAT`) >> simp[]) >>
  `FLAT (TAKE (LENGTH A + 1) key_rows) = Kpre ++ Kc /\
   FLAT (TAKE (LENGTH A + 1) site_rows) = FLAT (TAKE (LENGTH A) site_rows) ++ Sc` by
    simp[rich_listTheory.TAKE_EL_SNOC, rich_listTheory.SNOC_APPEND,
         Abbr `Kpre`, Abbr `Kc`, Abbr `Sc`] >>
  `LENGTH keys_all = LENGTH g` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `?gpre gc gpost. g = gpre ++ gc ++ gpost /\
    LENGTH Kpre = LENGTH gpre /\ LENGTH Kc = LENGTH gc /\ LENGTH Kpost = LENGTH gpost` by
    (qexistsl_tac [`TAKE (LENGTH Kpre) g`,
       `TAKE (LENGTH Kc) (DROP (LENGTH Kpre) g)`,
       `DROP (LENGTH Kc) (DROP (LENGTH Kpre) g)`] >>
     conj_tac >- metis_tac[TAKE_DROP, APPEND_ASSOC] >> simp[] >> gvs[] >> simp[]) >>
  `^native_inventory_Rq
    (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))
    i Kc Sc (EL (LENGTH A) certs)` by
    (qpat_x_assum `!h. h < LENGTH P ==> _` (qspec_then `LENGTH A` mp_tac) >>
     simp[EL_APPEND_EQN, Abbr `Kc`, Abbr `Sc`]) >>
  `ev_step
    (\key. case ALOOKUP
      (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) ++ ZIP (keys_all,g)) key of
      NONE => 0w | SOME w => w)
    p d b C' i (u with vs_gas_readings := []) = OK (r with vs_gas_readings := []) /\
    r.vs_gas_readings = gpost ++ tail /\
    trace_gas (((p,d,i.inst_id),fn,i,u)::
      dftGasFromListTraceDefs$trace_step p d n C fn i u) = ZIP (Kc,gc) /\
    gas_events_step n C fn.fn_name i u = Sc` by suspend "row_step" >>
  suspend "append_rows"
QED
Resume native_successful_cut_inventory[row_step]:
  Cases_on `i.inst_opcode = INVOKE`
  >- (simp[visit_gas_def] >>
      qpat_x_assum `(\obs i Kc Sc cert. _) _ _ _ _ _` mp_tac >>
      simp_tac bool_ss [LET_THM] >> simp[] >> strip_tac >>
      `MEM i scheduled` by
        (`PERM todo scheduled` by metis_tac[native_bubbles_perm] >>
         metis_tac[PERM_MEM_EQ, MEM_APPEND, MEM]) >>
      `?consumed later. scheduled = consumed ++ i::later` by metis_tac[MEM_SPLIT] >>
      irule (BETA_RULE native_cut_invoke_extension) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >>
      gvs[Abbr `Kpre`, Abbr `keys_all`] >>
      rpt conj_tac >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  suspend "plain_step"
QED
Resume native_successful_cut_inventory[append_rows]:
  simp_tac bool_ss [LET_THM, LENGTH_APPEND, LENGTH] >>
  conj_tac
  >- (rewrite_tac[inv_ev_trace_append] >>
      qexists_tac `u with vs_gas_readings := []` >> conj_tac
      >- (asm_rewrite_tac[]) >>
      simp[inv_ev_trace_def] >> qexists_tac `r with vs_gas_readings := []` >>
      simp[] >> qpat_x_assum `ev_step _ _ _ _ _ _ _ = _` mp_tac >> simp[]) >>
  conj_tac
  >- (simp[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp_tac list_ss [DROP_APPEND2]) >>
  conj_tac
  >- (drule_all (SRULE [] (Q.INST [`pre` |-> `[]`] (SPEC_ALL dft_remaining_inv_step))) >>
      simp[]) >>
  suspend "native_append"
QED
Resume native_successful_cut_inventory[native_append]:
  `trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn
      (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ (A ++ [i]))
      (s with vs_gas_readings := g ++ tail)) =
    ZIP (Kpre,TAKE (LENGTH Kpre) g) ++
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn
      (bb with bb_instructions := REPLICATE u.vs_inst_idx pad ++ [i]) u) /\
   gas_events_block n C fn.fn_name
      (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ (A ++ [i]))
      (s with vs_gas_readings := g ++ tail) =
    FLAT (TAKE (LENGTH A) site_rows) ++
    gas_events_block n C fn.fn_name
      (bb with bb_instructions := REPLICATE u.vs_inst_idx pad ++ [i]) u` by
    (mp_tac (Q.SPEC `A` native_prefix_cut) >>
     disch_then (qspec_then `s with vs_gas_readings := g ++ tail` mp_tac) >>
     disch_then (qspec_then `s.vs_inst_idx` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (qspecl_then [`n`, `C`, `fn`, `p`, `d`] mp_tac) >>
     disch_then (qspecl_then [`[i]`, `bb`, `pad`] mp_tac) >>
     simp_tac (srw_ss()) [LET_THM] >>
     qpat_assum `FOLDR _ _ A _ = OK u` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [] >> strip_tac >>
     asm_simp_tac bool_ss [arithmeticTheory.ADD_COMM]) >>
  `trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn
      (bb with bb_instructions := REPLICATE u.vs_inst_idx pad ++ [i]) u) = ZIP (Kc,gc) /\
   gas_events_block n C fn.fn_name
      (bb with bb_instructions := REPLICATE u.vs_inst_idx pad ++ [i]) u = Sc` by
    (conj_tac
     >- (once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs] >>
         simp[get_instruction_def, EL_APPEND_EQN] >>
         simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs),
              get_instruction_def, trace_gas_append, trace_gas_cons] >>
         qpat_x_assum `trace_gas (_::_) = ZIP (Kc,gc)` mp_tac >>
         simp[trace_gas_cons]) >>
     once_rewrite_tac[gas_events_block_def] >>
     simp[get_instruction_def, EL_APPEND_EQN] >>
     simp[Once gas_events_block_def, get_instruction_def]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  qpat_assum `trace_gas (dftGasFromListTraceDefs$trace_block _ _ _ _ _
    (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ (A ++ [i])) _) = _`
    (fn th => rewrite_tac[th]) >>
  qpat_assum `gas_events_block _ _ _
    (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ (A ++ [i])) _ = _`
    (fn th => rewrite_tac[th]) >>
  simp[rich_listTheory.ZIP_APPEND, rich_listTheory.TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
  `LENGTH gpre - (LENGTH gc + LENGTH gpre) = 0` by decide_tac >> simp[]
QED
Resume native_successful_cut_inventory[plain_step]:
  qpat_x_assum `(\obs i Kc Sc cert. _) _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [LET_THM] >> simp[] >> strip_tac >>
  Cases_on `i.inst_opcode = GAS`
  >- suspend "gas_step" >>
  gvs[] >>
  drule_all dftBlockSimTheory.step_inst_ok_non_gas_oracle >> strip_tac >>
  conj_tac
  >- (simp[Once ev_step_def] >> metis_tac[step_inst_non_invoke]) >>
  simp[visit_gas_def, trace_step_noninvoke, gas_events_step_def] >>
  qpat_x_assum `u.vs_gas_readings = _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >> simp[]
QED
Resume native_successful_cut_inventory[gas_step]:
  `?w. gc = [w]` by (Cases_on `gc` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  gvs[] >>
  `u.vs_gas_readings = w::(gpost ++ tail)` by
    (qpat_x_assum `u.vs_gas_readings = _` mp_tac >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >> simp[]) >>
  qmatch_goalsub_abbrev_tac `ev_step orc` >>
  `orc (p,d,i.inst_id) = w` by suspend "gas_lookup" >>
  qpat_x_assum `step_inst n C i u = OK r` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_gas_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  simp[Once ev_step_def, visit_gas_def, trace_step_noninvoke,
       gas_events_step_def, update_var_def, ev_gas_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp_tac bool_ss [APPEND, list_case_def]
QED
Resume native_successful_cut_inventory[gas_lookup]:
  qmatch_asmsub_abbrev_tac `ALOOKUP obs (p,d,i.inst_id)` >>
  `ALOOKUP obs (p,d,i.inst_id) = NONE \/ ALOOKUP obs (p,d,i.inst_id) = SOME w` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     simp[LIST_REL_APPEND_EQ, LENGTH_MAP]) >>
  `ALOOKUP (ZIP (Kpre ++ [(p,d,i.inst_id)] ++ Kpost,gpre ++ [w] ++ gpost))
      (p,d,i.inst_id) = SOME w` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     simp[MAP_ZIP, GSYM rich_listTheory.ZIP_APPEND, MEM_APPEND]) >>
  simp[Abbr `orc`, alistTheory.ALOOKUP_APPEND]
QED
Finalise native_successful_cut_inventory

Theorem native_lookup_fill_schedule_result:
  !body K g.
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  dft_remaining_inv fn bb todo t /\ ~t.vs_call_ctx.cc_static /\
  dft_head_bubbles (\x y.
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo scheduled /\
  EVERY (from_block bb.bb_instructions) body /\
  LIST_REL (\h i. h.inst_id = i.inst_id) scheduled body /\
  bt = bb with bb_instructions := REPLICATE j pad ++ body /\ t.vs_inst_idx = j /\
  ctx_inst_ids_distinct C' /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (DROP t.vs_inst_idx bt.bb_instructions)) ==>
  let obs = trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t);
      orc = (\key. case ALOOKUP (obs ++ ZIP (K,g)) key of
        NONE => 0w | SOME w => w)
  in dft_res_rel
    (ev_suffix orc p d b C' todo (t with vs_gas_readings := []))
    (restore_result [] (exec_block b C' bt t))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp_tac pure_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `ev_suffix orc` >>
  `ALL_DISTINCT (MAP FST (trace_gas
     (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)))` by
    (irule trace_gas_names_distinct >> irule native_inventory_suffix_distinct >> simp[] >>
     qpat_x_assum `ctx_inst_ids_distinct C'` mp_tac >>
     simp_tac bool_ss [ctx_inst_ids_distinct_def] >> strip_tac >>
     simp[EVERY_MEM] >> rpt strip_tac >>
     drule_all venomWfPropsTheory.all_distinct_flat_map_member >> BETA_TAC >> strip_tac >>
     drule_all venomWfPropsTheory.all_distinct_flat_map_member >> simp[]) >>
  `trace_agrees orc (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)` by
    (simp_tac pure_ss [Abbr `orc`] >>
     irule (cj 1 native_lookup_fill_subtrace_agreement) >> simp[EVERY_MEM]) >>
  `restore_rel [] (exec_block b C' bt t)
     (ev_block orc p d b C' bt (t with vs_gas_readings := []))` by
    (irule (cj 2 dftGasFromListReplayTheory.trace_replay) >> qexists_tac `fn'` >> simp[]) >>
  `dft_remaining_inv fn bb todo (t with vs_gas_readings := [])` by
    (qpat_x_assum `dft_remaining_inv fn bb todo t` mp_tac >>
     simp[dft_remaining_inv_def, venomWfPropsTheory.strict_dom_vars_defined_def] >>
     metis_tac[]) >>
  `dft_res_rel
     (ev_suffix orc p d b C' todo (t with vs_gas_readings := []))
     (ev_suffix orc p d b C' scheduled (t with vs_gas_readings := []))` by
    (drule dftGasSimScheduleTheory.ev_head_bubbles >>
     disch_then irule >> simp[] >> qexists_tac `fn` >> simp[]) >>
  `EVERY (\i. MEM i bb.bb_instructions) scheduled` by
    (drule native_bubbles_perm >>
     disch_then (mp_tac o MATCH_MP PERM_MEM_EQ) >>
     fs[dft_remaining_inv_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  rename1 `EVERY (from_block bb.bb_instructions) actual_body` >>
  `ev_suffix orc p d b C' scheduled (t with vs_gas_readings := []) =
   ev_suffix orc p d b C' actual_body (t with vs_gas_readings := [])` by
    (irule dftGasSimScheduleTheory.ev_normalized_suffix_eq >> metis_tac[]) >>
  `ev_suffix orc p d b C' actual_body (t with vs_gas_readings := []) =
   ev_block orc p d b C' bt (t with vs_gas_readings := [])` by
    (irule dftGasSimBoundaryTheory.ev_suffix_block >> simp[DROP_APPEND]) >>
  qpat_x_assum `dft_res_rel _ _` mp_tac >>
  qpat_x_assum `restore_rel [] _ _` mp_tac >>
  simp[] >>
  Cases_on `exec_block b C' bt t` >>
  simp[restore_result_def, dft_res_rel_def, restore_rel_cases] >>
  rpt strip_tac >> gvs[dft_res_rel_def]
QED

Theorem native_selected_child_stopped_transport:
  !K.
  ^native_inventory_Rq
    (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))
    i Kc Sc (SOME (a,nm,ops,args,cf,cf',cs,ct,Uc)) /\
  i.inst_opcode = INVOKE /\
  ALL_DISTINCT (A ++ i::srcpost) /\
  dft_head_bubbles R (A ++ i::srcpost) (consumed ++ i::later) /\
  (!x y. R x y ==> dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y) /\
  inv_ev_trace orc p d b C' A
    (t with vs_gas_readings := []) (q with vs_gas_readings := []) /\
  inv_ev_trace orc p d b C' consumed
    (t with vs_gas_readings := []) (a with vs_gas_readings := []) /\
  K = Kpre ++ Kc ++ Kpost /\ g = gpre ++ gc ++ gpost /\
  LENGTH Kpre = LENGTH gpre /\ LENGTH Kc = LENGTH gc /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (MAP (ALOOKUP (trace_gas
      (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))) K) g /\
  q.vs_gas_readings = gc ++ gpost ++ tail /\
  ~(?u. step_inst n C i q = OK u) ==>
  (?k. k <= LENGTH Kc /\
    trace_gas (dftGasFromListTraceDefs$trace_step p d n C fn i q) =
      ZIP (TAKE k Kc, TAKE k gc) /\
    gas_events_step n C fn.fn_name i q = TAKE k Sc) /\
  (terminates (step_inst n C i q) ==>
    terminates (step_inst b C i q) /\
    ~(?u. step_inst b C i q = OK u) /\
    dft_res_rel (restore_result [] (step_inst b C i q))
      (restore_result [] (step_inst b C' i a)))
Proof
  gen_tac >> BETA_TAC >> strip_tac >>
  `(!op. MEM op i.inst_operands ==>
      eval_operand op (q with vs_gas_readings := []) =
      eval_operand op (a with vs_gas_readings := [])) /\
   (!callee vals. setup_callee callee vals (q with vs_gas_readings := []) =
      setup_callee callee vals (a with vs_gas_readings := []))` by
    (irule native_successful_cut_call_inputs >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `eval_operands ops q = SOME args /\
   setup_callee cf args q = SOME (cs with vs_gas_readings := gc ++ gpost ++ tail)` by
    suspend "setup" >>
  qpat_x_assum `(if _ then _ else _)` mp_tac >>
  simp[LET_THM] >> strip_tac >>
  gvs[MAP_APPEND, LIST_REL_APPEND_EQ] >>
  qpat_x_assum `!g' tail'. LIST_REL _ _ g' ==> _`
    (qspecl_then [`gc`, `gpost ++ tail`] mp_tac) >>
  simp[] >> strip_tac >>
  conj_tac >- suspend "prefix" >>
  suspend "result"
QED
Resume native_selected_child_stopped_transport[setup]:
  qpat_x_assum `(if _ then _ else _)` mp_tac >> simp[] >> strip_tac >>
  `!op. MEM op ops ==> MEM op i.inst_operands` by
    (fs[decode_invoke_def, AllCaseEqs()] >> metis_tac[MEM]) >>
  `eval_operands ops q = eval_operands ops a` by
    (irule eval_operands_agree >> rpt strip_tac >> metis_tac[gas_eval_operand]) >>
  simp[] >>
  qpat_x_assum `!callee vals. _` (qspecl_then [`cf`, `args`] mp_tac) >>
  simp[gas_setup_callee] >>
  Cases_on `setup_callee cf args q` >> simp[] >> strip_tac >>
  drule gas_setup_callee_readings >> strip_tac >>
  qpat_x_assum `_ with vs_gas_readings := [] = _`
    (mp_tac o Q.AP_TERM `\z. z with vs_gas_readings := x.vs_gas_readings`) >>
  simp[venom_state_component_equality]
QED
Resume native_selected_child_stopped_transport[prefix]:
  qpat_x_assum `!n'. ?k. _ /\ _ /\ _` (qspec_then `n` strip_assume_tac) >>
  qexists_tac `k` >>
  simp[Once (cj 1 dftGasFromListTraceDefsTheory.trace_defs),
       Once gas_events_step_def]
QED
Resume native_selected_child_stopped_transport[result]:
  strip_tac >>
  `terminates (run_blocks n C cf (cs with vs_gas_readings := gc ++ gpost ++ tail))` by
    (qpat_x_assum `terminates (step_inst _ _ _ _)` mp_tac >>
     simp[Once step_inst_def] >>
     Cases_on `run_blocks n C cf (cs with vs_gas_readings := gc ++ gpost ++ tail)` >>
     simp[passSimulationDefsTheory.terminates_def, AllCaseEqs()]) >>
  qpat_x_assum `(?n'. terminates _) ==> _` mp_tac >>
  impl_tac >- metis_tac[] >> strip_tac >>
  `run_blocks n C cf (cs with vs_gas_readings := gc ++ gpost ++ tail) =
   run_blocks b C cf (cs with vs_gas_readings := gc ++ gpost ++ tail)` by
    (Cases_on `n <= b`
     >- (sym_tac >> irule (cj 3 venomExecProofsTheory.fuel_mono) >>
         conj_tac
         >- (Cases_on `run_blocks n C cf (cs with vs_gas_readings := gc ++ gpost ++ tail)` >>
             gvs[passSimulationDefsTheory.terminates_def]) >>
         qexists_tac `n` >> simp[]) >>
     irule (cj 3 venomExecProofsTheory.fuel_mono) >> conj_tac
     >- (Cases_on `run_blocks b C cf (cs with vs_gas_readings := gc ++ gpost ++ tail)` >>
         gvs[passSimulationDefsTheory.terminates_def]) >>
     qexists_tac `b` >> simp[]) >>
  `step_inst b C i q = step_inst n C i q` by simp[step_inst_def] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  Cases_on `run_blocks b C cf (cs with vs_gas_readings := gc ++ gpost ++ tail)` >>
  gvs[step_inst_def, passSimulationDefsTheory.terminates_def,
      restore_result_def, dft_res_rel_def, AllCaseEqs()]
QED
Finalise native_selected_child_stopped_transport

Theorem native_inventory_stopped_cut_prefix:
  !body key_rows site_rows certs.
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv fn bb todo t /\
  (s with vs_gas_readings := []) = (t with vs_gas_readings := []) /\
  dft_head_bubbles (\x y.
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo scheduled /\
  EVERY (from_block bb.bb_instructions) body /\
  LIST_REL (\h x. h.inst_id = x.inst_id) scheduled body /\
  bt = bb with bb_instructions := REPLICATE j pad ++ body /\ t.vs_inst_idx = j /\
  ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
  ~t.vs_call_ctx.cc_static /\ terminates (exec_block b C' bt t) /\
  gas_count_block b C' bt t <= LENGTH t.vs_gas_readings /\
  (?post. todo = P ++ post) /\
  LENGTH key_rows = LENGTH P /\ LENGTH site_rows = LENGTH P /\ LENGTH certs = LENGTH P /\
  (!h. h < LENGTH P ==>
    ^native_inventory_Rq
      (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))
      (EL h P) (EL h key_rows) (EL h site_rows) (EL h certs)) /\
  ALL_DISTINCT (FLAT key_rows) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (MAP (ALOOKUP (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)))
      (FLAT key_rows)) g ==>
  !A i n rest frontpost q.
    todo = A ++ i::rest /\ P = A ++ i::frontpost /\
    EVERY (\x. ~is_terminator x.inst_opcode) A /\
    FOLDR (dft_exec_cons n C) OK A (s with vs_gas_readings := g ++ tail) = OK q /\
    (is_terminator i.inst_opcode \/ ~(?u. step_inst n C i q = OK u)) ==>
    ?k. k <= LENGTH (FLAT key_rows) /\
      trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn
        (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
        (s with vs_gas_readings := g ++ tail)) =
        ZIP (TAKE k (FLAT key_rows), TAKE k g) /\
      gas_events_block n C fn.fn_name
        (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
        (s with vs_gas_readings := g ++ tail) = TAKE k (FLAT site_rows)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  rename1 `EVERY (from_block bb.bb_instructions) actual_body` >>
  mp_tac (Q.SPECL [`actual_body`, `key_rows`, `site_rows`, `certs`]
    native_successful_cut_inventory) >>
  (impl_tac >- (simp[] >> gvs[])) >>
  disch_then (qspecl_then [`A`, `n`, `i::rest`, `i::frontpost`, `q`] mp_tac) >>
  qpat_x_assum `todo = A ++ i::rest /\ _` strip_assume_tac >>
  (impl_tac >- asm_rewrite_tac[]) >>
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  `LENGTH A < LENGTH P` by simp[] >>
  `LENGTH A < LENGTH key_rows /\ LENGTH A < LENGTH site_rows` by metis_tac[] >>
  qabbrev_tac `Kpre = FLAT (TAKE (LENGTH A) key_rows)` >>
  qabbrev_tac `Kc = EL (LENGTH A) key_rows` >>
  qabbrev_tac `Kpost = FLAT (DROP (SUC (LENGTH A)) key_rows)` >>
  qabbrev_tac `Spre = FLAT (TAKE (LENGTH A) site_rows)` >>
  qabbrev_tac `Sc = EL (LENGTH A) site_rows` >>
  qabbrev_tac `Spost = FLAT (DROP (SUC (LENGTH A)) site_rows)` >>
  `FLAT key_rows = Kpre ++ Kc ++ Kpost /\
   FLAT site_rows = Spre ++ Sc ++ Spost` by
    (conj_tac
     >- (simp_tac pure_ss [Abbr `Kpre`, Abbr `Kc`, Abbr `Kpost`] >>
         qspecl_then [`LENGTH A`, `key_rows`] mp_tac rich_listTheory.TAKE_DROP_SUC >>
         simp[] >> disch_then (mp_tac o Q.AP_TERM `FLAT`) >> simp[]) >>
     simp_tac pure_ss [Abbr `Spre`, Abbr `Sc`, Abbr `Spost`] >>
     qspecl_then [`LENGTH A`, `site_rows`] mp_tac rich_listTheory.TAKE_DROP_SUC >>
     simp[] >> disch_then (mp_tac o Q.AP_TERM `FLAT`) >> simp[]) >>
  `LENGTH (FLAT key_rows) = LENGTH g` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `?gpre gc gpost. g = gpre ++ gc ++ gpost /\
    LENGTH Kpre = LENGTH gpre /\ LENGTH Kc = LENGTH gc /\ LENGTH Kpost = LENGTH gpost` by
    (qexistsl_tac [`TAKE (LENGTH Kpre) g`,
       `TAKE (LENGTH Kc) (DROP (LENGTH Kpre) g)`,
       `DROP (LENGTH Kc) (DROP (LENGTH Kpre) g)`] >>
     conj_tac >- metis_tac[TAKE_DROP, APPEND_ASSOC] >> simp[] >> gvs[] >> simp[]) >>
  `^native_inventory_Rq
    (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))
    i Kc Sc (EL (LENGTH A) certs)` by
    (qpat_x_assum `!h. h < LENGTH P ==> _` (qspec_then `LENGTH A` mp_tac) >>
     simp[EL_APPEND_EQN, Abbr `Kc`, Abbr `Sc`]) >>
  `q.vs_gas_readings = gc ++ gpost ++ tail` by
    (qpat_x_assum `q.vs_gas_readings = _` mp_tac >>
     simp_tac pure_ss [GSYM APPEND_ASSOC, Abbr `Kpre`] >>
     asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp_tac bool_ss []) >>
  `?kc. kc <= LENGTH Kc /\
    trace_gas (((p,d,i.inst_id),fn,i,q)::
      dftGasFromListTraceDefs$trace_step p d n C fn i q) = ZIP (TAKE kc Kc,TAKE kc gc) /\
    gas_events_step n C fn.fn_name i q = TAKE kc Sc` by suspend "row" >>
  suspend "compose"
QED
Resume native_inventory_stopped_cut_prefix[row]:
  markerLib.RESUME_TAC >> (
  Cases_on `i.inst_opcode = INVOKE` >- suspend "invoke" >>
  qpat_x_assum `(\obs i Kc Sc cert. _) _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [LET_THM] >> simp[] >> strip_tac >>
  Cases_on `i.inst_opcode = GAS` >- suspend "gas" >>
  qexists_tac `0` >> gvs[] >>
  simp[trace_gas_cons, visit_gas_def, trace_step_noninvoke, gas_events_step_def])
QED
Resume native_inventory_stopped_cut_prefix[gas]:
  markerLib.RESUME_TAC >> (
  `?w. gc = [w]` by (Cases_on `gc` >> gvs[LENGTH_EQ_NUM_compute]) >>
  qexists_tac `1` >> gvs[] >>
  simp[trace_gas_cons, visit_gas_def, trace_step_noninvoke, gas_events_step_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp_tac (srw_ss()) [])
QED
Resume native_inventory_stopped_cut_prefix[invoke]:
  markerLib.RESUME_TAC >> (
  `~is_terminator i.inst_opcode` by
    (qpat_assum `i.inst_opcode = INVOKE` (fn th => rewrite_tac[th, is_terminator_def])) >>
  `~(?u. step_inst n C i q = OK u)` by metis_tac[] >>
  qpat_assum `(\obs i Kc Sc cert. _) _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [LET_THM] >> asm_rewrite_tac[] >> strip_tac >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT todo /\ EVERY (\x. MEM x bb.bb_instructions) todo` by
    (qpat_x_assum `dft_remaining_inv fn bb todo t` mp_tac >>
     simp_tac bool_ss [dft_remaining_inv_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) todo)` by
    (irule ALL_DISTINCT_MAP_INJ >> asm_rewrite_tac[] >> rpt strip_tac >>
     irule (Q.ISPEC `\x:instruction. x.inst_id` dftCorrectnessTheory.all_distinct_map_mem_inj) >>
     conj_tac >- asm_rewrite_tac[] >>
     qexists_tac `bb.bb_instructions` >> asm_rewrite_tac[] >>
     qpat_x_assum `EVERY (\x. MEM x bb.bb_instructions) todo` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> metis_tac[]) >>
  `PERM todo scheduled` by metis_tac[native_bubbles_perm] >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) scheduled) /\
   EVERY (\x. MEM x bb.bb_instructions) scheduled` by
    metis_tac[PERM_MAP, ALL_DISTINCT_PERM, PERM_EVERY] >>
  `?consumed later. scheduled = consumed ++ i::later` by
    metis_tac[MEM_SPLIT, PERM_MEM_EQ, MEM_APPEND, MEM] >>
  qpat_x_assum `scheduled = _` SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `inv_ev_trace orc p d b C' A` >>
  `inv_ev_trace orc p d b C' consumed (t with vs_gas_readings := [])
    (a with vs_gas_readings := [])` by
    (simp_tac pure_ss [Abbr `orc`] >> irule native_selected_target_event_cut >> simp[] >>
     conj_tac >- fs[o1_ctx_shape_def] >>
     qexistsl_tac [`bb.bb_instructions`, `i`, `later`] >> simp[DROP_APPEND] >>
     qpat_x_assum `ALL_DISTINCT (MAP _ (consumed ++ i::later))` mp_tac >>
     qpat_x_assum `EVERY _ (consumed ++ i::later)` mp_tac >>
     simp_tac (srw_ss()) [MAP_APPEND, EVERY_APPEND]) >>
  suspend "transport")
QED
Resume native_inventory_stopped_cut_prefix[transport]:
  markerLib.RESUME_TAC >> (
  `?kc. kc <= LENGTH Kc /\
    trace_gas (dftGasFromListTraceDefs$trace_step p d n C fn i q) =
      ZIP (TAKE kc Kc, TAKE kc gc) /\
    gas_events_step n C fn.fn_name i q = TAKE kc Sc` by
    (qpat_assum `inv_ev_trace orc p d b C' A _ _`
       (mp_then (Pat `inv_ev_trace _ _ _ _ _ A _ _`) mp_tac
         (cj 1 native_selected_child_stopped_transport)) >>
     disch_then irule >> suspend "transport_premises") >>
  qexists_tac `kc` >> simp[trace_gas_cons, visit_gas_def])
QED
Resume native_inventory_stopped_cut_prefix[transport_premises]:
  markerLib.RESUME_TAC >> (
  simp_tac bool_ss [] >>
  conj_tac >- gvs[] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  qpat_assum `inv_ev_trace orc p d b C' consumed _ _`
    (irule_at (Pat `inv_ev_trace _ _ _ _ _ _ _ _`)) >>
  qpat_x_assum `todo = A ++ i::rest` SUBST_ALL_TAC >>
  qpat_assum `dft_head_bubbles _ (A ++ i::rest) _`
    (irule_at (Pat `dft_head_bubbles _ _ _`)) >>
  qpat_x_assum `EL (LENGTH A) certs = _` SUBST_ALL_TAC >>
  qpat_assum `(\obs i Kc Sc cert. _) _ _ _ _ _`
    (irule_at (Pat `if _ then _ else _`) o SIMP_RULE bool_ss []) >>
  qpat_assum `q.vs_gas_readings = gc ++ gpost ++ tail`
    (irule_at (Pat `q.vs_gas_readings = _`)) >>
  qpat_assum `LENGTH Kpre = LENGTH gpre`
    (irule_at (Pat `LENGTH _ = LENGTH _`)) >>
  qexists_tac `Kpost` >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac >- asm_rewrite_tac[] >>
  rpt strip_tac >> metis_tac[dft_crossing_swap_pair])
QED
Resume native_inventory_stopped_cut_prefix[compose]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `!h. h < LENGTH P ==> _` kall_tac >>
  qpat_x_assum `(\obs i Kc Sc cert. _) _ _ _ _ _` kall_tac >>
  `trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn
     (bb with bb_instructions := REPLICATE q.vs_inst_idx pad ++ i::rest) q) =
     ZIP (TAKE kc Kc,TAKE kc gc) /\
   gas_events_block n C fn.fn_name
     (bb with bb_instructions := REPLICATE q.vs_inst_idx pad ++ i::rest) q = TAKE kc Sc` by
    suspend "stop_eq" >>
  `trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn
     (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
     (s with vs_gas_readings := g ++ tail)) =
     ZIP (Kpre,TAKE (LENGTH Kpre) g) ++ ZIP (TAKE kc Kc,TAKE kc gc) /\
   gas_events_block n C fn.fn_name
     (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
     (s with vs_gas_readings := g ++ tail) = Spre ++ TAKE kc Sc` by
    suspend "prefix_eq" >>
  suspend "lists")
QED
Resume native_inventory_stopped_cut_prefix[stop_eq]:
  markerLib.RESUME_TAC >> (
  conj_tac
  >- (once_rewrite_tac[cj 2 dftGasFromListTraceDefsTheory.trace_defs] >>
      simp[get_instruction_def, EL_APPEND_EQN] >>
      Cases_on `step_inst n C i q` >> gvs[trace_gas_append]) >>
  once_rewrite_tac[gas_events_block_def] >>
  simp[get_instruction_def, EL_APPEND_EQN] >>
  Cases_on `step_inst n C i q` >> gvs[])
QED
Resume native_inventory_stopped_cut_prefix[prefix_eq]:
  markerLib.RESUME_TAC >> (
  mp_tac (Q.SPEC `A` native_prefix_cut) >>
  disch_then (qspec_then `s with vs_gas_readings := g ++ tail` mp_tac) >>
  disch_then (qspec_then `s.vs_inst_idx` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`n`, `C`, `fn`, `p`, `d`] mp_tac) >>
  disch_then (qspecl_then [`i::rest`, `bb`, `pad`] mp_tac) >>
  simp_tac (srw_ss()) [LET_THM] >>
  qpat_assum `FOLDR _ _ A _ = OK q` (fn th => rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  asm_simp_tac bool_ss [])
  >> (gvs[])
QED
Resume native_inventory_stopped_cut_prefix[lists]:
  markerLib.RESUME_TAC >> (
  `LENGTH Spre = LENGTH Kpre` by
    (qpat_assum `trace_gas (dftGasFromListTraceDefs$trace_block _ _ _ _ _
       (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ A) _) = _`
       (mp_tac o Q.AP_TERM `LENGTH`) >>
     qpat_assum `gas_events_block _ _ _
       (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ A) _ = _`
       (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[dftGasFromListReadingsTheory.trace_gas_lengths, gas_events_length] >>
     gvs[]) >>
  `kc <= LENGTH Sc` by
    (qpat_assum `trace_gas (dftGasFromListTraceDefs$trace_block _ _ _ _ _
       (bb with bb_instructions := REPLICATE q.vs_inst_idx pad ++ i::rest) _) = _`
       (mp_tac o Q.AP_TERM `LENGTH`) >>
     qpat_assum `gas_events_block _ _ _
       (bb with bb_instructions := REPLICATE q.vs_inst_idx pad ++ i::rest) _ = _`
       (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[dftGasFromListReadingsTheory.trace_gas_lengths, gas_events_length] >>
     rpt strip_tac >> metis_tac[rich_listTheory.LENGTH_TAKE_LE]) >>
  `LENGTH gpre - (LENGTH gc + LENGTH gpre) = 0 /\
   kc - LENGTH gc = 0 /\ kc - LENGTH Sc = 0` by decide_tac >>
  qexists_tac `LENGTH Kpre + kc` >>
  conj_tac >- (asm_rewrite_tac[LENGTH_APPEND] >> decide_tac) >>
  simp[rich_listTheory.TAKE_APPEND, TAKE_LENGTH_TOO_LONG,
       rich_listTheory.ZIP_APPEND])
QED
Finalise native_inventory_stopped_cut_prefix

Theorem native_inventory_invoke_budget_equal:
  !body key_rows site_rows certs.
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv fn bb todo t /\
  (s with vs_gas_readings := []) = (t with vs_gas_readings := []) /\
  dft_head_bubbles (\x y.
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo scheduled /\
  EVERY (from_block bb.bb_instructions) body /\
  LIST_REL (\h x. h.inst_id = x.inst_id) scheduled body /\
  bt = bb with bb_instructions := REPLICATE j pad ++ body /\ t.vs_inst_idx = j /\
  ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
  ~t.vs_call_ctx.cc_static /\ terminates (exec_block b C' bt t) /\
  gas_count_block b C' bt t <= LENGTH t.vs_gas_readings /\
  (?post. todo = P ++ post) /\
  LENGTH key_rows = LENGTH P /\ LENGTH site_rows = LENGTH P /\ LENGTH certs = LENGTH P /\
  (!h. h < LENGTH P ==>
    ^native_inventory_Rq
      (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))
      (EL h P) (EL h key_rows) (EL h site_rows) (EL h certs)) /\
  ALL_DISTINCT (FLAT key_rows) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (MAP (ALOOKUP (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)))
      (FLAT key_rows)) g ==>
  !A i rest frontpost n q.
    todo = A ++ i::rest /\ P = A ++ i::frontpost /\
    EVERY (\x. ~is_terminator x.inst_opcode) A /\
    FOLDR (dft_exec_cons n C) OK A (s with vs_gas_readings := g ++ tail) = OK q /\
    i.inst_opcode = INVOKE /\ terminates (step_inst n C i q) ==>
    step_inst b C i q = step_inst n C i q
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  rename1 `EVERY (from_block bb.bb_instructions) actual_body` >>
  mp_tac (Q.SPECL [`actual_body`, `key_rows`, `site_rows`, `certs`]
    native_successful_cut_inventory) >>
  (impl_tac >- (simp[] >> gvs[])) >>
  disch_then (qspecl_then [`A`, `n`, `i::rest`, `i::frontpost`, `q`] mp_tac) >>
  qpat_x_assum `todo = A ++ i::rest /\ _` strip_assume_tac >>
  (impl_tac >- asm_rewrite_tac[]) >>
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  suspend "rows"
QED
Resume native_inventory_invoke_budget_equal[rows]:
  `LENGTH A < LENGTH P` by simp[] >>
  `LENGTH A < LENGTH key_rows /\ LENGTH A < LENGTH site_rows` by metis_tac[] >>
  qabbrev_tac `Kpre = FLAT (TAKE (LENGTH A) key_rows)` >>
  qabbrev_tac `Kc = EL (LENGTH A) key_rows` >>
  qabbrev_tac `Kpost = FLAT (DROP (SUC (LENGTH A)) key_rows)` >>
  qabbrev_tac `Sc = EL (LENGTH A) site_rows` >>
  `FLAT key_rows = Kpre ++ Kc ++ Kpost` by
    (simp_tac pure_ss [Abbr `Kpre`, Abbr `Kc`, Abbr `Kpost`] >>
     qspecl_then [`LENGTH A`, `key_rows`] mp_tac rich_listTheory.TAKE_DROP_SUC >>
     simp[] >> disch_then (mp_tac o Q.AP_TERM `FLAT`) >> simp[]) >>
  `LENGTH (FLAT key_rows) = LENGTH g` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `?gpre gc gpost. g = gpre ++ gc ++ gpost /\
    LENGTH Kpre = LENGTH gpre /\ LENGTH Kc = LENGTH gc /\ LENGTH Kpost = LENGTH gpost` by
    (qexistsl_tac [`TAKE (LENGTH Kpre) g`,
       `TAKE (LENGTH Kc) (DROP (LENGTH Kpre) g)`,
       `DROP (LENGTH Kc) (DROP (LENGTH Kpre) g)`] >>
     conj_tac >- metis_tac[TAKE_DROP, APPEND_ASSOC] >> simp[] >> gvs[] >> simp[]) >>
  `^native_inventory_Rq
    (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))
    i Kc Sc (EL (LENGTH A) certs)` by
    (qpat_x_assum `!h. h < LENGTH P ==> _` (qspec_then `LENGTH A` mp_tac) >>
     simp[EL_APPEND_EQN, Abbr `Kc`, Abbr `Sc`]) >>
  qpat_assum `(\obs i Kc Sc cert. _) _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [LET_THM] >> asm_rewrite_tac[] >> strip_tac >>
  `q.vs_gas_readings = gc ++ gpost ++ tail` by
    (qpat_x_assum `q.vs_gas_readings = _` mp_tac >>
     simp_tac pure_ss [GSYM APPEND_ASSOC, Abbr `Kpre`] >>
     asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp_tac bool_ss []) >>
  suspend "cuts"
QED
Resume native_inventory_invoke_budget_equal[cuts]:
  `ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT todo /\ EVERY (\x. MEM x bb.bb_instructions) todo` by
    (qpat_x_assum `dft_remaining_inv fn bb todo t` mp_tac >>
     simp_tac bool_ss [dft_remaining_inv_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) todo)` by
    (irule ALL_DISTINCT_MAP_INJ >> asm_rewrite_tac[] >> rpt strip_tac >>
     irule (Q.ISPEC `\x:instruction. x.inst_id` dftCorrectnessTheory.all_distinct_map_mem_inj) >>
     conj_tac >- asm_rewrite_tac[] >>
     qexists_tac `bb.bb_instructions` >> asm_rewrite_tac[] >>
     qpat_x_assum `EVERY (\x. MEM x bb.bb_instructions) todo` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> metis_tac[]) >>
  `PERM todo scheduled` by metis_tac[native_bubbles_perm] >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) scheduled) /\
   EVERY (\x. MEM x bb.bb_instructions) scheduled` by
    metis_tac[PERM_MAP, ALL_DISTINCT_PERM, PERM_EVERY] >>
  `?consumed later. scheduled = consumed ++ i::later` by
    metis_tac[MEM_SPLIT, PERM_MEM_EQ, MEM_APPEND, MEM] >>
  qpat_x_assum `scheduled = _` SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `inv_ev_trace orc p d b C' A` >>
  `inv_ev_trace orc p d b C' consumed (t with vs_gas_readings := [])
    (a with vs_gas_readings := [])` by
    (simp_tac pure_ss [Abbr `orc`] >> irule native_selected_target_event_cut >> simp[] >>
     conj_tac >- fs[o1_ctx_shape_def] >>
     qexistsl_tac [`bb.bb_instructions`, `i`, `later`] >> simp[DROP_APPEND] >>
     qpat_x_assum `ALL_DISTINCT (MAP _ (consumed ++ i::later))` mp_tac >>
     qpat_x_assum `EVERY _ (consumed ++ i::later)` mp_tac >>
     simp_tac (srw_ss()) [MAP_APPEND, EVERY_APPEND]) >>
  `(!op. MEM op i.inst_operands ==>
      eval_operand op (q with vs_gas_readings := []) =
      eval_operand op (a with vs_gas_readings := [])) /\
   (!callee vals. setup_callee callee vals (q with vs_gas_readings := []) =
      setup_callee callee vals (a with vs_gas_readings := []))` by
    (qpat_x_assum `todo = A ++ i::rest` SUBST_ALL_TAC >>
     drule_at (Pat `dft_head_bubbles _ _ _`) native_successful_cut_call_inputs >>
     disch_then irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
     rpt strip_tac >> metis_tac[dft_crossing_swap_pair]) >>
  suspend "setup"
QED
Resume native_inventory_invoke_budget_equal[setup]:
  `!op. MEM op ops ==> MEM op i.inst_operands` by
    (fs[decode_invoke_def, AllCaseEqs()] >> metis_tac[MEM]) >>
  `eval_operands ops q = SOME args` by
    (`eval_operands ops q = eval_operands ops a` by
       (irule eval_operands_agree >> rpt strip_tac >> metis_tac[gas_eval_operand]) >>
     simp[]) >>
  `setup_callee cf args q = SOME (cs with vs_gas_readings := gc ++ gpost ++ tail)` by
    (qpat_x_assum `!callee vals. _` (qspecl_then [`cf`, `args`] mp_tac) >>
     simp[gas_setup_callee] >>
     Cases_on `setup_callee cf args q` >> simp[] >> strip_tac >>
     drule gas_setup_callee_readings >> strip_tac >>
     qpat_x_assum `_ with vs_gas_readings := [] = _`
       (mp_tac o Q.AP_TERM `\z. z with vs_gas_readings := x.vs_gas_readings`) >>
     simp[venom_state_component_equality]) >>
  suspend "budget"
QED
Resume native_inventory_invoke_budget_equal[budget]:
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (MAP (ALOOKUP (trace_gas (dftGasFromListTraceDefs$trace_blocks
      ((d,i.inst_id)::p) d b C' (dft_fn cf) cs))) Kc) gc` by
    (gvs[MAP_APPEND, LIST_REL_APPEND_EQ]) >>
  qpat_x_assum `!g' tail'. LIST_REL _ _ g' ==> _`
    (qspecl_then [`gc`, `gpost ++ tail`] mp_tac) >>
  simp[] >> strip_tac >>
  `terminates (run_blocks n C cf (cs with vs_gas_readings := gc ++ gpost ++ tail))` by
    (qpat_x_assum `terminates (step_inst _ _ _ _)` mp_tac >>
     simp[Once step_inst_def] >>
     Cases_on `run_blocks n C cf (cs with vs_gas_readings := gc ++ gpost ++ tail)` >>
     simp[passSimulationDefsTheory.terminates_def, AllCaseEqs()]) >>
  qpat_x_assum `(?n'. terminates _) ==> _` mp_tac >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `run_blocks n C cf (cs with vs_gas_readings := gc ++ gpost ++ tail) =
   run_blocks b C cf (cs with vs_gas_readings := gc ++ gpost ++ tail)` by
    (Cases_on `n <= b`
     >- (sym_tac >> irule (cj 3 venomExecProofsTheory.fuel_mono) >>
         conj_tac
         >- (qpat_x_assum `terminates (run_blocks n C cf _)` mp_tac >>
             Cases_on `run_blocks n C cf (cs with vs_gas_readings := gc ++ gpost ++ tail)` >>
             simp[passSimulationDefsTheory.terminates_def]) >>
         qexists_tac `n` >> simp[]) >>
     irule (cj 3 venomExecProofsTheory.fuel_mono) >> conj_tac
     >- (qpat_x_assum `terminates (run_blocks b C cf _)` mp_tac >>
         Cases_on `run_blocks b C cf (cs with vs_gas_readings := gc ++ gpost ++ tail)` >>
         simp[passSimulationDefsTheory.terminates_def]) >>
     qexists_tac `b` >> simp[]) >>
  simp[step_inst_def]
QED
Finalise native_inventory_invoke_budget_equal

Theorem native_normalized_target_frontier_replay:
  !body.
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  EVERY (\i. MEM i bi) (done ++ z::later) /\
  EVERY (from_block bi) body /\
  LIST_REL (\h i. h.inst_id = i.inst_id) (done ++ z::later) body /\
  bt = bb with bb_instructions := REPLICATE j pad ++ body /\
  t.vs_inst_idx = j /\
  EVERY (\i. ~is_terminator i.inst_opcode) done /\
  FOLDR (dft_exec_cons b C') OK done t = OK tz /\
  trace_agrees orc (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)
  ==>
  inv_ev_trace orc p d b C' done
    (t with vs_gas_readings := []) (tz with vs_gas_readings := []) /\
  restore_rel [] (step_inst b C' z tz)
    (ev_step orc p d b C' z (tz with vs_gas_readings := []))
Proof
  gen_tac >> strip_tac >>
  `trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn'
     (bb with bb_instructions := REPLICATE j pad ++ (done ++ z::later)) t) =
   trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)` by
    (rename1 `EVERY (from_block bi) actual_body` >>
     qspecl_then [`done ++ z::later`, `actual_body`, `t`] mp_tac
       native_normalized_block_observations >>
     simp[] >> disch_then (qspecl_then [`b`, `C'`, `fn'`, `p`, `d`] mp_tac) >> simp[]) >>
  `trace_agrees orc (dftGasFromListTraceDefs$trace_block p d b C' fn'
     (bb with bb_instructions := REPLICATE j pad ++ (done ++ z::later)) t)` by
    metis_tac[trace_agrees_def] >>
  qspecl_then [`done`, `t`, `j`] mp_tac native_prefix_cut >> simp[] >>
  disch_then (qspecl_then [`b`, `C'`, `fn'`, `p`, `d`, `z::later`, `bb`, `pad`] mp_tac) >>
  simp[] >> strip_tac >>
  `trace_agrees orc (dftGasFromListTraceDefs$trace_block p d b C' fn'
     (bb with bb_instructions := REPLICATE j pad ++ done) t) /\
   trace_agrees orc (dftGasFromListTraceDefs$trace_block p d b C' fn'
     (bb with bb_instructions := REPLICATE (j + LENGTH done) pad ++ z::later) tz)` by
    (rule_assum_tac (PURE_REWRITE_RULE [trace_agrees_def, GSYM APPEND_ASSOC, APPEND]) >>
     pure_rewrite_tac[trace_agrees_def, GSYM APPEND_ASSOC, APPEND] >>
     metis_tac[EVERY_APPEND]) >>
  conj_tac
  >- (irule native_fixed_native_prefix >> simp[] >>
      qexistsl_tac [`bb with bb_instructions := REPLICATE j pad ++ done`, `fn'`, `[]`] >>
      simp[DROP_APPEND]) >>
  `trace_agrees orc (((p,d,z.inst_id),fn',z,tz)::
     dftGasFromListTraceDefs$trace_step p d b C' fn' z tz)` by
    (qpat_x_assum `trace_agrees _ (dftGasFromListTraceDefs$trace_block _ _ _ _ _ _ tz)` mp_tac >>
     simp[Once (cj 2 dftGasFromListTraceDefsTheory.trace_defs), get_instruction_def,
          EL_APPEND_EQN, trace_agrees_cons, trace_agrees_append]) >>
  irule (cj 1 dftGasFromListReplayTheory.trace_replay) >>
  qexists_tac `fn'` >> simp[]
QED

Theorem native_inventory_frontier_no_pass:
  !body key_rows site_rows certs.
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv fn bb todo t /\
  (s with vs_gas_readings := []) = (t with vs_gas_readings := []) /\
  dft_head_bubbles (\x y.
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo scheduled /\
  EVERY (from_block bb.bb_instructions) body /\
  LIST_REL (\h x. h.inst_id = x.inst_id) scheduled body /\
  bt = bb with bb_instructions := REPLICATE j pad ++ body /\ t.vs_inst_idx = j /\
  ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
  ~t.vs_call_ctx.cc_static /\ terminates (exec_block b C' bt t) /\
  gas_count_block b C' bt t <= LENGTH t.vs_gas_readings /\
  LENGTH key_rows = LENGTH (before ++ [z]) /\
  LENGTH site_rows = LENGTH (before ++ [z]) /\ LENGTH certs = LENGTH (before ++ [z]) /\
  (!h. h < LENGTH (before ++ [z]) ==>
    ^native_inventory_Rq
      (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))
      (EL h (before ++ [z])) (EL h key_rows) (EL h site_rows) (EL h certs)) /\
  ALL_DISTINCT (FLAT key_rows) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (MAP (ALOOKUP (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)))
      (FLAT key_rows)) g /\
  todo = before ++ z::after /\ scheduled = done ++ z::later /\
  EVERY (\i. ~is_terminator i.inst_opcode) done /\
  FOLDR (dft_exec_cons b C') OK done t = OK tz /\
  ~is_terminator z.inst_opcode /\ ~(?u. step_inst b C' z tz = OK u)
  ==> !n q. ~(FOLDR (dft_exec_cons n C) OK (before ++ [z])
                   (s with vs_gas_readings := g ++ tail) = OK q)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `EVERY (from_block bb.bb_instructions) actual_body` >>
  `PERM todo scheduled` by metis_tac[native_bubbles_perm] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  `EVERY (\i. MEM i bb.bb_instructions) scheduled` by
    (qpat_x_assum `!h. h < _ ==> _` kall_tac >>
     drule PERM_MEM_EQ >> strip_tac >>
     fs[dft_remaining_inv_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (before ++ [z])` by
    (qpat_x_assum `!h. h < _ ==> _` kall_tac >>
     simp[EVERY_APPEND, EVERY_MEM] >> rpt strip_tac >>
     `MEM i bb.bb_instructions /\
      id_before (MAP (\i. i.inst_id) bb.bb_instructions) i.inst_id z.inst_id` by
       (fs[dft_remaining_inv_def, EVERY_MEM] >>
        first_x_assum irule >>
        simp[dftSsaPreserveTheory.id_before_append, id_before_cons]) >>
     metis_tac[dft_wf_order_nonterminator]) >>
  qabbrev_tac `orc = (\key. case ALOOKUP
    (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) ++
     ZIP (FLAT key_rows,g)) key of NONE => 0w | SOME w => w)` >>
  `inv_ev_trace orc p d b C' (before ++ [z])
     (t with vs_gas_readings := []) (q with vs_gas_readings := [])` by
    suspend "source_cut" >>
  `trace_agrees orc (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)` by
    suspend "agreement" >>
  `inv_ev_trace orc p d b C' done
     (t with vs_gas_readings := []) (tz with vs_gas_readings := []) /\
   restore_rel [] (step_inst b C' z tz)
     (ev_step orc p d b C' z (tz with vs_gas_readings := []))` by
    (irule native_normalized_target_frontier_replay >> metis_tac[]) >>
  suspend "contradiction"
QED
Resume native_inventory_frontier_no_pass[source_cut]:
  `todo = (before ++ [z]) ++ after` by simp[] >>
  qspecl_then [`actual_body`, `key_rows`, `site_rows`, `certs`] mp_tac
    (Q.INST [`P` |-> `before ++ [z]`] native_successful_cut_inventory) >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (qspecl_then [`before ++ [z]`, `n`, `after`, `[]`, `q`] mp_tac) >>
  simp_tac bool_ss [APPEND_NIL] >>
  (impl_tac >- asm_rewrite_tac[]) >>
  simp[LET_THM, Abbr `orc`]
QED
Resume native_inventory_frontier_no_pass[agreement]:
  `ALL_DISTINCT scheduled` by
    metis_tac[dft_remaining_inv_def, ALL_DISTINCT_PERM] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) scheduled)` by
    (irule ALL_DISTINCT_MAP_INJ >> reverse conj_tac
     >- asm_rewrite_tac[] >>
     rpt strip_tac >>
     irule (Q.ISPEC `\i:instruction. i.inst_id` all_distinct_map_mem_inj) >>
     conj_tac >- asm_rewrite_tac[] >>
     qexists_tac `bb.bb_instructions` >>
     asm_simp_tac bool_ss [] >>
     qpat_x_assum `EVERY (\i. MEM i bb.bb_instructions) scheduled` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> metis_tac[]) >>
  `MAP (\i. i.inst_id) scheduled = MAP (\i. i.inst_id) actual_body` by
    (qpat_x_assum `LIST_REL (\h x. h.inst_id = x.inst_id) scheduled actual_body`
       mp_tac >>
     simp_tac bool_ss [MAP_EQ_EVERY2] >> metis_tac[LIST_REL_LENGTH]) >>
  simp_tac pure_ss [Abbr `orc`] >>
  irule (cj 1 native_lookup_fill_subtrace_agreement) >>
  simp[EVERY_MEM] >> irule trace_gas_names_distinct >>
  irule native_inventory_suffix_distinct >> conj_tac
  >- (simp[DROP_APPEND] >> metis_tac[]) >>
  qpat_x_assum `o1_ctx_shape C'` mp_tac >>
  simp_tac bool_ss [o1_ctx_shape_def, ctx_inst_ids_distinct_def] >>
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all venomWfPropsTheory.all_distinct_flat_map_member >>
  BETA_TAC >> strip_tac >>
  drule_all venomWfPropsTheory.all_distinct_flat_map_member >> simp[]
QED
Resume native_inventory_frontier_no_pass[contradiction]:
  `?w. ev_step orc p d b C' z (tz with vs_gas_readings := []) = OK w` by
    (qpat_x_assum `todo = _` SUBST_ALL_TAC >>
     qpat_x_assum `scheduled = _` SUBST_ALL_TAC >>
     drule_at (Pat `dft_head_bubbles _ _ _`) native_successful_cut_frontier_step >>
     disch_then irule >>
     asm_simp_tac bool_ss [] >> conj_tac
     >- (rpt strip_tac >> drule_all dft_crossing_swap_pair >> simp[]) >>
     conj_tac >- metis_tac[dft_remaining_inv_def] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  Cases_on `step_inst b C' z tz` >> gvs[restore_rel_cases]
QED
Finalise native_inventory_frontier_no_pass

(* The selected frontier environment is notation, not a logical definition. *)
val native_inventory_frontierq = ``
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv fn bb todo t /\
  (s with vs_gas_readings := []) = (t with vs_gas_readings := []) /\
  dft_head_bubbles (\x y.
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo scheduled /\
  EVERY (from_block bb.bb_instructions) frontier_body /\
  LIST_REL (\h x. h.inst_id = x.inst_id) scheduled frontier_body /\
  bt = bb with bb_instructions := REPLICATE j pad ++ frontier_body /\ t.vs_inst_idx = j /\
  ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
  ~t.vs_call_ctx.cc_static /\ terminates (exec_block b C' bt t) /\
  gas_count_block b C' bt t <= LENGTH t.vs_gas_readings /\
  LENGTH key_rows = LENGTH (before ++ [z]) /\
  LENGTH site_rows = LENGTH (before ++ [z]) /\ LENGTH certs = LENGTH (before ++ [z]) /\
  (!h. h < LENGTH (before ++ [z]) ==>
    ^native_inventory_Rq
      (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))
      (EL h (before ++ [z])) (EL h key_rows) (EL h site_rows) (EL h certs)) /\
  ALL_DISTINCT (FLAT key_rows) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (MAP (ALOOKUP (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)))
      (FLAT key_rows)) g /\
  todo = before ++ z::after /\ scheduled = done ++ z::later /\
  EVERY (\i. ~is_terminator i.inst_opcode) done /\
  EVERY (\i. ~is_terminator i.inst_opcode) before /\
  FOLDR (dft_exec_cons b C') OK done t = OK tz /\
  exec_block b C' bt t = dft_exec_suffix b C' [z] tz /\
  (is_terminator z.inst_opcode \/ ~(?u. step_inst b C' z tz = OK u)) /\
  (((?u. exec_block b C' bt t = OK u) \/
    (?v u. exec_block b C' bt t = IntRet v u)) ==> after = [])``;

Theorem native_inventory_contained_stop:
  !frontier_body key_rows site_rows certs.
  ^native_inventory_frontierq ==>
  !n. ?A i rest frontpost q.
    todo = A ++ i::rest /\ before ++ [z] = A ++ i::frontpost /\
    EVERY (\x. ~is_terminator x.inst_opcode) A /\
    FOLDR (dft_exec_cons n C) OK A (s with vs_gas_readings := g ++ tail) = OK q /\
    (is_terminator i.inst_opcode \/ ~(?u. step_inst n C i q = OK u))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >>
  qspecl_then [`before ++ [z]`, `n`, `C`, `s with vs_gas_readings := g ++ tail`]
    (qx_choose_then `A` (qx_choose_then `rest` (qx_choose_then `q`
      (map_every assume_tac o CONJUNCTS)))) native_selected_maximal_cut >>
  Cases_on `rest = []`
  >- (`A = before ++ [z]` by metis_tac[APPEND_NIL] >>
      Cases_on `is_terminator z.inst_opcode`
      >- (qpat_x_assum `EVERY _ A` mp_tac >>
          qpat_x_assum `A = _` (fn th => rewrite_tac[th, EVERY_APPEND, EVERY_DEF]) >>
          simp[]) >>
      `~(?u. step_inst b C' z tz = OK u)` by metis_tac[] >>
      drule_all native_inventory_frontier_no_pass >> metis_tac[]) >>
  qpat_x_assum `rest = [] \/ _` mp_tac >> simp[] >> strip_tac >>
  qexistsl_tac [`A`, `i`, `more ++ after`, `more`, `q`] >>
  simp[] >> metis_tac[APPEND_ASSOC, APPEND]
QED

Theorem native_inventory_all_budget_prefix:
  !frontier_body key_rows site_rows certs.
  ^native_inventory_frontierq ==>
  !n. ?k. k <= LENGTH (FLAT key_rows) /\
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn
      (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
      (s with vs_gas_readings := g ++ tail)) =
      ZIP (TAKE k (FLAT key_rows), TAKE k g) /\
    gas_events_block n C fn.fn_name
      (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
      (s with vs_gas_readings := g ++ tail) = TAKE k (FLAT site_rows)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >>
  drule_all native_inventory_contained_stop >>
  disch_then (qspecl_then [`tail`, `n`] (qx_choose_then `A`
    (qx_choose_then `i` (qx_choose_then `rest` (qx_choose_then `frontpost`
      (qx_choose_then `q` (map_every assume_tac o CONJUNCTS))))))) >>
  qspecl_then [`frontier_body`, `key_rows`, `site_rows`, `certs`] mp_tac
    (Q.INST [`P` |-> `before ++ [z]`] native_inventory_stopped_cut_prefix) >>
  (impl_tac >- (asm_rewrite_tac[] >> qexists_tac `after` >>
    qpat_x_assum `todo = before ++ z::after` mp_tac >>
    qpat_x_assum `before ++ [z] = _` mp_tac >>
    qpat_x_assum `todo = A ++ i::rest` mp_tac >>
    rpt (pop_assum kall_tac) >> simp[APPEND_ASSOC])) >>
  disch_then (qspecl_then [`A`, `i`, `n`, `rest`, `frontpost`, `q`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> simp[]
QED
Theorem native_event_cut_suffix[local]:
  !A s q. inv_ev_trace orc p d b C A s q ==>
    ev_suffix orc p d b C (A ++ rest) s = ev_suffix orc p d b C rest q
Proof
  Induct >> simp[inv_ev_trace_def, dftGasSimBoundaryTheory.ev_suffix_def] >>
  rpt strip_tac >> simp[] >> metis_tac[]
QED

Theorem native_inventory_stopped_cut_event_result:
  !body key_rows site_rows certs.
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv fn bb todo t /\
  (s with vs_gas_readings := []) = (t with vs_gas_readings := []) /\
  dft_head_bubbles (\x y.
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo scheduled /\
  EVERY (from_block bb.bb_instructions) body /\
  LIST_REL (\h x. h.inst_id = x.inst_id) scheduled body /\
  bt = bb with bb_instructions := REPLICATE j pad ++ body /\ t.vs_inst_idx = j /\
  ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
  ~t.vs_call_ctx.cc_static /\ terminates (exec_block b C' bt t) /\
  gas_count_block b C' bt t <= LENGTH t.vs_gas_readings /\
  (?post. todo = P ++ post) /\
  LENGTH key_rows = LENGTH P /\ LENGTH site_rows = LENGTH P /\ LENGTH certs = LENGTH P /\
  (!h. h < LENGTH P ==>
    ^native_inventory_Rq
      (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))
      (EL h P) (EL h key_rows) (EL h site_rows) (EL h certs)) /\
  ALL_DISTINCT (FLAT key_rows) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (MAP (ALOOKUP (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)))
      (FLAT key_rows)) g ==>
  !A i rest frontpost q.
    todo = A ++ i::rest /\ P = A ++ i::frontpost /\
    EVERY (\x. ~is_terminator x.inst_opcode) A /\
    FOLDR (dft_exec_cons b C) OK A (s with vs_gas_readings := g ++ tail) = OK q /\
    (is_terminator i.inst_opcode \/ ~(?u. step_inst b C i q = OK u)) /\
    terminates (exec_block b C
      (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
      (s with vs_gas_readings := g ++ tail)) ==>
    let orc = (\key. case ALOOKUP
      (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t) ++
       ZIP (FLAT key_rows,g)) key of NONE => 0w | SOME w => w) in
    dft_res_rel
      (restore_result [] (exec_block b C
        (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
        (s with vs_gas_readings := g ++ tail)))
      (ev_suffix orc p d b C' todo (t with vs_gas_readings := []))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  rename1 `EVERY (from_block bb.bb_instructions) actual_body` >>
  qspecl_then [`actual_body`, `key_rows`, `site_rows`, `certs`] mp_tac
    native_successful_cut_inventory >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (qspecl_then [`A`, `b`, `i::rest`, `i::frontpost`, `q`] mp_tac) >>
  qpat_x_assum `todo = A ++ i::rest /\ _` (map_every assume_tac o CONJUNCTS) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `inv_ev_trace orc p d b C' A` >>
  simp_tac pure_ss [LET_THM] >>
  `exec_block b C
      (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
      (s with vs_gas_readings := g ++ tail) =
    exec_block b C (bb with bb_instructions := REPLICATE q.vs_inst_idx pad ++ i::rest) q` by
    suspend "native_cut" >>
  `ev_suffix orc p d b C' todo (t with vs_gas_readings := []) =
    ev_suffix orc p d b C' (i::rest) (q with vs_gas_readings := [])` by
    metis_tac[native_event_cut_suffix] >>
  `i.inst_opcode <> GAS` by suspend "notgas" >>
  Cases_on `i.inst_opcode = INVOKE` >- suspend "invoke" >>
  suspend "plain"
QED
Resume native_inventory_stopped_cut_event_result[native_cut]:
  qspecl_then [`A`, `s with vs_gas_readings := g ++ tail`, `s.vs_inst_idx`]
    mp_tac native_prefix_cut >> simp[] >>
  disch_then (qspecl_then [`b`, `C`, `fn`, `p`, `d`, `i::rest`, `bb`, `pad`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> asm_rewrite_tac[] >> simp[]
QED
Resume native_inventory_stopped_cut_event_result[notgas]:
  strip_tac >>
  `inst_wf i` by (fs[dft_remaining_inv_def, EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  drule_all dftGasInvOracleExchangeTheory.inv_ev_gas_shape >> strip_tac >>
  qpat_x_assum `is_terminator _ \/ _` mp_tac >>
  simp[is_terminator_def, step_inst_non_invoke, step_inst_base_def, exec_gas_def] >>
  CASE_TAC >> simp[]
QED
Resume native_inventory_stopped_cut_event_result[plain]:
  `restore_rel [] (step_inst b C i q)
     (ev_step orc p d b C' i (q with vs_gas_readings := []))` by
    (simp[Once ev_step_def, step_inst_non_invoke] >>
     irule step_base_restore >> simp[]) >>
  qpat_x_assum `q.vs_inst_idx = _` kall_tac >>
  asm_rewrite_tac[] >>
  qpat_x_assum `restore_rel [] _ _` mp_tac >>
  qpat_x_assum `is_terminator _ \/ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  once_rewrite_tac[exec_block_def, dftGasSimBoundaryTheory.ev_suffix_def] >>
  simp[get_instruction_def, EL_APPEND_EQN] >>
  Cases_on `step_inst b C i q` >>
  gvs[restore_rel_cases, restore_result_def, dft_res_rel_def] >>
  Cases_on `v.vs_halted` >> simp[restore_result_def, dft_res_rel_def]
QED
Resume native_inventory_stopped_cut_event_result[invoke]:
  `~is_terminator i.inst_opcode` by simp[is_terminator_def] >>
  `~(?u. step_inst b C i q = OK u)` by metis_tac[] >>
  `LENGTH A < LENGTH P` by simp[] >>
  `LENGTH A < LENGTH key_rows /\ LENGTH A < LENGTH site_rows` by metis_tac[] >>
  qabbrev_tac `Kpre = FLAT (TAKE (LENGTH A) key_rows)` >>
  qabbrev_tac `Kc = EL (LENGTH A) key_rows` >>
  qabbrev_tac `Kpost = FLAT (DROP (SUC (LENGTH A)) key_rows)` >>
  qabbrev_tac `Sc = EL (LENGTH A) site_rows` >>
  `FLAT key_rows = Kpre ++ Kc ++ Kpost` by
    (simp_tac pure_ss [Abbr `Kpre`, Abbr `Kc`, Abbr `Kpost`] >>
     qspecl_then [`LENGTH A`, `key_rows`] mp_tac rich_listTheory.TAKE_DROP_SUC >>
     simp[] >> disch_then (mp_tac o Q.AP_TERM `FLAT`) >> simp[]) >>
  `LENGTH (FLAT key_rows) = LENGTH g` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `?gpre gc gpost. g = gpre ++ gc ++ gpost /\
    LENGTH Kpre = LENGTH gpre /\ LENGTH Kc = LENGTH gc /\ LENGTH Kpost = LENGTH gpost` by
    (qexistsl_tac [`TAKE (LENGTH Kpre) g`,
       `TAKE (LENGTH Kc) (DROP (LENGTH Kpre) g)`,
       `DROP (LENGTH Kc) (DROP (LENGTH Kpre) g)`] >>
     conj_tac >- metis_tac[TAKE_DROP, APPEND_ASSOC] >> simp[] >> gvs[] >> simp[]) >>
  `^native_inventory_Rq
    (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))
    i Kc Sc (EL (LENGTH A) certs)` by
    (qpat_x_assum `!h. h < LENGTH P ==> _` (qspec_then `LENGTH A` mp_tac) >>
     simp[EL_APPEND_EQN, Abbr `Kc`, Abbr `Sc`]) >>
  `q.vs_gas_readings = gc ++ gpost ++ tail` by
    (qpat_x_assum `q.vs_gas_readings = _` mp_tac >>
     simp_tac pure_ss [GSYM APPEND_ASSOC, Abbr `Kpre`] >>
     asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp_tac bool_ss []) >>
  qpat_assum `(\obs i Kc Sc cert. _) _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [LET_THM] >> asm_rewrite_tac[] >> strip_tac >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT todo /\ EVERY (\x. MEM x bb.bb_instructions) todo` by
    (qpat_x_assum `dft_remaining_inv fn bb todo t` mp_tac >>
     simp_tac bool_ss [dft_remaining_inv_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) todo)` by
    (irule ALL_DISTINCT_MAP_INJ >> asm_rewrite_tac[] >> rpt strip_tac >>
     irule (Q.ISPEC `\x:instruction. x.inst_id` dftCorrectnessTheory.all_distinct_map_mem_inj) >>
     conj_tac >- asm_rewrite_tac[] >>
     qexists_tac `bb.bb_instructions` >> asm_rewrite_tac[] >>
     qpat_x_assum `EVERY (\x. MEM x bb.bb_instructions) todo` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> metis_tac[]) >>
  `PERM todo scheduled` by metis_tac[native_bubbles_perm] >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) scheduled) /\
   EVERY (\x. MEM x bb.bb_instructions) scheduled` by
    metis_tac[PERM_MAP, ALL_DISTINCT_PERM, PERM_EVERY] >>
  `?consumed later. scheduled = consumed ++ i::later` by
    metis_tac[MEM_SPLIT, PERM_MEM_EQ, MEM_APPEND, MEM] >>
  qpat_x_assum `scheduled = _` SUBST_ALL_TAC >>
  `inv_ev_trace orc p d b C' consumed (t with vs_gas_readings := [])
    (a with vs_gas_readings := [])` by
    (simp_tac pure_ss [Abbr `orc`] >> irule native_selected_target_event_cut >> simp[] >>
     conj_tac >- fs[o1_ctx_shape_def] >>
     qexistsl_tac [`bb.bb_instructions`, `i`, `later`] >> simp[DROP_APPEND] >>
     qpat_x_assum `ALL_DISTINCT (MAP _ (consumed ++ i::later))` mp_tac >>
     qpat_x_assum `EVERY _ (consumed ++ i::later)` mp_tac >>
     simp_tac (srw_ss()) [MAP_APPEND, EVERY_APPEND]) >>
  suspend "invoke_result"
QED
Resume native_inventory_stopped_cut_event_result[invoke_result]:
  `terminates (step_inst b C i q)` by
    (qpat_x_assum `terminates (exec_block b C _ _)` mp_tac >>
     asm_rewrite_tac[] >> once_rewrite_tac[exec_block_def] >>
     simp[get_instruction_def, EL_APPEND_EQN] >>
     Cases_on `step_inst b C i q` >>
     simp[passSimulationDefsTheory.terminates_def]) >>
  `terminates (step_inst b C i q) /\
   ~(?u. step_inst b C i q = OK u) /\
   dft_res_rel (restore_result [] (step_inst b C i q))
      (restore_result [] (step_inst b C' i a))` by
    (qpat_assum `inv_ev_trace orc p d b C' A _ _`
       (mp_then (Pat `inv_ev_trace _ _ _ _ _ A _ _`) mp_tac
         (cj 2 native_selected_child_stopped_transport)) >>
     disch_then irule >> suspend "invoke_transport_premises") >>
  suspend "invoke_event"
QED
Resume native_inventory_stopped_cut_event_result[invoke_transport_premises]:
  simp_tac bool_ss [] >>
  conj_tac >- (gvs[] >> (metis_tac[])) >>
  conj_tac >- asm_rewrite_tac[] >>
  (conj_tac
   >- (qpat_assum `inv_ev_trace orc p d b C' consumed _ _`
         (irule_at (Pat `inv_ev_trace _ _ _ _ _ _ _ _`)) >>
       qpat_x_assum `todo = A ++ i::rest` SUBST_ALL_TAC >>
       qpat_assum `dft_head_bubbles _ (A ++ i::rest) _`
         (irule_at (Pat `dft_head_bubbles _ _ _`)) >>
       conj_tac >- (rpt strip_tac >> metis_tac[dft_crossing_swap_pair]) >>
       asm_rewrite_tac[])) >>
  qpat_x_assum `EL (LENGTH A) certs = _` SUBST_ALL_TAC >>
  qpat_assum `(\obs i Kc Sc cert. _) _ _ _ _ _`
    (irule_at (Pat `if _ then _ else _`) o SIMP_RULE bool_ss []) >>
  qpat_assum `q.vs_gas_readings = gc ++ gpost ++ tail`
    (irule_at (Pat `q.vs_gas_readings = _`)) >>
  qpat_assum `LENGTH Kpre = LENGTH gpre`
    (irule_at (Pat `LENGTH _ = LENGTH _`)) >>
  qexists_tac `Kpost` >>
  conj_tac >- metis_tac[] >>
  (metis_tac[])
QED
Resume native_inventory_stopped_cut_event_result[invoke_event]:
  `(!op. MEM op i.inst_operands ==>
      eval_operand op (q with vs_gas_readings := []) =
      eval_operand op (a with vs_gas_readings := [])) /\
   (!callee vals. setup_callee callee vals (q with vs_gas_readings := []) =
      setup_callee callee vals (a with vs_gas_readings := []))` by
    (qpat_x_assum `todo = A ++ i::rest` SUBST_ALL_TAC >>
     drule_at (Pat `dft_head_bubbles _ _ _`) native_successful_cut_call_inputs >>
     disch_then irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
     rpt strip_tac >> metis_tac[dft_crossing_swap_pair]) >>
  `!op. MEM op ops ==> MEM op i.inst_operands` by
    (fs[decode_invoke_def, AllCaseEqs()] >> metis_tac[MEM]) >>
  `eval_operands ops (q with vs_gas_readings := []) = SOME args /\
   setup_callee (dft_fn cf) args (q with vs_gas_readings := []) =
     SOME (cs with vs_gas_readings := [])` by
    (reverse conj_tac >- simp[gas_setup_callee] >>
     `eval_operands ops q = eval_operands ops a` by
       (irule eval_operands_agree >> rpt strip_tac >> metis_tac[gas_eval_operand]) >>
     simp[gas_eval_operands]) >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) (DROP t.vs_inst_idx bt.bb_instructions))` by
    (`MAP (\x. x.inst_id) (consumed ++ i::later) = MAP (\x. x.inst_id) actual_body` by
       (simp_tac pure_ss [MAP_EQ_EVERY2] >> metis_tac[LIST_REL_LENGTH]) >>
     simp[DROP_APPEND] >> metis_tac[]) >>
  `ctx_inst_ids_distinct C'` by fs[o1_ctx_shape_def] >>
  `MEM ((p,d,i.inst_id),fn',i,a)
     (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t)` by simp[] >>
  `trace_agrees orc (dftGasFromListTraceDefs$trace_blocks
     ((d,i.inst_id)::p) d b C' (dft_fn cf) cs)` by
    (simp_tac pure_ss [Abbr `orc`] >>
     drule_all native_inventory_child_agreement >>
     simp_tac pure_ss [LET_THM] >> metis_tac[]) >>
  `restore_rel [] (run_blocks b C' (dft_fn cf) cs)
     (ev_blocks orc ((d,i.inst_id)::p) d b C' (dft_fn cf)
       (cs with vs_gas_readings := []))` by
    (drule (cj 3 dftGasFromListReplayTheory.trace_replay) >> simp[]) >>
  suspend "invoke_finish"
QED
Resume native_inventory_stopped_cut_event_result[invoke_finish]:
  qpat_x_assum `q.vs_inst_idx = _` (SUBST_ALL_TAC o SYM) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `dft_res_rel (restore_result [] (step_inst b C i q)) _` mp_tac >>
  qpat_x_assum `terminates (step_inst b C i q)` mp_tac >>
  qpat_x_assum `~(?u. step_inst b C i q = OK u)` mp_tac >>
  qpat_x_assum `restore_rel [] _ _` mp_tac >>
  qpat_x_assum `decode_invoke i = _` mp_tac >>
  qpat_x_assum `lookup_function nm C'.ctx_functions = _` mp_tac >>
  qpat_x_assum `eval_operands ops a = _` mp_tac >>
  qpat_x_assum `setup_callee (dft_fn cf) args a = _` mp_tac >>
  qpat_x_assum `eval_operands ops (q with vs_gas_readings := []) = _` mp_tac >>
  qpat_x_assum `setup_callee (dft_fn cf) args (q with vs_gas_readings := []) = _` mp_tac >>
  qpat_x_assum `i.inst_opcode = INVOKE` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  once_rewrite_tac[exec_block_def, dftGasSimBoundaryTheory.ev_suffix_def] >>
  simp[get_instruction_def, EL_APPEND_EQN, Once ev_step_def, GSYM gas_eval_operands] >>
  Cases_on `step_inst b C i q` >> gvs[passSimulationDefsTheory.terminates_def] >>
  qpat_x_assum `dft_res_rel _ _` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `run_blocks b C' (dft_fn cf) cs` >>
  gvs[restore_rel_cases, restore_result_def, dft_res_rel_def] >>
  simp[AllCaseEqs()]
QED
Finalise native_inventory_stopped_cut_event_result

Theorem native_stopped_suffix_budget_lift[local]:
  !A n b C x q i rest frontpost.
  EVERY (\j. ~is_terminator j.inst_opcode) A /\
  FOLDR (dft_exec_cons n C) OK A x = OK q /\
  (is_terminator i.inst_opcode \/ ~(?u. step_inst n C i q = OK u)) /\
  terminates (dft_exec_suffix n C (A ++ i::rest) x) /\
  (!H h r fp u.
    A ++ i::rest = H ++ h::r /\ A ++ i::frontpost = H ++ h::fp /\
    EVERY (\j. ~is_terminator j.inst_opcode) H /\
    FOLDR (dft_exec_cons n C) OK H x = OK u /\
    h.inst_opcode = INVOKE /\ terminates (step_inst n C h u) ==>
    step_inst b C h u = step_inst n C h u) ==>
  dft_exec_suffix b C (A ++ i::rest) x =
    dft_exec_suffix n C (A ++ i::rest) x
Proof
  Induct >- (
    rpt gen_tac >> simp[] >> strip_tac >>
    `terminates (step_inst n C i x)` by
      (Cases_on `step_inst n C i x` >>
       gvs[dftIndexedExecTheory.dft_exec_suffix_def,
           passSimulationDefsTheory.terminates_def]) >>
    `step_inst b C i x = step_inst n C i x` by
      (Cases_on `i.inst_opcode = INVOKE`
       >- (first_x_assum irule >> simp[] >>
           qexistsl_tac [`[]`, `frontpost`, `rest`] >> simp[]) >>
       simp[step_inst_non_invoke]) >>
    once_rewrite_tac[dftIndexedExecTheory.dft_exec_suffix_def] >>
    simp[] >> Cases_on `step_inst n C i x` >> gvs[]) >>
  rpt gen_tac >> simp[] >> strip_tac >>
  gvs[dftIndexedExecTheory.dft_exec_cons_def, AllCaseEqs()] >> (
  rename1 `step_inst n C h x = OK v` >>
  `step_inst b C h x = OK v` by
    (Cases_on `h.inst_opcode = INVOKE`
     >- (`step_inst b C h x = step_inst n C h x` suffices_by simp[] >>
         first_x_assum irule >>
         simp[passSimulationDefsTheory.terminates_def] >>
         qexistsl_tac [`[]`, `A ++ i::frontpost`, `A ++ i::rest`] >> simp[]) >>
     metis_tac[step_inst_non_invoke]) >>
  once_rewrite_tac[dftIndexedExecTheory.dft_exec_suffix_def] >> simp[] >>
  first_x_assum irule >>
  conj_tac
  >- (qexists_tac `frontpost` >> rpt strip_tac >>
      first_x_assum irule >> simp[] >>
      qexistsl_tac [`h::H`, `fp`, `r`] >>
      simp[dftIndexedExecTheory.dft_exec_cons_def]) >>
  conj_tac
  >- (qpat_x_assum `terminates _` mp_tac >>
      simp[dftIndexedExecTheory.dft_exec_suffix_def]) >>
  qexists_tac `q` >> simp[])
QED

Theorem native_stopped_cut_budget_lift:
  let x = s with vs_gas_readings := g ++ tail;
      source_residual = bb with
        bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo in
  todo = A ++ i::rest /\ P = A ++ i::frontpost /\
  EVERY (\j. ~is_terminator j.inst_opcode) A /\
  FOLDR (dft_exec_cons n C) OK A x = OK q /\
  (is_terminator i.inst_opcode \/ ~(?u. step_inst n C i q = OK u)) /\
  terminates (exec_block n C source_residual x) /\
  (!H h r fp u.
    todo = H ++ h::r /\ P = H ++ h::fp /\
    EVERY (\j. ~is_terminator j.inst_opcode) H /\
    FOLDR (dft_exec_cons n C) OK H x = OK u /\
    h.inst_opcode = INVOKE /\ terminates (step_inst n C h u) ==>
    step_inst b C h u = step_inst n C h u) ==>
  exec_block b C source_residual x = exec_block n C source_residual x /\
  terminates (exec_block b C source_residual x)
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  `!f. exec_block f C
     (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
     (s with vs_gas_readings := g ++ tail) =
   dft_exec_suffix f C todo (s with vs_gas_readings := g ++ tail)` by
    (gen_tac >> irule dftIndexedExecTheory.dft_exec_suffix_boundary >>
     simp[NoAsms, DROP_APPEND]) >>
  gvs[] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  `dft_exec_suffix b C (A ++ i::rest) (s with vs_gas_readings := g ++ tail) =
   dft_exec_suffix n C (A ++ i::rest) (s with vs_gas_readings := g ++ tail)` by
    (irule native_stopped_suffix_budget_lift >>
     asm_simp_tac bool_ss [] >>
     conj_tac >- (qexists_tac `frontpost` >> first_assum ACCEPT_TAC) >>
     qexists_tac `q` >> asm_simp_tac bool_ss []) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac []
QED

Theorem native_successful_suffix_cut[local]:
  !pre n C x rest.
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  ((?u. dft_exec_suffix n C (pre ++ rest) x = OK u) \/
   (?v u. dft_exec_suffix n C (pre ++ rest) x = IntRet v u)) ==>
  ?q. FOLDR (dft_exec_cons n C) OK pre x = OK q /\
      dft_exec_suffix n C (pre ++ rest) x = dft_exec_suffix n C rest q
Proof
  Induct >- simp[] >> rpt gen_tac >> simp_tac bool_ss [EVERY_DEF, APPEND] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?u. step_inst n C h x = OK u` by
    (qpat_x_assum `(?u. dft_exec_suffix _ _ _ _ = OK u) \/ _` mp_tac >>
     simp[dftIndexedExecTheory.dft_exec_suffix_def] >>
     Cases_on `step_inst n C h x` >> simp[] >>
     metis_tac[dft_swap_nonterminator_no_intret]) >>
  qpat_x_assum `(?u. dft_exec_suffix _ _ _ _ = OK u) \/ _` mp_tac >>
  simp[dftIndexedExecTheory.dft_exec_suffix_def] >> strip_tac >>
  first_x_assum (qspecl_then [`n`, `C`, `u with vs_inst_idx := SUC x.vs_inst_idx`, `rest`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `q` >>
  simp[dftIndexedExecTheory.dft_exec_cons_def]
QED

Theorem native_inventory_success_residual:
  !frontier_body key_rows site_rows certs.
  ^native_inventory_frontierq ==>
  let x = s with vs_gas_readings := g ++ tail;
      source_residual = bb with
        bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo in
  dft_res_rel (restore_result [] (exec_block b C source_residual x))
              (restore_result [] (exec_block b C' bt t)) ==>
  ((?u. exec_block b C' bt t = OK u) \/
   (?v u. exec_block b C' bt t = IntRet v u)) ==>
  gas_events_block b C fn.fn_name source_residual x = FLAT site_rows /\
  (!u. exec_block b C source_residual x = OK u ==> u.vs_gas_readings = tail) /\
  (!v u. exec_block b C source_residual x = IntRet v u ==> u.vs_gas_readings = tail) /\
  residual_result tail (exec_block b C' bt t) (exec_block b C source_residual x)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp_tac pure_ss [LET_THM] >> rpt disch_tac >>
  `after = []` by metis_tac[] >>
  `is_terminator z.inst_opcode` by
    (qpat_x_assum `(?u. exec_block b C' bt t = OK u) \/ _` mp_tac >>
     qpat_x_assum `exec_block b C' bt t = _` (fn th => rewrite_tac[th]) >>
     Cases_on `is_terminator z.inst_opcode` >> simp[] >>
     simp[dftIndexedExecTheory.dft_exec_suffix_def] >>
     Cases_on `step_inst b C' z tz` >> simp[] >>
     metis_tac[dft_swap_nonterminator_no_intret]) >>
  `(?u. exec_block b C
    (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
    (s with vs_gas_readings := g ++ tail) = OK u) \/
   (?v u. exec_block b C
    (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
    (s with vs_gas_readings := g ++ tail) = IntRet v u)` by
    (qpat_x_assum `dft_res_rel _ _` mp_tac >>
     qpat_x_assum `(?u. exec_block b C' bt t = OK u) \/ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `exec_block b C' bt t` >>
     Cases_on `exec_block b C
       (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
       (s with vs_gas_readings := g ++ tail)` >>
     simp[restore_result_def, dft_res_rel_def]) >>
  suspend "saturation"
QED
Resume native_inventory_success_residual[saturation]:
  markerLib.RESUME_TAC >>
  `exec_block b C
    (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
    (s with vs_gas_readings := g ++ tail) =
   dft_exec_suffix b C todo (s with vs_gas_readings := g ++ tail)` by
    (irule dftIndexedExecTheory.dft_exec_suffix_boundary >> simp[NoAsms, DROP_APPEND]) >>
  `?q. FOLDR (dft_exec_cons b C) OK before
          (s with vs_gas_readings := g ++ tail) = OK q` by
    (mp_tac (Q.SPEC `before` native_successful_suffix_cut) >>
     disch_then (qspecl_then [`b`, `C`, `s with vs_gas_readings := g ++ tail`, `[z]`] mp_tac) >>
     simp[] >> metis_tac[APPEND_NIL, APPEND]) >>
  qspecl_then [`frontier_body`, `key_rows`, `site_rows`, `certs`] mp_tac
    (Q.INST [`P` |-> `before ++ [z]`] native_successful_cut_inventory) >>
  (impl_tac >- (asm_rewrite_tac[] >> qexists_tac `after` >> simp[])) >>
  disch_then (qspecl_then [`before`, `b`, `z::after`, `[z]`, `q`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> simp_tac pure_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `z.inst_opcode <> INVOKE /\ z.inst_opcode <> GAS` by
    (qpat_x_assum `is_terminator z.inst_opcode` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `z.inst_opcode` >> simp[is_terminator_def]) >>
  `EL (LENGTH before) key_rows = [] /\ EL (LENGTH before) site_rows = []` by
    (qpat_x_assum `!h. h < _ ==> _` (qspec_then `LENGTH before` mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  `FLAT (TAKE (LENGTH before) key_rows) = FLAT key_rows /\
   FLAT (TAKE (LENGTH before) site_rows) = FLAT site_rows` by
    (qpat_x_assum `!h. h < _ ==> _` kall_tac >>
     `LENGTH key_rows = SUC (LENGTH before) /\
      LENGTH site_rows = SUC (LENGTH before)` by simp[] >>
     qpat_assum `LENGTH key_rows = SUC _`
       (mp_then Any assume_tac vyperMiscTheory.TAKE_SNOC_EL) >>
     qpat_assum `LENGTH site_rows = SUC _`
       (mp_then Any assume_tac vyperMiscTheory.TAKE_SNOC_EL) >>
     metis_tac[FLAT_APPEND, FLAT, APPEND_NIL]) >>
  suspend "terminal"
QED
Resume native_inventory_success_residual[terminal]:
  markerLib.RESUME_TAC >>
  `LENGTH (FLAT key_rows) = LENGTH g` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `q.vs_gas_readings = tail` by
    (qpat_x_assum `q.vs_gas_readings = _` mp_tac >>
     asm_simp_tac (srw_ss()) [DROP_APPEND]) >>
  qspecl_then [`before`, `s with vs_gas_readings := g ++ tail`, `s.vs_inst_idx`]
    mp_tac native_prefix_cut >>
  (impl_tac >- asm_simp_tac bool_ss [venom_state_accfupds, venom_state_fupdfupds]) >>
  disch_then (qspecl_then [`b`, `C`, `fn`, `p`, `d`, `[z]`, `bb`, `pad`] mp_tac) >>
  simp_tac pure_ss [LET_THM] >>
  asm_simp_tac (srw_ss()) [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "silent_terminal"
QED
Resume native_inventory_success_residual[silent_terminal]:
  markerLib.RESUME_TAC >>
  qmatch_goalsub_abbrev_tac `gas_events_block b C fn.fn_name br q` >>
  `get_instruction br q.vs_inst_idx = SOME z` by
    simp[Abbr `br`, get_instruction_def, EL_APPEND_EQN] >>
  `gas_events_block b C fn.fn_name br q = []` by
    (qpat_x_assum `get_instruction br _ = _` mp_tac >>
     qpat_x_assum `is_terminator z.inst_opcode` mp_tac >>
     qpat_x_assum `z.inst_opcode <> GAS` mp_tac >>
     qpat_x_assum `z.inst_opcode <> INVOKE` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >>
     simp[Once gas_events_block_def, Once gas_events_step_def] >>
     Cases_on `step_inst b C z q` >> simp[]) >>
  `gas_count_suffix 0 q (exec_block b C br q)` by
    metis_tac[cj 2 gas_count_suffix, cj 2 gas_events_length, LENGTH] >>
  `dft_exec_suffix b C (before ++ [z]) (s with vs_gas_readings := g ++ tail) =
   exec_block b C br q` by
    (simp_tac pure_ss [Abbr `br`] >> metis_tac[APPEND_NIL, APPEND, APPEND_ASSOC]) >>
  `(!u. dft_exec_suffix b C (before ++ [z]) (s with vs_gas_readings := g ++ tail) = OK u ==>
      u.vs_gas_readings = tail) /\
   (!v u. dft_exec_suffix b C (before ++ [z]) (s with vs_gas_readings := g ++ tail) = IntRet v u ==>
      u.vs_gas_readings = tail)` by
    (qpat_x_assum `gas_count_suffix _ _ _` mp_tac >>
     qpat_x_assum `dft_exec_suffix _ _ _ _ = exec_block _ _ _ _` mp_tac >>
     qpat_x_assum `q.vs_gas_readings = tail` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `exec_block b C br q` >> simp[gas_count_suffix_def] >> metis_tac[]) >>
  asm_simp_tac bool_ss [] >> suspend "residual"
QED
Resume native_inventory_success_residual[residual]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `dft_res_rel _ _` mp_tac >>
  qpat_x_assum `(?u. exec_block b C' bt t = OK u) \/ _` mp_tac >>
  asm_simp_tac (srw_ss()) [] >>
  qpat_x_assum `gas_count_suffix _ _ _` mp_tac >>
  qpat_x_assum `q.vs_gas_readings = tail` mp_tac >>
  rpt (pop_assum kall_tac) >>
  Cases_on `exec_block b C br q` >>
  Cases_on `dft_exec_suffix b C' [z] tz` >>
  simp[gas_count_suffix_def, restore_result_def, dft_res_rel_def,
       residual_result_def, stateEquivTheory.lift_result_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `src = dst with vs_gas_readings := _` >>
  qpat_x_assum `_ with vs_gas_readings := [] = _`
    (mp_tac o Q.AP_TERM `\a. a with vs_gas_readings := src.vs_gas_readings`) >>
  simp_tac (srw_ss()) [] >> metis_tac[]
QED
Finalise native_inventory_success_residual

Theorem native_residual_schedule_packet:
  !body.
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv fn bb todo t /\
  (s with vs_gas_readings := []) = (t with vs_gas_readings := []) /\
  dft_head_bubbles (\x y.
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo scheduled /\
  EVERY (from_block bb.bb_instructions) body /\
  LIST_REL (\h i. h.inst_id = i.inst_id) scheduled body /\
  bt = bb with bb_instructions := REPLICATE j pad ++ body /\ t.vs_inst_idx = j /\
  ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
  ~t.vs_call_ctx.cc_static /\ terminates (exec_block b C' bt t) /\
  gas_count_block b C' bt t <= LENGTH t.vs_gas_readings /\
  ^native_inventory_IHq ==>
  let obs = trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t);
      source_residual = bb with
        bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo in
  ?K S U.
    let M = MAP (ALOOKUP obs) K in
    ALL_DISTINCT K /\ EVERY (block_region p d (MAP (\i. i.inst_id) todo)) K /\
    LENGTH K = LENGTH S /\
    PERM (MAP THE (FILTER IS_SOME M) ++ U) t.vs_gas_readings /\
    (!u. exec_block b C' bt t = OK u ==> EVERY IS_SOME M /\ U = u.vs_gas_readings) /\
    (!v u. exec_block b C' bt t = IntRet v u ==>
      EVERY IS_SOME M /\ U = u.vs_gas_readings) /\
    (!g tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M g ==>
      (!n. ?k. k <= LENGTH K /\
        trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn source_residual
          (s with vs_gas_readings := g ++ tail)) = ZIP (TAKE k K, TAKE k g) /\
        gas_events_block n C fn.fn_name source_residual
          (s with vs_gas_readings := g ++ tail) = TAKE k S) /\
      ((?n. terminates (exec_block n C source_residual
          (s with vs_gas_readings := g ++ tail))) ==>
        terminates (exec_block b C source_residual (s with vs_gas_readings := g ++ tail)) /\
        dft_res_rel
          (restore_result [] (exec_block b C source_residual (s with vs_gas_readings := g ++ tail)))
          (restore_result [] (exec_block b C' bt t)) /\
        (((?u. exec_block b C' bt t = OK u) \/
          (?v u. exec_block b C' bt t = IntRet v u)) ==>
          gas_events_block b C fn.fn_name source_residual
            (s with vs_gas_readings := g ++ tail) = S /\
          (!u. exec_block b C source_residual (s with vs_gas_readings := g ++ tail) = OK u ==>
            u.vs_gas_readings = tail) /\
          (!v u. exec_block b C source_residual (s with vs_gas_readings := g ++ tail) = IntRet v u ==>
            u.vs_gas_readings = tail) /\
          residual_result tail (exec_block b C' bt t)
            (exec_block b C source_residual (s with vs_gas_readings := g ++ tail)))))
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `EVERY (from_block bb.bb_instructions) actual_body` >>
  `?done z later before after tz.
    scheduled = done ++ z::later /\ todo = before ++ z::after /\
    EVERY (\i. ~is_terminator i.inst_opcode) done /\
    FOLDR (dft_exec_cons b C') OK done t = OK tz /\
    tz.vs_inst_idx = j + LENGTH done /\
    exec_block b C' bt t = dft_exec_suffix b C' [z] tz /\
    (is_terminator z.inst_opcode \/ ~(?u. step_inst b C' z tz = OK u)) /\
    EVERY (\i. ~is_terminator i.inst_opcode) before /\
    FILTER (\i. i.inst_opcode = INVOKE) (before ++ [z]) =
      FILTER (\i. i.inst_opcode = INVOKE) (done ++ [z]) /\
    (((?u. exec_block b C' bt t = OK u) \/
      (?v u. exec_block b C' bt t = IntRet v u)) ==> after = [])` by
    (mp_tac (Q.SPEC `actual_body` native_schedule_stopping_frontier) >>
     (impl_tac >- gvs[]) >> asm_rewrite_tac[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  `EVERY (\i. MEM i bb.bb_instructions) scheduled` by
    (drule native_bubbles_perm >>
     qpat_x_assum `dft_remaining_inv fn bb todo t` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp_tac bool_ss [dft_remaining_inv_def] >> rpt strip_tac >>
     fs[EVERY_MEM] >> metis_tac[PERM_MEM_EQ]) >>
  `MAP FST (MAP (\(e,f,i,a). (i,a))
    (FILTER (\(e,f,i,a). e = (p,d,i.inst_id) /\ i.inst_opcode = INVOKE)
      (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))) =
    FILTER (\i. i.inst_opcode = INVOKE) (before ++ [z])` by
    (mp_tac (Q.SPEC `actual_body`
       (Q.INST [`bi` |-> `bb.bb_instructions`] native_frontier_root_calls)) >>
     (impl_tac >- gvs[]) >> simp[]) >>
  suspend "select"
QED
Resume native_residual_schedule_packet[select]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.SPEC `actual_body`
    (Q.INST [`P` |-> `before ++ [z]`] native_frontier_mask_inventory)) >>
  (impl_tac >- (asm_rewrite_tac[] >> conj_tac
    >- (qexists_tac `after` >> simp[]) >>
    qpat_x_assum `((?u. exec_block b C' bt t = OK u) \/ _) ==> after = []` mp_tac >>
    qpat_x_assum `exec_block b C' bt t = _` mp_tac >>
    rpt (pop_assum kall_tac) >> simp[])) >>
  simp_tac pure_ss [LET_THM] >>
  disch_then (qx_choose_then `key_rows` (qx_choose_then `site_rows`
    (qx_choose_then `certs` (map_every assume_tac o CONJUNCTS)))) >>
  simp_tac pure_ss [LET_THM] >>
  qexistsl_tac [`FLAT key_rows`, `FLAT site_rows`,
    `MAP SND (FILTER (\kw. ~MEM (FST kw) (FLAT key_rows))
       (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))) ++
     DROP (LENGTH (trace_gas (dftGasFromListTraceDefs$trace_block p d b C' fn' bt t))) t.vs_gas_readings`] >>
  asm_rewrite_tac[] >> rpt gen_tac >> disch_tac >>
  rename1 `EVERY (from_block bb.bb_instructions) frontier_body` >>
  `^native_inventory_frontierq` by
    (gvs[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac[]) >>
  (conj_tac >- (mp_tac (Q.SPECL [`frontier_body`, `key_rows`, `site_rows`, `certs`]
      native_inventory_all_budget_prefix) >>
    (impl_tac >- (simp_tac pure_ss [LET_THM] >> asm_rewrite_tac[] >> NO_TAC)) >>
    simp[] >> NO_TAC)) >>
  suspend "bounded"
QED
Resume native_residual_schedule_packet[bounded]:
  markerLib.RESUME_TAC >> disch_then (qx_choose_then `n` assume_tac) >>
  qspecl_then [`frontier_body`, `key_rows`, `site_rows`, `certs`] mp_tac
    (Q.INST [`P` |-> `before ++ [z]`] native_inventory_invoke_budget_equal) >>
  (impl_tac >- (asm_rewrite_tac[] >> qexists_tac `after` >> simp[])) >>
  disch_tac >>
  qspecl_then [`frontier_body`, `key_rows`, `site_rows`, `certs`] mp_tac
    native_inventory_contained_stop >>
  (impl_tac >- (simp_tac pure_ss [LET_THM] >> asm_rewrite_tac[])) >>
  disch_then (qspec_then `n` (qx_choose_then `A` (qx_choose_then `i`
    (qx_choose_then `rest` (qx_choose_then `frontpost` (qx_choose_then `q`
      (map_every assume_tac o CONJUNCTS))))))) >>
  mp_tac (Q.INST [`P` |-> `before ++ [z]`] native_stopped_cut_budget_lift) >>
  simp_tac pure_ss [LET_THM] >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm_rewrite_tac[] >> suspend "result"
QED
Resume native_residual_schedule_packet[result]:
  markerLib.RESUME_TAC >>
  qspecl_then [`frontier_body`, `key_rows`, `site_rows`, `certs`] mp_tac
    native_inventory_contained_stop >>
  (impl_tac >- (simp_tac pure_ss [LET_THM] >> asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (qspec_then `b` (qx_choose_then `Ab` (qx_choose_then `ib`
    (qx_choose_then `restb` (qx_choose_then `postb` (qx_choose_then `qb`
      (map_every assume_tac o CONJUNCTS))))))) >>
  qspecl_then [`frontier_body`, `key_rows`, `site_rows`, `certs`] mp_tac
    (Q.INST [`P` |-> `before ++ [z]`] native_inventory_stopped_cut_event_result) >>
  (impl_tac >- (asm_rewrite_tac[] >> qexists_tac `after` >>
    qpat_x_assum `todo = before ++ z::after` mp_tac >>
    qpat_x_assum `before ++ [z] = Ab ++ ib::postb` mp_tac >>
    qpat_x_assum `todo = Ab ++ ib::restb` mp_tac >>
    rpt (pop_assum kall_tac) >> simp[APPEND_ASSOC])) >>
  disch_then (qspecl_then [`Ab`, `ib`, `restb`, `postb`, `qb`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  simp_tac pure_ss [LET_THM] >> disch_tac >>
  suspend "compose"
QED
Resume native_residual_schedule_packet[compose]:
  markerLib.RESUME_TAC >>
  `ctx_inst_ids_distinct C'` by fs[o1_ctx_shape_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) todo)` by
    (qpat_x_assum `dft_remaining_inv fn bb todo t` mp_tac >>
     qpat_x_assum `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >>
     irule ALL_DISTINCT_MAP_INJ >>
     fs[dft_remaining_inv_def, EVERY_MEM] >> rpt strip_tac >>
     drule dftCorrectnessTheory.all_distinct_map_mem_inj >>
     disch_then irule >> metis_tac[]) >>
  `PERM todo scheduled` by metis_tac[native_bubbles_perm] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) scheduled)` by
    metis_tac[PERM_MAP, ALL_DISTINCT_PERM] >>
  `MAP (\i. i.inst_id) scheduled = MAP (\i. i.inst_id) frontier_body` by
    (irule LIST_EQ >> fs[LIST_REL_EL_EQN, EL_MAP]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (DROP t.vs_inst_idx bt.bb_instructions))` by
    (qpat_x_assum `bt = _` mp_tac >>
     qpat_x_assum `t.vs_inst_idx = j` mp_tac >>
     qpat_x_assum `MAP (\i. i.inst_id) scheduled = MAP (\i. i.inst_id) frontier_body` mp_tac >>
     qpat_x_assum `ALL_DISTINCT (MAP (\i. i.inst_id) scheduled)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >> gvs[DROP_APPEND]) >>
  qspecl_then [`frontier_body`, `FLAT key_rows`, `g`] mp_tac
    native_lookup_fill_schedule_result >>
  (impl_tac >- asm_rewrite_tac[]) >>
  simp_tac pure_ss [LET_THM] >> disch_tac >>
  `dft_res_rel
    (restore_result [] (exec_block b C
      (bb with bb_instructions := REPLICATE s.vs_inst_idx pad ++ todo)
      (s with vs_gas_readings := g ++ tail)))
    (restore_result [] (exec_block b C' bt t))` by
      metis_tac[dft_res_rel_trans] >>
  asm_rewrite_tac[] >>
  qspecl_then [`frontier_body`, `key_rows`, `site_rows`, `certs`] mp_tac
    native_inventory_success_residual >>
  (impl_tac >- (simp_tac pure_ss [LET_THM] >> asm_rewrite_tac[] >> metis_tac[])) >>
  simp_tac pure_ss [LET_THM] >>
  qpat_x_assum `dft_res_rel _ (restore_result [] (exec_block b C' bt t))` mp_tac >>
  qpat_x_assum `terminates (exec_block b C _ _)` mp_tac >>
  qpat_x_assum `exec_block b C _ _ = exec_block n C _ _` mp_tac >>
  qpat_x_assum `exec_block b C' bt t = _` mp_tac >>
  qpat_x_assum `todo = before ++ z::after` mp_tac >>
  qpat_x_assum `todo = Ab ++ ib::restb` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt disch_tac >> gvs[] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac[]
QED
Finalise native_residual_schedule_packet

Theorem native_pseudo_fold_cases[local]:
  !xs s. EVERY (\i. is_pseudo i.inst_opcode) xs ==>
    (?t. FOLDR (dft_exec_cons b C) OK xs s = OK t) \/
    (?e. FOLDR (dft_exec_cons b C) OK xs s = Error e)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `~is_terminator h.inst_opcode /\
   ((?u. step_inst b C h s = OK u) \/ (?e. step_inst b C h s = Error e))` by
    (Cases_on `h.inst_opcode = PHI`
     >- simp[step_inst_non_invoke, step_inst_base_def, is_terminator_def] >>
     `is_param_opcode h.inst_opcode` by
       (Cases_on `h.inst_opcode` >> gvs[is_pseudo_def, is_param_opcode_def]) >>
     conj_tac
     >- (Cases_on `h.inst_opcode` >> gvs[is_pseudo_def, is_terminator_def]) >>
     metis_tac[step_inst_param_ok_or_error]) >>
  gvs[dftIndexedExecTheory.dft_exec_cons_def] >> metis_tac[]
QED

Theorem native_pseudo_suffix_skip[local]:
  !xs a bb t br rest.
    EVERY (\i. is_pseudo i.inst_opcode) xs /\
    DROP a.vs_inst_idx bb.bb_instructions = xs ++ rest /\
    DROP t.vs_inst_idx br.bb_instructions = rest /\
    FOLDR (dft_exec_cons n C) OK xs a = OK t ==>
    exec_block n C bb a = exec_block n C br t /\
    trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bb a) =
      trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn br t) /\
    gas_events_block n C fn.fn_name bb a = gas_events_block n C fn.fn_name br t
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[] >> conj_tac
      >- (irule venomExecProofsTheory.exec_block_same_suffix >> simp[]) >>
      conj_tac
      >- (AP_TERM_TAC >> irule native_trace_block_suffix_cong >> simp[]) >>
      irule gas_events_block_suffix_cong >> simp[]) >>
  `a.vs_inst_idx < LENGTH bb.bb_instructions /\
   get_instruction bb a.vs_inst_idx = SOME h` by
    (conj_asm1_tac
     >- (qpat_x_assum `DROP _ _ = (h::xs) ++ rest`
           (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
         simp[LENGTH_DROP]) >>
     qpat_x_assum `DROP _ _ = (h::xs) ++ rest`
       (mp_tac o AP_TERM ``HD:instruction list -> instruction``) >>
     simp[get_instruction_def, HD_DROP]) >>
  `h.inst_opcode <> GAS /\ h.inst_opcode <> INVOKE /\
   ~is_terminator h.inst_opcode` by
    (Cases_on `h.inst_opcode` >> gvs[is_pseudo_def, is_terminator_def]) >>
  gvs[dftIndexedExecTheory.dft_exec_cons_def, AllCaseEqs()] >>
  `DROP (SUC a.vs_inst_idx) bb.bb_instructions =
     xs ++ DROP t.vs_inst_idx br.bb_instructions` by
    (qpat_x_assum `DROP _ _ = h::_`
       (mp_tac o AP_TERM ``DROP 1:instruction list -> instruction list``) >>
     simp[rich_listTheory.DROP_DROP_T, arithmeticTheory.ADD1]) >>
  `exec_block n C bb (t' with vs_inst_idx := SUC a.vs_inst_idx) = exec_block n C br t /\
   trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bb
      (t' with vs_inst_idx := SUC a.vs_inst_idx)) =
     trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn br t) /\
   gas_events_block n C fn.fn_name bb (t' with vs_inst_idx := SUC a.vs_inst_idx) =
     gas_events_block n C fn.fn_name br t` by
    (first_x_assum irule >> simp[]) >>
  conj_tac
  >- (CONV_TAC (LAND_CONV (REWR_CONV exec_block_def)) >> simp[]) >>
  conj_tac
  >- (CONV_TAC (LAND_CONV (RAND_CONV
        (REWR_CONV (cj 2 dftGasFromListTraceDefsTheory.trace_defs)))) >>
      simp[dftGasFromListTraceDefsTheory.trace_step_noninvoke, visit_gas_def]) >>
  CONV_TAC (LAND_CONV (REWR_CONV gas_events_block_def)) >>
  simp[gas_events_step_def]
QED

Theorem native_pseudo_entry_bridge[local]:
  bb.bb_instructions = pre ++ rest /\
  EVERY (\i. is_pseudo i.inst_opcode) pre /\
  EVERY (\i. ~is_pseudo i.inst_opcode) rest /\
  eval_phis s pre = OK sp /\
  FOLDR (dft_exec_cons b D) OK (DROP (phi_prefix_length pre) pre)
    (sp with vs_inst_idx := phi_prefix_length pre) = OK t /\
  t.vs_inst_idx = LENGTH pre ==>
  !n W C pad fn p d.
    let br = bb with bb_instructions := REPLICATE (LENGTH pre) pad ++ rest in
    run_block n C bb (s with vs_gas_readings := W) =
      exec_block n C br (t with vs_gas_readings := W) /\
    (case eval_phis (s with vs_gas_readings := W) bb.bb_instructions of
       OK u => gas_count_block n C bb
         (u with vs_inst_idx := phi_prefix_length bb.bb_instructions) | _ => 0) =
      gas_count_block n C br (t with vs_gas_readings := W) /\
    (case eval_phis (s with vs_gas_readings := W) bb.bb_instructions of
       OK u => trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bb
         (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)) | _ => []) =
      trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn br
        (t with vs_gas_readings := W)) /\
    (case eval_phis (s with vs_gas_readings := W) bb.bb_instructions of
       OK u => gas_events_block n C fn.fn_name bb
         (u with vs_inst_idx := phi_prefix_length bb.bb_instructions) | _ => []) =
      gas_events_block n C fn.fn_name br (t with vs_gas_readings := W)
Proof
  strip_tac >> drule_all native_pseudo_phase_readings >> strip_tac >>
  map_every qx_gen_tac [`n`, `ws`, `C`, `pad`, `fn`, `p`, `d`] >>
  simp_tac pure_ss [LET_THM] >>
  `EVERY (\i. i.inst_opcode <> PHI) rest` by
    (fs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `phi_prefix_length pre <= LENGTH pre` by
    simp[venomExecProofsTheory.phi_prefix_length_le] >>
  `phi_prefix_length pre - LENGTH pre = 0` by decide_tac >>
  `exec_block n C bb ((sp with vs_gas_readings := ws) with
      vs_inst_idx := phi_prefix_length pre) =
      exec_block n C (bb with bb_instructions := REPLICATE (LENGTH pre) pad ++ rest)
        (t with vs_gas_readings := ws) /\
   trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn bb
      ((sp with vs_gas_readings := ws) with vs_inst_idx := phi_prefix_length pre)) =
      trace_gas (dftGasFromListTraceDefs$trace_block p d n C fn
        (bb with bb_instructions := REPLICATE (LENGTH pre) pad ++ rest)
        (t with vs_gas_readings := ws)) /\
   gas_events_block n C fn.fn_name bb
      ((sp with vs_gas_readings := ws) with vs_inst_idx := phi_prefix_length pre) =
      gas_events_block n C fn.fn_name
        (bb with bb_instructions := REPLICATE (LENGTH pre) pad ++ rest)
        (t with vs_gas_readings := ws)` by
    (irule native_pseudo_suffix_skip >>
     qexistsl_tac [`rest`, `DROP (phi_prefix_length pre) pre`] >>
     simp[DROP_APPEND, rich_listTheory.EVERY_DROP, arithmeticTheory.SUB_EQ_0]) >>
  simp[run_block_def, dftIndexedExecTheory.dft_phi_prefix_append,
       dftIndexedExecTheory.dft_eval_phis_append] >>
  metis_tac[gas_events_length]
QED

Theorem native_block_entry_residual_boundary:
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
  strict_dom_vars_defined fn s /\ fn_reachable fn s.vs_current_bb /\
  ctx_labels_bound C s.vs_labels /\ ctx_labels_bound C' s.vs_labels /\
  ~s.vs_call_ctx.cc_static /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb' /\
  terminates (run_block b C' bb' s) ==>
  let pre = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions;
      todo = FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions;
      j = LENGTH pre in
  ?sp t scheduled body.
    bb.bb_instructions = pre ++ todo /\
    bb'.bb_instructions = pre ++ body /\ bb'.bb_label = bb.bb_label /\
    EVERY (\i. is_pseudo i.inst_opcode) pre /\
    EVERY (\i. ~is_pseudo i.inst_opcode) todo /\
    EVERY (\i. ~is_pseudo i.inst_opcode) body /\
    eval_phis s pre = OK sp /\
    FOLDR (dft_exec_cons b C') OK (DROP (phi_prefix_length pre) pre)
      (sp with vs_inst_idx := phi_prefix_length pre) = OK t /\
    t.vs_inst_idx = j /\ t.vs_gas_readings = s.vs_gas_readings /\
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
    EVERY inst_shape_ok bb.bb_instructions /\
    dft_remaining_inv fn bb todo t /\
    ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
    ~t.vs_call_ctx.cc_static /\
    dft_head_bubbles (\x y.
      MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
      ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
      id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
      ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
      todo scheduled /\
    EVERY (from_block bb.bb_instructions) body /\
    LIST_REL (\h i. h.inst_id = i.inst_id) scheduled body /\
    (!bx rest. bx.bb_label = bb.bb_label /\ bx.bb_instructions = pre ++ rest /\
      EVERY (\i. ~is_pseudo i.inst_opcode) rest ==>
      !n ws D pad f p d.
      let br = bb with bb_instructions := REPLICATE j pad ++ rest in
      run_block n D bx (s with vs_gas_readings := ws) =
        exec_block n D br (t with vs_gas_readings := ws) /\
      (case eval_phis (s with vs_gas_readings := ws) bx.bb_instructions of
         OK u => gas_count_block n D bx
           (u with vs_inst_idx := phi_prefix_length bx.bb_instructions) | _ => 0) =
        gas_count_block n D br (t with vs_gas_readings := ws) /\
      (case eval_phis (s with vs_gas_readings := ws) bx.bb_instructions of
         OK u => trace_gas (dftGasFromListTraceDefs$trace_block p d n D f bx
           (u with vs_inst_idx := phi_prefix_length bx.bb_instructions)) | _ => []) =
        trace_gas (dftGasFromListTraceDefs$trace_block p d n D f br
          (t with vs_gas_readings := ws)) /\
      (case eval_phis (s with vs_gas_readings := ws) bx.bb_instructions of
         OK u => gas_events_block n D f.fn_name bx
           (u with vs_inst_idx := phi_prefix_length bx.bb_instructions) | _ => []) =
        gas_events_block n D f.fn_name br (t with vs_gas_readings := ws))
Proof
  strip_tac >> simp_tac pure_ss [LET_THM] >>
  `wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
   EVERY inst_wf bb.bb_instructions /\
   EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
   EVERY inst_shape_ok bb.bb_instructions /\ pseudos_prefix bb /\
   ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
   bb.bb_label = s.vs_current_bb` by suspend "structure" >>
  drule_all dftRunRelTheory.dft_fn_rel_lookup_order >> strip_tac >>
  drule_all dftRunRelTheory.dft_block_head_bubbles >> strip_tac >>
  rename1 `bb'.bb_instructions = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++ out_body` >>
  qabbrev_tac `pre = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions` >>
  qabbrev_tac `todo = FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions` >>
  `bb.bb_instructions = pre ++ todo /\
   EVERY (\i. is_pseudo i.inst_opcode) pre /\
   EVERY (\i. ~is_pseudo i.inst_opcode) todo /\
   EVERY (from_block bb.bb_instructions) out_body /\
   EVERY (\i. ~is_pseudo i.inst_opcode) out_body /\
   bb'.bb_label = bb.bb_label` by suspend "partition" >>
  `?sp t. eval_phis s pre = OK sp /\
     FOLDR (dft_exec_cons b C') OK (DROP (phi_prefix_length pre) pre)
       (sp with vs_inst_idx := phi_prefix_length pre) = OK t` by suspend "phase" >>
  qexistsl_tac [`sp`, `t`, `norm`, `out_body`] >>
  simp_tac pure_ss [] >>
  `t.vs_inst_idx = LENGTH pre /\ t.vs_gas_readings = s.vs_gas_readings /\
   dft_remaining_inv fn bb todo t /\
   ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
   ~t.vs_call_ctx.cc_static` by suspend "initialize" >>
  simp[] >> conj_tac
  >- (irule LIST_REL_mono >> qexists_tac `\h i. h.inst_id = i.inst_id /\
          (!fuel ctx s. step_inst fuel ctx h s = step_inst fuel ctx i s)` >> simp[]) >>
  suspend "bridge"
QED

Resume native_block_entry_residual_boundary[structure]:
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
              venomExecPropsTheory.lookup_block_label] >>
  `wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_pseudos_prefix fn /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)` by
    fs[dftRunRelTheory.dft_fn_rel_def] >>
  `EVERY inst_shape_ok (fn_insts fn)` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >>
     first_x_assum drule >>
     simp[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  simp[] >> rpt conj_tac
  >- (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[])
  >- metis_tac[dftGasInvContractBoundaryTheory.inv_dft_fn_rel_block_no_alloca]
  >- (irule ctxLookupAgreeHelpersTheory.EVERY_fn_block >> goal_assum (drule_at Any) >> simp[])
  >- fs[fn_pseudos_prefix_def, EVERY_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (\f. FLAT (MAP (\b. MAP (\i. i.inst_id)
     b.bb_instructions) f.fn_blocks)) C.ctx_functions))` by
    fs[o1_ctx_shape_def, ctx_inst_ids_distinct_def] >>
  drule_all venomWfPropsTheory.all_distinct_flat_map_member >>
  BETA_TAC >> strip_tac >>
  drule_all venomWfPropsTheory.all_distinct_flat_map_member >> simp[]
QED
Resume native_block_entry_residual_boundary[partition]:
  `EVERY (from_block bb.bb_instructions) out_body /\
   bb'.bb_label = bb.bb_label` by fs[dft_block_rel_def] >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) out_body` by
    (fs[EVERY_MEM, from_block_def] >> metis_tac[flip_operands_is_pseudo]) >>
  simp[Abbr `pre`, Abbr `todo`, EVERY_FILTER] >>
  fs[venomWfPropsTheory.pseudos_prefix_split] >>
  `FILTER (\i. is_pseudo i.inst_opcode) ps = ps /\
   FILTER (\i. ~is_pseudo i.inst_opcode) rs = rs /\
   FILTER (\i. is_pseudo i.inst_opcode) rs = [] /\
   FILTER (\i. ~is_pseudo i.inst_opcode) ps = []` by
    (simp[FILTER_EQ_ID, FILTER_EQ_NIL] >> fs[EVERY_MEM]) >>
  simp[FILTER_APPEND_DISTRIB]
QED
Resume native_block_entry_residual_boundary[phase]:
  `run_block b C' bb' s =
    case eval_phis s pre of
      OK u => FOLDR (dft_exec_cons b C') (dft_exec_suffix b C' out_body)
        (DROP (phi_prefix_length pre) pre)
        (u with vs_inst_idx := phi_prefix_length pre)
    | Error e => Error e` by
    (irule dftIndexedExecTheory.dft_run_block_prefix >> simp[]) >>
  qspecl_then [`s`, `pre`] strip_assume_tac eval_phis_ok_or_error_defs
  >- (qexists_tac `s'` >> simp[] >>
      `EVERY (\i. ~is_terminator i.inst_opcode)
         (DROP (phi_prefix_length pre) pre)` by
        (irule rich_listTheory.EVERY_DROP >> simp[EVERY_MEM] >>
         qx_gen_tac `i` >> strip_tac >>
         `is_pseudo i.inst_opcode` by fs[EVERY_MEM] >>
         pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
         Cases_on `i.inst_opcode` >> simp[is_pseudo_def, is_terminator_def]) >>
      `(?t. FOLDR (dft_exec_cons b C') OK (DROP (phi_prefix_length pre) pre)
         (s' with vs_inst_idx := phi_prefix_length pre) = OK t) \/
       (?e. FOLDR (dft_exec_cons b C') OK (DROP (phi_prefix_length pre) pre)
         (s' with vs_inst_idx := phi_prefix_length pre) = Error e)` by
        (irule native_pseudo_fold_cases >> simp[rich_listTheory.EVERY_DROP]) >>
      pop_assum strip_assume_tac
      >- metis_tac[] >>
      qpat_x_assum `terminates _` mp_tac >>
      asm_rewrite_tac[] >>
      simp[Once dftRunRelTheory.dft_exec_prefix_continue] >>
      simp[passSimulationDefsTheory.terminates_def]) >>
  fs[passSimulationDefsTheory.terminates_def]
QED
Resume native_block_entry_residual_boundary[initialize]:
  `EVERY (\i. inst_wf i /\ ~is_terminator i.inst_opcode) pre` by
    (simp[EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >> conj_tac
     >- fs[EVERY_MEM] >>
     `is_pseudo i.inst_opcode` by fs[EVERY_MEM] >>
     pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `i.inst_opcode` >> simp[is_pseudo_def, is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (DROP (phi_prefix_length pre) pre)` by
    (irule rich_listTheory.EVERY_DROP >> fs[EVERY_MEM]) >>
  `t.vs_inst_idx = phi_prefix_length pre + LENGTH (DROP (phi_prefix_length pre) pre)` by
    (qspecl_then [`DROP (phi_prefix_length pre) pre`,
       `sp with vs_inst_idx := phi_prefix_length pre`, `phi_prefix_length pre`]
       mp_tac native_prefix_cut >>
     (impl_tac >- simp[]) >>
     disch_then (mp_tac o cj 4 o SRULE [LET_THM]) >>
     disch_then (qspecl_then [`b`, `C'`] mp_tac) >> simp[]) >>
  `phi_prefix_length pre <= LENGTH pre` by
    simp[venomExecProofsTheory.phi_prefix_length_le] >>
  `t.vs_inst_idx = LENGTH pre` by fs[] >>
  `t.vs_gas_readings = s.vs_gas_readings` by
    metis_tac[native_pseudo_phase_readings] >>
  drule_all dftAvailabilityTheory.dft_pseudo_initialization >> strip_tac >>
  `t.vs_call_ctx = s.vs_call_ctx` by
    (drule_all dftRunRelTheory.dft_prefix_call_ctx >>
     drule dftRunRelTheory.dft_eval_phis_call_ctx >> simp[]) >>
  simp[] >>
  simp[Abbr `todo`] >> irule dftRunRelTheory.dft_remaining_inv_initialized >>
  simp[] >> qexistsl_tac [`C'`, `b`, `s`, `sp`] >>
  gvs[Abbr `pre`] >>
  rpt strip_tac >>
  qpat_x_assum `ctx_labels_bound C s.vs_labels` mp_tac >>
  simp[dftRunRelTheory.ctx_labels_bound_def] >>
  disch_then irule >> qexistsl_tac [`fn`, `i`] >> simp[] >>
  simp[fn_insts_def] >> irule venomInstTheory.fmp_fn_insts_blocks_intro >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume native_block_entry_residual_boundary[bridge]:
  rpt gen_tac >> strip_tac >>
  `!pad. bx with bb_instructions := REPLICATE (LENGTH pre) pad ++ rest =
   bb with bb_instructions := REPLICATE (LENGTH pre) pad ++ rest` by
    simp[basic_block_component_equality] >>
  drule_all native_pseudo_entry_bridge >> simp[]
QED
Finalise native_block_entry_residual_boundary

Theorem native_dft_strict_dom_transport:
  fn' = dft_fn fn /\ dft_fn_rel fn fn' ==>
  (strict_dom_vars_defined fn' x <=> strict_dom_vars_defined fn x)
Proof
  strip_tac >>
  `fn' = fn with fn_blocks := fn'.fn_blocks` by
    (gvs[dft_fn_def] >> pairarg_tac >> simp[]) >>
  qpat_x_assum `fn' = dft_fn fn` kall_tac >>
  `wf_function fn /\ LIST_REL dftScheduleOrder$dft_block_rel fn.fn_blocks fn'.fn_blocks` by
    gvs[dft_fn_rel_def] >>
  `!d n. fn_dominates fn' d n <=> fn_dominates fn d n` by
    metis_tac[dftSsaPreserveTheory.dft_block_rel_dominates] >>
  simp[venomWfPropsTheory.strict_dom_vars_defined_def] >>
  eq_tac >> rpt strip_tac
  >- (drule_all dftSsaPreserveTheory.dft_blocks_member_left >> strip_tac >>
      `ALL_DISTINCT (MAP (\i. i.inst_id) d_bb.bb_instructions)` by
        metis_tac[dftCorrectnessTheory.bb_inst_ids_distinct] >>
      drule_all dftSsaPreserveTheory.dft_block_rel_member >> strip_tac >>
      metis_tac[dftSsaPreserveTheory.dft_block_rel_label,
                dftStructuralTheory.flip_operands_inst_outputs]) >>
  drule_all dftSsaPreserveTheory.dft_blocks_member_right >> strip_tac >>
  drule_all dftSsaPreserveTheory.dft_block_rel_origin >> strip_tac >>
  metis_tac[dftSsaPreserveTheory.dft_block_rel_label,
            dftStructuralTheory.flip_operands_inst_outputs]
QED

Theorem native_blocks_successor_admissible:
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\ MEM fn C.ctx_functions /\
  fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
  strict_dom_vars_defined fn s /\ fn_reachable fn s.vs_current_bb /\
  ctx_labels_bound C s.vs_labels /\ ctx_labels_bound C' s.vs_labels /\
  ~s.vs_call_ctx.cc_static /\ terminates (run_blocks (SUC b) C' fn' s) /\
  gas_count_blocks (SUC b) C' fn' s <= LENGTH s.vs_gas_readings /\
  lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb' /\
  run_block b C' bb' s = OK u /\ ~u.vs_halted ==>
  strict_dom_vars_defined fn u /\ fn_reachable fn u.vs_current_bb /\
  ctx_labels_bound C u.vs_labels /\ ctx_labels_bound C' u.vs_labels /\
  ~u.vs_call_ctx.cc_static /\ terminates (run_blocks b C' fn' u) /\
  gas_count_blocks b C' fn' u <= LENGTH u.vs_gas_readings
Proof
  strip_tac >>
  `MEM fn' C'.ctx_functions` by
    (rev_drule_all LIST_REL_MEM_IMP >> simp[]) >>
  `wf_function fn' /\ fn_inst_wf fn'` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[o1_fn_shape_def]) >>
  `MEM bb' fn'.fn_blocks /\ bb'.bb_label = s.vs_current_bb` by
    (fs[lookup_block_def] >> drule FIND_P >>
     drule venomInstTheory.FIND_MEM >> simp[]) >>
  `strict_dom_vars_defined fn' s` by
    metis_tac[native_dft_strict_dom_transport] >>
  `fn' = fn with fn_blocks := fn'.fn_blocks` by
    (gvs[dft_fn_def] >> pairarg_tac >> simp[]) >>
  `!lbl. fn_reachable fn' lbl <=> fn_reachable fn lbl` by
    (fs[dft_fn_rel_def] >>
     metis_tac[dftSsaPreserveTheory.dft_block_rel_reachable]) >>
  `EVERY inst_wf bb'.bb_instructions` by
    metis_tac[fn_inst_wf_def, EVERY_MEM] >>
  `strict_dom_vars_defined fn' u` by
    metis_tac[venomWfPropsTheory.strict_dom_vars_defined_run_block_entry] >>
  `bb_well_formed bb'` by metis_tac[wf_function_def] >>
  `?q. eval_phis s bb'.bb_instructions = OK q /\
       exec_block b C' bb'
         (q with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = OK u` by
    (mp_tac (Q.SPECL [`s`, `bb'.bb_instructions`] eval_phis_ok_or_error_defs) >>
     strip_tac >> fs[run_block_def] >> metis_tac[]) >>
  `MEM u.vs_current_bb (bb_succs bb')` by
    (irule venomExecProofsTheory.exec_block_current_bb_in_succs >>
     reverse conj_tac
     >- (conj_tac >- metis_tac[bb_well_formed_def] >>
         qexistsl_tac [`C'`, `b`,
           `q with vs_inst_idx := phi_prefix_length bb'.bb_instructions`] >>
         simp[venomExecProofsTheory.phi_prefix_length_le]) >>
     fs[bb_well_formed_def] >> rpt strip_tac >>
     `i < LENGTH bb'.bb_instructions` by decide_tac >>
     qpat_x_assum `!j. _ /\ is_terminator _ ==> _` drule >>
     simp[] >> decide_tac) >>
  `fn_reachable fn' u.vs_current_bb` by
    (irule venomExecProofsTheory.fn_reachable_step >>
     qexists_tac `s.vs_current_bb` >>
     simp[fn_cfg_edge_def] >> metis_tac[]) >>
  `u.vs_call_ctx = s.vs_call_ctx` by
    (drule venomExecProofsTheory.exec_block_preserves_call_ctx >>
     drule dft_eval_phis_call_ctx >> simp[]) >>
  `gas_count_blocks (SUC b) C' fn' s =
     gas_count_block b C' bb'
       (q with vs_inst_idx := phi_prefix_length bb'.bb_instructions) +
     gas_count_blocks b C' fn' u` by
    simp[Once gas_count_blocks_def] >>
  `u.vs_gas_readings = DROP
     (gas_count_block b C' bb'
       (q with vs_inst_idx := phi_prefix_length bb'.bb_instructions))
     s.vs_gas_readings` by
    (mp_tac (cj 2 gas_count_suffix) >>
     disch_then (qspecl_then [`b`, `C'`, `bb'`,
       `q with vs_inst_idx := phi_prefix_length bb'.bb_instructions`] mp_tac) >>
     drule gas_count_phis_ok >> simp[gas_count_suffix_def]) >>
  gvs[Once run_blocks_unfold] >>
  metis_tac[native_dft_strict_dom_transport, ctx_labels_bound_run_block,
            LENGTH_DROP, arithmeticTheory.LESS_EQ_ADD_SUB]
QED

(* Whole-block projections keep the silent entry phase behind its boundary. *)
val native_block_gasq = ``\q r n D f bx x.
  case eval_phis x bx.bb_instructions of
    OK z => trace_gas (dftGasFromListTraceDefs$trace_block q r n D f bx
      (z with vs_inst_idx := phi_prefix_length bx.bb_instructions))
  | _ => []``;
val native_block_sitesq = ``\n D f bx x.
  case eval_phis x bx.bb_instructions of
    OK z => gas_events_block n D f.fn_name bx
      (z with vs_inst_idx := phi_prefix_length bx.bb_instructions)
  | _ => []``;
val native_block_packetq = ``\q r bx bx' x K S U.
  let obsx = ^native_block_gasq q r b C' fn' bx' x;
      R = run_block b C' bx' x in
  let M = MAP (ALOOKUP obsx) K in
  ALL_DISTINCT K /\
  EVERY (block_region q r (MAP (\i. i.inst_id)
    (FILTER (\i. ~is_pseudo i.inst_opcode) bx.bb_instructions))) K /\
  LENGTH K = LENGTH S /\
  PERM (MAP THE (FILTER IS_SOME M) ++ U) x.vs_gas_readings /\
  (!u. R = OK u ==> EVERY IS_SOME M /\ U = u.vs_gas_readings) /\
  (!v u. R = IntRet v u ==> EVERY IS_SOME M /\ U = u.vs_gas_readings) /\
  (!g tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M g ==>
    (!n. ?k. k <= LENGTH K /\
      ^native_block_gasq q r n C fn bx (x with vs_gas_readings := g ++ tail) =
        ZIP (TAKE k K, TAKE k g) /\
      ^native_block_sitesq n C fn bx (x with vs_gas_readings := g ++ tail) = TAKE k S) /\
    ((?n. terminates (run_block n C bx (x with vs_gas_readings := g ++ tail))) ==>
      terminates (run_block b C bx (x with vs_gas_readings := g ++ tail)) /\
      dft_res_rel (restore_result [] (run_block b C bx (x with vs_gas_readings := g ++ tail)))
        (restore_result [] R) /\
      (((?u. R = OK u) \/ (?v u. R = IntRet v u)) ==>
        ^native_block_sitesq b C fn bx (x with vs_gas_readings := g ++ tail) = S /\
        (!u. run_block b C bx (x with vs_gas_readings := g ++ tail) = OK u ==>
          u.vs_gas_readings = tail) /\
        (!v u. run_block b C bx (x with vs_gas_readings := g ++ tail) = IntRet v u ==>
          u.vs_gas_readings = tail) /\
        residual_result tail R (run_block b C bx (x with vs_gas_readings := g ++ tail)))))``;

Theorem native_whole_block_packet[local]:
  LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
  strict_dom_vars_defined fn s /\ fn_reachable fn s.vs_current_bb /\
  ctx_labels_bound C s.vs_labels /\ ctx_labels_bound C' s.vs_labels /\
  ~s.vs_call_ctx.cc_static /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb' /\
  terminates (run_block b C' bb' s) /\
  (case eval_phis s bb'.bb_instructions of
    OK z => gas_count_block b C' bb'
      (z with vs_inst_idx := phi_prefix_length bb'.bb_instructions) | _ => 0)
    <= LENGTH s.vs_gas_readings /\ ^native_inventory_IHq ==>
  ?K S U. ^native_block_packetq p d bb bb' s K S U
Proof
  strip_tac >>
  drule_all native_block_entry_residual_boundary >>
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  rename1 `EVERY (from_block bb.bb_instructions) actual_body` >>
  qabbrev_tac `pre = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions` >>
  qabbrev_tac `todo = FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions` >>
  qabbrev_tac `br = bb with bb_instructions := REPLICATE (LENGTH pre) ARB ++ actual_body` >>
  qabbrev_tac `sr = bb with bb_instructions := REPLICATE (LENGTH pre) ARB ++ todo` >>
  `!n ws D f p d.
    run_block n D bb (s with vs_gas_readings := ws) =
      exec_block n D sr (t with vs_gas_readings := ws) /\
    ^native_block_gasq p d n D f bb (s with vs_gas_readings := ws) =
      trace_gas (dftGasFromListTraceDefs$trace_block p d n D f sr
        (t with vs_gas_readings := ws)) /\
    ^native_block_sitesq n D f bb (s with vs_gas_readings := ws) =
      gas_events_block n D f.fn_name sr (t with vs_gas_readings := ws)` by
    (rpt gen_tac >> first_x_assum (qspecl_then [`bb`, `todo`] mp_tac) >>
     simp[Abbr `sr`, Abbr `pre`, Abbr `todo`]) >>
  `!n ws D f p d.
    run_block n D bb' (s with vs_gas_readings := ws) =
      exec_block n D br (t with vs_gas_readings := ws) /\
    ^native_block_gasq p d n D f bb' (s with vs_gas_readings := ws) =
      trace_gas (dftGasFromListTraceDefs$trace_block p d n D f br
        (t with vs_gas_readings := ws)) /\
    ^native_block_sitesq n D f bb' (s with vs_gas_readings := ws) =
      gas_events_block n D f.fn_name br (t with vs_gas_readings := ws)` by
    (rpt gen_tac >> first_x_assum (qspecl_then [`bb'`, `actual_body`] mp_tac) >>
     simp[Abbr `br`, Abbr `pre`]) >>
  `t with vs_gas_readings := s.vs_gas_readings = t` by
    (qpat_assum `t.vs_gas_readings = s.vs_gas_readings`
      (fn th => pure_rewrite_tac [GSYM th]) >> simp[]) >>
  `run_block b C' bb' s = exec_block b C' br t` by
    (qpat_assum `!n ws D f p d. run_block n D bb' _ = _ /\ _`
      (qspecl_then [`b`, `s.vs_gas_readings`, `C'`, `fn'`, `p`, `d`] mp_tac) >>
     simp_tac (srw_ss()) [] >> asm_rewrite_tac[]) >>
  `terminates (exec_block b C' br t) /\
   gas_count_block b C' br t <= LENGTH t.vs_gas_readings` by
    (qpat_x_assum `!bx rest. _` (qspecl_then [`bb'`, `actual_body`] mp_tac) >>
     qpat_x_assum `bb.bb_instructions = _` kall_tac >>
     simp[Abbr `br`, Abbr `pre`] >>
     disch_then (qspecl_then [`b`, `s.vs_gas_readings`, `C'`, `ARB`, `fn'`, `p`, `d`] mp_tac) >>
     simp_tac (srw_ss()) [] >> asm_rewrite_tac[] >> strip_tac >> fs[]) >>
  mp_tac (Q.SPEC `actual_body` (Q.INST [`bt` |-> `br`, `s` |-> `t`,
    `j` |-> `LENGTH (pre:instruction list)`, `pad` |-> `ARB`] native_residual_schedule_packet)) >>
  (impl_tac >- simp[Abbr `br`, Abbr `pre`, Abbr `todo`]) >>
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  rename1 `ALL_DISTINCT keys` >> rename1 `LENGTH keys = LENGTH sites` >>
  qexistsl_tac [`keys`, `sites`, `U`] >>
  simp_tac pure_ss [LET_THM] >>
  suspend "transport"
QED
Resume native_whole_block_packet[transport]:
  qpat_x_assum `bb.bb_instructions = _` kall_tac >>
  qpat_assum `!n ws D f p d. run_block n D bb' _ = _ /\ _`
    (qspecl_then [`b`, `s.vs_gas_readings`, `C'`, `fn'`, `p`, `d`] mp_tac) >>
  simp_tac (srw_ss()) [] >>
  qpat_assum `t with vs_gas_readings := s.vs_gas_readings = t`
    (fn th => pure_rewrite_tac [th]) >> strip_tac >>
  simp_tac (srw_ss()) [] >>
  gvs[Abbr `todo`, Abbr `sr`] >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!g tail. LIST_REL _ _ g ==> _`
    (qspecl_then [`g`, `tail`] mp_tac) >>
  simp[] >> metis_tac[]
QED
Finalise native_whole_block_packet

Theorem dft_blocks_gas_prefix_sound:
  dft_blocks_gas_prefix
Proof
  cheat
QED

