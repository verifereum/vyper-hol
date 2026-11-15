(* Uniform all-fillings prefix mask with entry-aligned oracle replay. *)
Theory dftGasPrefixProvider
Ancestors
  dftGasOracleKeyReplay dftGasToListReplay dftGasOracleDefs
  dftGasSimSwap dftGasSimLocalBoundary
  dftGasFromListRestore dftGasFromListReplay dftGasFromListReadings
  dftGasFromListReplayBoundary dftGasFromListTraceDefs dftGasFromListTraceNames
  dftGasToListTrace dftGasToListAgreement gasOracleReplay
  dftGasToListReachWitness dftGasToListVisitReplay
  dftGasFromListLocator dftGasFromListContextReach
  dftRunRel dftDefs o1PassContract contextRawReachable gasEvents gasCount
  venomExecSemantics venomState venomInst list sorting
  dftGasInvResidualTrace venomInstProps venomInstProofs stateEquivProofs
  dftBlockSim stateFrame venomEffects dftScheduleOrder
  dftGasInvSSAProbe unitShapeDefs venomWf option

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

Theorem dft_blocks_gas_prefix_sound:
  dft_blocks_gas_prefix
Proof
  cheat
QED

