(* Uniform all-fillings prefix mask with entry-aligned oracle replay. *)
Theory dftGasPrefixProvider
Ancestors
  dftGasOracleKeyReplay dftGasToListReplay dftGasOracleDefs
  dftGasFromListRestore dftGasFromListReplay dftGasFromListReadings
  dftGasFromListReplayBoundary dftGasFromListTraceDefs dftGasFromListTraceNames
  dftGasToListTrace dftGasToListAgreement gasOracleReplay
  dftGasToListReachWitness dftGasToListVisitReplay
  dftGasFromListLocator dftGasFromListContextReach
  dftRunRel dftDefs o1PassContract contextRawReachable gasEvents gasCount
  venomExecSemantics venomState venomInst list sorting

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

Theorem dft_blocks_gas_prefix_sound:
  dft_blocks_gas_prefix
Proof
  cheat
QED

