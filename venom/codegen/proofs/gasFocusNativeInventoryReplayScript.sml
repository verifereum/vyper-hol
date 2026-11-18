(* An actual native inventory and its compatible filling determine a single
   oracle for both entry replays, including the two visit projections. *)
Theory gasFocusNativeInventoryReplay
Ancestors
  alist[qualified,ignore_grammar] list rich_list
  dftGasFromListTraceDefs dftGasFromListTraceNames dftGasFromListReadings
  dftGasFromListTracePrefix[qualified,ignore_grammar]
  dftGasToListTrace[qualified,ignore_grammar] dftGasToListAgreement
  dftGasPrefixProvider dftGasOracleDefs gasOracleReplay contextRawReachable
  o1PassContract venomWf venomWfProps venomExecSemantics venomState venomInst

Theorem focus_native_inventory_entry_replay:
  o1_ctx_shape C7 /\ o1_ctx_shape C8 /\
  C7.ctx_entry = SOME nm /\ C8.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME f7 /\
  lookup_function nm C8.ctx_functions = SOME f8 /\
  fn_entry_label f7 = SOME lbl /\ fn_entry_label f8 = SOME lbl /\
  obs = trace_gas (dftGasFromListTraceDefs$trace_blocks [] 0 b C8 f8
    (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) /\
  (!e. run_blocks b C8 f8
    (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) <> Error e) /\
  ALL_DISTINCT keys /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (MAP (ALOOKUP obs) keys) raw /\
  (!n. ?k. k <= LENGTH keys /\
    trace_gas (dftGasFromListTraceDefs$trace_blocks [] 0 n C7 f7
      ((vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) with
        vs_gas_readings := raw ++ [0w])) = ZIP (TAKE k keys, TAKE k raw)) ==>
  ?orc.
    (!n. gas_res_rel (run_context n C7 (vs0 with vs_gas_readings := raw ++ [0w]))
                      (ev_context orc n C7 vs0)) /\
    (!n. gas_res_rel (run_context n C8 vs0) (ev_context orc n C8 vs0)) /\
    (!p d fn inst t. ev_reachable orc vs0 C7 p d fn inst t ==>
       ?ws. raw_reachable (vs0 with vs_gas_readings := raw ++ [0w]) C7 fn inst
              (t with vs_gas_readings := ws)) /\
    (!fn inst t. raw_reachable vs0 C8 fn inst t ==>
       ?p d. ev_reachable orc vs0 C8 p d fn inst
              (t with vs_gas_readings := vs0.vs_gas_readings))
Proof
  strip_tac >>
  qabbrev_tac `s = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` >>
  `LENGTH keys = LENGTH raw` by metis_tac[LIST_REL_LENGTH,LENGTH_MAP] >>
  `EVERY wf_function C7.ctx_functions /\ EVERY wf_function C8.ctx_functions` by
    (fs[o1_ctx_shape_def,EVERY_MEM,o1_fn_shape_def] >> metis_tac[]) >>
  `!n. dftGasFromListTraceDefs$trace_context n C8 vs0 =
       dftGasFromListTraceDefs$trace_blocks [] 0 n C8 f8 s` by
    simp[dftGasFromListTraceDefsTheory.trace_context_def,
         dftGasFromListTraceDefsTheory.trace_function_def,Abbr `s`] >>
  `ALL_DISTINCT (MAP FST obs)` by
    (qsuff_tac `ALL_DISTINCT (MAP FST (trace_gas
         (dftGasFromListTraceDefs$trace_context b C8 vs0)))`
     >- simp[] >>
     irule trace_context_gas_names_distinct >>
     qpat_assum `o1_ctx_shape C8` mp_tac >>
     simp_tac bool_ss [o1_ctx_shape_def,ctx_inst_ids_distinct_def] >>
     strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
     drule_all venomWfPropsTheory.all_distinct_flat_map_member >>
     BETA_TAC >> strip_tac >>
     drule_all venomWfPropsTheory.all_distinct_flat_map_member >> simp[]) >>
  qabbrev_tac `orc = (\key. case ALOOKUP (obs ++ ZIP (keys,raw)) key of
                    NONE => 0w | SOME w => w)` >>
  qexists_tac `orc` >> irule fixed_shared_oracle_replay >> asm_rewrite_tac[] >>
  conj_tac >- suspend "target_agreement" >> suspend "source_agreement"
QED

Resume focus_native_inventory_entry_replay[target_agreement]:
  gen_tac >> simp[] >>
  simp_tac pure_ss [Abbr `orc`] >>
  irule (cj 1 native_lookup_fill_subtrace_agreement) >> asm_rewrite_tac[] >>
  Cases_on `n <= b`
  >- (`?suffix. dftGasFromListTraceDefs$trace_blocks [] 0 b C8 f8 s =
          dftGasFromListTraceDefs$trace_blocks [] 0 n C8 f8 s ++ suffix` by
        (irule (cj 3 dftGasFromListTracePrefixTheory.trace_prefix) >> simp[]) >>
      simp[EVERY_MEM]) >>
  `dftGasFromListTraceDefs$trace_blocks [] 0 n C8 f8 s =
     dftGasFromListTraceDefs$trace_blocks [] 0 b C8 f8 s` by
    (irule (cj 3 dftGasFromListTracePrefixTheory.trace_stable) >> simp[] >> decide_tac) >>
  simp[EVERY_MEM]
QED

Resume focus_native_inventory_entry_replay[source_agreement]:
  gen_tac >>
  `trace_agrees orc (dftGasFromListTraceDefs$trace_blocks [] 0 n C7 f7
    (s with vs_gas_readings := raw ++ [0w]))` by
    (simp_tac pure_ss [Abbr `orc`] >>
     irule (cj 2 native_lookup_fill_subtrace_agreement) >> simp[] >>
     qpat_x_assum `!n. ?k. _` (qspec_then `n` strip_assume_tac) >>
     simp[ZIP_TAKE,EVERY_MEM] >> metis_tac[MEM_TAKE]) >>
  drule (cj 3 native_trace_oracle_agreement) >>
  disch_then (qspec_then `vs0.vs_gas_readings` mp_tac) >>
  simp[dftGasToListTraceTheory.trace_context_def,
       dftGasToListTraceTheory.trace_function_def,Abbr `s`]
QED

Finalise focus_native_inventory_entry_replay
