(* One fixed slot mask supplies replay, simulation and abort requests for
   each compatible filling of the same literal context state. *)
Theory dftGasMaskRequests
Ancestors
  dftGasPrefixProvider dftRequestsGas dftGasRequestContract dftContractGas
  dftGasRequestLift o1DftStageSsa
  o1RequestContract o1PassContract unitMemInv unitShapeDefs gasEvents gasCount
  dftDefs dftRunRel dftWf dftCorrectnessFinal venomInst venomWf
  venomExecSemantics venomState venomWfProps list

Theorem dft_ctx_entry[local]:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' /\
  C'.ctx_entry = SOME nm /\ lookup_function nm C'.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  terminates (run_context fuel C' vs') ==>
  ?fn. lookup_function nm C.ctx_functions = SOME fn /\ fn' = dft_fn fn /\
       fn_entry_label fn = SOME lbl /\ MEM fn C.ctx_functions /\
       dft_fn_rel fn fn' /\
       strict_dom_vars_defined fn
         (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) /\
       fn_reachable fn lbl /\ ctx_labels_bound C' vs'.vs_labels /\
       ~vs'.vs_call_ctx.cc_static /\
       run_context fuel C' vs' =
       run_blocks fuel C' fn'
         (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) /\
       terminates (run_blocks fuel C' fn'
         (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>))
Proof
  strip_tac >>
  `C'.ctx_functions = MAP dft_fn C.ctx_functions` by
    metis_tac[dft_ctx_functions_map] >>
  `?fn. lookup_function nm C.ctx_functions = SOME fn /\ fn' = dft_fn fn` by
    (qpat_x_assum `lookup_function nm C'.ctx_functions = _` mp_tac >>
     simp[lookup_function_map]) >>
  gvs[] >>
  `fn_entry_label fn = SOME lbl` by gvs[dft_fn_entry_label] >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `dft_fn_rel fn (dft_fn fn)` by
    (gvs[MEM_EL, LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]) >>
  `ctx_labels_bound (C' : venom_context) vs'.vs_labels` by
    (irule dft_ctx_labels_bound >> gvs[o1_run_state_ok_def]) >>
  `~vs'.vs_call_ctx.cc_static` by gvs[o1_run_state_ok_def] >>
  `run_context fuel C' vs' =
   run_blocks fuel C' (dft_fn fn)
     (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)` by
    (PURE_REWRITE_TAC [run_context_def] >>
     qpat_assum `C'.ctx_entry = C.ctx_entry` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_x_assum `SOME nm = C.ctx_entry`
       (fn th => PURE_REWRITE_TAC [SYM th]) >>
     simp[run_function_def, dft_fn_entry_label]) >>
  rpt conj_tac >> asm_rewrite_tac [] >> gvs[fn_reachable_def] >>
  irule venomWfPropsTheory.strict_dom_vars_defined_entry >> simp[]
QED

Theorem dft_ctx_gas_mask_requests:
  dft_blocks_gas_prefix /\
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\
  ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' /\
  C'.ctx_entry = SOME nm /\ lookup_function nm C'.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  terminates (run_context fuel C' vs') /\
  gas_count_blocks fuel C' fn'
    (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) <=
    LENGTH vs'.vs_gas_readings ==>
  ?fn raw_slots sites unused.
    lookup_function nm C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl /\
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) vs'.vs_gas_readings /\
    !gobs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
      (?extra. sites =
         gas_events_blocks fuel C fn
           (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                        vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra) /\
      ((?fr. terminates
               (run_context fr C (vs' with vs_gas_readings := gobs ++ tail))) ==>
       terminates (run_context fuel C (vs' with vs_gas_readings := gobs ++ tail)) /\
       !D. dead_wf D ==>
         ctx_sim_fuel I D C C' (vs' with vs_gas_readings := gobs ++ tail) vs' /\
         ctx_abort_rq D C C' (vs' with vs_gas_readings := gobs ++ tail) vs' /\
         (o1_lowered_inv C (vs' with vs_gas_readings := gobs ++ tail) ==>
          o1_lowered_inv C' vs')) /\
      !f_src. ?extra. sites =
         gas_events_blocks f_src C fn
           (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                        vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra

Proof
  strip_tac >> drule_all dft_ctx_entry >> strip_tac >>
  `C.ctx_entry = SOME nm` by metis_tac[] >>
  qpat_x_assum `dft_blocks_gas_prefix`
    (mp_tac o REWRITE_RULE [dft_blocks_gas_prefix_def]) >>
  disch_then (qspecl_then [`fuel`, `C`, `C'`, `fn`, `fn'`,
     `vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>`]
     mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  qexistsl [`fn`, `raw_slots`, `sites`, `unused`] >>
  rpt (conj_tac >- fs[]) >>
  rpt gen_tac >> strip_tac >>
  `!f_src. ?extra. sites =
     gas_events_blocks f_src C fn
       (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                    vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra` by
    (gen_tac >>
     qpat_assum `!gobs tail f_src. _ ==> _`
       (qspecl_then [`gobs`, `tail`, `f_src`] mp_tac) >>
     impl_tac >- simp[] >> simp[venom_state_component_equality]) >>
  qpat_x_assum `!gobs tail. LIST_REL _ _ _ ==> _`
    (qspecl_then [`gobs`, `tail`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  conj_tac
  >- (qexists_tac `extra` >> simp[venom_state_component_equality]) >>
  conj_tac >- (
    disch_then (qx_choose_then `fr` assume_tac) >>
    `!f. run_context f C (vs' with vs_gas_readings := gobs ++ tail) =
       run_blocks f C fn
         ((vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
            with vs_gas_readings := gobs ++ tail)` by
      (qpat_assum `C.ctx_entry = SOME nm`
         (fn th => PURE_REWRITE_TAC [run_context_def, th]) >>
       simp[run_function_def, venom_state_component_equality]) >>
    `terminates (run_blocks fr C fn
       ((vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
          with vs_gas_readings := gobs ++ tail))` by metis_tac[] >>
    qpat_x_assum `(?fuel_src. _) ==> _` mp_tac >>
    impl_tac >- (qexists_tac `fr` >> first_assum ACCEPT_TAC) >> strip_tac >>
    conj_tac >- metis_tac[] >> gen_tac >> disch_tac >>
    qpat_x_assum `!vs' nm lbl. _` (qspecl_then [`vs'`, `nm`, `lbl`] mp_tac) >>
    impl_tac >- simp[] >> strip_tac >>
    qpat_x_assum `!f. run_context f C _ = _` kall_tac >>
    irule dft_ctx_replay_rq_gas >> simp[] >> conj_tac
    >- (rpt strip_tac >> irule dft_ev_context_sim_rq >> simp[]) >>
    qexists_tac `orc` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Theorem dft_stage_gas_mask_requests:
  dft_blocks_gas_prefix /\
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' /\ o1_pre 7 C C' /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\ EVERY wf_ssa C.ctx_functions /\
  o1_run_state_ok vs' /\
  C'.ctx_entry = SOME nm /\ lookup_function nm C'.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  terminates (run_context fuel C' vs') /\
  gas_count_blocks fuel C' fn'
    (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) <=
    LENGTH vs'.vs_gas_readings ==>
  ?fn raw_slots sites unused.
    C.ctx_entry = SOME nm /\
    lookup_function nm C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl /\
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) vs'.vs_gas_readings /\
    !gobs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
      (?extra. sites =
         gas_events_blocks fuel C fn
           (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                        vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra) /\
      ((?fr. terminates
               (run_context fr C (vs' with vs_gas_readings := gobs ++ tail))) ==>
       terminates (run_context fuel C (vs' with vs_gas_readings := gobs ++ tail)) /\
       !D. dead_wf D ==>
         ctx_sim_fuel I D C C' (vs' with vs_gas_readings := gobs ++ tail) vs' /\
         ctx_abort_rq D C C' (vs' with vs_gas_readings := gobs ++ tail) vs' /\
         (o1_lowered_inv C (vs' with vs_gas_readings := gobs ++ tail) ==>
          o1_lowered_inv C' vs')) /\
      !f_src. ?extra. sites =
         gas_events_blocks f_src C fn
           (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                        vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra

Proof
  strip_tac >> drule_all dft_stage_fn_rel >> strip_tac >>
  drule ctx_pass_stage_dft >> strip_tac >>
  `ctx_labels_bound C vs'.vs_labels` by
    (irule dft_ctx_labels_bound >> gvs[o1_run_state_ok_def]) >>
  `C.ctx_entry = SOME nm` by gvs[] >>
  drule_all dft_ctx_gas_mask_requests >> strip_tac >>
  qexistsl [`fn`, `raw_slots`, `sites`, `unused`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
