(*
 * One gas-slot mask through the O1 pipeline.
 *
 * DFT chooses one mask of the output's readings before every filling
 * (o1DftStageSim.dft_stage_gas_mask).  The runs before it keep a source
 * run's gas events, each terminating run having a terminating image with
 * the same events; the CFG normalization after it keeps termination both
 * ways and the event count.  Composing these gives the mask's sites as a
 * prefix of the raw unit's events for every terminating filling, and the
 * all-dead simulation from the filled raw state to the output state.
 *)
Theory o1PipelineGasMask
Ancestors
  o1PipelineCompose o1ComposeSupport o1PassContract o1PassLift
  o1ContractTheorems o1DftStageSim o1DftStageSsa o1ContractCfgNormGas
  o1ContractCfgNorm o1ContractMakeSsa o1MakeSsaCfg o1ContractLowerDloadSim
  concretizeLayoutStageSimulation o1ContractFmpLowering ctxSealAgree
  o1SimplifyCfgGasEvents o1ContractSimplifyCfg o1ContractSue
  o1DretDesugarContract dftContractGas gasEvents gasEventsFuel gasCount
  ctxLookupAgree fcgPruning unitTransformDefs venomPipelineDriver
  venomPassSchedule venomExecSemantics venomInst venomState
  passSimulationDefs makeSsaCurrentEvents option list

(* ===== Runs at the entry ===== *)

Theorem run_context_entry[local]:
  ctx.ctx_entry = SOME nm /\ lookup_function nm ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  run_context fuel ctx s =
  run_blocks fuel ctx fn
    (s with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
Proof
  simp[run_context_def, run_function_def]
QED

Theorem run_context_terminates_entry[local]:
  terminates (run_context fuel ctx s) ==>
  ?nm fn lbl. ctx.ctx_entry = SOME nm /\
    lookup_function nm ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
Proof
  simp[run_context_def, run_function_def] >>
  Cases_on `ctx.ctx_entry` >> simp[terminates_def] >>
  Cases_on `lookup_function x ctx.ctx_functions` >> simp[terminates_def] >>
  Cases_on `fn_entry_label x'` >> simp[terminates_def]
QED

Theorem run_state_ok_entry_state[local]:
  o1_run_state_ok vs /\ fn_entry_label fn = SOME lbl ==>
  fn_entry_state fn
    (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
Proof
  simp[o1_run_state_ok_def, o1_initial_state_ok_def, fn_entry_state_def]
QED

Theorem run_state_ok_gas_readings[local]:
  o1_run_state_ok vs ==> o1_run_state_ok (vs with vs_gas_readings := g)
Proof
  simp[o1_run_state_ok_def, o1_initial_state_ok_def,
       lowerDloadDefsTheory.code_layout_valid_def]
QED

Theorem gas_events_blocks_terminates_le[local]:
  terminates (run_blocks f ctx fn s) /\ f <= M ==>
  run_blocks M ctx fn s = run_blocks f ctx fn s /\
  gas_events_blocks M ctx fn s = gas_events_blocks f ctx fn s
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`f`, `ctx`, `fn`, `s`, `M`] (cj 3 gas_events_fuel_extension)) >>
  impl_tac >- simp[] >> strip_tac >> first_x_assum irule >>
  Cases_on `run_blocks f ctx fn s` >> gvs[terminates_def]
QED

Theorem gas_events_blocks_terminates_eq[local]:
  terminates (run_blocks f1 ctx fn s) /\ terminates (run_blocks f2 ctx fn s) ==>
  gas_events_blocks f1 ctx fn s = gas_events_blocks f2 ctx fn s
Proof
  strip_tac >> `f1 <= f1 + f2 /\ f2 <= f1 + f2` by decide_tac >>
  metis_tac[gas_events_blocks_terminates_le]
QED

(* ===== Event transport, run by run ===== *)

(* Each lemma below gives, for a state w and contexts A, B: a terminating
   run of A at w has a terminating run of B at w with the same gas events
   at the entry. *)

Theorem gas_transport_trans[local]:
  (!f. terminates (run_context f A w) ==>
     ?f' nm fa fb la lb.
       A.ctx_entry = SOME nm /\ B.ctx_entry = SOME nm /\
       lookup_function nm A.ctx_functions = SOME fa /\
       lookup_function nm B.ctx_functions = SOME fb /\
       fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
       terminates (run_context f' B w) /\
       gas_events_blocks f' B fb
         (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
       gas_events_blocks f A fa
         (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)) /\
  (!f. terminates (run_context f B w) ==>
     ?f' nm fa fb la lb.
       B.ctx_entry = SOME nm /\ C.ctx_entry = SOME nm /\
       lookup_function nm B.ctx_functions = SOME fa /\
       lookup_function nm C.ctx_functions = SOME fb /\
       fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
       terminates (run_context f' C w) /\
       gas_events_blocks f' C fb
         (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
       gas_events_blocks f B fa
         (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)) /\
  terminates (run_context f A w) ==>
  ?f' nm fa fb la lb.
    A.ctx_entry = SOME nm /\ C.ctx_entry = SOME nm /\
    lookup_function nm A.ctx_functions = SOME fa /\
    lookup_function nm C.ctx_functions = SOME fb /\
    fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
    terminates (run_context f' C w) /\
    gas_events_blocks f' C fb
      (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
    gas_events_blocks f A fa
      (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)
Proof
  rpt strip_tac >>
  qpat_x_assum `!f. terminates (run_context f A w) ==> _` drule >> strip_tac >>
  qpat_x_assum `!f. terminates (run_context f B w) ==> _` drule >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem gas_transport_same_fuel[local]:
  ctx_sim D A B w w /\ o1_run_state_ok w /\ B.ctx_entry = A.ctx_entry /\
  (!nm fa. lookup_function nm A.ctx_functions = SOME fa ==>
     ?fb. lookup_function nm B.ctx_functions = SOME fb /\
       fn_entry_label fb = fn_entry_label fa /\
       !f st. fn_entry_state fa st ==>
         gas_events_blocks f A fa st = gas_events_blocks f B fb st) /\
  terminates (run_context f A w) ==>
  ?f' nm fa fb la lb.
    A.ctx_entry = SOME nm /\ B.ctx_entry = SOME nm /\
    lookup_function nm A.ctx_functions = SOME fa /\
    lookup_function nm B.ctx_functions = SOME fb /\
    fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
    terminates (run_context f' B w) /\
    gas_events_blocks f' B fb
      (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
    gas_events_blocks f A fa
      (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)
Proof
  rpt strip_tac >>
  drule run_context_terminates_entry >> strip_tac >>
  rename1 `lookup_function nm A.ctx_functions = SOME fa` >>
  rename1 `fn_entry_label fa = SOME lbl` >>
  qpat_x_assum `!nm fa. _` drule >> strip_tac >>
  `?f'. dead_result_rel D (run_context f A w) (run_context f' B w)` by
    metis_tac[ctx_sim_def] >>
  `terminates (run_context f' B w)` by metis_tac[dead_result_rel_terminates] >>
  qexistsl [`f'`, `nm`, `fa`, `fb`, `lbl`, `lbl`] >> gvs[] >>
  qabbrev_tac `st = w with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                              vs_inst_idx := 0 |>` >>
  `fn_entry_state fa st` by metis_tac[run_state_ok_entry_state] >>
  `run_context f A w = run_blocks f A fa st /\
   run_context f' B w = run_blocks f' B fb st` by
    (simp[Abbr `st`] >> conj_tac >> irule run_context_entry >> gvs[]) >>
  `terminates (run_blocks f A fa st) /\ terminates (run_blocks f' B fb st)` by
    metis_tac[] >>
  `f <= f + f' /\ f' <= f + f'` by decide_tac >>
  `gas_events_blocks (f + f') A fa st = gas_events_blocks f A fa st /\
   gas_events_blocks (f + f') B fb st = gas_events_blocks f' B fb st` by
    metis_tac[gas_events_blocks_terminates_le] >>
  metis_tac[]
QED

Theorem gas_transport_run_eq[local]:
  B.ctx_entry = A.ctx_entry /\
  (!nm fa. A.ctx_entry = SOME nm /\ lookup_function nm A.ctx_functions = SOME fa ==>
     ?fb. lookup_function nm B.ctx_functions = SOME fb /\
       fn_entry_label fb = fn_entry_label fa /\
       (!f st. gas_events_blocks f A fa st = gas_events_blocks f B fb st) /\
       !f. run_context f A w = run_context f B w) /\
  terminates (run_context f A w) ==>
  ?f' nm fa fb la lb.
    A.ctx_entry = SOME nm /\ B.ctx_entry = SOME nm /\
    lookup_function nm A.ctx_functions = SOME fa /\
    lookup_function nm B.ctx_functions = SOME fb /\
    fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
    terminates (run_context f' B w) /\
    gas_events_blocks f' B fb
      (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
    gas_events_blocks f A fa
      (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)
Proof
  rpt strip_tac >>
  drule run_context_terminates_entry >> strip_tac >>
  rename1 `lookup_function nm A.ctx_functions = SOME fa` >>
  rename1 `fn_entry_label fa = SOME lbl` >>
  qpat_x_assum `!nm fa. _` drule_all >> strip_tac >>
  qexistsl [`f`, `nm`, `fa`, `fb`, `lbl`, `lbl`] >> gvs[] >>
  metis_tac[]
QED

Theorem gas_transport_refl[local]:
  terminates (run_context f A w) ==>
  ?f' nm fa fb la lb.
    A.ctx_entry = SOME nm /\ A.ctx_entry = SOME nm /\
    lookup_function nm A.ctx_functions = SOME fa /\
    lookup_function nm A.ctx_functions = SOME fb /\
    fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
    terminates (run_context f' A w) /\
    gas_events_blocks f' A fb
      (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
    gas_events_blocks f A fa
      (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)
Proof
  strip_tac >> irule gas_transport_run_eq >> simp[] >> metis_tac[]
QED

(* ===== The runs before DFT ===== *)

Theorem o1_fn_passes_el[local]:
  EL 0 o1_fn_passes = CFP_Simple VP_MakeSSA /\
  EL 1 o1_fn_passes = CFP_Simple VP_LowerDload /\
  EL 2 o1_fn_passes = CFP_Simple VP_ConcretizeMemLoc /\
  EL 3 o1_fn_passes = CFP_Simple VP_FmpLowering /\
  EL 4 o1_fn_passes = CFP_Simple VP_MakeSSA /\
  EL 5 o1_fn_passes = CFP_Simple VP_SimplifyCFG /\
  EL 6 o1_fn_passes = CFP_Simple VP_SingleUseExpansion /\
  EL 7 o1_fn_passes = CFP_Simple VP_DFT /\
  EL 8 o1_fn_passes = CFP_Simple VP_CFGNormalization /\
  LENGTH o1_fn_passes = 9
Proof
  EVAL_TAC
QED

Theorem o1_run_contracts_same_gas[local]:
  k < LENGTH o1_fn_passes /\ k <> 7 ==> o1_run_contract rp D k
Proof
  strip_tac >> fs[o1_fn_passes_def] >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/
   k = 8` by decide_tac >>
  gvs[o1_contract_make_ssa_1, o1_contract_lower_dload,
      o1_contract_concretize_mem_loc, o1_contract_fmp_lowering,
      o1_contract_make_ssa_2, o1_contract_simplify_cfg, o1_contract_sue,
      o1_contract_cfg_normalization]
QED

Theorem o1_walk_step_same[local]:
  ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k) C C' /\
  o1_pre k C C' /\ o1_ctx_shape C /\
  dead_wf D /\ k < 7 /\ o1_run_state_ok vs /\ o1_inv D k C vs ==>
  ctx_sim D C C' vs vs /\ o1_inv D (SUC k) C' vs
Proof
  strip_tac >>
  `o1_run_contract rpolicy D k` by
    (irule o1_run_contracts_same_gas >> simp[o1_fn_passes_el]) >>
  fs[o1_run_contract_def, o1_stage_contract_def] >>
  first_x_assum (qspecl_then [`C`, `C'`, `vs`] mp_tac) >> simp[]
QED

val make_ssa_tac =
  `EVERY make_ssa_input_ok C.ctx_functions` by
    fs[o1_pre_def, EVERY_MEM, o1_fn_row_def] >>
  drule gas_transport_same_fuel >> disch_then irule >> fs[] >>
  rpt strip_tac >>
  drule_all make_ssa_stage_gas_events >> strip_tac >>
  qexists_tac `fn'` >> simp[] >>
  drule make_ssa_stage_functions >> strip_tac >>
  drule makeSsaCurrentEventsTheory.current_events_lookup_functions >>
  disch_then (qspec_then `nm` mp_tac) >>
  gvs[optionTheory.OPTREL_def] >>
  metis_tac[make_ssa_current_fn_entry_label];

Theorem o1_walk_step_gas[local]:
  ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k) C C' /\
  o1_pre k C C' /\ o1_ctx_shape C /\ C'.ctx_entry = C.ctx_entry /\
  dead_wf D /\ k < 7 /\ o1_run_state_ok w /\ o1_inv D k C w /\
  terminates (run_context f C w) ==>
  ?f' nm fa fb la lb.
    C.ctx_entry = SOME nm /\ C'.ctx_entry = SOME nm /\
    lookup_function nm C.ctx_functions = SOME fa /\
    lookup_function nm C'.ctx_functions = SOME fb /\
    fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
    terminates (run_context f' C' w) /\
    gas_events_blocks f' C' fb
      (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
    gas_events_blocks f C fa
      (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)
Proof
  strip_tac >>
  `ctx_sim D C C' w w` by metis_tac[o1_walk_step_same] >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6` by decide_tac >>
  pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (REWRITE_RULE [o1_fn_passes_el])
  >~ [`VP_MakeSSA`] >- make_ssa_tac
  >~ [`VP_LowerDload`]
  >- (gvs[o1_inv_def] >> drule_all lower_dload_stage_sim_events >>
      metis_tac[])
  >~ [`VP_ConcretizeMemLoc`]
  >- (gvs[o1_inv_def, o1_src_inv_def] >>
      `ctx_inst_ids_distinct C` by fs[o1_ctx_shape_def] >>
      `EVERY all_reachable C.ctx_functions /\
       EVERY fn_defs_reach_uses C.ctx_functions` by
        fs[EVERY_MEM, make_ssa_input_ok_def] >>
      mp_tac (Q.INST [`vs` |-> `w`, `fuel` |-> `f`]
                layout_stage_terminating_events) >>
      impl_tac >- metis_tac[] >>
      metis_tac[])
  >~ [`VP_FmpLowering`]
  >- (`?names. callee_first names C.ctx_functions` by
        (gvs[o1_inv_def] >> metis_tac[]) >>
      `fmp_free_ctx C` by (gvs[o1_inv_def, o1_static_inv_def]) >>
      `EVERY (\fn. fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn)
         C.ctx_functions` by fs[fmp_free_ctx_def] >>
      irule gas_transport_run_eq >> simp[] >> rpt strip_tac >>
      drule_all fmp_lowering_stage_gas_events >> strip_tac >>
      qexists_tac `fn'` >> simp[] >>
      qpat_x_assum `fn_seal_eq _ _`
        (mp_tac o Q.AP_TERM `\g. g.fn_blocks` o REWRITE_RULE [fn_seal_eq_def]) >>
      simp[] >> strip_tac >> fs[fn_entry_label_def, entry_block_def])
  >~ [`VP_MakeSSA`] >- make_ssa_tac
  >~ [`VP_SimplifyCFG`]
  >- (`EVERY simplify_cfg_fn_ok C.ctx_functions` by
        (gvs[o1_inv_def, o1_ctx_shape_def, o1_ssa_inv_def, EVERY_MEM] >>
         rpt strip_tac >> irule simplify_cfg_fn_ok_ssa >>
         metis_tac[o1_fn_shape_def]) >>
      drule run_context_terminates_entry >> strip_tac >>
      drule_all simplify_cfg_stage_gas_prefix >>
      disch_then (qspec_then `f` strip_assume_tac) >>
      gvs[] >> metis_tac[])
  >> drule gas_transport_same_fuel >> disch_then irule >> fs[] >>
  rpt strip_tac >>
  `EVERY (o1_fn_row 6) C.ctx_functions` by fs[o1_pre_def] >>
  drule_all sue_stage_gas_events >> strip_tac >>
  qexists_tac `fn'` >> simp[]
QED

Theorem o1_walk_before_dft[local]:
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  (!k. k <= LENGTH o1_fn_passes ==> (stage k).ctx_entry = (stage 0).ctx_entry) /\
  dead_wf D /\ o1_run_state_ok w /\ o1_inv D 0 (stage 0) w ==>
  !n. n < 7 ==>
    ctx_sim D (stage 0) (stage (SUC n)) w w /\
    o1_inv D (SUC n) (stage (SUC n)) w /\
    !f. terminates (run_context f (stage 0) w) ==>
     ?f' nm fa fb la lb.
       (stage 0).ctx_entry = SOME nm /\ (stage (SUC n)).ctx_entry = SOME nm /\
       lookup_function nm (stage 0).ctx_functions = SOME fa /\
       lookup_function nm (stage (SUC n)).ctx_functions = SOME fb /\
       fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
       terminates (run_context f' (stage (SUC n)) w) /\
       gas_events_blocks f' (stage (SUC n)) fb
         (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
       gas_events_blocks f (stage 0) fa
         (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)
Proof
  strip_tac >>
  `!k. k < 7 ==>
     ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
       (stage k) (stage (SUC k)) /\
     o1_pre k (stage k) (stage (SUC k)) /\ o1_ctx_shape (stage k) /\
     (stage (SUC k)).ctx_entry = (stage k).ctx_entry` by
    (gen_tac >> strip_tac >>
     `k < LENGTH o1_fn_passes /\ k <= LENGTH o1_fn_passes /\
      SUC k <= LENGTH o1_fn_passes` by simp[o1_fn_passes_el] >>
     simp[o1_pre_def] >> metis_tac[]) >>
  `!k. k < 7 /\ o1_inv D k (stage k) w ==>
     ctx_sim D (stage k) (stage (SUC k)) w w /\
     o1_inv D (SUC k) (stage (SUC k)) w /\
     !f. terminates (run_context f (stage k) w) ==>
     ?f' nm fa fb la lb.
       (stage k).ctx_entry = SOME nm /\ (stage (SUC k)).ctx_entry = SOME nm /\
       lookup_function nm (stage k).ctx_functions = SOME fa /\
       lookup_function nm (stage (SUC k)).ctx_functions = SOME fb /\
       fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
       terminates (run_context f' (stage (SUC k)) w) /\
       gas_events_blocks f' (stage (SUC k)) fb
         (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
       gas_events_blocks f (stage k) fa
         (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!k. k < 7 ==> _` (qspec_then `k` mp_tac) >>
     impl_tac >- simp[] >> strip_tac >>
     mp_tac (Q.INST [`C` |-> `stage k`, `C'` |-> `stage (SUC k)`, `vs` |-> `w`]
               o1_walk_step_same) >>
     impl_tac >- fs[] >> strip_tac >> rpt strip_tac >>
     TRY (first_assum ACCEPT_TAC) >>
     irule o1_walk_step_gas >> fs[] >> metis_tac[]) >>
  Induct
  >- (strip_tac >> qpat_assum `!k. k < 7 /\ _ ==> _` (qspec_then `0` mp_tac) >>
      fs[]) >>
  strip_tac >> `n < 7 /\ SUC n < 7` by decide_tac >>
  qpat_x_assum `n < 7 ==> _` mp_tac >> impl_tac >- decide_tac >> strip_tac >>
  qpat_assum `!k. k < 7 /\ _ ==> _` (qspec_then `SUC n` mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  rpt conj_tac
  >- metis_tac[ctx_sim_trans]
  >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> irule gas_transport_trans >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac `stage (SUC n)` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
