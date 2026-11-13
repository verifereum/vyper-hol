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
 * When DFT's block lemma holds, the runs before it also keep the first n
 * events of a run safe up to the cut n, terminating or not, so the sites
 * start with those n raw events.
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
  passSimulationDefs makeSsaCurrentEvents venomPipelineRunner
  o1FnScheduleDecompHelpers o1PrewalkSafeUpto o1SafeUpto
  o1ContractLowerDloadStage concretizeStageShape o1ContractMakeSsaSrc
  option list

(* ===== Runs at the entry ===== *)

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
    (simp[Abbr `st`] >> conj_tac >> irule run_context_entry_blocks >> gvs[]) >>
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

Theorem filled_entry_state[local]:
  (vs with vs_gas_readings := g) with
    <| vs_prev_bb := NONE; vs_current_bb := l; vs_inst_idx := 0 |> =
  vs with <| vs_gas_readings := g; vs_prev_bb := NONE; vs_current_bb := l;
             vs_inst_idx := 0 |>
Proof
  simp[venom_state_component_equality]
QED

(* ===== DFT and CFG normalization: the walk ===== *)

fun spec_stage n th =
  REWRITE_RULE [] (numLib.REDUCE_RULE (REWRITE_RULE [o1_fn_passes_el] (Q.SPEC n th)));

(* ===== Safe prefixes before DFT ===== *)

(* The cut prefixes of the entry events: for a cut n and a state w, the
   first n events of A's entry run at some fuel are the first n of B's at
   some fuel. *)
Theorem gas_prefix_trans[local]:
  B.ctx_entry = A.ctx_entry /\
  (!nm fa la f.
     A.ctx_entry = SOME nm /\ lookup_function nm A.ctx_functions = SOME fa /\
     fn_entry_label fa = SOME la /\
     n <= LENGTH (gas_events_blocks f A fa
            (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)) ==>
     ?f' fb lb.
       lookup_function nm B.ctx_functions = SOME fb /\ fn_entry_label fb = SOME lb /\
       n <= LENGTH (gas_events_blocks f' B fb
              (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>)) /\
       TAKE n (gas_events_blocks f' B fb
         (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>)) =
       TAKE n (gas_events_blocks f A fa
         (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>))) /\
  (!nm fb lb f.
     B.ctx_entry = SOME nm /\ lookup_function nm B.ctx_functions = SOME fb /\
     fn_entry_label fb = SOME lb /\
     n <= LENGTH (gas_events_blocks f B fb
            (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>)) ==>
     ?f' fc lc.
       lookup_function nm C.ctx_functions = SOME fc /\ fn_entry_label fc = SOME lc /\
       n <= LENGTH (gas_events_blocks f' C fc
              (w with <| vs_prev_bb := NONE; vs_current_bb := lc; vs_inst_idx := 0 |>)) /\
       TAKE n (gas_events_blocks f' C fc
         (w with <| vs_prev_bb := NONE; vs_current_bb := lc; vs_inst_idx := 0 |>)) =
       TAKE n (gas_events_blocks f B fb
         (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>))) ==>
  !nm fa la f.
    A.ctx_entry = SOME nm /\ lookup_function nm A.ctx_functions = SOME fa /\
    fn_entry_label fa = SOME la /\
    n <= LENGTH (gas_events_blocks f A fa
           (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)) ==>
    ?f' fc lc.
      lookup_function nm C.ctx_functions = SOME fc /\ fn_entry_label fc = SOME lc /\
      n <= LENGTH (gas_events_blocks f' C fc
             (w with <| vs_prev_bb := NONE; vs_current_bb := lc; vs_inst_idx := 0 |>)) /\
      TAKE n (gas_events_blocks f' C fc
        (w with <| vs_prev_bb := NONE; vs_current_bb := lc; vs_inst_idx := 0 |>)) =
      TAKE n (gas_events_blocks f A fa
        (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>))
Proof
  rpt strip_tac >>
  qpat_x_assum `!nm fa la f. A.ctx_entry = _ /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  `B.ctx_entry = SOME nm` by metis_tac[] >>
  qpat_x_assum `!nm fb lb f. B.ctx_entry = _ /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  metis_tac[]
QED

(* Same entry events at the same fuel give the same cut prefix. *)
Theorem gas_prefix_same_events[local]:
  o1_run_state_ok w /\
  (!nm fa. lookup_function nm A.ctx_functions = SOME fa ==>
     ?fb. lookup_function nm B.ctx_functions = SOME fb /\
       fn_entry_label fb = fn_entry_label fa /\
       !f st. fn_entry_state fa st ==>
         gas_events_blocks f A fa st = gas_events_blocks f B fb st) ==>
  !nm fa la f.
    A.ctx_entry = SOME nm /\ lookup_function nm A.ctx_functions = SOME fa /\
    fn_entry_label fa = SOME la /\
    n <= LENGTH (gas_events_blocks f A fa
           (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)) ==>
    ?f' fb lb.
      lookup_function nm B.ctx_functions = SOME fb /\ fn_entry_label fb = SOME lb /\
      n <= LENGTH (gas_events_blocks f' B fb
             (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>)) /\
      TAKE n (gas_events_blocks f' B fb
        (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>)) =
      TAKE n (gas_events_blocks f A fa
        (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>))
Proof
  rpt strip_tac >>
  qpat_x_assum `!nm fa. _` drule >> strip_tac >>
  qexistsl [`f`, `fb`, `la`] >>
  `fn_entry_state fa
     (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)` by
    metis_tac[run_state_ok_entry_state] >>
  qpat_x_assum `!f st. _`
    (qspecl_then [`f`, `w with <| vs_prev_bb := NONE; vs_current_bb := la;
                                  vs_inst_idx := 0 |>`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> fs[]
QED

val make_ssa_prefix_tac =
  `EVERY make_ssa_input_ok C.ctx_functions` by
    fs[o1_pre_def, EVERY_MEM, o1_fn_row_def] >>
  match_mp_tac gas_prefix_same_events >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  drule_all make_ssa_stage_gas_events >> strip_tac >>
  qexists_tac `fn'` >> simp[] >>
  drule make_ssa_stage_functions >> strip_tac >>
  drule makeSsaCurrentEventsTheory.current_events_lookup_functions >>
  disch_then (qspec_then `nm` mp_tac) >>
  gvs[optionTheory.OPTREL_def] >>
  metis_tac[make_ssa_current_fn_entry_label];

(* One walk run before DFT keeps the cut prefix.  LowerDload and
   ConcretizeMemLoc need the run to be safe up to the cut; the others keep
   the entry events at every fuel. *)
Theorem o1_walk_step_prefix[local]:
  ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k) C C' /\
  o1_pre k C C' /\ o1_ctx_shape C /\
  dead_wf D /\ k < 7 /\ o1_run_state_ok w /\
  (k = 1 ==> ?names. callee_first names C.ctx_functions /\ o1_safe_upto D lo n C w) /\
  (k = 2 ==> (?names. callee_first names C.ctx_functions) /\
             EVERY ssa_form C.ctx_functions /\
             o1_ptr_safe_upto D lo n C w /\ alloca_frontier_upto n C w) /\
  (k = 3 ==> (?names. callee_first names C.ctx_functions) /\ fmp_free_ctx C) ==>
  !nm fa la f.
    C.ctx_entry = SOME nm /\ lookup_function nm C.ctx_functions = SOME fa /\
    fn_entry_label fa = SOME la /\
    n <= LENGTH (gas_events_blocks f C fa
           (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)) ==>
    ?f' fb lb.
      lookup_function nm C'.ctx_functions = SOME fb /\ fn_entry_label fb = SOME lb /\
      n <= LENGTH (gas_events_blocks f' C' fb
             (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>)) /\
      TAKE n (gas_events_blocks f' C' fb
        (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>)) =
      TAKE n (gas_events_blocks f C fa
        (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>))
Proof
  strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6` by decide_tac >>
  pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (REWRITE_RULE [] o numLib.REDUCE_RULE o
                  REWRITE_RULE [o1_fn_passes_el]) >>
  rpt (qpat_x_assum `_ /\ _` strip_assume_tac) >>
  rpt (qpat_x_assum `?names. _` strip_assume_tac)
  >~ [`VP_MakeSSA`] >- make_ssa_prefix_tac
  >~ [`VP_LowerDload`]
  >- (rpt strip_tac >>
      drule_all lower_dload_stage_events_upto >> strip_tac >>
      qexistsl [`fuel'`, `fn'`, `la`] >> simp[])
  >~ [`VP_ConcretizeMemLoc`]
  >- (rpt strip_tac >>
      `ctx_inst_ids_distinct C` by fs[o1_ctx_shape_def] >>
      `EVERY all_reachable C.ctx_functions /\
       EVERY fn_defs_reach_uses C.ctx_functions` by
        fs[o1_pre_def, o1_fn_row_def, EVERY_MEM, make_ssa_input_ok_def] >>
      mp_tac (Q.INST [`vs` |-> `w`, `fuel` |-> `f`, `name` |-> `nm`,
                      `fn` |-> `fa`, `lbl` |-> `la`,
                      `s` |-> `w with <| vs_prev_bb := NONE; vs_current_bb := la;
                                         vs_inst_idx := 0 |>`]
                layout_stage_prefix_events) >>
      impl_tac >- (simp[] >> metis_tac[]) >>
      strip_tac >> qexistsl [`fuel'`, `fn'`, `la`] >> simp[])
  >~ [`VP_FmpLowering`]
  >- (`EVERY (\fn. fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn)
         C.ctx_functions` by fs[fmp_free_ctx_def] >>
      match_mp_tac gas_prefix_same_events >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >>
      drule_all fmp_lowering_stage_gas_events >> strip_tac >>
      qexists_tac `fn'` >> simp[] >>
      qpat_x_assum `fn_seal_eq _ _`
        (mp_tac o Q.AP_TERM `\g. g.fn_blocks` o REWRITE_RULE [fn_seal_eq_def]) >>
      simp[] >> strip_tac >> fs[fn_entry_label_def, entry_block_def])
  >~ [`VP_MakeSSA`] >- make_ssa_prefix_tac
  >~ [`VP_SimplifyCFG`]
  >- (`EVERY simplify_cfg_fn_ok C.ctx_functions` by
        (gvs[o1_pre_def, o1_fn_row_def, o1_ctx_shape_def, EVERY_MEM] >>
         rpt strip_tac >> irule simplify_cfg_fn_ok_ssa >>
         metis_tac[o1_fn_shape_def]) >>
      rpt strip_tac >>
      drule_all simplify_cfg_stage_gas_prefix >>
      disch_then (qspec_then `f` strip_assume_tac) >>
      qexistsl [`fuel'`, `fn'`, `la`] >> simp[TAKE_APPEND1])
  >> match_mp_tac gas_prefix_same_events >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  `EVERY (o1_fn_row 6) C.ctx_functions` by fs[o1_pre_def] >>
  drule_all sue_stage_gas_events >> strip_tac >>
  qexists_tac `fn'` >> simp[]
QED

(* The runs before DFT keep the cut prefix of a run safe up to the cut:
   the walk input's safety gives the safety LowerDload and
   ConcretizeMemLoc read. *)
Theorem o1_walk_before_dft_prefix[local]:
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  (!k. k <= LENGTH o1_fn_passes ==> (stage k).ctx_entry = (stage 0).ctx_entry) /\
  callee_first names (stage 0).ctx_functions /\
  dead_wf D /\ o1_run_state_ok w /\ o1_safe_upto D lo n (stage 0) w ==>
  !m. m <= 7 ==>
  !nm fa la f.
    (stage 0).ctx_entry = SOME nm /\
    lookup_function nm (stage 0).ctx_functions = SOME fa /\
    fn_entry_label fa = SOME la /\
    n <= LENGTH (gas_events_blocks f (stage 0) fa
           (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)) ==>
    ?f' fb lb.
      lookup_function nm (stage m).ctx_functions = SOME fb /\
      fn_entry_label fb = SOME lb /\
      n <= LENGTH (gas_events_blocks f' (stage m) fb
             (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>)) /\
      TAKE n (gas_events_blocks f' (stage m) fb
        (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>)) =
      TAKE n (gas_events_blocks f (stage 0) fa
        (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>))
Proof
  strip_tac >>
  `!k. k < 7 ==>
     ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
       (stage k) (stage (SUC k)) /\
     o1_pre k (stage k) (stage (SUC k)) /\ o1_ctx_shape (stage k) /\
     (stage k).ctx_entry = (stage 0).ctx_entry` by
    (gen_tac >> strip_tac >>
     `k < LENGTH o1_fn_passes /\ k <= LENGTH o1_fn_passes /\
      SUC k <= LENGTH o1_fn_passes` by simp[o1_fn_passes_el] >>
     simp[o1_pre_def] >> metis_tac[]) >>
  (* the facts LowerDload, ConcretizeMemLoc and FmpLowering read *)
  `ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) (o1_walk_view rpolicy 0)
     (stage 0) (stage 1) /\
   ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) (o1_walk_view rpolicy 1)
     (stage 1) (stage 2) /\
   ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) (o1_walk_view rpolicy 2)
     (stage 2) (stage 3)` by
    (qpat_assum `!k. k < LENGTH _ ==> _`
       (fn th => assume_tac (spec_stage `0` th) >> assume_tac (spec_stage `1` th) >>
                 assume_tac (spec_stage `2` th)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `o1_ctx_shape (stage 0) /\ o1_ctx_shape (stage 1) /\ o1_ctx_shape (stage 2) /\
   EVERY (o1_fn_row 0) (stage 0).ctx_functions /\
   EVERY (o1_fn_row 1) (stage 1).ctx_functions /\
   EVERY (o1_fn_row 2) (stage 2).ctx_functions` by
    (qpat_assum `!k. k <= LENGTH _ ==> o1_ctx_shape _`
       (fn th => assume_tac (spec_stage `0` th) >> assume_tac (spec_stage `1` th) >>
                 assume_tac (spec_stage `2` th)) >>
     qpat_assum `!k. k <= LENGTH _ ==> EVERY _ _`
       (fn th => assume_tac (spec_stage `0` th) >> assume_tac (spec_stage `1` th) >>
                 assume_tac (spec_stage `2` th)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `EVERY make_ssa_input_ok (stage 0).ctx_functions /\
   EVERY make_ssa_input_ok (stage 2).ctx_functions` by
    fs[EVERY_MEM, o1_fn_row_def] >>
  `callee_first names (stage 1).ctx_functions` by
    metis_tac[make_ssa_src_stage_callee_first] >>
  `callee_first names (stage 2).ctx_functions` by
    metis_tac[lower_dload_stage_callee_first] >>
  `o1_safe_upto D lo n (stage 1) w` by
    (drule_all make_ssa_stage_safe_upto >> simp[]) >>
  `EVERY ssa_form (stage 1).ctx_functions` by
    metis_tac[make_ssa_stage_wf_ssa, venomWfTheory.wf_ssa_def, EVERY_MEM] >>
  `EVERY ssa_form (stage 2).ctx_functions` by
    metis_tac[lower_dload_stage_ssa_form] >>
  `o1_ptr_safe_upto D lo n (stage 2) w /\ alloca_frontier_upto n (stage 2) w` by
    (drule_all lower_dload_stage_safe_upto >> simp[]) >>
  `fmp_free_ctx (stage 3) /\ callee_first names (stage 3).ctx_functions` by
    (`reserved_intervals_wf (stage 2).ctx_global_reserved /\
      EVERY (\fn. fn.fn_eom = NONE) (stage 2).ctx_functions /\
      fmp_free_ctx (stage 2)` by fs[o1_ptr_safe_upto_def] >>
     drule_all concretize_stage_shape >> strip_tac >> simp[]) >>
  (* the runs one by one *)
  Induct
  >- (rpt strip_tac >> qexistsl [`f`, `fa`, `la`] >> simp[]) >>
  strip_tac >> `m < 7 /\ m <= 7` by decide_tac >>
  qpat_x_assum `m <= 7 ==> _` (fn th => assume_tac (MP th (ASSUME ``m <= 7``))) >>
  qpat_assum `!k. k < 7 ==> _` (qspec_then `m` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  mp_tac (Q.INST [`A` |-> `stage 0`, `B` |-> `stage (m:num)`, `C` |-> `stage (SUC m)`]
            gas_prefix_trans) >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC >>
      mp_tac (Q.INST [`C` |-> `stage (m:num)`, `C'` |-> `stage (SUC m)`, `k` |-> `m:num`]
                o1_walk_step_prefix) >>
      impl_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
      disch_then ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Theorem take_prefix_extend[local]:
  sites = l ++ e /\ TAKE n l = TAKE n m ==> sites = TAKE n m ++ (DROP n l ++ e)
Proof
  strip_tac >> pop_assum (fn th => rewrite_tac[GSYM th]) >>
  asm_rewrite_tac[APPEND_ASSOC, TAKE_DROP]
QED

(* DFT's mask, with the prefix half when the DFT block lemma holds. *)
Theorem dft_stage_gas_mask_cond[local]:
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
    (!gobs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
      (?extra. sites =
         gas_events_blocks fuel C fn
           (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                        vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra) /\
      ((?fr. terminates
               (run_context fr C (vs' with vs_gas_readings := gobs ++ tail))) ==>
       terminates (run_context fuel C (vs' with vs_gas_readings := gobs ++ tail)) /\
       !D. ctx_sim D C C' (vs' with vs_gas_readings := gobs ++ tail) vs')) /\
    (dft_blocks_gas_prefix ==>
     !gobs tail.
       LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
       !f_src. ?extra. sites =
         gas_events_blocks f_src C fn
           (vs' with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                        vs_current_bb := lbl; vs_inst_idx := 0 |>) ++ extra)
Proof
  strip_tac >> Cases_on `dft_blocks_gas_prefix`
  >- (drule_all dft_stage_gas_mask_prefix >> strip_tac >>
      qexistsl [`fn`, `raw_slots`, `sites`, `unused`] >> simp[] >>
      metis_tac[])
  >> drule_all dft_stage_gas_mask >> strip_tac >>
  qexistsl [`fn`, `raw_slots`, `sites`, `unused`] >> simp[]
QED

Theorem o1_walk_gas_mask[local]:
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  (!k. k <= LENGTH o1_fn_passes ==> (stage k).ctx_entry = (stage 0).ctx_entry) /\
  callee_first names (stage 0).ctx_functions /\
  o1_run_state_ok vs_out /\
  (stage 9).ctx_entry = SOME nm /\
  lookup_function nm (stage 9).ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  terminates (run_context fuel (stage 9) vs_out) /\
  gas_count_blocks fuel (stage 9) fn
    (vs_out with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) <=
    LENGTH vs_out.vs_gas_readings ==>
  ?raw_slots sites unused.
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) vs_out.vs_gas_readings /\
    (!gobs tail D.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs /\
      dead_wf D /\
      o1_inv D 0 (stage 0) (vs_out with vs_gas_readings := gobs ++ tail) /\
      (?fr. terminates (run_context fr (stage 0)
                          (vs_out with vs_gas_readings := gobs ++ tail))) ==>
      (!fr. terminates (run_context fr (stage 0)
                          (vs_out with vs_gas_readings := gobs ++ tail)) ==>
         ?fa la extra.
           lookup_function nm (stage 0).ctx_functions = SOME fa /\
           fn_entry_label fa = SOME la /\
           sites =
             gas_events_blocks fr (stage 0) fa
               (vs_out with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                               vs_current_bb := la; vs_inst_idx := 0 |>) ++ extra) /\
      ctx_sim D (stage 0) (stage 9) (vs_out with vs_gas_readings := gobs ++ tail)
        vs_out) /\
    (dft_blocks_gas_prefix ==>
     !gobs tail D lo n f fa la.
       LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs /\
       dead_wf D /\
       o1_safe_upto D lo n (stage 0) (vs_out with vs_gas_readings := gobs ++ tail) /\
       lookup_function nm (stage 0).ctx_functions = SOME fa /\
       fn_entry_label fa = SOME la /\
       n <= LENGTH (gas_events_blocks f (stage 0) fa
              (vs_out with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                              vs_current_bb := la; vs_inst_idx := 0 |>)) ==>
       ?extra. sites =
         TAKE n (gas_events_blocks f (stage 0) fa
              (vs_out with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                              vs_current_bb := la; vs_inst_idx := 0 |>)) ++ extra)
Proof
  strip_tac >>
  `(stage 0).ctx_entry = SOME nm /\ (stage 7).ctx_entry = SOME nm /\
   (stage 8).ctx_entry = SOME nm` by
    (qpat_assum `!k. k <= LENGTH _ ==> (stage k).ctx_entry = _`
       (fn th => mp_tac (Q.SPEC `9` th) >> mp_tac (Q.SPEC `8` th) >>
                 mp_tac (Q.SPEC `7` th)) >>
     fs[o1_fn_passes_el]) >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_DFT) (o1_walk_view rpolicy 7)
     (stage 7) (stage 8) /\
   ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization)
     (o1_walk_view rpolicy 8) (stage 8) (stage 9)` by
    (qpat_assum `!k. k < LENGTH _ ==> _`
       (fn th => assume_tac (spec_stage `8` th) >> assume_tac (spec_stage `7` th)) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `o1_ctx_shape (stage 7) /\ o1_ctx_shape (stage 8) /\
   EVERY (o1_fn_row 7) (stage 7).ctx_functions /\
   EVERY (o1_fn_row 8) (stage 8).ctx_functions` by
    (qpat_assum `!k. k <= LENGTH _ ==> o1_ctx_shape _`
       (fn th => assume_tac (spec_stage `8` th) >> assume_tac (spec_stage `7` th)) >>
     qpat_assum `!k. k <= LENGTH _ ==> EVERY _ _`
       (fn th => assume_tac (spec_stage `8` th) >> assume_tac (spec_stage `7` th)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `o1_pre 7 (stage 7) (stage 8)` by simp[o1_pre_def] >>
  `EVERY wf_ssa (stage 7).ctx_functions` by
    fs[EVERY_MEM, o1_fn_row_def] >>
  `EVERY wf_ssa (stage 8).ctx_functions` by metis_tac[dft_stage_wf_ssa] >>
  (* termination and the count, back through CFG normalization *)
  drule_all cfg_norm_stage_terminates_back >>
  disch_then (qx_choose_then `fn8` strip_assume_tac) >>
  `fn_entry_label fn8 = SOME lbl` by gvs[] >>
  qabbrev_tac `e = vs_out with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                                  vs_inst_idx := 0 |>` >>
  `fn_entry_state fn8 e` by metis_tac[run_state_ok_entry_state] >>
  `run_context fuel (stage 9) vs_out = run_blocks fuel (stage 9) fn e` by
    (simp[Abbr `e`] >> irule run_context_entry_blocks >> simp[]) >>
  `?fuel8. terminates (run_blocks fuel8 (stage 8) fn8 e)` by metis_tac[] >>
  `run_context fuel8 (stage 8) vs_out = run_blocks fuel8 (stage 8) fn8 e` by
    (simp[Abbr `e`] >> irule run_context_entry_blocks >> simp[]) >>
  mp_tac (Q.INST [`C` |-> `stage 8`, `C'` |-> `stage 9`, `name` |-> `nm`,
                  `fn` |-> `fn8`, `view` |-> `o1_walk_view rpolicy 8`]
            cfg_norm_stage_gas_events_prefix) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `fn9` strip_assume_tac) >>
  `fn9 = fn` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  first_x_assum (qspecl_then [`e`, `fuel8`] mp_tac) >> simp[] >> strip_tac >>
  `gas_events_blocks fuel' (stage 9) fn e = gas_events_blocks fuel (stage 9) fn e` by
    (irule gas_events_blocks_terminates_eq >> metis_tac[]) >>
  `gas_count_blocks fuel8 (stage 8) fn8 e <= LENGTH vs_out.vs_gas_readings` by
    (`gas_count_blocks fuel8 (stage 8) fn8 e = gas_count_blocks fuel (stage 9) fn e` by
       (simp[GSYM (cj 3 gas_events_length)] >> metis_tac[APPEND_NIL]) >>
     simp[]) >>
  (* the DFT mask at the output state *)
  mp_tac (Q.INST [`C` |-> `stage 7`, `C'` |-> `stage 8`, `vs'` |-> `vs_out`,
                  `fuel` |-> `fuel8`, `fn'` |-> `fn8`,
                  `view` |-> `o1_walk_view rpolicy 7`] dft_stage_gas_mask_cond) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (qx_choosel_then [`fn7`, `raw_slots`, `sites`, `unused`]
                strip_assume_tac) >>
  qexistsl [`raw_slots`, `sites`, `unused`] >> simp[] >>
  reverse conj_tac
  >- ((* the safe prefix *)
      rpt strip_tac >>
      qpat_x_assum `dft_blocks_gas_prefix ==> _`
        (fn th => mp_tac (Q.SPECL [`gobs`, `tail`] (UNDISCH th))) >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
      RULE_ASSUM_TAC (REWRITE_RULE [GSYM filled_entry_state]) >>
      rewrite_tac [GSYM filled_entry_state] >>
      mp_tac (Q.INST [`w` |-> `vs_out with vs_gas_readings := gobs ++ tail`]
                o1_walk_before_dft_prefix) >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          simp[run_state_ok_gas_readings]) >>
      disch_then (qspec_then `7` mp_tac) >> impl_tac >- simp[] >>
      disch_then (qspecl_then [`nm`, `fa`, `la`, `f`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (qx_choosel_then [`f7`, `fc`, `lc`] strip_assume_tac) >>
      `fc = fn7` by metis_tac[SOME_11] >>
      `lc = lbl` by metis_tac[SOME_11] >>
      qpat_x_assum `!f_src. _` (qspec_then `f7` strip_assume_tac) >>
      metis_tac[take_prefix_extend]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `dft_blocks_gas_prefix ==> _` kall_tac >>
  qabbrev_tac `w = vs_out with vs_gas_readings := gobs ++ tail` >>
  `o1_run_state_ok w` by simp[Abbr `w`, run_state_ok_gas_readings] >>
  qpat_x_assum `!gobs tail. _` (qspecl_then [`gobs`, `tail`] mp_tac) >>
  simp[] >> strip_tac >>
  mp_tac (Q.INST [`w` |-> `w`] o1_walk_before_dft) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then `6` mp_tac) >> simp[] >> strip_tac >>
  rename1 `terminates (run_context fr0 (stage 0) w)` >>
  `?f7. terminates (run_context f7 (stage 7) w)` by metis_tac[] >>
  `terminates (run_context fuel8 (stage 7) w) /\
   !D. ctx_sim D (stage 7) (stage 8) w vs_out` by metis_tac[] >>
  `ctx_bisim (stage 8) (stage 9)` by
    (irule cfg_norm_stage_bisim >> metis_tac[]) >>
  `ctx_sim D (stage 8) (stage 9) vs_out vs_out` by
    (irule ctx_bisim_ctx_sim >>
     fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
     metis_tac[o1_ctx_shape_run_context_no_intret]) >>
  reverse conj_tac >- metis_tac[ctx_sim_trans] >>
  rpt strip_tac >>
  qpat_x_assum `!f. terminates (run_context f (stage 0) w) ==> _` drule >>
  strip_tac >> gvs[] >>
  qexists_tac `extra` >>
  `run_context fuel8 (stage 7) w =
     run_blocks fuel8 (stage 7) fn7
       (w with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) /\
   run_context f' (stage 7) w =
     run_blocks f' (stage 7) fn7
       (w with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)` by
    (conj_tac >> irule run_context_entry_blocks >> simp[]) >>
  `gas_events_blocks fuel8 (stage 7) fn7
     (w with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) =
   gas_events_blocks f' (stage 7) fn7
     (w with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)` by
    (irule gas_events_blocks_terminates_eq >> metis_tac[]) >>
  fs[]
QED

(* ===== The pipeline ===== *)

Theorem o1_walk_stages[local]:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  reachable_fcg_acyclic unit.cu_context fcg /\
  ALL_DISTINCT (unit_label_namespace unit) /\
  run_callee_first rpolicy o1_fn_passes (fcg_postorder fcg entry)
    (prune_unit_fcg_unreachable unit fcg) s = SOME (unit', s') /\
  ir_supply_inst_ok s /\ EVERY (o1_fn_row 0) unit.cu_context.ctx_functions ==>
  (?names. callee_first names
     (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions) /\
  ?stage.
    stage 0 = (prune_unit_fcg_unreachable unit fcg).cu_context /\
    stage 9 = unit'.cu_context /\
    (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
    (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
    (!k. k <= LENGTH o1_fn_passes ==>
       EVERY (o1_fn_row k) (stage k).ctx_functions) /\
    (!k. k <= LENGTH o1_fn_passes ==> (stage k).ctx_entry = (stage 0).ctx_entry)
Proof
  strip_tac >> drule_all o1_ctx_shape_prune >> strip_tac >>
  drule_all o1_walk_callee_first >> strip_tac >>
  fs[run_callee_first_def] >>
  drule_at (Pos (el 3)) (Q.INST [`R` |-> `o1_fn_row`] o1_schedule_stages) >>
  impl_tac
  >- fs[o1_fn_passes_steps, o1_step_contracts_from_rows, o1_prune_every] >>
  strip_tac >>
  conj_tac >- metis_tac[] >>
  qexists_tac `stage` >> rpt conj_tac
  >- simp[]
  >- fs[o1_fn_passes_el]
  >- (rpt strip_tac >> first_x_assum drule >> simp[o1_walk_view_def])
  >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem o1_prune_gas_events[local]:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  lookup_function entry unit.cu_context.ctx_functions = SOME fn ==>
  !fuel vs. gas_events_blocks fuel unit.cu_context fn vs =
    gas_events_blocks fuel (prune_unit_fcg_unreachable unit fcg).cu_context fn vs
Proof
  rpt strip_tac >>
  `ctx_wf unit.cu_context /\ wf_invoke_targets unit.cu_context` by
    metis_tac[o1_ctx_shape_wf] >>
  drule_all prune_unit_ctx_agree >> strip_tac >>
  `fcg_is_reachable fcg entry` by metis_tac[fcg_analyze_entry_reachable] >>
  `fn_calls_within (fcg_is_reachable fcg) fn` by metis_tac[ctx_agree_def] >>
  irule (cj 3 gas_events_defs_ctx_agree) >>
  qexists_tac `fcg_is_reachable fcg` >> simp[]
QED

Theorem o1_prune_gas_transport[local]:
  o1_ctx_shape u.cu_context /\ u.cu_context.ctx_entry = SOME entry /\
  terminates (run_context f u.cu_context w) ==>
  ?f' nm fa fb la lb.
    u.cu_context.ctx_entry = SOME nm /\
    (prune_unit_fcg_unreachable u (fcg_analyze u.cu_context)).cu_context.ctx_entry =
      SOME nm /\
    lookup_function nm u.cu_context.ctx_functions = SOME fa /\
    lookup_function nm
      (prune_unit_fcg_unreachable u (fcg_analyze u.cu_context)).cu_context.ctx_functions =
      SOME fb /\
    fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
    terminates (run_context f'
      (prune_unit_fcg_unreachable u (fcg_analyze u.cu_context)).cu_context w) /\
    gas_events_blocks f'
      (prune_unit_fcg_unreachable u (fcg_analyze u.cu_context)).cu_context fb
      (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
    gas_events_blocks f u.cu_context fa
      (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)
Proof
  strip_tac >>
  `!fuel vs. run_context fuel u.cu_context vs =
     run_context fuel
       (prune_unit_fcg_unreachable u (fcg_analyze u.cu_context)).cu_context vs` by
    (mp_tac (Q.INST [`M` |-> `\c fn inst s. T`, `unit` |-> `u`,
                     `fcg` |-> `fcg_analyze u.cu_context`] o1_prune_sim) >>
     simp[]) >>
  `fcg_is_reachable (fcg_analyze u.cu_context) entry` by
    metis_tac[fcg_analyze_entry_reachable, o1_ctx_shape_wf] >>
  irule gas_transport_run_eq >>
  simp[prune_unit_fcg_unreachable_fields, lookup_function_prune_fcg_reachable] >>
  metis_tac[o1_prune_gas_events]
QED

Theorem o1_pipeline_gas_mask:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy o1_pipeline_spec unit =
    SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\ o1_run_state_ok vs_out /\
  out.po_unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm out.po_unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  terminates (run_context fuel out.po_unit.cu_context vs_out) /\
  gas_count_blocks fuel out.po_unit.cu_context fn
    (vs_out with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) <=
    LENGTH vs_out.vs_gas_readings ==>
  ?raw_slots sites unused.
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) vs_out.vs_gas_readings /\
    (!gobs tail D.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs /\
      (?fr. terminates (run_context fr unit.cu_context
                          (vs_out with vs_gas_readings := gobs ++ tail))) /\
      dead_wf D /\
      o1_pre_walk_inv D unit.cu_context (vs_out with vs_gas_readings := gobs ++ tail) ==>
      (?fn0 lbl0. unit.cu_context.ctx_entry = SOME nm /\
         lookup_function nm unit.cu_context.ctx_functions = SOME fn0 /\
         fn_entry_label fn0 = SOME lbl0 /\
         !fr. terminates (run_context fr unit.cu_context
                            (vs_out with vs_gas_readings := gobs ++ tail)) ==>
           ?extra. sites =
             gas_events_blocks fr unit.cu_context fn0
               (vs_out with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                               vs_current_bb := lbl0; vs_inst_idx := 0 |>) ++ extra) /\
      ctx_sim D unit.cu_context out.po_unit.cu_context
        (vs_out with vs_gas_readings := gobs ++ tail) vs_out) /\
    (dft_blocks_gas_prefix ==>
     !gobs tail D lo n f fa la.
       LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs /\
       dead_wf D /\
       o1_safe_upto D lo n unit.cu_context (vs_out with vs_gas_readings := gobs ++ tail) /\
       lookup_function nm unit.cu_context.ctx_functions = SOME fa /\
       fn_entry_label fa = SOME la /\
       n <= LENGTH (gas_events_blocks f unit.cu_context fa
              (vs_out with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                              vs_current_bb := la; vs_inst_idx := 0 |>)) ==>
       ?extra. sites =
         TAKE n (gas_events_blocks f unit.cu_context fa
              (vs_out with <| vs_gas_readings := gobs ++ tail; vs_prev_bb := NONE;
                              vs_current_bb := la; vs_inst_idx := 0 |>)) ++ extra)
Proof
  strip_tac >> drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)`
    by simp[irSupplyTheory.init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  drule o1_pre_walk_runs >>
  disch_then (qx_choosel_then [`mid`, `tm`] strip_assume_tac) >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_SimplifyCFG`,
                  `u` |-> `unit`, `u'` |-> `mid`, `s` |-> `init_ir_supply unit`,
                  `s'` |-> `tm`] mapped_pass_stage) >>
  impl_tac >- simp[o1_contract_simplify_cfg_pre_walk] >> strip_tac >>
  `ALL_DISTINCT (unit_label_namespace mid)` by
    metis_tac[unit_labels_wf_namespace] >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_DretDesugar`,
                  `u` |-> `mid`, `u'` |-> `pre`, `s` |-> `tm`,
                  `s'` |-> `t`] mapped_pass_stage) >>
  impl_tac >- simp[o1_contract_dret_desugar_pre_walk] >> strip_tac >>
  `pre.cu_context = mid.cu_context` by metis_tac[dret_desugar_stage_identity] >>
  drule_at (Pos (el 6)) o1_walk_stages >> impl_tac
  >- (gvs[] >> metis_tac[unit_labels_wf_namespace]) >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `names` assume_tac)
                (qx_choose_then `stage` strip_assume_tac)) >>
  qabbrev_tac `P = prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)` >>
  `P.cu_context.ctx_entry = SOME entry` by
    (simp[Abbr `P`, prune_unit_fcg_unreachable_fields] >> metis_tac[]) >>
  `(stage 9).ctx_entry = SOME entry` by
    (qpat_assum `!k. k <= LENGTH _ ==> (stage k).ctx_entry = _`
       (qspec_then `9` mp_tac) >> simp[o1_fn_passes_el]) >>
  `nm = entry` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `stage 9 = _` (fn th => fs[GSYM th] >> assume_tac th) >>
  mp_tac (Q.INST [`nm` |-> `entry`] o1_walk_gas_mask) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`raw_slots`, `sites`, `unused`] strip_assume_tac) >>
  qexistsl [`raw_slots`, `sites`, `unused`] >> simp[] >>
  (* static facts of the pre-walk *)
  `ctx_wf pre.cu_context` by metis_tac[o1_ctx_shape_wf] >>
  `fcg_is_reachable (fcg_analyze pre.cu_context) entry` by
    metis_tac[fcg_analyze_entry_reachable] >>
  `unit.cu_context.ctx_entry = SOME entry` by metis_tac[] >>
  `EVERY (\fn. EVERY (\inst. inst.inst_opcode <> PHI) (fn_insts fn))
     unit.cu_context.ctx_functions` by
    (fs[unitShapeDefsTheory.o1_source_unit_ok_def, EVERY_MEM] >> rpt strip_tac >>
     res_tac >> gvs[unitShapeDefsTheory.raw_opcode_ok_def]) >>
  `EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions` by
    (fs[o1_ctx_shape_def, unit_defs_reach_uses_def, EVERY_MEM] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_no_phi >>
     simp[EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  reverse conj_tac
  >- ((* the safe prefix: raw unit to SimplifyCFG's output, the pruned walk
         input, then the walk *)
      rpt strip_tac >>
      RULE_ASSUM_TAC (REWRITE_RULE [GSYM filled_entry_state]) >>
      rewrite_tac [GSYM filled_entry_state] >>
      `o1_run_state_ok (vs_out with vs_gas_readings := gobs ++ tail)` by
        simp[run_state_ok_gas_readings] >>
      `o1_safe_upto D lo n (stage 0) (vs_out with vs_gas_readings := gobs ++ tail)` by
        (qpat_x_assum `stage 0 = _` (fn th => rewrite_tac[th]) >>
         qunabbrev_tac `P` >>
         mp_tac (Q.INST [`s` |-> `init_ir_supply unit`,
                         `vs` |-> `vs_out with vs_gas_readings := gobs ++ tail`]
                   o1_walk_input_safe_upto) >>
         impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
      mp_tac (Q.SPECL [`rpolicy`, `any_view`, `unit.cu_context`, `mid.cu_context`,
                       `vs_out with vs_gas_readings := gobs ++ tail`, `entry`, `fa`,
                       `la`] simplify_cfg_stage_gas_prefix) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (qspec_then `f` (qx_choosel_then [`f1`, `fm`, `ex1`]
                                    strip_assume_tac)) >>
      `lookup_function entry (stage 0).ctx_functions = SOME fm /\
       !g st. gas_events_blocks g (stage 0) fm st =
              gas_events_blocks g mid.cu_context fm st` by
        (qpat_x_assum `stage 0 = _` (fn th => rewrite_tac[th]) >>
         qunabbrev_tac `P` >>
         `lookup_function entry pre.cu_context.ctx_functions = SOME fm` by
           metis_tac[] >>
         conj_tac >- metis_tac[lookup_function_prune_fcg_reachable] >>
         mp_tac (Q.INST [`fcg` |-> `fcg_analyze pre.cu_context`, `unit` |-> `pre`,
                         `fn` |-> `fm`] o1_prune_gas_events) >>
         impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
         rpt strip_tac >> metis_tac[]) >>
      qpat_x_assum `dft_blocks_gas_prefix ==> _`
        (fn th => mp_tac (Q.SPECL [`gobs`, `tail`, `D`, `lo`, `n`, `f1`, `fm`, `la`]
                            (UNDISCH th))) >>
      qabbrev_tac `st = (vs_out with vs_gas_readings := gobs ++ tail) with
                          <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>` >>
      `gas_events_blocks f1 (stage 0) fm st =
       gas_events_blocks f unit.cu_context fa st ++ ex1` by metis_tac[] >>
      `n <= LENGTH (gas_events_blocks f1 (stage 0) fm st)` by
        (qpat_x_assum `gas_events_blocks f1 (stage 0) fm st = _`
           (fn th => rewrite_tac[th, LENGTH_APPEND]) >> decide_tac) >>
      `TAKE n (gas_events_blocks f1 (stage 0) fm st) =
       TAKE n (gas_events_blocks f unit.cu_context fa st)` by
        (qpat_x_assum `gas_events_blocks f1 (stage 0) fm st = _`
           (fn th => rewrite_tac[th]) >>
         irule TAKE_APPEND1 >> first_assum ACCEPT_TAC) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `dft_blocks_gas_prefix ==> _` kall_tac >>
  qpat_x_assum `!gobs tail D. _` (qspecl_then [`gobs`, `tail`, `D`] assume_tac) >>
  qabbrev_tac `w = vs_out with vs_gas_readings := gobs ++ tail` >>
  `o1_run_state_ok w` by simp[Abbr `w`, run_state_ok_gas_readings] >>
  `ctx_sim D unit.cu_context pre.cu_context w w /\
   o1_walk_src_inv D pre.cu_context w` by metis_tac[] >>
  (* pruning *)
  `(!fuel vs. run_context fuel pre.cu_context vs =
              run_context fuel (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs) /\
   !vs. mem_inv raw_mem_ok pre.cu_context vs ==>
     mem_inv raw_mem_ok (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs` by
    (irule o1_prune_sim >> metis_tac[raw_mem_ok_ctx_free]) >>
  `o1_walk_src_inv D (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context w` by
    (qpat_x_assum `o1_walk_src_inv D pre.cu_context w` mp_tac >>
     rewrite_tac[o1_walk_src_inv_def] >> strip_tac >> conj_tac
     >- (irule o1_src_inv_prune >> metis_tac[])
     >> conj_tac >> irule o1_prune_every >> first_assum ACCEPT_TAC) >>
  `ctx_sim D unit.cu_context (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context w w` by
    (irule ctx_sim_run_context_eq >> qexists_tac `pre.cu_context` >> simp[]) >>
  (* the raw unit's events reach the walk's input *)
  `!f. terminates (run_context f unit.cu_context w) ==>
       ?f' nm fa fb la lb.
         unit.cu_context.ctx_entry = SOME nm /\ mid.cu_context.ctx_entry = SOME nm /\
         lookup_function nm unit.cu_context.ctx_functions = SOME fa /\
         lookup_function nm mid.cu_context.ctx_functions = SOME fb /\
         fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
         terminates (run_context f' mid.cu_context w) /\
         gas_events_blocks f' mid.cu_context fb
           (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
         gas_events_blocks f unit.cu_context fa
           (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)` by
    (rpt strip_tac >> drule run_context_terminates_entry >> strip_tac >>
     drule_all simplify_cfg_stage_gas_prefix >>
     disch_then (qspec_then `f` strip_assume_tac) >> gvs[] >> metis_tac[]) >>
  `!f. terminates (run_context f mid.cu_context w) ==>
       ?f' nm fa fb la lb.
         mid.cu_context.ctx_entry = SOME nm /\ pre.cu_context.ctx_entry = SOME nm /\
         lookup_function nm mid.cu_context.ctx_functions = SOME fa /\
         lookup_function nm pre.cu_context.ctx_functions = SOME fb /\
         fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
         terminates (run_context f' pre.cu_context w) /\
         gas_events_blocks f' pre.cu_context fb
           (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
         gas_events_blocks f mid.cu_context fa
           (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)` by
    (qpat_x_assum `pre.cu_context = _` (fn th => rewrite_tac[th] >> assume_tac th) >>
     rpt strip_tac >> irule gas_transport_refl >> simp[]) >>
  `!f. terminates (run_context f pre.cu_context w) ==>
       ?f' nm fa fb la lb.
         pre.cu_context.ctx_entry = SOME nm /\ (stage 0).ctx_entry = SOME nm /\
         lookup_function nm pre.cu_context.ctx_functions = SOME fa /\
         lookup_function nm (stage 0).ctx_functions = SOME fb /\
         fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
         terminates (run_context f' (stage 0) w) /\
         gas_events_blocks f' (stage 0) fb
           (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
         gas_events_blocks f pre.cu_context fa
           (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)` by
    (qpat_x_assum `stage 0 = _` (fn th => rewrite_tac[th]) >>
     qunabbrev_tac `P` >> rpt strip_tac >>
     irule o1_prune_gas_transport >> metis_tac[]) >>
  `!f. terminates (run_context f unit.cu_context w) ==>
       ?f' nm fa fb la lb.
         unit.cu_context.ctx_entry = SOME nm /\ (stage 0).ctx_entry = SOME nm /\
         lookup_function nm unit.cu_context.ctx_functions = SOME fa /\
         lookup_function nm (stage 0).ctx_functions = SOME fb /\
         fn_entry_label fa = SOME la /\ fn_entry_label fb = SOME lb /\
         terminates (run_context f' (stage 0) w) /\
         gas_events_blocks f' (stage 0) fb
           (w with <| vs_prev_bb := NONE; vs_current_bb := lb; vs_inst_idx := 0 |>) =
         gas_events_blocks f unit.cu_context fa
           (w with <| vs_prev_bb := NONE; vs_current_bb := la; vs_inst_idx := 0 |>)` by
    (rpt strip_tac >> irule gas_transport_trans >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexists_tac `pre.cu_context` >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >> irule gas_transport_trans >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexists_tac `mid.cu_context` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `?fr0. terminates (run_context fr0 (stage 0) w)` by metis_tac[] >>
  `o1_inv D 0 (stage 0) w` by (fs[o1_inv_def] >> metis_tac[]) >>
  qpat_x_assum `LIST_REL _ raw_slots gobs /\ _ ==> _` mp_tac >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  reverse conj_tac >- metis_tac[ctx_sim_trans] >>
  `unit.cu_context.ctx_entry = SOME entry` by gvs[] >>
  `?nm0 fn0 lbl0. unit.cu_context.ctx_entry = SOME nm0 /\
     lookup_function nm0 unit.cu_context.ctx_functions = SOME fn0 /\
     fn_entry_label fn0 = SOME lbl0` by metis_tac[run_context_terminates_entry] >>
  `nm0 = entry` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  qexistsl [`fn0`, `lbl0`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!f. terminates (run_context f unit.cu_context w) ==> _` drule >>
  strip_tac >>
  qpat_x_assum `!fr. terminates (run_context fr (stage 0) w) ==> _` drule >>
  strip_tac >> gvs[] >> metis_tac[]
QED
