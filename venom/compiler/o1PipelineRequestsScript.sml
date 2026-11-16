(*
 * S4's request companion: run_venom_pipeline_correct with ctx_abort_rq
 * added under the same chosen input state.  When the unoptimized run
 * aborts, the optimized run aborts with requests that are a prefix of the
 * unoptimized run's, each agreeing up to the dead bytes D.  The halt case
 * is already in ctx_sim (dead_result_rel).
 *
 * The composition mirrors o1PipelineCompose with ctx_sim paired with
 * ctx_abort_rq: the walk's run companions (o1RequestRuns and the
 * LowerDload, ConcretizeMemLoc and DFT companions), the two pre-walk runs,
 * and pruning, which leaves runs unchanged.
 *)
Theory o1PipelineRequests
Ancestors
  o1LabelFlowStaticContracts
  o1RequestContract o1RequestRuns o1LowerDloadRequests
  concretizeStageRequests dftRequestsGas o1PipelineCorrect o1PipelineCompose
  o1ComposeSupport o1PassContract o1ContractTheorems o1ScheduleDecomp
  o1FnScheduleDecompHelpers o1DretDesugarContract o1ContractSimplifyCfg
  o1ContractLowerDloadStage o1ContractConcretize o1ContractDft o1ContractMakeSsa
  o1DftStageSsa dftContractGas
  concretizeStageShape concretizeStageSim concretizeStageStatic
  concretizeStageFramePtr concretizeStageTaint ptrStaticDiscipline
  rawReachableFmp
  ctxLookupAgree ctxLookupAgreeHelpers ptrDiscipline unitMemInv unitTransformDefs unitShapeDefs
  venomPipelineDriver venomPipelineRunner venomFnScheduleRunner
  venomPassSchedule venomPassDispatcher venomInst venomExecSemantics
  venomState fcgDefs fcgPruning fcgPostorder fcgAnalysisProps
  contextCodegenRel venomMemDefs list rich_list

(* ===== The three remaining walk runs ===== *)

Theorem lower_dload_run_rq:
  o1_run_rq_contract_gas rpolicy D fmp 1
Proof
  simp[o1_run_rq_contract_gas_def, o1_fn_passes_def] >> irule o1_stage_contract_rq_lift >>
  reverse conj_tac >- (mp_tac lower_dload_run_contract >> simp[o1_run_contract_def, o1_fn_passes_def]) >>
  `EL 1 o1_fn_passes = CFP_Simple VP_LowerDload` by simp[o1_fn_passes_def] >>
  simp[o1_inv_def] >> rpt strip_tac >>
  fs[o1_run_state_ok_def] >> metis_tac[lower_dload_stage_abort_rq_static]
QED

Theorem concretize_run_rq:
  o1_run_rq_contract_gas rpolicy D fmp 2
Proof
  `EL 2 o1_fn_passes = CFP_Simple VP_ConcretizeMemLoc` by EVAL_TAC >>
  simp[o1_run_rq_contract_gas_def, o1_stage_rq_contract_gas_def, fmp_variant_def,
       fmp_variant_room_def, pass_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  qexists_tac `vs'` >> simp[gas_variant_refl] >> strip_tac >>
  gvs[o1_inv_def, o1_src_inv_def, o1_static_inv_def] >>
  `ctx_inst_ids_distinct C` by fs[o1_ctx_shape_def] >>
  `EVERY all_reachable C.ctx_functions /\
   EVERY fn_defs_reach_uses C.ctx_functions` by
    fs[listTheory.EVERY_MEM, make_ssa_input_ok_def] >>
  drule_all concretize_stage_shape >> strip_tac >>
  `EVERY ssa_form C'.ctx_functions` by
    (irule concretize_stage_ssa_form >> metis_tac[]) >>
  `ctx_has_dalloca C ==>
   ?eom. max_live_eom C' = SOME eom /\ eom <= w2n vs'.vs_initial_fmp` by
    metis_tac[] >>
  `ctx_sim_fuel I D C C' vs' vs'` by
    (irule concretize_stage_sim_fuel >> simp[] >> metis_tac[]) >>
  `ctx_abort_rq D C C' vs' vs'` by
    (irule concretize_stage_abort_rq >> simp[] >> metis_tac[]) >>
  `mem_inv (static_mem_ok eom) C' vs'` by
    (irule concretize_stage_static_mem >> simp[] >> metis_tac[]) >>
  `?P. EVERY (fn_static_ptr_ok P) C'.ctx_functions` by
    (qpat_assum `ptr_discipline lo C vs'`
       (strip_assume_tac o REWRITE_RULE [ptr_discipline_def]) >>
     qexists_tac `P` >> irule concretize_stage_static_ptr_ok >>
     qexistsl [`C`, `rpolicy`, `o1_walk_view rpolicy 2`] >>
     fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     irule fn_ptr_ok_static >> res_tac) >>
  `!stk PG G tn fn inst s.
     frame_reachable vs' C' stk PG G tn fn inst s ==>
     access_ok eom G fn inst s /\ taint_ok fn tn inst s` by
    (mp_tac (Q.INST [`vs` |-> `vs'`] concretize_stage_frame_ptr_ok) >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  `taint_within D C' vs'` by
    (irule concretize_stage_taint_within >> simp[] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

Theorem dft_stage_sim_rq_gas:
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' /\ o1_pre 7 C C' /\
  dead_wf D /\ o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim_fuel I D C C' vs vs' /\
       ctx_abort_rq D C C' vs vs' /\
       (o1_lowered_inv C vs ==> o1_lowered_inv C' vs')
Proof
  strip_tac >> drule_all dft_stage_fn_rel >> strip_tac >>
  drule ctx_pass_stage_dft >> strip_tac >>
  irule dft_ctx_sim_rq_gas >> simp[] >>
  irule dft_ctx_labels_bound >> gvs[o1_run_state_ok_def]
QED

Theorem dft_run_rq:
  o1_run_rq_contract_gas rpolicy D fmp 7
Proof
  simp[o1_run_rq_contract_gas_def, o1_fn_passes_def,
       o1_stage_rq_contract_gas_def, fmp_variant_def, pass_fuel_def,
       o1_inv_def, o1_ssa_inv_def] >>
  rpt strip_tac >>
  Cases_on `EVERY wf_ssa C.ctx_functions`
  >- (drule_all dft_stage_sim_rq_gas >> strip_tac >>
      qexists_tac `vs` >> rw[] >> irule dft_stage_wf_ssa >> metis_tac[]) >>
  qexists_tac `vs'` >> simp[gas_variant_refl]
QED

Theorem o1_run_rq_contracts:
  k < LENGTH o1_fn_passes ==> o1_run_rq_contract_gas rp D fmp k
Proof
  simp[o1_fn_passes_def] >> strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/
   k = 8` by decide_tac >>
  gvs[make_ssa_run_rq_1, lower_dload_run_rq, concretize_run_rq,
      fmp_lowering_run_rq, make_ssa_run_rq_2, simplify_cfg_run_rq,
      sue_run_rq, dft_run_rq, cfg_norm_run_rq]
QED

(* ===== Composition ===== *)

Theorem guarded_ctx_sim_rq_trans:
  dead_wf D /\
  (!b. o1_run_state_ok b ==>
    ?a. gas_variant a b /\
      (Inv A a ==> ctx_sim_fuel f D A B a b /\ ctx_abort_rq D A B a b /\ Mid B b)) /\
  (!c. o1_run_state_ok c ==>
    ?b. gas_variant b c /\
      (Mid B b ==> ctx_sim_fuel g D B C b c /\ ctx_abort_rq D B C b c /\ Post C c)) /\
  o1_run_state_ok c ==>
  ?a. gas_variant a c /\
    (Inv A a ==> ctx_sim_fuel (g o f) D A C a c /\ ctx_abort_rq D A C a c /\ Post C c)
Proof
  strip_tac >>
  qpat_x_assum `!c. _` (qspec_then `c` mp_tac) >>
  simp[] >> strip_tac >>
  `o1_run_state_ok b` by metis_tac[gas_variant_run_state_ok] >>
  qpat_x_assum `!b. _` (qspec_then `b` mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `a` >> conj_tac
  >- metis_tac[gas_variant_trans] >>
  strip_tac >> metis_tac[ctx_sim_fuel_trans, ctx_abort_rq_trans]
QED

Theorem o1_walk_stages_rq:
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D /\ o1_run_state_ok vs_out ==>
  ?vs_in. raw_variant fmp vs_in vs_out /\
    (o1_inv D 0 (stage 0) vs_in /\
     fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) vs_out ==>
     ctx_sim_fuel (cfg_norm_fuel (stage (LENGTH o1_fn_passes))) D (stage 0) (stage (LENGTH o1_fn_passes)) vs_in vs_out /\
     ctx_abort_rq D (stage 0) (stage (LENGTH o1_fn_passes)) vs_in vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out)
Proof
  strip_tac >>
  drule o1_walk_stages_max_live_eom >> strip_tac >>
  `!k vs. k < LENGTH o1_fn_passes /\ o1_run_state_ok vs ==>
    ?vi. fmp_variant (if k = 3 then SOME fmp else NONE) vi vs /\
      (o1_inv D k (stage k) vi /\
       fmp_variant_room (if k = 3 then SOME fmp else NONE)
         (stage (SUC k)) vs ==>
       ctx_sim_fuel (pass_fuel (EL k o1_fn_passes) (stage (SUC k))) D (stage k) (stage (SUC k)) vi vs /\ ctx_abort_rq D (stage k) (stage (SUC k)) vi vs /\
       o1_inv D (SUC k) (stage (SUC k)) vs)` by
    (rpt gen_tac >> strip_tac >>
     `o1_run_rq_contract_gas rpolicy D fmp k` by simp[o1_run_rq_contracts] >>
     fs[o1_run_rq_contract_gas_def, o1_stage_rq_contract_gas_def, o1_pre_def] >>
     `k <= LENGTH o1_fn_passes /\ SUC k <= LENGTH o1_fn_passes` by simp[] >>
     `EVERY (o1_fn_row k) (stage k).ctx_functions /\
      EVERY (o1_fn_row (SUC k)) (stage (SUC k)).ctx_functions` by simp[] >>
     first_x_assum (qspecl_then [`stage k`, `stage (SUC k)`, `vs`] mp_tac) >>
     simp[]) >>
  `!m Inv n. dead_wf D /\ m < n /\ n <= LENGTH o1_fn_passes /\
  (!k vo. m <= k /\ k < n /\ o1_run_state_ok vo ==>
     ?vi. gas_variant vi vo /\
       (Inv k (stage k) vi ==>
        ctx_sim_fuel (pass_fuel (EL k o1_fn_passes) (stage (SUC k))) D
          (stage k) (stage (SUC k)) vi vo /\
        ctx_abort_rq D (stage k) (stage (SUC k)) vi vo /\
        Inv (SUC k) (stage (SUC k)) vo)) ==>
  !vo. o1_run_state_ok vo ==>
    ?vi. gas_variant vi vo /\
      (Inv m (stage m) vi ==>
       ctx_sim_fuel (pass_fuel (EL (PRE n) o1_fn_passes) (stage n)) D
         (stage m) (stage n) vi vo /\
       ctx_abort_rq D (stage m) (stage n) vi vo /\ Inv n (stage n) vo)` by
    (map_every qx_gen_tac [`m`, `Inv`] >> Induct >> rpt strip_tac >- fs[] >>
  Cases_on `m = n` >- (gvs[] >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `dead_wf D /\ m < n /\ _ ==> _` mp_tac >> impl_tac
  >- (simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  strip_tac >>
  `pass_fuel (EL (PRE n) o1_fn_passes) (stage n) = I` by
    (`0 < n /\ n < 9` by fs[o1_fn_passes_def] >>
     `n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/
      n = 7 \/ n = 8` by decide_tac >>
     gvs[o1_fn_passes_def, pass_fuel_def]) >>
  REWRITE_TAC [prim_recTheory.PRE] >>
  `pass_fuel (EL n o1_fn_passes) (stage (SUC n)) =
   pass_fuel (EL n o1_fn_passes) (stage (SUC n)) o I` by
    simp[combinTheory.I_o_ID] >>
  pop_assum SUBST1_TAC >>
  irule guarded_ctx_sim_rq_trans >> simp[] >>
  qexistsl_tac [`stage n`, `Inv n`] >> simp[] >>
  rpt strip_tac >> fs[] >> first_x_assum irule >> simp[]) >>
  (* MakeSSA's and LowerDload's runs (k < 2) keep their input state: their
     plain contracts need no headroom. *)
  `!k vs. k < 2 /\ o1_run_state_ok vs /\ o1_inv D k (stage k) vs ==>
     ctx_sim_fuel (pass_fuel (EL k o1_fn_passes) (stage (SUC k))) D (stage k) (stage (SUC k)) vs vs /\ ctx_abort_rq D (stage k) (stage (SUC k)) vs vs /\
     o1_inv D (SUC k) (stage (SUC k)) vs` by
    (rpt gen_tac >> strip_tac >>
     `o1_run_contract rpolicy D k` by
       (`k = 0 \/ k = 1` by decide_tac >> pop_assum strip_assume_tac >>
        gvs[o1_contract_make_ssa_1, o1_contract_lower_dload]) >>
     fs[o1_run_contract_def, o1_stage_contract_def, o1_pre_def] >>
     `k < LENGTH o1_fn_passes /\ SUC k <= LENGTH o1_fn_passes` by
       simp[o1_fn_passes_def] >>
     `EVERY (o1_fn_row k) (stage k).ctx_functions /\
      EVERY (o1_fn_row (SUC k)) (stage (SUC k)).ctx_functions` by simp[] >>
     `ctx_sim_fuel (pass_fuel (EL k o1_fn_passes) (stage (SUC k))) D
        (stage k) (stage (SUC k)) vs vs /\
      o1_inv D (SUC k) (stage (SUC k)) vs` by
       (first_x_assum (qspecl_then [`stage k`, `stage (SUC k)`, `vs`] mp_tac) >>
        simp[]) >>
     simp[] >> `k = 0 \/ k = 1` by decide_tac >>
     pop_assum strip_assume_tac >> gvs[o1_inv_def, o1_fn_passes_def]
     >- (`ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA)
            (o1_walk_view rpolicy 0) (stage 0) (stage 1)` by
           (qpat_x_assum `!k'. k' < 9 ==> ctx_pass_stage _ _ _ _ _`
              (qspec_then `0` mp_tac) >> simp[]) >>
         irule bisim_stage_abort_rq >> simp[] >> conj_tac
         >- (irule (Q.INST [`rpolicy` |-> `rpolicy`,
                            `view` |-> `o1_walk_view rpolicy 0`]
                     make_ssa_stage_bisim) >>
             simp[] >> fs[o1_walk_src_inv_def] >>
             qexists_tac `rpolicy` >> simp[]) >>
         qexistsl_tac [`CFP_Simple VP_MakeSSA`, `rpolicy`,
                       `o1_walk_view rpolicy 0`] >> simp[]) >>
     irule lower_dload_stage_abort_rq >> simp[] >>
     conj_tac
     >- (qpat_x_assum `callee_first _ (stage 1).ctx_functions` mp_tac >>
         rpt (pop_assum kall_tac) >> metis_tac[]) >>
     qexistsl_tac [`rpolicy`, `o1_walk_view rpolicy 1`] >>
     qpat_x_assum `!k'. k' < 9 ==> ctx_pass_stage _ _ _ _ _`
       (qspec_then `1` mp_tac) >> simp[]) >>
  `LENGTH o1_fn_passes = 9` by simp[o1_fn_passes_def] >>
  gvs[] >>
  `max_live_eom (stage 3) = max_live_eom (stage 9) /\
   max_live_eom (stage 4) = max_live_eom (stage 9) /\
   max_live_eom (stage 5) = max_live_eom (stage 9) /\
   max_live_eom (stage 6) = max_live_eom (stage 9) /\
   max_live_eom (stage 7) = max_live_eom (stage 9) /\
   max_live_eom (stage 8) = max_live_eom (stage 9)` by
    (qpat_x_assum `!j. j + 3 <= _ ==> _`
       (fn th => map_every (fn n => mp_tac (Q.SPEC n th))
                   [`0`, `1`, `2`, `3`, `4`, `5`, `6`]) >>
     simp[]) >>
  (* Every run but FmpLowering's, with the headroom of the last stage's
     layout end carried along the GAS variants. *)
  `!k vs. k < 9 /\ k <> 3 /\ o1_run_state_ok vs ==>
    ?vi. gas_variant vi vs /\
      (o1_inv D k (stage k) vi /\ (!eom. max_live_eom (stage 9) = SOME eom ==> eom <= w2n vi.vs_initial_fmp) ==>
       ctx_sim_fuel (pass_fuel (EL k o1_fn_passes) (stage (SUC k))) D (stage k) (stage (SUC k)) vi vs /\ ctx_abort_rq D (stage k) (stage (SUC k)) vi vs /\
       o1_inv D (SUC k) (stage (SUC k)) vs /\ (!eom. max_live_eom (stage 9) = SOME eom ==> eom <= w2n vs.vs_initial_fmp))` by
    (rpt strip_tac >> Cases_on `k < 2`
     >- (qexists_tac `vs` >> simp[gas_variant_refl] >> strip_tac >>
         qpat_x_assum `!k vs. k < 2 /\ _ ==> _`
           (qspecl_then [`k`, `vs`] mp_tac) >> simp[]) >>
     qpat_x_assum `!k vs. k < 9 /\ o1_run_state_ok vs ==> _`
       (qspecl_then [`k`, `vs`] mp_tac) >>
     simp[fmp_variant_def] >> strip_tac >>
     qexists_tac `vi` >> simp[] >> strip_tac >>
     `vs.vs_initial_fmp = vi.vs_initial_fmp` by
       metis_tac[gas_variant_initial_fmp] >>
     `max_live_eom (stage (SUC k)) = max_live_eom (stage 9)` by
       (`k = 2 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8` by decide_tac >>
        pop_assum strip_assume_tac >> gvs[]) >>
     `fmp_variant_room NONE (stage (SUC k)) vs` by gvs[fmp_variant_room_def] >>
     `ctx_sim_fuel (pass_fuel (EL k o1_fn_passes) (stage (SUC k))) D (stage k) (stage (SUC k)) vi vs /\ ctx_abort_rq D (stage k) (stage (SUC k)) vi vs /\
      o1_inv D (SUC k) (stage (SUC k)) vs` by (first_x_assum irule >> simp[]) >>
     simp[]) >>
  `!vo. o1_run_state_ok vo ==>
     ?vi. gas_variant vi vo /\
       (o1_inv D 0 (stage 0) vi /\ (!eom. max_live_eom (stage 9) = SOME eom ==> eom <= w2n vi.vs_initial_fmp) ==>
        ctx_sim_fuel I D (stage 0) (stage 3) vi vo /\ ctx_abort_rq D (stage 0) (stage 3) vi vo /\ o1_inv D 3 (stage 3) vo /\ (!eom. max_live_eom (stage 9) = SOME eom ==> eom <= w2n vo.vs_initial_fmp))` by
    (rpt strip_tac >>
     qpat_x_assum `!m Inv n. _`
       (qspecl_then [`0`, `\k C v. o1_inv D k C v /\
         (!eom. max_live_eom (stage 9) = SOME eom ==> eom <= w2n v.vs_initial_fmp)`, `3`] mp_tac) >>
     simp[o1_fn_passes_def, pass_fuel_def] >>
     impl_tac >- (simp[] >> rpt strip_tac >>

     qpat_x_assum `!k vs. k < 9 /\ k <> 3 /\ _ ==> _`
       (qspecl_then [`k`, `vo'`] mp_tac) >>
     impl_tac >- fs[] >>
     simp[pass_fuel_def, o1_fn_passes_def]) >> simp[]) >>
  `!vo. o1_run_state_ok vo ==>
     ?vi. gas_variant vi vo /\
       (o1_inv D 4 (stage 4) vi /\ (!eom. max_live_eom (stage 9) = SOME eom ==> eom <= w2n vi.vs_initial_fmp) ==>
        ctx_sim_fuel (cfg_norm_fuel (stage 9)) D (stage 4) (stage 9) vi vo /\ ctx_abort_rq D (stage 4) (stage 9) vi vo /\ o1_inv D 9 (stage 9) vo /\ (!eom. max_live_eom (stage 9) = SOME eom ==> eom <= w2n vo.vs_initial_fmp))` by
    (rpt strip_tac >>
     qpat_x_assum `!m Inv n. _`
       (qspecl_then [`4`, `\k C v. o1_inv D k C v /\
         (!eom. max_live_eom (stage 9) = SOME eom ==> eom <= w2n v.vs_initial_fmp)`, `9`] mp_tac) >>
     simp[o1_fn_passes_def, pass_fuel_def] >>
     impl_tac >- (simp[] >> rpt strip_tac >>

     qpat_x_assum `!k vs. k < 9 /\ k <> 3 /\ _ ==> _`
       (qspecl_then [`k`, `vo'`] mp_tac) >>
     impl_tac >- fs[] >>
     simp[pass_fuel_def, o1_fn_passes_def]) >> simp[]) >>
  qpat_x_assum `!vo. o1_run_state_ok vo ==> ?vi. gas_variant vi vo /\ (o1_inv D 4 _ _ /\ _ ==> _)`
    (qspec_then `vs_out` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `v4` strip_assume_tac) >>
  `o1_run_state_ok v4` by metis_tac[gas_variant_run_state_ok] >>
  qpat_x_assum `!k vs. k < 9 /\ o1_run_state_ok vs ==> _`
    (qspecl_then [`3`, `v4`] mp_tac) >>
  simp[fmp_variant_def] >>
  disch_then (qx_choose_then `v3` strip_assume_tac) >>
  `o1_run_state_ok v3` by metis_tac[raw_variant_run_state_ok] >>
  qpat_x_assum `!vo. o1_run_state_ok vo ==> ?vi. gas_variant vi vo /\ (o1_inv D 0 _ _ /\ _ ==> _)`
    (qspec_then `v3` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `vi` strip_assume_tac) >>
  qexists_tac `vi` >> conj_tac
  >- metis_tac[gas_raw_variant_trans, raw_gas_variant_trans] >>
  strip_tac >>
  `v4.vs_initial_fmp = vs_out.vs_initial_fmp /\
   vi.vs_initial_fmp = v3.vs_initial_fmp` by
    metis_tac[gas_variant_initial_fmp] >>
  `v3.vs_initial_fmp = fmp` by
    (fs[raw_variant_def] >> imp_res_tac gas_variant_initial_fmp >> fs[]) >>
  `!eom. max_live_eom (stage 9) = SOME eom ==>
     eom <= w2n vs_out.vs_initial_fmp /\ w2n vs_out.vs_initial_fmp <= w2n fmp` by
    fs[fmp_variant_room_def] >>
  `(!eom. max_live_eom (stage 9) = SOME eom ==> eom <= w2n vi.vs_initial_fmp)` by (rpt strip_tac >> first_x_assum drule >> gvs[]) >>
  `(!eom. max_live_eom (stage 9) = SOME eom ==> eom <= w2n v4.vs_initial_fmp)` by (rpt strip_tac >> first_x_assum drule >> gvs[]) >>
  `fmp_variant_room (SOME fmp) (stage 4) v4` by
    (gvs[fmp_variant_room_def] >> metis_tac[]) >>
  gvs[pass_fuel_def] >>
  `ctx_sim_fuel I D (stage 3) (stage 4) v3 v4` by fs[o1_fn_passes_def] >>
  `ctx_sim_fuel (I o I) D (stage 0) (stage 4) vi v4` by
    (irule ctx_sim_fuel_trans >> metis_tac[]) >>
  `ctx_sim_fuel (cfg_norm_fuel (stage 9) o (I o I)) D (stage 0) (stage 9)
     vi vs_out` by
    (irule ctx_sim_fuel_trans >> metis_tac[]) >>
  `ctx_abort_rq D (stage 0) (stage 4) vi v4` by
    (irule ctx_abort_rq_trans >> metis_tac[]) >>
  `ctx_abort_rq D (stage 0) (stage 9) vi vs_out` by
    (irule ctx_abort_rq_trans >> metis_tac[]) >>
  fs[combinTheory.I_o_ID]
QED

(* The two pre-walk runs: SimplifyCFG is a bisimulation, DretDesugar the
   identity. *)
Theorem o1_pre_walk_rq:
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit s =
    SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s ==>
  !D vs. o1_run_state_ok vs /\ o1_pre_walk_inv D unit.cu_context vs ==>
         ctx_abort_rq D unit.cu_context unit'.cu_context vs vs
Proof
  strip_tac >> drule o1_pre_walk_runs >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_SimplifyCFG`,
                  `u` |-> `unit`, `u'` |-> `mid`, `s'` |-> `t`]
            mapped_pass_stage) >>
  impl_tac >- simp[o1_contract_simplify_cfg_pre_walk] >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_DretDesugar`,
                  `u` |-> `mid`, `s` |-> `t`, `u'` |-> `unit'`]
            mapped_pass_stage) >>
  impl_tac
  >- simp[o1_contract_dret_desugar_pre_walk, unit_labels_wf_namespace] >>
  strip_tac >>
  `unit'.cu_context = mid.cu_context` by metis_tac[dret_desugar_stage_identity] >>
  rpt strip_tac >> simp[] >>
  irule simplify_cfg_pre_walk_abort_rq >> metis_tac[]
QED

Theorem o1_walk_rq:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  reachable_fcg_acyclic unit.cu_context fcg /\
  ALL_DISTINCT (unit_label_namespace unit) /\
  run_callee_first rpolicy o1_fn_passes (fcg_postorder fcg entry)
    (prune_unit_fcg_unreachable unit fcg) s = SOME (unit', s') /\
  ir_supply_inst_ok s /\ EVERY (o1_fn_row 0) unit.cu_context.ctx_functions /\
  dead_wf D /\ o1_run_state_ok vs_out ==>
    ?vs_in. raw_variant fmp vs_in vs_out /\
      (o1_walk_src_inv D (prune_unit_fcg_unreachable unit fcg).cu_context vs_in /\
       fmp_variant_room (SOME fmp) unit'.cu_context vs_out ==>
       ctx_sim_fuel (cfg_norm_fuel unit'.cu_context) D (prune_unit_fcg_unreachable unit fcg).cu_context
               unit'.cu_context vs_in vs_out /\
       ctx_abort_rq D (prune_unit_fcg_unreachable unit fcg).cu_context
               unit'.cu_context vs_in vs_out /\
       o1_lowered_inv unit'.cu_context vs_out)
Proof
  strip_tac >> drule_all o1_ctx_shape_prune >> strip_tac >>
  drule_all o1_walk_callee_first >> strip_tac >>
  fs[run_callee_first_def] >>
  drule_at (Pos (el 3)) (Q.INST [`R` |-> `o1_fn_row`] o1_schedule_stages) >>
  impl_tac
  >- fs[o1_fn_passes_steps, o1_step_contracts_from_rows, o1_prune_every] >>
  strip_tac >>
  `?names. callee_first names (stage 0).ctx_functions` by
    (qexists_tac `fcg_postorder fcg entry` >> gvs[]) >>
  `(!C vs. o1_inv D 0 C vs <=>
           o1_walk_src_inv D C vs /\ ?names. callee_first names C.ctx_functions) /\
   o1_inv D (LENGTH o1_fn_passes) = o1_lowered_inv` by
    simp[o1_inv_def, o1_fn_passes_def] >>
  `?vi. raw_variant fmp vi vs_out /\
    (o1_inv D 0 (stage 0) vi /\
     fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) vs_out ==>
     ctx_sim_fuel (cfg_norm_fuel (stage (LENGTH o1_fn_passes))) D (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
     ctx_abort_rq D (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out)` by
    (irule o1_walk_stages_rq >> fs[] >> qexists_tac `rpolicy` >>
     rpt strip_tac >> first_x_assum drule >> simp[o1_walk_view_def]) >>
  gvs[] >> metis_tac[]
QED

(* ===== The pipeline ===== *)

Theorem o1_pipeline_rq_facts:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy o1_pipeline_spec unit =
    SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit ==>
  !D fmp vs_out. dead_wf D /\ o1_run_state_ok vs_out ==>
    ?vs_in. raw_variant fmp vs_in vs_out /\
      (o1_pre_walk_inv D unit.cu_context vs_in /\
       fmp_variant_room (SOME fmp) out.po_unit.cu_context vs_out ==>
       ctx_sim_fuel (cfg_norm_fuel out.po_unit.cu_context) D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       ctx_abort_rq D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       o1_lowered_inv out.po_unit.cu_context vs_out)
Proof
  strip_tac >> drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)`
    by simp[irSupplyTheory.init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  `!D vs. o1_run_state_ok vs /\ o1_pre_walk_inv D unit.cu_context vs ==>
          ctx_abort_rq D unit.cu_context pre.cu_context vs vs` by
    (rpt strip_tac >> irule o1_pre_walk_rq >> metis_tac[]) >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 6)) o1_walk_rq >>
  disch_then (qspecl_then [`vs_out`, `fmp`, `D`] mp_tac) >> impl_tac
  >- (gvs[] >> metis_tac[unit_labels_wf_namespace]) >>
  disch_then (qx_choose_then `vs` strip_assume_tac) >>
  qexists_tac `vs` >> simp[] >> strip_tac >>
  `o1_run_state_ok vs` by metis_tac[raw_variant_run_state_ok] >>
  `ctx_sim_fuel I D unit.cu_context pre.cu_context vs vs /\
   ctx_abort_rq D unit.cu_context pre.cu_context vs vs /\
   o1_walk_src_inv D pre.cu_context vs` by metis_tac[] >>
  `(!fuel vs. run_context fuel pre.cu_context vs =
      run_context fuel (prune_unit_fcg_unreachable pre
        (fcg_analyze pre.cu_context)).cu_context vs) /\
   !vs. mem_inv raw_mem_ok pre.cu_context vs ==>
     mem_inv raw_mem_ok (prune_unit_fcg_unreachable pre
       (fcg_analyze pre.cu_context)).cu_context vs` by
    (irule o1_prune_sim >> metis_tac[raw_mem_ok_ctx_free]) >>
  `o1_walk_src_inv D (prune_unit_fcg_unreachable pre
                        (fcg_analyze pre.cu_context)).cu_context vs` by
    (qpat_x_assum `o1_walk_src_inv D pre.cu_context vs` mp_tac >>
     rewrite_tac[o1_walk_src_inv_def] >> strip_tac >> conj_tac
     >- (irule o1_src_inv_prune >> metis_tac[])
     >> conj_tac >> irule o1_prune_every >> first_assum ACCEPT_TAC) >>
  `ctx_sim_fuel I D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs` by
    (irule ctx_sim_run_context_eq >> qexists_tac `pre.cu_context` >> simp[]) >>
  `ctx_abort_rq D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs` by
    (irule ctx_abort_rq_run_context_eq >> qexists_tac `pre.cu_context` >> simp[]) >>
  `ctx_sim_fuel (cfg_norm_fuel out.po_unit.cu_context o I) D
     unit.cu_context out.po_unit.cu_context vs vs_out` by
    (irule ctx_sim_fuel_trans >> metis_tac[]) >>
  simp[combinTheory.I_o_ID] >> metis_tac[ctx_abort_rq_trans]
QED

(* S4's request companion: run_venom_pipeline_correct's premises and guard,
   with the abort companion added under the same chosen input state. *)
Theorem run_venom_pipeline_correct_requests:
  !D lo rpolicy unit out vs_out.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\ o1_run_state_ok vs_out /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context /\ dead_wf D /\
    (!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
           eom <= w2n vs_out.vs_initial_fmp)
    ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (raw_unit_memory_ok unit.cu_context vs_in /\
       ptr_discipline lo unit.cu_context vs_in /\
       taint_within D unit.cu_context vs_in /\
       mem_inv dload_offset_ok unit.cu_context vs_in /\
       mem_inv dload_headroom_ok unit.cu_context vs_in ==>
       ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       ctx_abort_rq D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       o1_lowered_inv out.po_unit.cu_context vs_out)
Proof
  rpt strip_tac >>
  `fmp_free_ctx unit.cu_context` by (irule source_fmp_free >> fs[]) >>
  `EVERY pre_fmp_ops unit.cu_context.ctx_functions /\
   ~ctx_has_dalloca unit.cu_context` by
    (simp[EVERY_MEM] >>
     metis_tac[source_pre_fmp_ops, o1_source_unit_ok_no_dalloca]) >>
  (* At an input state whose free-memory pointer is its initial one, no
     reachable state moves it: the raw phase's FMP facts hold. *)
  `!vi. vi.vs_fmp = vi.vs_initial_fmp /\
        raw_unit_memory_ok unit.cu_context vi /\
        ptr_discipline lo unit.cu_context vi /\
        taint_within D unit.cu_context vi /\
        mem_inv dload_offset_ok unit.cu_context vi /\
        mem_inv dload_headroom_ok unit.cu_context vi ==>
        o1_pre_walk_inv D unit.cu_context vi` by
    (rpt strip_tac >>
     `mem_inv raw_mem_ok unit.cu_context vi` by
       (simp[raw_unit_memory_ok_mem_inv] >> rpt gen_tac >> strip_tac >>
        drule raw_reachable_fmp_fixed >> simp[] >> strip_tac >>
        drule raw_reachable_initial_fmp >> strip_tac >>
        `inst.inst_opcode <> DALLOCA` by
          (`EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)` by
             (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >>
              metis_tac[]) >>
           imp_res_tac EVERY_active_inst >> gvs[]) >>
        simp[dalloca_no_wrap_def]) >>
     `o1_src_inv D unit.cu_context vi` by
       (fs[o1_src_inv_def] >> metis_tac[]) >>
     irule o1_source_pre_walk_inv >> simp[]) >>
  fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  mp_tac (Q.INST [`mem_ok` |-> `K T`, `calling_ok` |-> `K T`,
                  `post_ok` |-> `K T`] o1_pipeline_rq_facts) >>
  impl_tac >- fs[] >>
  disch_then (qspecl_then [`D`, `vs_out.vs_initial_fmp`, `vs_out`] mp_tac) >>
  simp[fmp_variant_room_def] >> strip_tac >>
  qexists_tac `vs_in` >>
  `gas_variant vs_in vs_out` by
    metis_tac[raw_variant_gas_variant, o1_run_state_ok_def] >>
  simp[] >> strip_tac >>
  `vs_in.vs_fmp = vs_in.vs_initial_fmp` by
    gvs[raw_variant_def, gas_variant_def, venom_state_component_equality] >>
  metis_tac[ctx_sim_fuel_imp_ctx_sim]
QED

Theorem lower_dload_run_abort_same[local]:
  ctx_pass_stage rpolicy (EL 1 o1_fn_passes) (o1_walk_view rpolicy 1) C C' /\
  o1_pre 1 C C' /\ dead_wf D /\ o1_ctx_shape C /\
  o1_run_state_ok vs /\ o1_inv D 1 C vs ==> ctx_abort_rq D C C' vs vs
Proof
  simp[o1_fn_passes_def, o1_inv_def] >> rpt strip_tac >>
  metis_tac[lower_dload_stage_abort_rq]
QED

Theorem concretize_run_abort_same[local]:
  ctx_pass_stage rpolicy (EL 2 o1_fn_passes) (o1_walk_view rpolicy 2) C C' /\
  o1_pre 2 C C' /\ dead_wf D /\ o1_ctx_shape C /\
  o1_run_state_ok vs /\ o1_inv D 2 C vs ==> ctx_abort_rq D C C' vs vs
Proof
  simp[o1_fn_passes_def] >> rpt strip_tac >>
  gvs[o1_inv_def, o1_src_inv_def] >>
  `ctx_inst_ids_distinct C` by fs[o1_ctx_shape_def] >>
  `EVERY all_reachable C.ctx_functions /\
   EVERY fn_defs_reach_uses C.ctx_functions` by
    fs[EVERY_MEM, make_ssa_input_ok_def] >>
  irule concretize_stage_abort_rq >> simp[] >> metis_tac[]
QED

Theorem ctx_abort_rq_empty[local]:
  ctx_abort_rq
    <| d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {} |> C C' vi vo ==>
  ctx_abort_rq D C C' vi vo
Proof
  simp[ctx_abort_rq_def, request_prefix_rel_EL] >>
  metis_tac[request_agree_except_empty]
QED

Theorem o1_run_abort_same[local]:
  k < LENGTH o1_fn_passes /\ k <> 7 /\
  ctx_pass_stage rp (EL k o1_fn_passes) (o1_walk_view rp k) C C' /\
  o1_pre k C C' /\ dead_wf D /\ o1_ctx_shape C /\
  o1_run_state_ok vs /\ o1_inv D k C vs ==> ctx_abort_rq D C C' vs vs
Proof
  strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 8`
    by fs[o1_fn_passes_def] >>
  gvs[] >> metis_tac (map (SRULE [])
    [make_ssa_run_abort_same_1, lower_dload_run_abort_same,
     concretize_run_abort_same, fmp_lowering_run_abort_same,
     make_ssa_run_abort_same_2, simplify_cfg_run_abort_same,
     sue_run_abort_same, cfg_norm_run_abort_same])
QED

Theorem o1_run_rq_contracts_all_dead[local]:
  k < LENGTH o1_fn_passes /\
  ctx_pass_stage rp (EL k o1_fn_passes) (o1_walk_view rp k) C C' /\
  o1_ctx_shape C /\ o1_pre k C C' /\ o1_run_state_ok vo ==>
  ?vi. gas_variant vi vo /\
    !D. dead_wf D ==> (o1_inv D k C vi ==>
      ctx_sim D C C' vi vo /\ ctx_abort_rq D C C' vi vo /\
      o1_inv D (SUC k) C' vo)
Proof
  strip_tac >> Cases_on `k = 7`
  >- (gvs[o1_inv_def] >> Cases_on `EVERY wf_ssa C.ctx_functions`
      >- (mp_tac (Q.INST
            [`rpolicy` |-> `rp`, `vs'` |-> `vo`, `view` |-> `o1_walk_view rp 7`,
             `D` |-> `<| d_stor := K (K {}); d_trans := K (K {});
                         d_imm := K {}; d_ret := K {} |>`]
            dft_stage_sim_rq_gas) >>
          impl_tac >- gvs[o1_fn_passes_def, dead_wf_def] >>
          strip_tac >> qexists_tac `vs` >>
          simp[] >> rpt gen_tac >> strip_tac >> strip_tac >>
          conj_tac >- (irule ctx_sim_empty >> first_assum ACCEPT_TAC) >>
          conj_tac >- (irule ctx_abort_rq_empty >> first_assum ACCEPT_TAC) >>
          simp[o1_ssa_inv_def] >> conj_tac
          >- fs[o1_ssa_inv_def] >>
          irule dft_stage_wf_ssa >>
          gvs[o1_fn_passes_def] >> metis_tac[]) >>
      qexists_tac `vo` >> simp[gas_variant_refl, o1_ssa_inv_def]) >>
  qexists_tac `vo` >> simp[gas_variant_refl] >> rpt strip_tac >>
  `o1_run_contract rp D k` by metis_tac[o1_run_contracts_same] >>
  fs[o1_run_contract_def, o1_stage_contract_def] >>
  metis_tac[o1_run_abort_same, ctx_sim_fuel_imp_ctx_sim]
QED

Theorem guarded_ctx_sim_rq_trans_all_dead[local]:
  (!b. o1_run_state_ok b ==>
    ?a. gas_variant a b /\
      !D. dead_wf D ==> (Inv D A a ==>
        ctx_sim D A B a b /\ ctx_abort_rq D A B a b /\ Mid D B b)) /\
  (!c. o1_run_state_ok c ==>
    ?b. gas_variant b c /\
      !D. dead_wf D ==> (Mid D B b ==>
        ctx_sim D B C b c /\ ctx_abort_rq D B C b c /\ Post D C c)) /\
  o1_run_state_ok c ==>
  ?a. gas_variant a c /\
    !D. dead_wf D ==> (Inv D A a ==>
      ctx_sim D A C a c /\ ctx_abort_rq D A C a c /\ Post D C c)
Proof
  strip_tac >>
  qpat_x_assum `!c. _` (qspec_then `c` mp_tac) >>
  simp[] >> strip_tac >>
  `o1_run_state_ok b` by metis_tac[gas_variant_run_state_ok] >>
  qpat_x_assum `!b. _` (qspec_then `b` mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `a` >> conj_tac
  >- metis_tac[gas_variant_trans] >>
  rpt strip_tac >> metis_tac[ctx_sim_trans, ctx_abort_rq_trans]
QED

Theorem o1_walk_stages_rq_all_dead[local]:
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  o1_run_state_ok vs_out ==>
  ?vs_in. gas_variant vs_in vs_out /\
    !D. dead_wf D ==> (o1_inv D 0 (stage 0) vs_in ==>
     ctx_sim D (stage 0) (stage (LENGTH o1_fn_passes)) vs_in vs_out /\
     ctx_abort_rq D (stage 0) (stage (LENGTH o1_fn_passes)) vs_in vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out)
Proof
  strip_tac >>
  `!k vs. k < LENGTH o1_fn_passes /\ o1_run_state_ok vs ==>
    ?vi. gas_variant vi vs /\
      !D. dead_wf D ==> (o1_inv D k (stage k) vi ==>
       ctx_sim D (stage k) (stage (SUC k)) vi vs /\
       ctx_abort_rq D (stage k) (stage (SUC k)) vi vs /\
       o1_inv D (SUC k) (stage (SUC k)) vs)` by
    (rpt gen_tac >> strip_tac >> irule o1_run_rq_contracts_all_dead >>
     simp[o1_pre_def] >> qexists_tac `rpolicy` >> simp[]) >>
  `LENGTH o1_fn_passes = 9` by simp[o1_fn_passes_def] >> gvs[] >>
  `!n. n < 9 ==> !vo. o1_run_state_ok vo ==>
    ?vi. gas_variant vi vo /\
      !D. dead_wf D ==> (o1_inv D 0 (stage 0) vi ==>
       ctx_sim D (stage 0) (stage (SUC n)) vi vo /\
       ctx_abort_rq D (stage 0) (stage (SUC n)) vi vo /\
       o1_inv D (SUC n) (stage (SUC n)) vo)` by
    (Induct
     >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
     rpt strip_tac >>
     ho_match_mp_tac (Q.INST
       [`B` |-> `stage (SUC n)`, `Mid` |-> `\D. o1_inv D (SUC n)`]
       guarded_ctx_sim_rq_trans_all_dead) >> simp[]) >>
  first_x_assum (qspec_then `8` mp_tac) >> simp[]
QED

Theorem o1_walk_rq_all_dead[local]:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  reachable_fcg_acyclic unit.cu_context fcg /\
  ALL_DISTINCT (unit_label_namespace unit) /\
  run_callee_first rpolicy o1_fn_passes (fcg_postorder fcg entry)
    (prune_unit_fcg_unreachable unit fcg) s = SOME (unit', s') /\
  ir_supply_inst_ok s /\ EVERY (o1_fn_row 0) unit.cu_context.ctx_functions /\
  o1_run_state_ok vs_out ==>
    ?vs_in. gas_variant vs_in vs_out /\
      !D. dead_wf D ==> (o1_walk_src_inv D (prune_unit_fcg_unreachable unit fcg).cu_context vs_in ==>
       ctx_sim D (prune_unit_fcg_unreachable unit fcg).cu_context
               unit'.cu_context vs_in vs_out /\
       ctx_abort_rq D (prune_unit_fcg_unreachable unit fcg).cu_context
               unit'.cu_context vs_in vs_out /\
       o1_lowered_inv unit'.cu_context vs_out)
Proof
  strip_tac >> drule_all o1_ctx_shape_prune >> strip_tac >>
  drule_all o1_walk_callee_first >> strip_tac >>
  fs[run_callee_first_def] >>
  drule_at (Pos (el 3)) (Q.INST [`R` |-> `o1_fn_row`] o1_schedule_stages) >>
  impl_tac
  >- fs[o1_fn_passes_steps, o1_step_contracts_from_rows, o1_prune_every] >>
  strip_tac >>
  `?names. callee_first names (stage 0).ctx_functions` by
    (qexists_tac `fcg_postorder fcg entry` >> gvs[]) >>
  `(!D C vs. o1_inv D 0 C vs <=>
           o1_walk_src_inv D C vs /\ ?names. callee_first names C.ctx_functions) /\
   (!D. o1_inv D (LENGTH o1_fn_passes) = o1_lowered_inv)` by
    simp[o1_inv_def, o1_fn_passes_def] >>
  `?vi. gas_variant vi vs_out /\
    !D. dead_wf D ==> (o1_inv D 0 (stage 0) vi ==>
     ctx_sim D (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
     ctx_abort_rq D (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out)` by
    (irule o1_walk_stages_rq_all_dead >> fs[] >> qexists_tac `rpolicy` >>
     rpt strip_tac >> first_x_assum drule >> simp[o1_walk_view_def]) >>
  qexists_tac `vi` >> gvs[] >> metis_tac[]
QED

Theorem o1_pipeline_rq_facts_all_dead[local]:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy o1_pipeline_spec unit =
    SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit ==>
  !vs_out. o1_run_state_ok vs_out ==>
    ?vs_in. gas_variant vs_in vs_out /\
      !D. dead_wf D ==> (o1_pre_walk_inv D unit.cu_context vs_in ==>
       ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       ctx_abort_rq D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       o1_lowered_inv out.po_unit.cu_context vs_out)
Proof
  strip_tac >> drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)`
    by simp[irSupplyTheory.init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  `!D vs. o1_run_state_ok vs /\ o1_pre_walk_inv D unit.cu_context vs ==>
          ctx_abort_rq D unit.cu_context pre.cu_context vs vs` by
    (rpt strip_tac >> irule o1_pre_walk_rq >> metis_tac[]) >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 6)) o1_walk_rq_all_dead >>
  disch_then (qspec_then `vs_out` mp_tac) >> impl_tac
  >- (gvs[] >> metis_tac[unit_labels_wf_namespace]) >>
  disch_then (qx_choose_then `vs` strip_assume_tac) >>
  qexists_tac `vs` >> simp[] >> gen_tac >> strip_tac >> strip_tac >>
  `o1_run_state_ok vs` by metis_tac[gas_variant_run_state_ok] >>
  `ctx_sim D unit.cu_context pre.cu_context vs vs /\
   ctx_abort_rq D unit.cu_context pre.cu_context vs vs /\
   o1_walk_src_inv D pre.cu_context vs` by metis_tac[ctx_sim_fuel_imp_ctx_sim] >>
  `(!fuel vs. run_context fuel pre.cu_context vs =
      run_context fuel (prune_unit_fcg_unreachable pre
        (fcg_analyze pre.cu_context)).cu_context vs) /\
   !vs. mem_inv raw_mem_ok pre.cu_context vs ==>
     mem_inv raw_mem_ok (prune_unit_fcg_unreachable pre
       (fcg_analyze pre.cu_context)).cu_context vs` by
    (irule o1_prune_sim >> metis_tac[raw_mem_ok_ctx_free]) >>
  `o1_walk_src_inv D (prune_unit_fcg_unreachable pre
                        (fcg_analyze pre.cu_context)).cu_context vs` by
    (qpat_x_assum `o1_walk_src_inv D pre.cu_context vs` mp_tac >>
     rewrite_tac[o1_walk_src_inv_def] >> strip_tac >> conj_tac
     >- (irule o1_src_inv_prune >> metis_tac[])
     >> conj_tac >> irule o1_prune_every >> first_assum ACCEPT_TAC) >>
  `ctx_sim D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs` by
    (qpat_x_assum `ctx_sim D unit.cu_context pre.cu_context vs vs` mp_tac >>
     rewrite_tac[ctx_sim_def] >> metis_tac[]) >>
  `ctx_abort_rq D unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs` by
    (irule ctx_abort_rq_run_context_eq >> qexists_tac `pre.cu_context` >> simp[]) >>
  metis_tac[ctx_sim_trans, ctx_abort_rq_trans]
QED

Theorem run_venom_pipeline_correct_requests_all_dead:
  !lo rpolicy unit out vs_out.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\ o1_run_state_ok vs_out /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context
    ==>
    ?vs_in. gas_variant vs_in vs_out /\
      !D. dead_wf D ==>
        (raw_unit_memory_ok unit.cu_context vs_in /\
         ptr_discipline lo unit.cu_context vs_in /\
         taint_within D unit.cu_context vs_in /\
         mem_inv dload_offset_ok unit.cu_context vs_in /\
         mem_inv dload_headroom_ok unit.cu_context vs_in ==>
         ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
         ctx_abort_rq D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
         o1_lowered_inv out.po_unit.cu_context vs_out)
Proof
  rpt strip_tac >>
  `fmp_free_ctx unit.cu_context` by (irule source_fmp_free >> fs[]) >>
  `!D vi. raw_unit_memory_ok unit.cu_context vi /\
        ptr_discipline lo unit.cu_context vi /\
        taint_within D unit.cu_context vi /\
        mem_inv dload_offset_ok unit.cu_context vi /\
        mem_inv dload_headroom_ok unit.cu_context vi ==>
        o1_pre_walk_inv D unit.cu_context vi` by
    (rpt strip_tac >>
     `o1_src_inv D unit.cu_context vi` by
       (fs[o1_src_inv_def, raw_unit_memory_ok_mem_inv,
           o1_source_unit_ok_no_dalloca] >> metis_tac[]) >>
     irule o1_source_pre_walk_inv >> simp[]) >>
  fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule_all o1_pipeline_rq_facts_all_dead >> strip_tac >> metis_tac[]
QED
