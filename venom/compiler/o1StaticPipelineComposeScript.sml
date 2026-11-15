(* Static O1 uses one source oracle for simulation, requests and memory. *)
Theory o1StaticPipelineCompose
Ancestors
  o1PipelineCompose o1PassContract o1ContractMakeSsa o1ContractLowerDloadStage
  o1ContractConcretize o1ContractFmpLowering o1ContractSimplifyCfg o1ContractSue
  o1ContractCfgNorm o1LowerDloadRequests o1RequestContract dftWaveStaticGasContract
  o1DftStageSsa dftContractGas o1ComposeSupport o1PassLift unitTransformDefs
  unitShapeDefs unitMemInv ptrDiscipline lowerDloadDefs venomPassSchedule
  venomState venomInst venomExecSemantics staticAbortDefs list rich_list

Theorem ctx_sim_abort_rq_I_trans[local]:
  dead_wf D /\
  ctx_sim_fuel I D A B a b /\ ctx_abort_rq D A B a b /\
  ctx_sim_fuel I D B C b c /\ ctx_abort_rq D B C b c ==>
  ctx_sim_fuel I D A C a c /\ ctx_abort_rq D A C a c
Proof
  strip_tac >>
  `ctx_sim_fuel (I o I) D A C a c` by
    (irule ctx_sim_fuel_trans >> metis_tac[]) >>
  fs[combinTheory.I_o_ID] >> metis_tac[ctx_abort_rq_trans]
QED

Theorem o1_walk_stages_sim_static_abort:
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==>
       EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok vs_out /\
  vs_out.vs_fmp = vs_out.vs_initial_fmp /\ code_layout_valid vs_out /\
  (vs_out.vs_call_ctx.cc_static ==>
    !fn inst l. MEM fn (stage 7).ctx_functions /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode = CODECOPY /\ MEM (Label l) inst.inst_operands ==>
      l IN FDOM vs_out.vs_labels) ==>
  ?vs_in. raw_variant fmp vs_in vs_out /\
    (o1_inv D 0 (stage 0) vs_in /\
     fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) vs_out ==>
     ctx_sim_fuel (cfg_norm_fuel (stage (LENGTH o1_fn_passes))) D (stage 0) (stage (LENGTH o1_fn_passes)) vs_in vs_out /\
       ctx_abort_rq D (stage 0) (stage (LENGTH o1_fn_passes)) vs_in vs_out /\
       (o1_lowered_inv (stage (LENGTH o1_fn_passes)) vs_out \/
        ((?eom. max_live_eom (stage (LENGTH o1_fn_passes)) = SOME eom /\
           mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                     lowered_mem_fact eom ctx fn inst s) (stage (LENGTH o1_fn_passes)) vs_out) /\
         !fuel. terminates (run_context fuel (stage 0) vs_in) ==>
                ?u. run_context fuel (stage 0) vs_in = Abort ExHalt_abort u)))
Proof
  strip_tac >>
  drule o1_walk_stages_max_live_eom >> disch_tac >>
  `LENGTH o1_fn_passes = 9` by EVAL_TAC >>
  `!k. k < 9 ==> o1_pre k (stage k) (stage (SUC k))` by
    (rw[o1_pre_def] >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `!k. k < LENGTH o1_fn_passes ==> ctx_pass_stage _ _ _ _ _`
    (fn th => map_every
      (fn n => assume_tac (SIMP_RULE (srw_ss()) [o1_fn_passes_def] (Q.SPEC n th)))
      [`0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`, `8`]) >>
  `EVERY wf_ssa (stage 7).ctx_functions` by
    (qpat_x_assum `!k. k <= LENGTH o1_fn_passes ==> EVERY _ _`
       (fn th => assume_tac th >>
         mp_tac (SIMP_RULE (srw_ss()) [o1_fn_passes_def, o1_fn_row_def,
                     EVERY_MEM] (Q.SPEC `7` th))) >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape _`
    (fn th => assume_tac th >> map_every
      (fn n => assume_tac (SIMP_RULE (srw_ss()) [o1_fn_passes_def]
        (Q.SPEC n th))) [`0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`, `8`, `9`]) >>
  qpat_x_assum `!k. k < 9 ==> o1_pre _ _ _`
    (fn th => assume_tac th >> map_every
      (fn n => assume_tac (SIMP_RULE (srw_ss()) [] (Q.SPEC n th)))
      [`0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`, `8`]) >>
  `LIST_REL (\fn fn'. fn' = dft_fn fn) (stage 7).ctx_functions (stage 8).ctx_functions /\
   (stage 8).ctx_entry = (stage 7).ctx_entry /\
   LIST_REL dft_fn_rel (stage 7).ctx_functions (stage 8).ctx_functions` by
    (irule dft_stage_fn_rel >> simp[] >> metis_tac[]) >>
  `EVERY wf_ssa (stage 8).ctx_functions` by
    (irule dft_stage_wf_ssa >> simp[] >> metis_tac[]) >>
  `ctx_labels_bound (stage 7) vs_out.vs_labels` by
    (irule dft_ctx_labels_bound >> simp[]) >>
  `?v7. gas_variant v7 vs_out /\
     ctx_sim_fuel I D (stage 7) (stage 8) v7 vs_out /\
     (dead_wf D ==> ctx_abort_rq D (stage 7) (stage 8) v7 vs_out) /\
     (o1_lowered_inv (stage 7) v7 ==>
       o1_lowered_inv (stage 8) vs_out \/
       ((?eom. max_live_eom (stage 8) = SOME eom /\
          mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                    lowered_mem_fact eom ctx fn inst s) (stage 8) vs_out) /\
        !fuel. terminates (run_context fuel (stage 7) v7) ==>
           ?u. run_context fuel (stage 7) v7 = Abort ExHalt_abort u))` by
    (irule dft_ctx_sim_gas_wave_static_abort >>
     gvs[ctx_pass_stage_def] >> metis_tac[]) >>
  `o1_initial_state_ok v7 /\ v7.vs_fmp = v7.vs_initial_fmp /\
   code_layout_valid v7 /\ v7.vs_initial_fmp = vs_out.vs_initial_fmp` by
    (gvs[gas_variant_def, venom_state_component_equality,
         o1_initial_state_ok_def, code_layout_valid_def] >> metis_tac[]) >>
  `?v3. raw_variant fmp v3 v7 /\
    (o1_inv D 3 (stage 3) v3 /\ fmp_variant_room (SOME fmp) (stage 4) v7 ==>
     ctx_sim_fuel I D (stage 3) (stage 4) v3 v7 /\
     ctx_abort_rq D (stage 3) (stage 4) v3 v7 /\
     o1_inv D 4 (stage 4) v7)` by
    (irule (SIMP_RULE (srw_ss()) [] o1_static_stage_fmp_lowering) >>
     metis_tac[]) >>
  qexists_tac `v3` >> conj_tac
  >- metis_tac[raw_gas_variant_trans] >>
  strip_tac >>
  `o1_initial_state_ok v3 /\ v3.vs_fmp = v3.vs_initial_fmp /\
   code_layout_valid v3 /\ v3.vs_initial_fmp = fmp` by
    (gvs[raw_variant_def, gas_variant_def, venom_state_component_equality,
         o1_initial_state_ok_def, code_layout_valid_def] >> metis_tac[]) >>
  `max_live_eom (stage 3) = max_live_eom (stage 9) /\
   max_live_eom (stage 4) = max_live_eom (stage 9)` by
    (qpat_x_assum `!j. _ <= LENGTH o1_fn_passes ==> max_live_eom _ = _`
      (fn th => map_every
        (fn n => assume_tac (SIMP_RULE (srw_ss()) [o1_fn_passes_def]
          (Q.SPEC n th))) [`1`, `6`]) >> metis_tac[]) >>
  `fmp_variant_room NONE (stage 3) v3 /\
   fmp_variant_room (SOME fmp) (stage 4) v7` by
    (fs[fmp_variant_room_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `ctx_sim_fuel I D (stage 0) (stage 1) v3 v3 /\
   o1_inv D 1 (stage 1) v3` by
    (mp_tac (Q.SPECL [`stage 0`, `stage 1`, `v3`] o1_static_stage_make_ssa_1) >>
     simp[pass_fuel_def, o1_fn_passes_def]) >>
  `ctx_sim_fuel I D (stage 1) (stage 2) v3 v3 /\
   o1_inv D 2 (stage 2) v3` by
    (mp_tac (Q.SPECL [`stage 1`, `stage 2`, `v3`] o1_static_stage_lower_dload) >>
     simp[pass_fuel_def, o1_fn_passes_def]) >>
  `ctx_sim_fuel I D (stage 2) (stage 3) v3 v3 /\
   ctx_abort_rq D (stage 2) (stage 3) v3 v3 /\ o1_inv D 3 (stage 3) v3` by
    (mp_tac (Q.SPECL [`stage 2`, `stage 3`, `v3`]
       o1_static_stage_concretize_mem_loc_headroom) >>
     simp[pass_fuel_def, o1_fn_passes_def]) >>
  `ctx_abort_rq D (stage 0) (stage 1) v3 v3` by
    (`ctx_bisim (stage 0) (stage 1)` by
       (irule make_ssa_stage_bisim >>
        fs[o1_inv_def, o1_walk_src_inv_def] >> metis_tac[]) >>
     irule ctx_bisim_ctx_abort_rq >>
     gvs[o1_initial_state_ok_def, ctx_pass_stage_def]) >>
  `ctx_abort_rq D (stage 1) (stage 2) v3 v3` by
    (irule lower_dload_stage_abort_rq_static >>
     fs[o1_inv_def] >> metis_tac[]) >>
  `ctx_sim_fuel I D (stage 0) (stage 3) v3 v3 /\
   ctx_abort_rq D (stage 0) (stage 3) v3 v3` by
    metis_tac[ctx_sim_abort_rq_I_trans] >>
  `ctx_sim_fuel I D (stage 3) (stage 4) v3 v7 /\
   ctx_abort_rq D (stage 3) (stage 4) v3 v7 /\ o1_inv D 4 (stage 4) v7` by
    metis_tac[] >>
  `ctx_sim_fuel I D (stage 4) (stage 5) v7 v7 /\ o1_inv D 5 (stage 5) v7` by
    (mp_tac (Q.SPECL [`stage 4`, `stage 5`, `v7`] o1_static_stage_make_ssa_2) >>
     simp[pass_fuel_def, o1_fn_passes_def]) >>
  `ctx_sim_fuel I D (stage 5) (stage 6) v7 v7 /\ o1_inv D 6 (stage 6) v7` by
    (mp_tac (Q.SPECL [`stage 5`, `stage 6`, `v7`] o1_static_stage_simplify_cfg) >>
     simp[pass_fuel_def, o1_fn_passes_def]) >>
  `ctx_sim_fuel I D (stage 6) (stage 7) v7 v7 /\ o1_inv D 7 (stage 7) v7` by
    (mp_tac (Q.SPECL [`stage 6`, `stage 7`, `v7`] o1_static_stage_sue) >>
     simp[pass_fuel_def, o1_fn_passes_def]) >>
  `ctx_abort_rq D (stage 4) (stage 5) v7 v7 /\
   ctx_abort_rq D (stage 5) (stage 6) v7 v7 /\
   ctx_abort_rq D (stage 6) (stage 7) v7 v7` by
    (`ctx_bisim (stage 4) (stage 5)` by
       (irule make_ssa_stage_bisim >> fs[o1_inv_def] >> metis_tac[]) >>
     `EVERY simplify_cfg_fn_ok (stage 5).ctx_functions` by
       (qpat_x_assum `o1_ctx_shape (stage 5)` mp_tac >>
        qpat_x_assum `o1_inv D 5 (stage 5) v7` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[o1_ctx_shape_def, o1_inv_def, o1_ssa_inv_def, EVERY_MEM] >>
        rpt strip_tac >> irule simplify_cfg_fn_ok_ssa >>
        metis_tac[o1_fn_shape_def]) >>
     `ctx_bisim (stage 5) (stage 6)` by
       (irule simplify_cfg_stage_bisim >> metis_tac[]) >>
     `ctx_bisim (stage 6) (stage 7)` by
       (irule sue_stage_bisim >> fs[o1_inv_def, o1_ssa_inv_def, o1_pre_def] >>
        metis_tac[]) >>
     rpt conj_tac >> irule ctx_bisim_ctx_abort_rq >>
     gvs[o1_initial_state_ok_def, ctx_pass_stage_def]) >>
  `ctx_sim_fuel I D (stage 0) (stage 7) v3 v7 /\
   ctx_abort_rq D (stage 0) (stage 7) v3 v7` by
    metis_tac[ctx_sim_abort_rq_I_trans] >>
  `o1_lowered_inv (stage 7) v7` by fs[o1_inv_def, o1_ssa_inv_def] >>
  `ctx_sim_fuel (cfg_norm_fuel (stage 9)) D (stage 8) (stage 9) vs_out vs_out /\
   ctx_abort_rq D (stage 8) (stage 9) vs_out vs_out` by
    (conj_tac
     >- (rw[ctx_sim_fuel_def] >> irule cfg_norm_stage_run_fuel >>
         fs[o1_initial_state_ok_def] >> metis_tac[]) >>
     irule ctx_bisim_ctx_abort_rq >> fs[o1_initial_state_ok_def] >>
     metis_tac[cfg_norm_stage_bisim, ctx_pass_stage_def]) >>
  `ctx_sim_fuel I D (stage 0) (stage 8) v3 vs_out /\
   ctx_abort_rq D (stage 0) (stage 8) v3 vs_out` by
    metis_tac[ctx_sim_abort_rq_I_trans] >>
  `ctx_sim_fuel (cfg_norm_fuel (stage 9) o I) D (stage 0) (stage 9) v3 vs_out` by
    (irule ctx_sim_fuel_trans >> metis_tac[]) >>
  simp[combinTheory.I_o_ID] >> conj_tac
  >- fs[combinTheory.I_o_ID] >>
  conj_tac >- metis_tac[ctx_abort_rq_trans] >>
  `max_live_eom (stage 9) = max_live_eom (stage 8)` by
    metis_tac[cfg_norm_stage_max_live_eom] >>
  Cases_on `o1_lowered_inv (stage 8) vs_out`
  >- (disj1_tac >> fs[o1_lowered_inv_def] >>
      irule cfg_norm_stage_mem_inv >>
      fs[o1_initial_state_ok_def] >>
      metis_tac[mem_corr_closed_rf_lowered_mem_fact]) >>
  disj2_tac >> fs[] >> conj_tac
  >- (irule cfg_norm_stage_mem_inv_lowered_abort >>
      fs[o1_initial_state_ok_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `dead_result_rel D (run_context fuel (stage 0) v3)
                     (run_context fuel (stage 7) v7)` by
    fs[ctx_sim_fuel_def] >>
  `terminates (run_context fuel (stage 7) v7)` by
    metis_tac[dead_result_rel_terminates] >>
  `?u. run_context fuel (stage 7) v7 = Abort ExHalt_abort u` by metis_tac[] >>
  Cases_on `run_context fuel (stage 0) v3` >>
  gvs[dead_result_rel_def] >> rename1 `reason <> Revert_abort` >>
  Cases_on `reason` >> gvs[]
QED
