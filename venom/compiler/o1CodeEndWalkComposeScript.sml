Theory o1CodeEndWalkCompose
Ancestors
  o1StaticPipelineCompose o1CodeEndConcretizeTransport fmpStageRel
  o1CodeEndSimplifyCfgTransport o1CodeEndSueTransport unitTransformDefs
  o1PipelineCompose o1CodeEndLowerStage o1CodeEndLowerLifetime
  o1CodeEndMiddleTransport o1CodeEndSsaProtectedUses
  o1CodeEndStructuralTransport o1CodeEndDftTransport
  o1CodeEndConcretizeLifetime o1CodeEndFmpLifetime
  o1PassContract o1ContractMakeSsa venomState
  o1ContractFmpLowering o1CodeEndFmpTransport o1CodeEndSsaTransport
  venomPassSchedule venomInst list words

Theorem o1_code_end_walk_stages_sim:
  (!k. k < LENGTH o1_fn_passes ==>
    ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
      (stage k) (stage (SUC k))) /\
  ctx_pass_stage rpolicy (EL 3 o1_fn_passes)
    (\C' f observed. o1_walk_view rpolicy 3 C' f observed /\
      EVERY fmp_sig_no_param observed.cu_context.ctx_functions)
    (stage 3) (stage 4) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==>
    EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  (!k. k <= 3 ==> EVERY no_raw_fmp_ops (stage k).ctx_functions) /\
  dead_wf D /\ o1_run_state_ok vs_out /\
  LENGTH vs_out.vs_data_section < dimword (:256) DIV 2 ==>
  ?vi. raw_variant fmp vi vs_out /\
    (o1_inv D 0 (stage 0) vi /\
     mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
       s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
       (stage 1) vi /\
     (!f i. MEM f (stage 1).ctx_functions /\ MEM i (fn_insts f) ==>
       ~MEM (Label "code_end") i.inst_operands) /\
     fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) vs_out ==>
     ctx_sim_fuel (cfg_norm_fuel (stage (LENGTH o1_fn_passes))) D
       (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out /\
     code_end_offset_ok (raw_reachable vs_out) (stage (LENGTH o1_fn_passes)))
Proof
  strip_tac >>
  `LENGTH o1_fn_passes = 9` by EVAL_TAC >>
  `max_live_eom (stage 4) = max_live_eom (stage 9)` by
    (drule o1_walk_stages_max_live_eom >> strip_tac >>
     qpat_assum `!j. _` (qspec_then `1` mp_tac) >>
     qpat_x_assum `!j. _` (qspec_then `6` mp_tac) >> simp[]) >>
  `!k. k < 9 ==> o1_pre k (stage k) (stage (SUC k))` by
    simp[o1_pre_def] >>
  map_every (fn q =>
    qpat_assum `!k. k < LENGTH _ ==> _` (qspec_then q assume_tac) >>
    qpat_assum `!k. k < 9 ==> _` (qspec_then q assume_tac) >>
    qpat_assum `!k. k <= LENGTH _ ==> o1_ctx_shape _`
      (qspec_then q assume_tac) >>
    qpat_assum `!k. k <= LENGTH _ ==> EVERY _ _`
      (qspec_then q assume_tac))
    [`0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`, `8`, `9`] >>
  qpat_x_assum `!k. k < LENGTH _ ==> _` kall_tac >>
  qpat_x_assum `!k. k < 9 ==> _` kall_tac >>
  qpat_x_assum `!k. k <= LENGTH _ ==> o1_ctx_shape _` kall_tac >>
  qpat_x_assum `!k. k <= LENGTH _ ==> EVERY _ _` kall_tac >>
  fs[o1_fn_passes_def] >>
  mp_tac dft_code_end_stage_contract_gas >>
  simp[o1_stage_contract_gas_def, o1_fn_passes_def] >> strip_tac >>
  first_x_assum (qspecl_then [`stage 7`, `stage 8`, `vs_out`] mp_tac) >>
  simp[] >>
  disch_then (qx_choose_then `vo` strip_assume_tac) >>
  qabbrev_tac `vi = vo with <| vs_fmp := fmp; vs_initial_fmp := fmp |>` >>
  `raw_variant fmp vi vo` by
    simp[Abbr `vi`, raw_variant_def, gas_variant_def] >>
  qexists_tac `vi` >> conj_tac
  >- metis_tac[raw_gas_variant_trans] >>
  strip_tac >>
  `o1_run_state_ok vo` by metis_tac[gas_variant_run_state_ok] >>
  `o1_run_state_ok vi` by metis_tac[raw_variant_run_state_ok] >>
  `vi.vs_data_section = vs_out.vs_data_section` by
    (fs[gas_variant_def, Abbr `vi`] >>
     qpat_x_assum `vs_out = _` SUBST1_TAC >> simp[]) >>
  `o1_inv D 1 (stage 1) vi /\
   ctx_sim_fuel I D (stage 0) (stage 1) vi vi` by
    (mp_tac make_ssa_run_contract_1 >>
     simp[o1_run_contract_def, o1_stage_contract_def, o1_fn_passes_def] >> strip_tac >>
     first_x_assum drule_all >>
     simp[o1_fn_passes_def, pass_fuel_def]) >>
  suspend "forward"
QED

Resume o1_code_end_walk_stages_sim[forward]:
  gvs[] >>
  mp_tac (Q.INST [`v` |-> `vi`] lower_dload_code_end_stage_contract) >>
  simp[o1_stage_contract_def] >>
  disch_then (qspecl_then [`stage 1`, `stage 2`, `vi`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  drule_all lower_dload_stage_protected_lifetime >> strip_tac >>
  `EVERY no_raw_fmp_ops (stage 2).ctx_functions` by simp[] >>
  `EVERY no_raw_fmp_ops (stage 3).ctx_functions` by simp[] >>
  drule_all ((PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] (SRULE [o1_fn_passes_def] code_end_middle_stage_contracts))) >>
  strip_tac >>
  drule_all concretize_stage_protected_lifetime >> strip_tac >>
  drule_all fmp_stage_protected_lifetime >> strip_tac >>
  `fmp_variant_room (SOME fmp) (stage 4) vo` by
    (fs[fmp_variant_room_def] >> metis_tac[gas_variant_initial_fmp]) >>
  `ctx_sim_fuel I D (stage 3) (stage 4) vi vo /\
   o1_inv D 4 (stage 4) vo` by
    (mp_tac (Q.INST [`C` |-> `stage 3`, `C'` |-> `stage 4`,
                    `vs'` |-> `vo`, `fmp` |-> `fmp`]
       o1_static_stage_fmp_lowering_fixed) >>
     impl_tac >- fs[o1_run_state_ok_def] >>
     fs[Abbr `vi`] >> metis_tac[]) >>
  `code_end_offset_ok (raw_reachable vo) (stage 4)` by
    (mp_tac (Q.INST [`D` |-> `D`, `C` |-> `stage 3`, `C'` |-> `stage 4`,
                     `vs'` |-> `vo`, `fmp` |-> `fmp`, `rpolicy` |-> `rpolicy`]
       fmp_lowering_code_end_relocate) >>
     impl_tac >- fs[Abbr `vi`] >> simp[]) >>
  mp_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]
    make_ssa_code_end_run_contract) >>
  simp[o1_stage_contract_def] >> strip_tac >>
  first_x_assum (qspecl_then [`stage 4`, `stage 5`, `vo`] mp_tac) >>
  simp[] >> (impl_tac >- (fs[APPEND_ASSOC] >> metis_tac[])) >> strip_tac >>
  `EVERY make_ssa_input_ok (stage 4).ctx_functions` by
    (qpat_x_assum `EVERY (o1_fn_row 4) _` mp_tac >>
     simp[EVERY_MEM, o1_fn_row_def] >> metis_tac[]) >>
  drule_all (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] make_ssa_stage_protected_uses) >> strip_tac >>
  map_every (fn n =>
    mp_tac (SPEC n code_end_structural_stage_contracts) >>
    simp[o1_stage_contract_def, o1_fn_passes_def] >> strip_tac >>
    first_x_assum (qspecl_then [`stage ^n`, `stage (SUC ^n)`, `vo`] mp_tac) >>
    (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >> fs[])
    [``5:num``, ``6:num``] >>
  mp_tac (Q.SPEC `8` code_end_structural_stage_contracts) >>
  simp[o1_stage_contract_def, o1_fn_passes_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  fs[pass_fuel_def] >>
  map_every (fn k =>
    `ctx_sim_fuel I D (stage 0) (stage ^k) vi vi` by
      metis_tac[SRULE [] (Q.INST [`f` |-> `I`, `g` |-> `I`] ctx_sim_fuel_trans)])
    [``2:num``, ``3:num``] >>
  map_every (fn k =>
    `ctx_sim_fuel I D (stage 0) (stage ^k) vi vo` by
      metis_tac[SRULE [] (Q.INST [`f` |-> `I`, `g` |-> `I`] ctx_sim_fuel_trans)])
    [``4:num``, ``5:num``, ``6:num``, ``7:num``] >>
  `ctx_sim_fuel I D (stage 0) (stage 8) vi vs_out` by
    metis_tac[SRULE [] (Q.INST [`f` |-> `I`, `g` |-> `I`] ctx_sim_fuel_trans)] >>
  metis_tac[SRULE [] (Q.INST [`f` |-> `I`] ctx_sim_fuel_trans)]
QED
Finalise o1_code_end_walk_stages_sim

Theorem o1_code_end_pre_dft_bound_fixed:
  (!k. k < LENGTH o1_fn_passes ==>
    ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
      (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok vs_out /\
  vs_out.vs_fmp = vs_out.vs_initial_fmp /\ code_layout_valid vs_out /\
  LENGTH vs_out.vs_data_section < dimword (:256) DIV 2 /\
  v7 = (vs_out with vs_gas_readings := rds) /\
  vi = (v7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  o1_inv D 0 (stage 0) vi /\
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
    s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
    (stage 1) vi /\
  (!fn inst. MEM fn (stage 1).ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "code_end") inst.inst_operands) /\
  fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) vs_out ==>
  code_end_offset_ok (raw_reachable v7) (stage 7)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`D` |-> `D`, `stage` |-> `stage`, `rpolicy` |-> `rpolicy`,
    `vs_out` |-> `vs_out`, `fmp` |-> `fmp`, `rds` |-> `rds`]
      o1_walk_pre_dft_stage_facts_static_abort_fixed) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  PURE_REWRITE_TAC [LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  qpat_assum `v7 = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  qpat_assum `vi = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule o1_walk_stages_max_live_eom >> strip_tac >>
  `LENGTH o1_fn_passes = 9` by EVAL_TAC >>
  `!k. k < 9 ==> o1_pre k (stage k) (stage (SUC k))` by
    (rw[o1_pre_def] >> first_x_assum irule >> simp[]) >>
  map_every (fn k =>
    qpat_assum `!k. k < LENGTH _ ==> _` (qspec_then k assume_tac) >>
    qpat_assum `!k. k < 9 ==> _` (qspec_then k assume_tac) >>
    qpat_assum `!k. k <= LENGTH _ ==> o1_ctx_shape _` (qspec_then k assume_tac) >>
    qpat_assum `!k. k <= LENGTH _ ==> EVERY _ _` (qspec_then k assume_tac))
    [`1`, `2`, `3`, `4`, `5`, `6`, `7`] >>
  `max_live_eom (stage 3) = max_live_eom (stage 9) /\
   max_live_eom (stage 4) = max_live_eom (stage 9)` by
    (qpat_x_assum `!j. _ <= LENGTH o1_fn_passes ==> max_live_eom _ = _`
      (fn th => map_every (fn k =>
        assume_tac (SIMP_RULE (srw_ss()) [o1_fn_passes_def] (Q.SPEC k th))) [`1`, `6`]) >>
     metis_tac[]) >>
  fs[o1_fn_passes_def] >>
  `code_layout_valid v7` by
    (qpat_assum `code_layout_valid vs_out`
       (mp_tac o REWRITE_RULE [lowerDloadDefsTheory.code_layout_valid_def]) >>
     simp[lowerDloadDefsTheory.code_layout_valid_def]) >>
  `code_layout_valid vi` by
    (qpat_assum `code_layout_valid v7`
       (mp_tac o REWRITE_RULE [lowerDloadDefsTheory.code_layout_valid_def]) >>
     simp[lowerDloadDefsTheory.code_layout_valid_def]) >>
  `o1_initial_state_ok v7 /\ v7.vs_fmp = v7.vs_initial_fmp` by
    fs[o1_initial_state_ok_def] >>
  `o1_initial_state_ok vi /\ vi.vs_fmp = vi.vs_initial_fmp` by
    fs[o1_initial_state_ok_def] >>
  `vi.vs_code = vs_out.vs_code /\ vi.vs_data_section = vs_out.vs_data_section` by fs[] >>
  `code_end_offset_ok (raw_reachable vi) (stage 2)` by
    (qpat_assum `o1_inv D 1 (stage 1) vi`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [o1_inv_def]) >>
     mp_tac (Q.INST [`C` |-> `stage 1`, `C'` |-> `stage 2`, `D` |-> `D`,
       `vs` |-> `vi`, `v` |-> `vi`, `rpolicy` |-> `rpolicy`,
       `view` |-> `o1_walk_view rpolicy 1`] lower_dload_stage_code_end_static) >>
     simp[] >> metis_tac[]) >>
  `?eom. max_live_eom (stage 3) = SOME eom` by
    fs[o1_inv_def, o1_static_inv_def] >>
  `eom <= w2n vi.vs_initial_fmp /\ fmp_variant_room (SOME fmp) (stage 4) v7` by
    (fs[fmp_variant_room_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `code_end_offset_ok (raw_reachable vi) (stage 3)` by
    (irule concretize_code_end_offset_ok >> metis_tac[]) >>
  `code_end_offset_ok (raw_reachable v7) (stage 4)` by
    (mp_tac (Q.INST [`D` |-> `D`, `C` |-> `stage 3`, `C'` |-> `stage 4`,
       `vs'` |-> `v7`, `fmp` |-> `fmp`, `rpolicy` |-> `rpolicy`]
       fmp_lowering_code_end_relocate_static) >>
     qpat_assum `vi = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >> simp[]) >>
  drule_all lower_dload_stage_protected_lifetime >> strip_tac >>
  drule_all concretize_stage_protected_lifetime >> strip_tac >>
  `fmp_stage_ctx rpolicy D (stage 3) (stage 4) vi v7 fmp eom` by
    fs[fmp_stage_ctx_def] >>
  drule_all fmp_stage_protected_lifetime_static >> strip_tac >>
  `EVERY make_ssa_input_ok (stage 4).ctx_functions` by
    fs[o1_fn_row_def, EVERY_MEM] >>
  `v7.vs_vars = FEMPTY /\ ~v7.vs_halted` by fs[o1_initial_state_ok_def] >>
  `code_end_offset_ok (raw_reachable v7) (stage 5)` by
    (irule (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] code_end_ssa_stage_bound) >>
     fs[] >> metis_tac[]) >>
  drule_all (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] make_ssa_stage_protected_uses) >>
  strip_tac >>
  `o1_ssa_inv (stage 5) v7` by fs[o1_inv_def] >>
  drule_all simplify_cfg_code_end_stage_preserves >> strip_tac >>
  `EVERY wf_ssa (stage 6).ctx_functions` by fs[o1_inv_def, o1_ssa_inv_def] >>
  mp_tac (Q.INST [`C` |-> `stage 6`, `C'` |-> `stage 7`, `vs` |-> `v7`,
    `rpolicy` |-> `rpolicy`, `view` |-> `o1_walk_view rpolicy 6`]
    sue_code_end_stage_preserves) >> simp[]
QED
