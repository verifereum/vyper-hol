Theory o1CodeEndWalkCompose
Ancestors
  o1PipelineCompose o1CodeEndLowerStage o1CodeEndLowerLifetime
  o1CodeEndMiddleTransport o1CodeEndSsaProtectedUses
  o1CodeEndStructuralTransport o1CodeEndDftTransport
  o1CodeEndConcretizeLifetime o1CodeEndFmpLifetime
  o1PassContract o1ContractMakeSsa venomState
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
  dead_wf D /\ o1_run_state_ok vs_out /\
  LENGTH vs_out.vs_data_section < dimword (:256) DIV 2 ==>
  ?vi. gas_variant vi vs_out /\
    (o1_inv D 0 (stage 0) vi /\
     mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
       s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
       (stage 1) vi /\
     (!f i. MEM f (stage 1).ctx_functions /\ MEM i (fn_insts f) ==>
       ~MEM (Label "code_end") i.inst_operands) ==>
     ctx_sim_fuel (cfg_norm_fuel (stage (LENGTH o1_fn_passes))) D
       (stage 0) (stage (LENGTH o1_fn_passes)) vi vs_out /\
     o1_inv D (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs_out /\
     code_end_offset_ok (raw_reachable vs_out) (stage (LENGTH o1_fn_passes)))
Proof
  strip_tac >>
  `LENGTH o1_fn_passes = 9` by EVAL_TAC >>
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
  disch_then (qx_choose_then `vi` strip_assume_tac) >>
  qexists `vi` >> simp[] >> strip_tac >>
  `o1_run_state_ok vi` by metis_tac[gas_variant_run_state_ok] >>
  `vi.vs_data_section = vs_out.vs_data_section` by
    (fs[gas_variant_def] >>
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
  drule_all ((PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] (SRULE [o1_fn_passes_def] code_end_middle_stage_contracts))) >>
  strip_tac >>
  drule_all concretize_stage_protected_lifetime >> strip_tac >>
  drule_all fmp_stage_protected_lifetime >> strip_tac >>
  `EVERY make_ssa_input_ok (stage 4).ctx_functions` by
    (qpat_x_assum `EVERY (o1_fn_row 4) _` mp_tac >>
     simp[EVERY_MEM, o1_fn_row_def] >> metis_tac[]) >>
  drule_all (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] make_ssa_stage_protected_uses) >> strip_tac >>
  map_every (fn n =>
    mp_tac (Q.SPEC n code_end_structural_stage_contracts) >>
    simp[o1_stage_contract_def, o1_fn_passes_def] >> strip_tac >>
    first_x_assum drule_all >> strip_tac) [`5`, `6`] >>
  qpat_x_assum `o1_inv D 7 _ _ /\ _ ==> _` mp_tac >>
  simp[] >> strip_tac >>
  mp_tac (Q.SPEC `8` code_end_structural_stage_contracts) >>
  simp[o1_stage_contract_def, o1_fn_passes_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  fs[pass_fuel_def] >>
  map_every (fn k =>
    `ctx_sim_fuel I D (stage 0) (stage ^k) vi vi` by
      metis_tac[SRULE [] (Q.INST [`f` |-> `I`, `g` |-> `I`] ctx_sim_fuel_trans)])
    [``2:num``, ``3:num``, ``4:num``, ``5:num``, ``6:num``, ``7:num``] >>
  `ctx_sim_fuel I D (stage 0) (stage 8) vi vs_out` by
    metis_tac[SRULE [] (Q.INST [`f` |-> `I`, `g` |-> `I`] ctx_sim_fuel_trans)] >>
  metis_tac[SRULE [] (Q.INST [`f` |-> `I`] ctx_sim_fuel_trans)]
QED
Finalise o1_code_end_walk_stages_sim
