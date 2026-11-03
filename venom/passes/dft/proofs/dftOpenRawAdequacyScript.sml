Theory dftOpenRawAdequacy
Ancestors
  dftOpenErase dftOpenAdequacy dftOpenMachine dftOpenFuel
  venomExecSemantics venomExecProofs venomInst dftSparseOracle arithmetic list
  contextRawReachable contextCodegenRel venomInstProps

(* Reflect the endpoint against the actual native result, not against an
   arbitrary label on a segment: delivery overwrites instruction indices. *)
Theorem dft_open_step_endpoint_reflect:
  dft_sparse_oracle a xs /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  0 < k /\
  dft_first_hit (dft_open_next a ctx)
    (dft_open_inst_exit fn budget bb stack s.vs_inst_idx)
    (DftOpen (DftAt fn budget bb s) stack n) k d ==>
  ?rr m. n <= m /\
    dft_open_result_eq (dft_open_materialize_result xs m rr)
      (step_inst budget ctx inst (dft_open_materialize xs n s)) /\
    (case rr of
       OK t => d = dft_open_deliver fn budget bb inst s stack m rr
     | _ => dft_open_classified_exit stack rr d m)
Proof
  strip_tac >>
  `dft_open_step_segment a xs ctx fn budget bb inst s stack n
    (step_inst budget ctx inst (dft_open_materialize xs n s))`
    by (irule dft_open_step_forward_segment >> simp[]) >>
  gvs[dft_open_step_segment_def] >>
  `d' = d` by metis_tac[dft_first_hit_unique] >>
  metis_tac[]
QED

Theorem dft_open_step_OK_nonterminator:
  dft_sparse_oracle a xs /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\
  step_inst budget ctx inst (dft_open_materialize xs n s) = OK after ==>
  ?k m t. 0 < k /\ n <= m /\
    FUNPOW (dft_open_next a ctx) k
      (DftOpen (DftAt fn budget bb s) stack n) =
      DftOpen (DftAt fn budget bb t) stack m /\
    dft_open_materialize xs m t = after with vs_inst_idx := SUC s.vs_inst_idx
Proof
  strip_tac >> drule_all dft_open_step_forward_segment >>
  disch_then (qspecl_then [`stack`, `fn`] mp_tac) >>
  simp[dft_open_step_segment_def] >> strip_tac >>
  Cases_on `rr` >>
  gvs[dft_open_materialize_result_def, dft_open_result_eq_def,
      stateEquivTheory.lift_result_def] >>
  gvs[dft_open_deliver_def, dft_open_continue_def, dft_first_hit_def] >>
  qexistsl_tac [`k`, `m`, `v with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[dft_open_materialize_def]
QED

Theorem dft_open_extend_nonterminator:
  dft_sparse_oracle a xs /\
  FUNPOW (dft_open_next a ctx) j c = DftOpen (DftAt fn b bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst (dft_open_materialize xs n s) = OK after ==>
  ?h m t. j < h /\ n <= m /\
    FUNPOW (dft_open_next a ctx) h (dft_shift_config fuel c) =
      DftOpen (DftAt fn (b+fuel) bb t) (MAP (dft_shift_frame fuel) stack) m /\
    dft_open_materialize xs m t = after with vs_inst_idx := SUC s.vs_inst_idx
Proof
  strip_tac >>
  `step_inst (b+fuel) ctx inst (dft_open_materialize xs n s) = OK after`
    by (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  drule dft_shift_active >> disch_then (qspec_then `fuel` assume_tac) >>
  drule_all dft_open_step_OK_nonterminator >>
  disch_then (qspecl_then [`MAP (dft_shift_frame fuel) stack`, `fn`] mp_tac) >>
  strip_tac >>
  qexistsl_tac [`k+j`, `m`, `t`] >>
  simp[FUNPOW_ADD]
QED

Theorem dft_open_step_OK_terminator:
  dft_sparse_oracle a xs /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ ~after.vs_halted /\
  step_inst budget ctx inst (dft_open_materialize xs n s) = OK after ==>
  ?k m t. 0 < k /\ n <= m /\
    FUNPOW (dft_open_next a ctx) k
      (DftOpen (DftAt fn budget bb s) stack n) =
      DftOpen (DftEnter fn budget t) stack m /\
    dft_open_materialize xs m t = after
Proof
  strip_tac >> drule_all dft_open_step_forward_segment >>
  disch_then (qspecl_then [`stack`, `fn`] mp_tac) >>
  simp[dft_open_step_segment_def] >> strip_tac >>
  Cases_on `rr` >>
  gvs[dft_open_materialize_result_def, dft_open_result_eq_def,
      stateEquivTheory.lift_result_def] >>
  `~v.vs_halted` by gvs[dft_open_materialize_def] >>
  gvs[dft_open_deliver_def, dft_open_continue_def, dft_first_hit_def] >>
  metis_tac[]
QED

Theorem dft_open_materialized_entry:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis (dft_open_materialize xs n s) bb.bb_instructions = OK sp ==>
  ?t. dft_open_next a ctx (DftOpen (DftEnter fn (SUC b) s) stack n) =
      DftOpen (DftAt fn b bb t) stack n /\
    dft_open_materialize xs n t =
      sp with vs_inst_idx := phi_prefix_length bb.bb_instructions
Proof
  strip_tac >>
  `dft_open_result_eq (OK sp)
    (dft_open_materialize_result xs n (eval_phis s bb.bb_instructions))`
    by metis_tac[dft_open_phis_materialize] >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  gvs[dft_open_materialize_result_def, dft_open_result_eq_def,
      stateEquivTheory.lift_result_def] >>
  qexists_tac `v with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  simp[dft_open_next_def, dft_open_materialize_def]
QED

Theorem dft_open_extend_block:
  dft_sparse_oracle a xs /\
  FUNPOW (dft_open_next a ctx) j c = DftOpen (DftAt fn b bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ ~after.vs_halted /\
  step_inst fuel ctx inst (dft_open_materialize xs n s) = OK after /\
  lookup_block after.vs_current_bb fn.fn_blocks = SOME nb /\
  eval_phis after nb.bb_instructions = OK sp ==>
  ?h m t. j < h /\ n <= m /\
    FUNPOW (dft_open_next a ctx) h (dft_shift_config (SUC fuel) c) =
      DftOpen (DftAt fn (b+fuel) nb t)
        (MAP (dft_shift_frame (SUC fuel)) stack) m /\
    dft_open_materialize xs m t =
      sp with vs_inst_idx := phi_prefix_length nb.bb_instructions
Proof
  strip_tac >>
  `step_inst (b+SUC fuel) ctx inst (dft_open_materialize xs n s) = OK after`
    by (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  drule dft_shift_active >> disch_then (qspec_then `SUC fuel` assume_tac) >>
  drule_all dft_open_step_OK_terminator >>
  disch_then (qspecl_then [`MAP (dft_shift_frame (SUC fuel)) stack`, `fn`] mp_tac) >>
  strip_tac >>
  `lookup_block t.vs_current_bb fn.fn_blocks = SOME nb` by gvs[dft_open_materialize_def] >>
  `eval_phis (dft_open_materialize xs m t) nb.bb_instructions = OK sp` by simp[] >>
  drule_all dft_open_materialized_entry >>
  disch_then (qspecl_then [`MAP (dft_shift_frame (SUC fuel)) stack`, `ctx`,
    `b+fuel`, `a`] mp_tac) >>
  strip_tac >> gvs[ADD_CLAUSES] >>
  qexistsl_tac [`SUC (k+j)`, `m`, `t'`] >>
  pure_rewrite_tac[FUNPOW_SUC, FUNPOW_ADD] >> simp[]
QED

Theorem dft_open_extend_callee:
  FUNPOW (dft_open_next a ctx) j c = DftOpen (DftAt fn b bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops (dft_open_materialize xs n s) = SOME args /\
  setup_callee callee args (dft_open_materialize xs n s) = SOME cs /\
  lookup_block cs.vs_current_bb callee.fn_blocks = SOME cb /\
  eval_phis cs cb.bb_instructions = OK callee_phis ==>
  ?t. FUNPOW (dft_open_next a ctx) (2+j) (dft_shift_config 1 c) =
    DftOpen (DftAt callee b cb t)
      (DftCaller fn (b+1) bb inst s :: MAP (dft_shift_frame 1) stack) n /\
    dft_open_materialize xs n t =
      callee_phis with vs_inst_idx := phi_prefix_length cb.bb_instructions
Proof
  strip_tac >>
  `eval_operands ops s = SOME args` by gvs[dft_open_materialize_def] >>
  `?ghost. setup_callee callee args s = SOME ghost /\
    dft_open_materialize xs n ghost = cs` by
    (qpat_x_assum `setup_callee _ _ (dft_open_materialize _ _ _) = _` mp_tac >>
     simp[dft_open_setup_materialize] >>
     Cases_on `setup_callee callee args s` >> simp[]) >>
  `lookup_block ghost.vs_current_bb callee.fn_blocks = SOME cb`
    by gvs[dft_open_materialize_def] >>
  `eval_phis (dft_open_materialize xs n ghost) cb.bb_instructions = OK callee_phis` by simp[] >>
  `?t. dft_open_next a ctx
      (DftOpen (DftEnter callee (SUC b) ghost)
        (DftCaller fn (b+1) bb inst s :: MAP (dft_shift_frame 1) stack) n) =
      DftOpen (DftAt callee b cb t)
        (DftCaller fn (b+1) bb inst s :: MAP (dft_shift_frame 1) stack) n /\
      dft_open_materialize xs n t = callee_phis with vs_inst_idx := phi_prefix_length cb.bb_instructions`
    by (irule dft_open_materialized_entry >> simp[]) >>
  drule dft_shift_active >> disch_then (qspec_then `1` assume_tac) >>
  qexists_tac `t` >>
  pure_rewrite_tac[FUNPOW_ADD] >>
  simp[Once FUNPOW, FUNPOW_SUC] >>
  gvs[GSYM ADD1] >>
  pure_rewrite_tac[FUNPOW_2] >>
  simp[dft_open_next_def, dft_open_invoke_def]
QED

(* The lookup clause keeps the active block aligned with the native state. *)
Definition dft_raw_budget_observation_def:
  dft_raw_budget_observation a vs0 ctx entry lbl fn inst observed <=>
    ?fuel j b bb ghost stack n.
      FUNPOW (dft_open_next a ctx) j
        (DftOpen (DftEnter entry fuel
          (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                      vs_inst_idx := 0|>)) [] 0) =
        DftOpen (DftAt fn b bb ghost) stack n /\
      lookup_block observed.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb ghost.vs_inst_idx = SOME inst /\
      observed = dft_open_materialize vs0.vs_gas_readings n ghost
End

Theorem dft_raw_active_lookup[local]:
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  get_instruction bb s.vs_inst_idx = SOME inst
Proof
  rw[active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb'`
    by (irule MEM_lookup_block >> simp[]) >>
  gvs[get_instruction_def]
QED

Theorem dft_raw_budget_adequacy:
  !vs0 ctx fn inst observed.
    raw_reachable vs0 ctx fn inst observed ==>
    !a name entry lbl.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME entry /\
      fn_entry_label entry = SOME lbl /\
      EVERY (\f. ALL_DISTINCT (MAP (\b. b.bb_label) f.fn_blocks)) ctx.ctx_functions /\
      dft_sparse_oracle a vs0.vs_gas_readings ==>
      MEM fn ctx.ctx_functions /\
      dft_raw_budget_observation a vs0 ctx entry lbl fn inst observed
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac >> rpt gen_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "callee"
QED

Resume dft_raw_budget_adequacy[entry]:
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
      `MEM entry ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
      conj_tac >- simp[] >>
      gvs[enters_block_def] >>
      qmatch_asmsub_abbrev_tac `eval_phis initial _ = OK sp` >>
      `dft_open_materialize vs0.vs_gas_readings 0 initial = initial`
        by simp[dft_open_materialize_def, Abbr `initial`] >>
      `?t. dft_open_next a ctx (DftOpen (DftEnter entry (SUC 0) initial) [] 0) =
          DftOpen (DftAt entry 0 bb t) [] 0 /\
          dft_open_materialize vs0.vs_gas_readings 0 t =
            sp with vs_inst_idx := phi_prefix_length bb.bb_instructions`
        by (irule dft_open_materialized_entry >> simp[Abbr `initial`]) >>
      `sp.vs_current_bb = initial.vs_current_bb`
        by metis_tac[eval_phis_preserves_current_bb] >>
      `lookup_block (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_current_bb
          entry.fn_blocks = SOME bb` by (gvs[Abbr `initial`]) >>
      `ALL_DISTINCT (MAP (\b. b.bb_label) entry.fn_blocks)`
        by (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM] >>
            disch_then (qspec_then `entry` mp_tac) >> simp[]) >>
      drule_all dft_raw_active_lookup >> strip_tac >>
      gvs[Abbr `initial`] >>
      simp[dft_raw_budget_observation_def] >>
      qexistsl_tac [`1`, `1`, `0`, `t`, `[]`, `0`] >>
      gvs[FUNPOW_1, dft_open_materialize_def] >>
      qpat_x_assum `t with vs_gas_readings := _ = _` (mp_tac o Q.AP_TERM `\v. v.vs_inst_idx`) >>
      simp[] >> metis_tac[]
QED

Resume dft_raw_budget_adequacy[next]:
  strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      conj_tac >- simp[] >>
      gvs[dft_raw_budget_observation_def] >>
      drule_all dft_open_extend_nonterminator >> strip_tac >>
      `s'.vs_current_bb = ghost.vs_current_bb`
        by (drule_all step_preserves_control_flow >>
            simp[dft_open_materialize_def]) >>
      `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)`
        by (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM] >>
            disch_then (qspec_then `fn` mp_tac) >> simp[]) >>
      `lookup_block (s' with vs_inst_idx := SUC ghost.vs_inst_idx).vs_current_bb
        fn.fn_blocks = SOME bb` by simp[] >>
      drule_all dft_raw_active_lookup >> simp[] >> strip_tac >>
      `t.vs_inst_idx = SUC ghost.vs_inst_idx`
        by (qpat_x_assum `dft_open_materialize _ _ _ = _`
              (mp_tac o Q.AP_TERM `\v. v.vs_inst_idx`) >>
            simp[dft_open_materialize_def]) >>
      qexistsl_tac [`fuel'+fuel`, `h`, `b+fuel`, `t`,
        `MAP (dft_shift_frame fuel) stack`, `m`] >>
      gvs[dft_shift_config_def, dft_shift_control_def]
QED

Resume dft_raw_budget_adequacy[block]:
  strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      conj_tac >- simp[] >>
      gvs[dft_raw_budget_observation_def, enters_block_def] >>
      drule_all dft_open_extend_block >> strip_tac >>
      `s_phi.vs_current_bb = s'.vs_current_bb`
        by metis_tac[eval_phis_preserves_current_bb] >>
      `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)`
        by (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM] >>
            disch_then (qspec_then `fn` mp_tac) >> simp[]) >>
      `lookup_block (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_current_bb
        fn.fn_blocks = SOME bb` by simp[] >>
      drule_all dft_raw_active_lookup >> simp[] >> strip_tac >>
      `t.vs_inst_idx = phi_prefix_length bb.bb_instructions`
        by (qpat_x_assum `dft_open_materialize _ _ _ = _`
              (mp_tac o Q.AP_TERM `\v. v.vs_inst_idx`) >>
            simp[dft_open_materialize_def]) >>
      qexistsl_tac [`fuel'+SUC fuel`, `h`, `b+fuel`, `t`,
        `MAP (dft_shift_frame (SUC fuel)) stack`, `m`] >>
      gvs[dft_shift_config_def, dft_shift_control_def]
QED

Resume dft_raw_budget_adequacy[callee]:
  strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      `MEM fn' ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
      conj_tac >- simp[] >>
      gvs[dft_raw_budget_observation_def, enters_block_def] >>
      drule_all dft_open_extend_callee >> strip_tac >>
      `s_phi.vs_current_bb = cs.vs_current_bb`
        by metis_tac[eval_phis_preserves_current_bb] >>
      `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)`
        by (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM] >>
            disch_then (qspec_then `fn'` mp_tac) >> simp[]) >>
      `lookup_block (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_current_bb
        fn'.fn_blocks = SOME bb` by simp[] >>
      drule_all dft_raw_active_lookup >> simp[] >> strip_tac >>
      `t.vs_inst_idx = phi_prefix_length bb.bb_instructions`
        by (qpat_x_assum `dft_open_materialize _ _ _ = _`
              (mp_tac o Q.AP_TERM `\v. v.vs_inst_idx`) >>
            simp[dft_open_materialize_def]) >>
      qexistsl_tac [`fuel+1`, `2+j`, `b`, `t`,
        `DftCaller fn (b+1) bb' inst ghost :: MAP (dft_shift_frame 1) stack`, `n`] >>
      gvs[dft_shift_config_def, dft_shift_control_def]
QED

Finalise dft_raw_budget_adequacy


Theorem dft_raw_inf_adequacy:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  fn_entry_label entry = SOME lbl /\
  EVERY (\f. ALL_DISTINCT (MAP (\b. b.bb_label) f.fn_blocks)) ctx.ctx_functions /\
  dft_sparse_oracle a vs0.vs_gas_readings /\
  raw_reachable vs0 ctx fn inst observed ==>
  ?j bb ghost stack n.
    FUNPOW (dft_next_inf a ctx) j
      (dft_erase (DftOpen (DftEnter entry 0
        (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0|>)) [] 0)) =
      dft_erase (DftOpen (DftAt fn 0 bb ghost) stack n) /\
    get_instruction bb ghost.vs_inst_idx = SOME inst /\
    observed = dft_open_materialize vs0.vs_gas_readings n ghost
Proof
  strip_tac >> drule_all dft_raw_budget_adequacy >> strip_tac >>
  gvs[dft_raw_budget_observation_def] >>
  drule dft_erase_active >> strip_tac >>
  qexistsl_tac [`j`, `bb`, `ghost`, `stack`, `n`] >>
  gvs[dft_erase_def, dft_fill_def, dft_fill_control_def]
QED
