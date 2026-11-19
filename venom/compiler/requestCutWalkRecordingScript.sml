Theory requestCutWalkRecording
Ancestors
  requestCutReplayLockstep requestCutSimplifyCfg requestCutReplayProofs
  requestCutFmpPaired requestCutConcretizePaired requestCutLowerDloadPaired
  o1StaticPipelineCompose o1PipelineCompose o1ContractSimplifyCfg
  o1PassContract o1PassLift e2eRequestCutDefs unitTransformDefs unitShapeDefs
  lowerDloadPtrRawReachable lowerDloadDefs fmpStageRel contextCodegenRel
  concretizePtrCoverageStaticMemReachability stepWriteFootprintBase
  venomPassSchedule venomExecSemantics venomWf venomState list finite_map

Theorem request_cut_walk_recording:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  (!j. j < LENGTH o1_fn_passes ==>
    ctx_pass_stage rp (EL j o1_fn_passes) (o1_walk_view rp j) (stage j) (stage (SUC j))) /\
  (!j. j <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage j)) /\
  (!j. j <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row j) (stage j).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok v7 /\ v7.vs_fmp = v7.vs_initial_fmp /\
  code_layout_valid v7 /\ fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) v7 /\
  vi = (v7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  clip7 = (v7 with vs_outcomes := TAKE (k - LENGTH v7.vs_requests) v7.vs_outcomes) /\
  clip = (vi with vs_outcomes := TAKE (k - LENGTH vi.vs_requests) vi.vs_outcomes) /\
  o1_inv D 0 (stage 0) clip /\ taint_within_rq_upto D k (stage 0) vi /\
  raw_reachable v7 (stage 7) fn i t /\ i.inst_opcode <> INVOKE /\
  LENGTH t.vs_requests = k /\ step_inst fuel (stage 7) i t = OK t' /\
  k < LENGTH t'.vs_requests ==>
  ?f j s sf u. raw_reachable vi (stage 0) f j s /\
    j.inst_opcode <> INVOKE /\ LENGTH s.vs_requests = k /\
    s.vs_outcomes = t.vs_outcomes /\ step_inst sf (stage 0) j s = OK u /\
    k < LENGTH u.vs_requests /\
    request_agree_except D (EL k u.vs_requests) (EL k t'.vs_requests)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `clip = (clip7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>)` by simp[] >>
  `code_layout_valid clip7` by
    (qpat_assum `code_layout_valid v7` (mp_tac o REWRITE_RULE [code_layout_valid_def]) >>
     simp[code_layout_valid_def]) >>
  `code_layout_valid clip` by
    (qpat_assum `code_layout_valid clip7` (mp_tac o REWRITE_RULE [code_layout_valid_def]) >>
     simp[code_layout_valid_def]) >>
  `o1_initial_state_ok clip7 /\ clip7.vs_fmp = clip7.vs_initial_fmp /\
   clip7.vs_initial_fmp = v7.vs_initial_fmp /\
   fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) clip7` by
    fs[o1_initial_state_ok_def, fmp_variant_room_def] >>
  `o1_initial_state_ok clip /\ clip.vs_fmp = clip.vs_initial_fmp /\
   clip.vs_initial_fmp = fmp /\
   vi.vs_vars = FEMPTY /\ ~vi.vs_halted /\ v7.vs_vars = FEMPTY /\ ~v7.vs_halted` by
    fs[o1_initial_state_ok_def] >>
  `(clip7 with vs_gas_readings := clip7.vs_gas_readings) = clip7` by
    simp[venom_state_component_equality] >>
  mp_tac (Q.INST [`rpolicy` |-> `rp`, `stage` |-> `stage`, `D` |-> `D`,
    `vs_out` |-> `clip7`, `rds` |-> `clip7.vs_gas_readings`, `fmp` |-> `fmp`]
    o1_walk_pre_dft_stage_facts_static_abort_fixed) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  PURE_REWRITE_TAC[LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  qpat_assum `(clip7 with vs_gas_readings := clip7.vs_gas_readings) = clip7`
    (fn th => PURE_REWRITE_TAC[th]) >>
  qpat_assum `clip = (clip7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>)`
    (fn th => PURE_REWRITE_TAC[GSYM th]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule o1_walk_stages_max_live_eom >> strip_tac >>
  qpat_assum `!j. j < LENGTH o1_fn_passes ==> ctx_pass_stage _ _ _ _ _`
    (fn th => map_every
       (fn n => assume_tac (SIMP_RULE (srw_ss()) [o1_fn_passes_def] (Q.SPEC n th)))
       [`0`,`1`,`2`,`3`,`4`,`5`,`6`]) >>
  qpat_assum `!j. j <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage j)`
    (fn th => map_every
       (fn n => assume_tac (SIMP_RULE (srw_ss()) [o1_fn_passes_def] (Q.SPEC n th)))
       [`0`,`1`,`2`,`3`,`4`,`5`,`6`,`7`]) >>
  qpat_assum `!j. j <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row j) _`
    (fn th => map_every
       (fn n => assume_tac (SIMP_RULE (srw_ss()) [o1_fn_passes_def] (Q.SPEC n th)))
       [`0`,`3`,`4`,`6`]) >>
  `EVERY make_ssa_input_ok (stage 0).ctx_functions /\
   EVERY make_ssa_input_ok (stage 4).ctx_functions /\
   EVERY simplify_cfg_fn_ok (stage 5).ctx_functions /\
   EVERY wf_ssa (stage 6).ctx_functions` by
    (fs[o1_inv_def, o1_ssa_inv_def, o1_walk_src_inv_def] >>
     fs[o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[simplify_cfg_fn_ok_ssa, o1_fn_shape_def]) >>
  `taint_within_rq_upto D k (stage 1) vi` by
    (drule_all (Q.INST [`C` |-> `stage 0`, `C'` |-> `stage 1`,
       `L` |-> `vi.vs_labels`] make_ssa_stage_lockstep) >> strip_tac >>
     metis_tac[lockstep_taint_within_rq_upto]) >>
  `LENGTH t.vs_requests < LENGTH t'.vs_requests` by simp[] >>
  drule_all (Q.INST [`C` |-> `stage 6`, `C'` |-> `stage 7`]
    sue_stage_recording_step) >>
  disch_then (qx_choosel_then [`f6`,`i6`,`s6`,`n6`,`u6`] strip_assume_tac) >>
  `i6.inst_opcode <> INVOKE /\ LENGTH s6.vs_requests < LENGTH u6.vs_requests` by simp[] >>
  drule_all (Q.INST [`C` |-> `stage 5`, `CT` |-> `stage 6`]
    simplify_cfg_stage_recording_step) >>
  disch_then (qx_choosel_then [`f5`,`s5`,`u5`] strip_assume_tac) >>
  `LENGTH s5.vs_requests < LENGTH u5.vs_requests` by simp[] >>
  drule_all (Q.INST [`C` |-> `stage 4`, `C'` |-> `stage 5`,
    `L` |-> `v7.vs_labels`] make_ssa_stage_lockstep) >>
  disch_then (qspec_then `v7` assume_tac) >>
  qpat_assum `raw_reachable v7 (stage 5) f5 i6 s5`
    (strip_assume_tac o MATCH_MP (SPEC_ALL ptr_raw_reachable_frame)) >>
  drule_all (Q.INST [`C` |-> `stage 4`, `C'` |-> `stage 5`,
    `vs` |-> `v7`, `fuel` |-> `n6`] lockstep_recording_pair) >>
  disch_then (qx_choosel_then [`stk4`,`G4`,`tn4`,`f4`,`i4`,`s4`,`u4`]
    strip_assume_tac) >>
  `?eom. max_live_eom (stage 3) = SOME eom` by
    fs[o1_inv_def,o1_static_inv_def] >>
  qpat_assum `!j. 3 + j <= LENGTH o1_fn_passes ==> _`
    (fn th => map_every
      (fn n => assume_tac (SIMP_RULE (srw_ss()) [o1_fn_passes_def] (Q.SPEC n th)))
      [`1`, `6`]) >>
  `max_live_eom (stage (LENGTH o1_fn_passes)) = max_live_eom (stage 3)` by
    simp[o1_fn_passes_def] >>
  `fmp_variant_room (SOME fmp) (stage 4) clip7` by
    (fs[fmp_variant_room_def] >> metis_tac[]) >>
  `eom <= w2n clip.vs_initial_fmp` by
    (fs[fmp_variant_room_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `fmp_stage_ctx rp D (stage 3) (stage 4) clip clip7 fmp eom` by
    (PURE_REWRITE_TAC[fmp_stage_ctx_def, o1_pre_def] >> simp[]) >>
  `i4.inst_opcode <> INVOKE /\ LENGTH s4.vs_requests = k /\ k < LENGTH u4.vs_requests` by simp[] >>
  `vi.vs_requests = v7.vs_requests /\ vi.vs_outcomes = v7.vs_outcomes` by simp[] >>
  drule_all request_cut_fmp_paired >>
  disch_then (qx_choosel_then [`stk3`,`PG3`,`G3`,`tn3`,`f3`,`s3`,`u3`]
    strip_assume_tac) >>
  qpat_assum `o1_inv D 1 (stage 1) clip`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [o1_inv_def]) >>
  qpat_assum `o1_inv D 2 (stage 2) clip`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [o1_inv_def]) >>
  `ctx_inst_ids_distinct (stage 2) /\ EVERY all_reachable (stage 2).ctx_functions /\
   EVERY fn_defs_reach_uses (stage 2).ctx_functions` by
    fs[o1_ctx_shape_def, make_ssa_input_ok_def, EVERY_MEM] >>
  qpat_assum `o1_src_inv D (stage 2) clip`
    (strip_assume_tac o REWRITE_RULE [o1_src_inv_def]) >>
  `ctx_has_dalloca (stage 2) ==> eom <= w2n clip.vs_initial_fmp` by simp[] >>
  drule_all (Q.INST [`C` |-> `stage 2`, `CT` |-> `stage 3`]
    request_cut_concretize_paired) >>
  disch_then (qx_choosel_then [`stk2`,`PG2`,`G2`,`tn2`,`f2`,`s2`,`u2`]
    strip_assume_tac) >>
  drule_all (Q.INST [`C` |-> `stage 1`, `CT` |-> `stage 2`]
    request_cut_lower_dload_paired) >>
  disch_then (qx_choosel_then [`stk1`,`PG1`,`G1`,`tn1`,`f1`,`s1`,`u1`]
    strip_assume_tac) >>
  `request_agree_except D (EL k u1.vs_requests) (EL k u4.vs_requests)` by
    metis_tac[request_agree_except_trans] >>
  drule_all (Q.INST [`C` |-> `stage 0`, `C'` |-> `stage 1`,
    `L` |-> `vi.vs_labels`] make_ssa_stage_lockstep) >>
  disch_then (qspec_then `vi` assume_tac) >>
  `LENGTH s1.vs_requests < LENGTH u1.vs_requests` by simp[] >>
  drule_all (Q.INST [`C` |-> `stage 0`, `C'` |-> `stage 1`,
    `vs` |-> `vi`, `fuel` |-> `n6`] lockstep_recording_pair) >>
  disch_then (qx_choosel_then [`stk0`,`G0`,`tn0`,`f0`,`i0`,`s0`,`u0`]
    strip_assume_tac) >>
  qexistsl_tac [`f0`,`i0`,`s0`,`n6`,`u0`] >>
  simp[] >> metis_tac[frame_reachable_raw]
QED
