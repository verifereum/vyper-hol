Theory requestCutPreDftReplay
Ancestors
  requestCutWalkRecording requestCutSourceRecording requestCutReplayPreWalk
  requestCutReplayProofs jointRequestCut e2eRequestCutDefs dftWf
  o1PipelineCompose o1ComposeSupport o1PassContract
  unitShapeDefs unitTransformDefs venomCompilerWf irSupply fcgPruning
  venomPassSchedule venomExecSemantics venomWf venomState list finite_map

(* The clipped abort relation compares the requests before the retained
   visit. The paired recording steps add the request at the cut. *)
Theorem request_cut_pre_dft_recording:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  unit_wf unit /\ o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,supply) /\ pre.cu_context.ctx_entry = SOME entry /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  (!j. j < LENGTH o1_fn_passes ==>
    ctx_pass_stage rp (EL j o1_fn_passes) (o1_walk_view rp j) (stage j) (stage (SUC j))) /\
  (!j. j <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage j)) /\
  (!j. j <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row j) (stage j).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok v7 /\ v7.vs_fmp = v7.vs_initial_fmp /\
  code_layout_valid v7 /\ fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) v7 /\
  vi = (v7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  clip = (vi with vs_outcomes := TAKE (k - LENGTH vi.vs_requests) vi.vs_outcomes) /\
  clip7 = (v7 with vs_outcomes := TAKE (k - LENGTH v7.vs_requests) v7.vs_outcomes) /\
  o1_inv D 0 (stage 0) clip /\ ctx_abort_rq D unit.cu_context (stage 7) clip clip7 /\
  raw_safe_rq_upto D 0 k unit.cu_context vi /\
  raw_reachable vi unit.cu_context fn i s /\ i.inst_opcode <> INVOKE /\
  LENGTH s.vs_requests = k /\ step_inst fuel unit.cu_context i s = OK u /\
  k < LENGTH u.vs_requests /\
  raw_reachable v7 (stage 7) gn j t /\ j.inst_opcode <> INVOKE /\
  LENGTH t.vs_requests = k /\ step_inst fuel' (stage 7) j t = OK z /\
  k < LENGTH z.vs_requests ==>
  t.vs_outcomes = s.vs_outcomes /\
  request_agree_except D (EL k u.vs_requests) (EL k z.vs_requests) /\
  LIST_REL (request_agree_except D) u.vs_requests z.vs_requests /\
  ctx_rq_upto D k unit.cu_context (stage 7) vi v7
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `o1_ctx_shape unit.cu_context` by simp[o1_source_unit_ok_ctx_shape] >>
  `ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok (init_ir_supply unit)` by
    fs[unit_wf_def, unit_labels_wf_namespace, init_ir_supply_inst_ok] >>
  `EVERY fn_defs_reach_uses unit.cu_context.ctx_functions /\
   EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) unit.cu_context.ctx_functions` by
    (fs[o1_source_unit_ok_def, unit_defs_reach_uses_def, raw_opcode_ok_def, EVERY_MEM] >>
     metis_tac[]) >>
  `vi.vs_vars = FEMPTY /\ ~vi.vs_halted /\
   vi.vs_requests = v7.vs_requests /\ vi.vs_outcomes = v7.vs_outcomes` by
    fs[o1_initial_state_ok_def] >>
  drule_all (Q.INST [`lo` |-> `0`, `C0` |-> `stage 0`, `vs` |-> `vi`]
    request_cut_pre_walk) >> strip_tac >>
  `taint_within_rq_upto D k (stage 0) vi` by fs[raw_safe_rq_upto_def] >>
  drule_all request_cut_walk_recording >>
  disch_then (qx_choosel_then [`f0`, `i0`, `s0`, `n0`, `u0`] strip_assume_tac) >>
  `LENGTH s0.vs_requests < LENGTH u0.vs_requests` by simp[] >>
  drule_all (Q.INST [`C0` |-> `stage 0`, `vs` |-> `vi`, `fuel` |-> `n0`,
    `i` |-> `i0`, `t` |-> `s0`, `t'` |-> `u0`] request_cut_pre_walk_recording) >>
  disch_then (qx_choosel_then [`f1`, `s1`, `u1`] strip_assume_tac) >>
  `i0.inst_opcode <> INVOKE /\ LENGTH s1.vs_requests = k /\ k < LENGTH u1.vs_requests` by simp[] >>
  `o1_ctx_shape (stage 7)` by
    (qpat_assum `!j. j <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage j)`
      (mp_tac o Q.SPEC `7`) >> simp[o1_fn_passes_def]) >>
  `EVERY wf_function unit.cu_context.ctx_functions /\
   EVERY wf_function (stage 7).ctx_functions` by
    fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
  `EL k u1.vs_requests = EL k u.vs_requests` by
    (mp_tac (Q.INST [`C` |-> `unit.cu_context`, `vs` |-> `vi`, `k` |-> `k`,
       `fn` |-> `f1`, `i` |-> `i0`, `s` |-> `s1`, `n` |-> `n0`, `u` |-> `u1`,
       `g` |-> `fn`, `j` |-> `i`, `t` |-> `s`, `m` |-> `fuel`, `v` |-> `u`]
       request_cut_same_recording) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `request_agree_except D (EL k u.vs_requests) (EL k z.vs_requests)` by metis_tac[] >>
  `LENGTH s.vs_requests = LENGTH t.vs_requests` by simp[] >>
  `t.vs_outcomes = s.vs_outcomes` by
    (mp_tac (Q.INST [`C` |-> `unit.cu_context`, `Ct` |-> `stage 7`,
       `vs` |-> `vi`, `vs0` |-> `v7`, `fn` |-> `fn`, `inst` |-> `i`, `s` |-> `s`,
       `fn'` |-> `gn`, `inst'` |-> `j`, `t` |-> `t`] recorded_index_same_outcomes) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
     f.fn_blocks) unit.cu_context.ctx_functions /\
   EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
     f.fn_blocks) (stage 7).ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[wf_fn_block_inst_ids_distinct]) >>
  `ctx_abort_rq D unit.cu_context (stage 7)
    (vi with vs_outcomes := TAKE (k - LENGTH vi.vs_requests) vi.vs_outcomes)
    (v7 with vs_outcomes := TAKE (k - LENGTH v7.vs_requests) v7.vs_outcomes)` by
    metis_tac[] >>
  drule_all (Q.INST [`C` |-> `unit.cu_context`, `C'` |-> `stage 7`,
    `vs` |-> `vi`, `vt` |-> `v7`, `s` |-> `s`, `t` |-> `t`]
    request_cut_compose_history) >>
  simp[]
QED
