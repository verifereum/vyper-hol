(* The compiled frame at a Venom call or create step: the step's request
   is the frame's next recorded request, answered by the head of the
   remaining outcomes.  Identity-finalizer case over the joint trace.

   TOP-LEVEL:
     call_trace_frame_suffix - a frame's later trace is a suffix
     normal_frame_trace_prefix_nonforward - prefix driver at any endpoint
       a revert forwarding never holds
     codegen_request_step_alignment - request and outcome alignment
 *)
Theory fnFrameRequestPrefix
Ancestors
  jointRequestCut fnFramePrefixDriver fnFramePrefix fnFramePrefixEntry
  fnBlockBodySteps fnFrameBoundaryEntryParams frameJointTrace
  frameJointTransition frameRel codegenEntryRel codegenAsmProgOk
  contextCodegenRel asmFrameRun asmFrameRel asmSem blockSimHelpers callTrace
  frameObsStep venomExecSemantics venomInstProofs venomWf venomState
  venomInst stackPlanGen codegenCorrectness codegenRel list rich_list arithmetic

(* ===== The frame's call trace along its own run ===== *)

Theorem frame_obs_tr_funpow[local]:
  !k d obs s s1.
    (!j. j <= k ==>
       ISL (FST (FUNPOW (step o SND) j (INL (),s))) /\
       d <= LENGTH (SND (FUNPOW (step o SND) j (INL (),s))).contexts) /\
    FUNPOW (step o SND) k (INL (),s) = (INL (),s1) /\
    (LENGTH s.contexts = d ==> obs.pending = NONE) /\
    LENGTH s1.contexts = d ==>
    ?obs1. obs1.pending = NONE /\
      frame_obs_tr d obs s (step s) = frame_obs_tr d obs1 s1 (step s1)
Proof
  Induct >- (rw[] >> gvs[] >> qexists_tac `obs` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `?r u. step s = (r,u)` by metis_tac[pairTheory.PAIR] >>
  `ISL r /\ d <= LENGTH u.contexts` by
    (first_x_assum (qspec_then `1` mp_tac) >> simp[]) >>
  `d <= LENGTH s.contexts` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  Cases_on `r` >> gvs[] >>
  `!j. FUNPOW (step o SND) (SUC j) (INL (),s) =
       FUNPOW (step o SND) j (INL (),u)` by simp[FUNPOW] >>
  once_rewrite_tac[frame_obs_tr_def] >> simp[] >>
  first_x_assum irule >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!j. j <= SUC k ==> _` (qspec_then `SUC j` mp_tac) >> fs[]) >>
  conj_tac >- metis_tac[] >>
  strip_tac >> rw[observe_def] >> gvs[] >>
  Cases_on `obs.pending` >> simp[] >>
  rename1 `SOME pv` >> PairCases_on `pv` >> simp[]
QED

Theorem call_trace_frame_suffix:
  FUNPOW (step o SND) k (INL (),es) = (INL (),es1) /\
  (!j. j <= k ==>
     ISL (FST (FUNPOW (step o SND) j (INL (),es))) /\
     LENGTH es.contexts <=
       LENGTH (SND (FUNPOW (step o SND) j (INL (),es))).contexts) /\
  LENGTH es1.contexts = LENGTH es.contexts ==>
  ?pre. call_trace es = pre ++ call_trace es1
Proof
  strip_tac >>
  qspecl_then [`k`, `LENGTH es.contexts`,
    `<|entries := []; readings := []; pending := NONE|>`, `es`, `es1`]
    mp_tac frame_obs_tr_funpow >>
  simp[] >> strip_tac >>
  simp[call_trace_def, frame_obs_def] >>
  qexists_tac `obs1.entries` >>
  `?r1 post1. step es1 = (r1,post1)` by metis_tac[pairTheory.PAIR] >>
  qspecl_then [`LENGTH es.contexts`,
    `<|entries := []; readings := []; pending := NONE|>`, `es1`, `r1`,
    `post1`, `obs1.entries`, `obs1.readings`] mp_tac frame_obs_tr_prefix >>
  `obs1 = <|entries := obs1.entries; readings := obs1.readings;
            pending := NONE|>` by simp[trace_obs_component_equality] >>
  pop_assum (fn th => ONCE_REWRITE_TAC [th]) >> simp[]
QED

Theorem asm_frame_prefix_call_trace_tail:
  asm_frame_prog_ok prog /\ asm_frame_rel_tail tail prog data es0 a es /\
  run_call es = SOME (r,t) /\ ~frame_resource_starved es0 r t /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog n a = AsmOK a1 ==>
  ?es1 pre. asm_frame_rel_tail tail prog data es0 a1 es1 /\
    call_trace es = pre ++ call_trace es1
Proof
  strip_tac >> drule_all asm_frame_prefix_trace_tail >> strip_tac >>
  qpat_x_assum `!n a1. asm_steps _ _ _ _ _ = _ ==> _` drule >>
  strip_tac >> qexists_tac `es1` >> simp[] >>
  irule call_trace_frame_suffix >>
  conj_tac >- gvs[asm_frame_rel_tail_def, asm_frame_rel_def] >>
  qexists_tac `k` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

(* ===== Pairing a recorded request with its outcome ===== *)

Theorem trace_request_pairing:
  !P L pa La pb Lb ra rb.
  L = pa ++ La /\ L = pb ++ Lb /\
  ra ++ FILTER P (MAP FST La) = FILTER P (MAP FST L) /\
  rb ++ FILTER P (MAP FST Lb) = FILTER P (MAP FST L) /\
  LENGTH ra < LENGTH rb /\ MAP SND Lb = TL (MAP SND La) ==>
  LENGTH ra < LENGTH (FILTER P (MAP FST L)) /\
  EL (LENGTH ra) (FILTER P (MAP FST L)) = EL (LENGTH ra) rb /\
  MAP SND La <> [] /\
  MEM (EL (LENGTH ra) (FILTER P (MAP FST L)), HD (MAP SND La)) L
Proof
  rpt strip_tac >>
  qpat_x_assum `MAP SND Lb = _` (assume_tac o Q.AP_TERM `LENGTH`) >>
  `ra = FILTER P (MAP FST pa)` by
    (qpat_x_assum `ra ++ _ = _` mp_tac >>
     qpat_assum `L = pa ++ La` SUBST1_TAC >>
     simp[FILTER_APPEND_DISTRIB, APPEND_11_LENGTH]) >>
  `rb = FILTER P (MAP FST pb)` by
    (qpat_x_assum `rb ++ _ = _` mp_tac >>
     qpat_assum `L = pb ++ Lb` SUBST1_TAC >>
     simp[FILTER_APPEND_DISTRIB, APPEND_11_LENGTH]) >>
  `pa ++ La = pb ++ Lb` by metis_tac[] >>
  qpat_x_assum `ra ++ _ = _` kall_tac >>
  qpat_x_assum `rb ++ _ = _` kall_tac >>
  qpat_x_assum `L = pb ++ Lb` kall_tac >>
  qpat_x_assum `L = pa ++ La` SUBST_ALL_TAC >>
  qpat_x_assum `ra = _` SUBST_ALL_TAC >>
  qpat_x_assum `rb = _` SUBST_ALL_TAC >>
  qpat_x_assum `pa ++ La = pb ++ Lb` mp_tac >>
  rewrite_tac[APPEND_EQ_APPEND] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[FILTER_APPEND_DISTRIB] >>
  Cases_on `l` >> fs[] >> Cases_on `t` >> fs[] >>
  PairCases_on `h` >> Cases_on `P h0` >> fs[] >> simp[EL_APPEND_EQN]
QED

(* ===== Prefix driver at a non-forwarding endpoint ===== *)

Theorem normal_frame_trace_prefix_nonforward:
  !j.
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  initial_ctx_rel_tail tail cpl prog unit.cu_context vs0 es0 /\
  joint_trace vs0 unit.cu_context q0 es qs
    (JointConfig laststk lastPG lastG lasttn lastfn lastinst laststate
      lastoms lastom lasths lasth) /\
  active_inst lastfn lastinst laststate /\
  ~MEM lastinst.inst_opcode [RETURNDATACOPY; ASSIGN; REVERT] /\
  (!k stk PG G tn fn inst s oms om hs h.
    k < LENGTH es /\
    EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    ~in_revert_forward fn s ==>
    source_memory_reads_disjoint cpl inst s /\
    context_source_memory_writes_disjoint cpl inst s) /\
  j <= LENGTH es ==>
  ?n ast.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n (entry_asm_state vs0 es0) = AsmOK ast /\
    normal_frame_plan rpolicy unit cpl prog vs0 es0 (EL j (q0::qs)) ast
Proof
  Induct >> rpt strip_tac
  >- (qexistsl_tac [`0`, `entry_asm_state vs0 es0`] >>
      simp[asm_steps_def] >> irule normal_frame_initial >>
      metis_tac[joint_trace_def]) >>
  `j < LENGTH es /\ j <= LENGTH es` by decide_tac >>
  `?n ast.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n (entry_asm_state vs0 es0) = AsmOK ast /\
    normal_frame_plan rpolicy unit cpl prog vs0 es0 (EL j (q0::qs)) ast` by
    (first_x_assum irule >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `?stk PG G tn fn inst s oms om hs h.
    EL j (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h` by
    (Cases_on `EL j (q0::qs)` >> metis_tac[]) >>
  `normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast` by metis_tac[] >>
  drule normal_frame_fn_shape >> strip_tac >>
  `~in_revert_forward fn s` by
    (irule joint_trace_nonforward_endpoint >> metis_tac[]) >>
  `joint_config_reachable vs0 unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
   joint_transition unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h)
    (EL j es) (EL (SUC j) (q0::qs))` by
    (drule joint_trace_edge_at >> disch_then (qspec_then `j` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode ==>
    source_memory_reads_disjoint cpl inst s /\
    context_source_memory_writes_disjoint cpl inst s` by metis_tac[] >>
  drule_all normal_frame_joint_step >>
  disch_then (qx_choosel_then [`m`, `next`] strip_assume_tac) >>
  qexistsl_tac [`n+m`, `next`] >> conj_tac
  >- (irule asm_steps_compose_ok >> qexists_tac `ast` >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

(* ===== Oracle fields of a planned configuration ===== *)

Theorem entry_bind_pairs_oracle:
  !pairs s. (entry_bind_pairs pairs s).vs_requests = s.vs_requests /\
            (entry_bind_pairs pairs s).vs_outcomes = s.vs_outcomes
Proof
  simp[entry_bind_pairs_normal]
QED

Theorem normal_frame_plan_oracle:
  normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast ==>
  ast.as_requests = s.vs_requests /\ ast.as_outcomes = s.vs_outcomes
Proof
  rw[normal_frame_plan_def]
  >- gvs[active_frame_plan_def, body_plan_inv_def, fn_frame_inv_def,
         context_venom_asm_rel_def, frame_view_def]
  >- gvs[active_frame_plan_def, body_plan_inv_def, fn_frame_inv_def,
         context_venom_asm_rel_def, frame_view_def] >>
  gvs[entry_frame_plan_def, fn_entry_state_rel_def, shared_state_rel_def,
      venom_asm_terminal_rel_def, entry_bind_pairs_oracle]
QED

(* ===== The step's request and outcome in the compiled frame ===== *)

Theorem active_inst_next_nonterminator:
  wf_function fn /\ active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst s = OK s' ==>
  ?inst'. active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rw[active_inst_def, wf_function_def] >>
  `bb_well_formed bb` by metis_tac[] >>
  `s'.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
  `SUC s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (fs[bb_well_formed_def] >>
     spose_not_then assume_tac >>
     `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by decide_tac >>
     Cases_on `bb.bb_instructions` >> gvs[LAST_EL]) >>
  qexists_tac `bb` >> simp[]
QED

Theorem codegen_request_step_alignment:
  !rpolicy unit cpl prog tail vs0 q0 es qs es0 s s' result final.
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  initial_ctx_rel_tail tail cpl prog unit.cu_context vs0 es0 /\
  joint_trace vs0 unit.cu_context q0 es qs
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel unit.cu_context inst s = OK s' /\
  LENGTH s.vs_requests < LENGTH s'.vs_requests /\
  (!j stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1.
    j <= LENGTH es /\
    EL j (q0::qs) = JointConfig stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1 /\
    inst1.inst_opcode <> INVOKE /\ ~is_terminator inst1.inst_opcode /\
    ~in_revert_forward fn1 s1 ==>
    source_memory_reads_disjoint cpl inst1 s1 /\
    context_source_memory_writes_disjoint cpl inst1 s1) /\
  run_call es0 = SOME (result,final) /\
  ~frame_resource_starved es0 result final ==>
  LENGTH s.vs_requests < LENGTH (call_requests es0) /\
  EL (LENGTH s.vs_requests) (call_requests es0) =
    EL (LENGTH s.vs_requests) s'.vs_requests /\
  s.vs_outcomes <> [] /\
  MEM (EL (LENGTH s.vs_requests) (call_requests es0), HD s.vs_outcomes)
    (call_trace es0)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all step_inst_request_outcomes >> strip_tac >>
  `~is_terminator inst.inst_opcode /\
   ~MEM inst.inst_opcode [RETURNDATACOPY; ASSIGN; REVERT]` by
    gvs[is_terminator_def] >>
  `EL (LENGTH es) (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h` by
    metis_tac[joint_trace_endpoint] >>
  qspec_then `LENGTH es`
    (drule_at (Pat `joint_trace _ _ _ _ _ _`) o GEN_ALL)
    normal_frame_trace_prefix_nonforward >>
  disch_then (qspecl_then [`tail`, `rpolicy`, `prog`, `es0`, `cpl`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[LESS_IMP_LESS_OR_EQ]) >>
  disch_then (qx_choosel_then [`n`, `ast`] strip_assume_tac) >>
  `normal_frame_plan rpolicy unit cpl prog vs0 es0
     (JointConfig stk PG G tn fn inst s oms om hs h) ast` by metis_tac[] >>
  drule normal_frame_fn_shape >> strip_tac >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  drule_all active_inst_next_nonterminator >> strip_tac >>
  `~in_revert_forward fn s` by
    (irule joint_trace_nonforward_endpoint >> metis_tac[LESS_EQ_REFL]) >>
  `joint_config_reachable vs0 unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h)` by
    metis_tac[joint_trace_reachable] >>
  qmatch_asmsub_abbrev_tac `active_inst fn inst' snext` >>
  `?q'. joint_transition unit.cu_context
     (JointConfig stk PG G tn fn inst s oms om hs h)
     (SOME (OriginOrdinary fuel s')) q'` by
    (simp[joint_transition_ordinary] >> metis_tac[]) >>
  `source_memory_reads_disjoint cpl inst s /\
   context_source_memory_writes_disjoint cpl inst s` by
    (first_x_assum irule >> simp[] >>
     qexistsl_tac [`G`, `PG`, `fn`, `h`, `hs`, `LENGTH es`, `om`, `oms`,
                   `stk`, `tn`] >> simp[]) >>
  `?m ast1. asm_steps (SND (compute_label_offsets prog))
       (build_offset_to_pc prog) prog m ast = AsmOK ast1 /\
     normal_frame_plan rpolicy unit cpl prog vs0 es0 q' ast1` by
    (irule normal_frame_joint_step >> metis_tac[]) >>
  `asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     prog (n+m) (entry_asm_state vs0 es0) = AsmOK ast1` by
    (irule asm_steps_compose_ok >> qexists_tac `ast` >> simp[]) >>
  `ast1.as_requests = s'.vs_requests /\ ast1.as_outcomes = s'.vs_outcomes` by
    (qpat_x_assum `joint_transition _ _ _ q'` mp_tac >>
     simp[joint_transition_ordinary] >> strip_tac >>
     qpat_x_assum `normal_frame_plan _ _ _ _ _ _ _ ast1` mp_tac >>
     qunabbrev_tac `snext` >> fs[] >> strip_tac >>
     drule normal_frame_plan_oracle >> simp[]) >>
  drule normal_frame_plan_oracle >> strip_tac >>
  drule_all codegen_assembly_frame_prog_ok >> strip_tac >>
  `assemble prog <> []` by metis_tac[codegen_assembly_nonempty] >>
  Q.SUBGOAL_THEN `vs0.vs_call_ctx.cc_created_in_tx \/ account_already_created
    (lookup_account (FST (HD es0.contexts)).msgParams.callee
      es0.rollback.accounts)` assume_tac
  >- (gvs[initial_ctx_rel_tail_def, initial_ctx_rel_def] >> metis_tac[]) >>
  drule_all asm_frame_rel_entry_tail >> strip_tac >>
  `?esa pa. asm_frame_rel_tail tail prog vs0.vs_data_section es0 ast esa /\
     call_trace es0 = pa ++ call_trace esa` by
    (irule asm_frame_prefix_call_trace_tail >> metis_tac[]) >>
  `?esb pb. asm_frame_rel_tail tail prog vs0.vs_data_section es0 ast1 esb /\
     call_trace es0 = pb ++ call_trace esb` by
    (irule asm_frame_prefix_call_trace_tail >> metis_tac[]) >>
  gvs[asm_frame_rel_tail_def, asm_frame_rel_def] >>
  qspecl_then [`\rq. T`, `call_trace es0`, `pa`,
    `call_trace esa`, `pb`, `call_trace esb`, `s.vs_requests`,
    `s'.vs_requests`] mp_tac trace_request_pairing >>
  simp[listTheory.FILTER_T, GSYM call_requests_def]
QED
