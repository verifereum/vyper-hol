(* Source event prefixes end at a GAS fetch, not at a GAS successor. *)
Theory gasFocusFmpCutFieldEvents
Ancestors concretizeLayoutStageSimulation[qualified] frameDecoratedPrefix frameFinitePrefix frameFiniteJointDecoration
  frameJointTransition frameJointTrace frameJointRevert concretizeLayoutCutSafe o1SafeUpto
  frameSelectedDecoration frameDecoratedEndpoints frameOriginHistory frameOriginReachable
  o1ContractSimplifyCfgSrcFrame
  contextCodegenRel gasEvents gasEventsFuel frameGasEvents blockSimHelpers
  gasFocusFmpCutSegments gasFocusFmpRetpcPoint gasFocusFmpCutRestorePrefix
  gasFocusFmpLocalEvents fmpStageBlockSimCode fmpStageRunnerFacts
  ptrStaticDiscipline passSimulationDefs o1PassContract venomWf
  lowerDloadPtrRawReachable o1LowerDloadGhost fmpLowerProps reachableNonhalted
  gasFocusFmpCutSites fmpStageRel gasFocusFmpCutControlSegments
  o1LowerDloadOpaque fmpAnalysisProps lowerDloadPtrSupport
  frameFiniteControl frameFiniteExecution fmpStageFmpStepsRestoreBounds fmpLowerDefs
  gasFocusFmpCutInvokePush gasFocusFmpCutInvokePop frameInvokeReturn
  gasFocusFmpJumpPoint gasFocusFmpRetPoint gasFocusFmpCutJumpEntry gasFocusFmpGasPair
  gasFocusFmpCutEntryStatic gasFocusFmpStagePin fmpStepStructural unitTransformDefs words
  venomExecSemantics venomInst venomState list rich_list arithmetic finite_map

Theorem fmp_cut_event_source_path[local]:
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  ALL_DISTINCT (fn_labels fn) /\
  EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions /\
  s = (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
  0 < n /\ n <= LENGTH (gas_events_blocks fuel C fn s) /\
  es = TAKE n (gas_events_blocks fuel C fn s) ==>
  ?p i q0 w qe.
    enters_block fn s p /\ active_inst fn i p /\
    q0 = JointConfig [] [] FEMPTY entry_taint fn i p [] FEMPTY []
      [OriginInitial s; OriginObserve (OriginSnapshot fn [] FEMPTY FEMPTY i p)] /\
    decorated_run_prefix C fn s q0 0 w qe es /\
    joint_trace vs C q0 (MAP FST w) (MAP SND w) qe /\
    gas_cut n vs (joint_state qe)
Proof
  strip_tac >>
  `finite_run_prefix C fn s es` by metis_tac[gas_events_blocks_prefix] >>
  drule (cj 2 finite_prefix_entry) >>
  disch_then (qx_choose_then `p` (qx_choose_then `i` strip_assume_tac)) >>
  qabbrev_tac `q0 = JointConfig [] [] FEMPTY entry_taint fn i p [] FEMPTY []
    [OriginInitial s; OriginObserve (OriginSnapshot fn [] FEMPTY FEMPTY i p)]` >>
  `decoration_entry fn p q0` by simp[Abbr `q0`, decoration_entry_def, decoration_at_def] >>
  `joint_initial vs C q0` by
    (simp[Abbr `q0`] >> irule joint_initial_entry >> gvs[]) >>
  `?w qe. decorated_run_prefix C fn s q0 0 w qe es` by
    (drule (cj 2 finite_prefix_decoration_complete) >>
     disch_then (qspecl_then [`q0`, `0`, `p`] mp_tac) >> simp[]) >>
  `joint_trace vs C q0 (MAP FST w) (MAP SND w) qe` by
    (simp[joint_trace_def] >>
     irule concretizeLayoutStageSimulationTheory.layout_segment_chain >> metis_tac[cj 2 decorated_prefix_segment]) >>
  qexistsl [`p`, `i`, `q0`, `w`, `qe`] >>
  simp[] >>
  drule (cj 2 decorated_prefix_end) >>
  disch_then (CONJUNCTS_THEN2 kall_tac
    (qx_choose_then `fe` (qx_choose_then `ie` (qx_choose_then `se` strip_assume_tac)))) >>
  `LENGTH es = n` by gvs[LENGTH_TAKE] >>
  Cases_on `qe` >>
  gvs[decoration_at_def, joint_state_def, gas_cut_def] >> decide_tac
QED

Theorem fmp_cut_event_cursor[local]:
  joint_trace vs C q0 (MAP FST path) (MAP SND path) qe /\
  gas_cut n vs (joint_state qe) /\ o1_ctx_shape C /\
  decoration_at fe ie se qe /\ ie.inst_opcode = GAS /\
  selected_segment C q0 path k (JointConfig stk PG G tn fn i s oms om hs h) w qr ==>
  frame_reachable vs C stk PG G tn fn i s /\ gas_cut n vs s /\
  ~in_revert_forward fn s
Proof
  strip_tac >>
  drule selected_segment_indices >> strip_tac >>
  `k <= LENGTH path` by decide_tac >>
  `joint_config_reachable vs C (EL k (q0::MAP SND path))` by
    (drule joint_trace_prefix_reachable >>
     disch_then (mp_tac o REWRITE_RULE[EVERY_EL]) >>
     disch_then (qspec_then `k` mp_tac) >> simp[]) >>
  conj_asm1_tac
  >- (gvs[joint_config_reachable_def] >>
      drule joint_origin_history_erasure >> metis_tac[origin_frame_erasure]) >>
  `k <= LENGTH (MAP FST path)` by simp[] >>
  conj_tac
  >- (drule_all trace_config_gas_cut >> gvs[joint_state_def]) >>
  `ALL_DISTINCT (fn_labels fn)` by
    (drule_all frame_reachable_raw_certificate >> strip_tac >>
     fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM]) >>
  Cases_on `qe` >> gvs[decoration_at_def] >>
  `k <= LENGTH (MAP FST path)` by (simp[] >> decide_tac) >>
  metis_tac[joint_trace_gas_nonrevert]
QED

(* Rebase a nonempty event prefix across a silent initial slice. *)
Theorem fmp_cut_event_silent_prefix[local]:
  es <> [] /\ finite_block_prefix C owner bb t1 es /\
  (!fuel. gas_events_block fuel C owner bb t =
          gas_events_block fuel C owner bb t1) ==>
  finite_block_prefix C owner bb t es
Proof
  strip_tac >> drule (cj 1 finite_prefix_realizable) >>
  disch_then (qx_choose_then `k` (qspec_then `k` mp_tac)) >>
  simp[] >> strip_tac >>
  `gas_events_block k C owner bb t = es ++ rest` by metis_tac[] >>
  `0 < LENGTH es /\ LENGTH es <= LENGTH (gas_events_block k C owner bb t)` by
    (Cases_on `es` >> gvs[]) >>
  qspecl_then [`k`, `C`, `owner`, `bb`, `t`, `LENGTH es`] mp_tac
    (cj 2 gas_events_take_prefix) >> simp[TAKE_APPEND1]
QED

Theorem fmp_cut_event_run_here[local]:
  enters_block fn t u /\ lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  finite_block_prefix C fn.fn_name bb u es ==>
  finite_run_prefix C fn t es
Proof
  rw[enters_block_def] >> gvs[] >> irule finite_prefix_run_here >> metis_tac[]
QED

Theorem fmp_cut_event_run_next[local]:
  enters_block fn t u /\ lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block k C bb u = OK post /\ ~post.vs_halted /\
  finite_run_prefix C fn post es ==>
  finite_run_prefix C fn t (gas_events_block k C fn.fn_name bb u ++ es)
Proof
  rw[enters_block_def] >> gvs[] >> irule finite_prefix_run_next >> metis_tac[]
QED

(* The strict endpoint bound is supplied by the actual next instruction. *)
Theorem fmp_cut_event_silent_execution[local]:
  lookup_function name C.ctx_functions = SOME fn /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  EVERY bb_well_formed fn.fn_blocks /\
  t.vs_inst_idx + d < LENGTH bb.bb_instructions /\
  (!k. fmp_target_run k C name t d u) /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS /\
              i.inst_opcode <> INVOKE) (TAKE d (DROP t.vs_inst_idx bb.bb_instructions)) ==>
  !k. exec_block k C bb t = exec_block k C bb u /\
      gas_events_block k C owner bb t = gas_events_block k C owner bb u
Proof
  strip_tac >> gen_tac >>
  metis_tac[fmp_target_run_exec_block, fmp_target_run_gas_events]
QED

Theorem fmp_cut_event_point[local]:
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ fmp_free_ctx C /\
  (!stk PG G tn fn inst s. frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s ==>
     access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
     (?P. fn_static_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
          ptr_use_static_ok P (fn_pv P fn) inst)) /\
  ~vs.vs_halted /\
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s /\
  active_inst fn inst s ==>
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  o1_fn_shape C fn /\ wf_function fn /\ ssa_form fn /\
  make_ssa_input_ok fn /\ pre_fmp_ops fn /\ all_reachable fn /\
  fn.fn_fmp_signature = NONE /\ opaque_use_ok fn /\ ~s.vs_halted /\
  access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
  (?P. fn_static_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
       ptr_use_static_ok P (fn_pv P fn) inst)
Proof
  strip_tac >>
  drule_all frame_reachable_raw_certificate >> strip_tac >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
    (irule fmp_lookup_function_self >>
     fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  `o1_fn_shape C fn /\ ssa_form fn /\ o1_fn_row 3 fn /\
   fn.fn_fmp_signature = NONE` by fs[o1_ctx_shape_def, fmp_free_ctx_def,EVERY_MEM] >>
  `wf_function fn /\ opaque_use_ok fn` by
    fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
  `make_ssa_input_ok fn /\ pre_fmp_ops fn` by fs[o1_fn_row_def] >>
  `all_reachable fn` by fs[make_ssa_input_ok_def] >>
  `~s.vs_halted` by metis_tac[frame_reachable_not_halted] >>
  simp[] >>
  qpat_assum `!stk PG G tn fn inst s. _ ==> access_ok _ _ _ _ _ /\ _`
    (drule_all_then ACCEPT_TAC)
QED

Theorem fmp_cut_event_label[local]:
  fmp_stage_rel D C4 sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  t.vs_current_bb = s.vs_current_bb
Proof
  rw[fmp_stage_rel_def, fmp_frame_rel_def] >> metis_tac[]
QED

(* At an unrestored cursor an active source fetch has a target slot. *)
Theorem fmp_cut_event_active_index[local]:
  active_inst fn i s /\ wf_function fn /\ pre_fmp_ops fn /\
  fn.fn_fmp_signature = NONE /\
  fmp_stage_rel D C4 sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C4.ctx_functions = SOME fn4 /\
  lookup_block t.vs_current_bb fn4.fn_blocks = SOME bb4 ==>
  t.vs_inst_idx < LENGTH bb4.bb_instructions /\
  t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (fs[active_inst_def] >> metis_tac[venomExecPropsTheory.MEM_lookup_block]) >>
  gvs[fmp_stage_rel_def] >> fs[fmp_frame_rel_def] >>
  drule_all fmp_restore_active_bound >> strip_tac >> gvs[]
QED

Theorem fmp_cut_event_silent_successor[local]:
  o1_ctx_shape C4 /\ wf_function fn /\ pre_fmp_ops fn /\
  fn.fn_fmp_signature = NONE /\ active_inst fn j s1 /\
  lookup_function fn.fn_name C4.ctx_functions = SOME fn4 /\
  lookup_block t.vs_current_bb fn4.fn_blocks = SOME bb4 /\
  t1.vs_current_bb = t.vs_current_bb /\
  fmp_stage_rel D C4 sm fmp0 raw0 eom F stk PG G tn fn s1 lo t1 ts /\
  (!k. fmp_target_run k C4 fn.fn_name t d t1) /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS /\
              i.inst_opcode <> INVOKE) (TAKE d (DROP t.vs_inst_idx bb4.bb_instructions)) ==>
  !k. exec_block k C4 bb4 t = exec_block k C4 bb4 t1 /\
      gas_events_block k C4 fn.fn_name bb4 t = gas_events_block k C4 fn.fn_name bb4 t1
Proof
  strip_tac >>
  `t1.vs_inst_idx < LENGTH bb4.bb_instructions` by
    (`lookup_block t1.vs_current_bb fn4.fn_blocks = SOME bb4` by simp[] >>
     drule_all fmp_cut_event_active_index >> simp[]) >>
  `t1.vs_inst_idx = t.vs_inst_idx + d` by
    (qpat_assum `!k. fmp_target_run k _ _ _ _ _`
       (qspec_then `0` (strip_assume_tac o REWRITE_RULE [fmp_target_run_def])) >> simp[]) >>
  `EVERY bb_well_formed fn4.fn_blocks` by
    (`MEM fn4 C4.ctx_functions` by metis_tac[lookup_function_MEM] >>
     `o1_fn_shape C4 fn4` by fs[o1_ctx_shape_def, EVERY_MEM] >>
     fs[o1_fn_shape_def, wf_function_compute]) >>
  metis_tac[fmp_cut_event_silent_execution]
QED

(* The active restored fetch is strictly after the silent restore slice's
   beginning, or at that beginning when the slice is empty. *)
Theorem fmp_cut_event_restore_fetch[local]:
  o1_ctx_shape C /\ lookup_function fn.fn_name C.ctx_functions = SOME fn4 /\
  lookup_block t.vs_current_bb fn4.fn_blocks = SOME bb4 /\
  u.vs_current_bb = t.vs_current_bb /\ u.vs_inst_idx = d + t.vs_inst_idx /\
  active_inst fn4 i u /\ t.vs_inst_idx < LENGTH bb4.bb_instructions /\
  (!fuel. fmp_target_run fuel C fn.fn_name t d u) /\
  (d <> 0 ==> d = 1 /\ ?id v r. EL t.vs_inst_idx bb4.bb_instructions =
                                   mk_inst id ASSIGN [Var v] [r]) ==>
  get_instruction bb4 u.vs_inst_idx = SOME i /\
  (!fuel. exec_block fuel C bb4 t = exec_block fuel C bb4 u /\
    gas_events_block fuel C fn.fn_name bb4 t = gas_events_block fuel C fn.fn_name bb4 u)
Proof
  strip_tac >>
  `MEM fn4 C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `o1_fn_shape C fn4` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `ALL_DISTINCT (fn_labels fn4) /\ EVERY bb_well_formed fn4.fn_blocks` by
    fs[o1_fn_shape_def, wf_function_compute] >>
  `get_instruction bb4 u.vs_inst_idx = SOME i` by
    (drule_all active_inst_block_lookup >> simp[]) >>
  simp[] >>
  `t.vs_inst_idx + d < LENGTH bb4.bb_instructions` by
    (gs[get_instruction_def, AllCaseEqs()] >> decide_tac) >>
  `EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> GAS /\
              j.inst_opcode <> INVOKE) (TAKE d (DROP t.vs_inst_idx bb4.bb_instructions))` by
    (Cases_on `d = 0` >> gs[] >> simp[Once DROP_EL_CONS, mk_inst_def, is_terminator_def]) >>
  drule_all fmp_cut_event_silent_execution >> simp[]
QED

(* Pending completed pieces use their source semantic fuel.  The target
   fuel is independent, and the next consumer can increase it. *)
Theorem fmp_cut_event_completed[local]:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  o1_ctx_shape C3 /\ o1_ctx_shape C4 /\ o1_pre 3 C3 C4 /\
  EVERY ssa_form C3.ctx_functions /\ fmp_free_ctx C3 /\
  callee_first names C3.ctx_functions /\
  (!stk PG G tn fn inst s. frame_reachable vs C3 stk PG G tn fn inst s /\ gas_cut n vs s ==>
     access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
     (?P. fn_static_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
          ptr_use_static_ok P (fn_pv P fn) inst)) /\
  taint_within_upto D n C3 vs /\
  eom <= fmp0 /\ raw0 = w2n vs.vs_fmp /\
  (!f i s. raw_reachable vs C3 f i s /\ gas_cut n vs s ==> dalloca_no_wrap i s) /\
  joint_trace vs C3 root (MAP FST path) (MAP SND path) last /\
  gas_cut n vs (joint_state last) /\ ~vs.vs_halted /\
  (?fe ie se. decoration_at fe ie se last /\ ie.inst_opcode = GAS) ==>
  (!C i s r q a w qe d. decorated_step C i s r q a w qe d ==>
    C = C3 ==>
    !post ev qn k stk PG G tn fn oms om hs h sm lo t ts fn4 bb4.
      r = OK post /\ ~is_terminator i.inst_opcode /\
      q = JointConfig stk PG G tn fn i s oms om hs h /\
      selected_segment C root path a q (w ++ [(ev,qn)]) qn /\
      decoration_consumes C i q post qe ev qn /\
      step_inst k C i s = OK post /\
      lookup_function fn.fn_name C4.ctx_functions = SOME fn4 /\
      lookup_block t.vs_current_bb fn4.fn_blocks = SOME bb4 /\
      fmp_stage_rel D C4 sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
      (* A real active successor, not termination of the suffix. *)
      decoration_entry fn (post with vs_inst_idx := SUC s.vs_inst_idx) qn ==>
      ?b G1 tn1 j oms1 om1 hs1 h1 sm1 lo1 t1.
        qn = JointConfig stk PG G1 tn1 fn j
            (post with vs_inst_idx := SUC s.vs_inst_idx) oms1 om1 hs1 h1 /\
        fmp_stage_rel D C4 sm1 fmp0 raw0 eom F stk PG G1 tn1 fn
          (post with vs_inst_idx := SUC s.vs_inst_idx) lo1 t1 ts /\
        (!m. b <= m ==>
          exec_block m C4 bb4 t = exec_block m C4 bb4 t1 /\
          gas_events_block m C4 fn.fn_name bb4 t =
            gas_events_step k C fn.fn_name i s ++
            gas_events_block m C4 fn.fn_name bb4 t1)) /\
  (!C bb s r q a w qe d. decorated_block C bb s r q a w qe d ==>
    C = C3 ==>
    !k stk PG G tn fn i oms om hs h sm lo t ts fn4 bb4.
      q = JointConfig stk PG G tn fn i s oms om hs h /\
      selected_segment C root path a q w qe /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      exec_block k C bb s = r /\
      ((?post. r = OK post) \/ (?ret send. r = IntRet ret send)) /\
      lookup_function fn.fn_name C4.ctx_functions = SOME fn4 /\
      lookup_block t.vs_current_bb fn4.fn_blocks = SOME bb4 /\
      fmp_stage_rel D C4 sm fmp0 raw0 eom F stk PG G tn fn s lo t ts ==>
      ?m r4 Ge tne ie se omse ome hse he sme le te.
        qe = JointConfig stk PG Ge tne fn ie se omse ome hse he /\
        fmp_stage_rel D C4 sme fmp0 raw0 eom T stk PG Ge tne fn se le te ts /\
        active_inst fn4 ie te /\
        (!j. step_inst j C4 ie te = r4) /\
        exec_block m C4 bb4 t = r4 /\
        gas_events_block m C4 fn.fn_name bb4 t = gas_events_block k C fn.fn_name bb s /\
        (case r of
           OK post => ?lbl. post = jump_to lbl se /\ r4 = OK (jump_to lbl te)
         | IntRet ret send => ?ret4. r4 = IntRet ret4 te /\ ret4.iret_values = ret.iret_values
         | _ => F)) /\
  (!C fn s r q a w qe d. decorated_run C fn s r q a w qe d ==>
    C = C3 ==>
    !k ret send stk PG G tn i se oms om hs h sm lo p t ts fn4.
      r = IntRet ret send /\ q = JointConfig stk PG G tn fn i se oms om hs h /\
      selected_segment C root path a q w qe /\
      run_blocks k C fn s = r /\
      lookup_function fn.fn_name C4.ctx_functions = SOME fn4 /\
      enters_block fn4 p t /\
      fmp_stage_rel D C4 sm fmp0 raw0 eom F stk PG G tn fn se lo t ts ==>
      ?m ret4 Ge tne ie sx omse ome hse he sme le te.
        qe = JointConfig stk PG Ge tne fn ie sx omse ome hse he /\
        fmp_stage_rel D C4 sme fmp0 raw0 eom T stk PG Ge tne fn sx le te ts /\
        active_inst fn4 ie te /\
        (!j. step_inst j C4 ie te = IntRet ret4 te) /\
        ret4.iret_values = ret.iret_values /\
        run_blocks m C4 fn4 p = IntRet ret4 te /\
        gas_events_blocks m C4 fn4 p = gas_events_blocks k C fn s)
Proof
  strip_tac >> ho_match_mp_tac decorated_step_strongind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (rpt strip_tac >>
      gvs[decoration_at_def, decoration_consumes_def, joint_transition_ordinary] >>
      `EVERY (o1_fn_row 3) C.ctx_functions` by fs[o1_pre_def] >>
      drule_all fmp_cut_event_cursor >> strip_tac >>
      drule_all fmp_cut_event_point >> strip_tac >>
      `EVERY (\h. !b z. h = SOME (b,z) /\ 0 < z ==>
                         b + z <= fmp_frame_base (w2n vs.vs_fmp) stk) PG` by
        ((drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`) focus_fmp_frame_sites_upto >>
         disch_then (qspecl_then [`w2n vs.vs_fmp`, `n`] mp_tac) >> simp[] >> (metis_tac[]))) >>
      `terminates (OK post)` by simp[terminates_def] >>
      `i.inst_opcode <> PHI` by (strip_tac >> fs[step_inst_base_opcode_eqs]) >>
      `post.vs_current_bb = s.vs_current_bb` by
        (irule (cj 1 finite_step_nonterminator_control) >>
         simp[finite_step_iff] >> metis_tac[]) >>
      `t.vs_current_bb = s.vs_current_bb` by
        metis_tac[fmp_cut_event_label] >>
      Cases_on `i.inst_opcode = RETPC_PARAM`
      >- (drule_all focus_fmp_retpc_point >> strip_tac >>
          rename1 `!fuel. fmp_target_run fuel C4 fn.fn_name t d t1` >>
          `t1.vs_current_bb = t.vs_current_bb` by
            (qpat_assum `fmp_stage_rel _ _ _ _ _ _ F _ _ _ _ _ _ _ t1 _`
               (mp_tac o MATCH_MP fmp_cut_event_label) >> simp[]) >>
          `EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> GAS /\
                      j.inst_opcode <> INVOKE) (TAKE d (DROP t.vs_inst_idx bb4.bb_instructions))` by
            (gvs[AllCaseEqs(), set_param_index_def, mk_inst_def, is_terminator_def]) >>
          qexistsl [`0`, `sm`, `lo`, `t1`] >> simp[] >>
          drule_all fmp_cut_event_silent_successor >> simp[gas_events_step_plain]) >>
      Cases_on `i.inst_opcode = DALLOCA`
      >- (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ F _ _ _ _ _ _ _ _ _`)
            focus_fmp_cut_restore_prefix >>
          disch_then (qspecl_then [`vs`, `rp`, `n`, `i`, `C`] mp_tac) >>
          simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
          rename1 `!fuel. fmp_target_run fuel C4 fn.fn_name t d u` >>
          `bb' = bb4` by fs[] >> pop_assum SUBST_ALL_TAC >>
          drule_all (SRULE [] (Q.INST [`vs` |-> `vs`, `n` |-> `n`,
                           `raw0` |-> `w2n vs.vs_fmp`, `k` |-> `k`]
                           focus_fmp_cut_dalloca_segment)) >> simp[] >> strip_tac >>
          rename1 `!fuel. fmp_target_run fuel C4 fn.fn_name u 4 t1` >>
          gvs[] >>
          `u.vs_inst_idx < LENGTH bb4.bb_instructions` by
            (CCONTR_TAC >> gvs[NOT_LESS, DROP_LENGTH_TOO_LONG]) >>
          `EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> GAS /\
                      j.inst_opcode <> INVOKE) (TAKE d (DROP t.vs_inst_idx bb4.bb_instructions))` by
            (qpat_x_assum `(case FLOOKUP _ _ of NONE => _ | SOME _ => _)` mp_tac >>
             CASE_TAC >> simp[] >> strip_tac >>
             simp[Once DROP_EL_CONS, mk_inst_def, is_terminator_def]) >>
          `!m. exec_block m C4 bb4 t = exec_block m C4 bb4 u /\
               gas_events_block m C4 fn.fn_name bb4 t = gas_events_block m C4 fn.fn_name bb4 u` by
            (`EVERY bb_well_formed fn4.fn_blocks` by
               (`MEM fn4 C4.ctx_functions` by metis_tac[lookup_function_MEM] >>
                `o1_fn_shape C4 fn4` by fs[o1_ctx_shape_def, EVERY_MEM] >>
                fs[o1_fn_shape_def, wf_function_compute]) >>
             `t.vs_inst_idx + d < LENGTH bb4.bb_instructions` by
               (gs[] >> decide_tac) >>
             `lookup_block t.vs_current_bb fn4.fn_blocks = SOME bb4` by simp[] >>
             drule_all fmp_cut_event_silent_execution >> simp[]) >>
          `t1.vs_current_bb = u.vs_current_bb` by
            (qpat_assum `fmp_stage_rel _ _ _ _ _ _ F _ _ _ _ _ _ _ t1 _`
               (mp_tac o MATCH_MP fmp_cut_event_label) >> simp[]) >>
          `EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> GAS /\
                      j.inst_opcode <> INVOKE) (TAKE 4 (DROP u.vs_inst_idx bb4.bb_instructions))` by
            simp[TAKE_APPEND1, mk_inst_def, is_terminator_def] >>
          `lookup_block u.vs_current_bb fn4.fn_blocks = SOME bb4` by simp[] >>
          drule_all fmp_cut_event_silent_successor >> strip_tac >>
          qrefine `0` >> goal_assum (drule_at Any) >>
          simp[gas_events_step_plain] >> metis_tac[]) >>
      `~MEM i.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI]` by simp[] >>
      drule_all focus_fmp_cut_ordinary_segment >> simp[] >> strip_tac >>
      `bb' = bb4` by fs[] >> pop_assum SUBST_ALL_TAC >>
      gvs[] >>
      rename1 `!f. step_inst f C4 i t = OK u` >>
      qexistsl [`0`, `sm`, `lo`, `u with vs_inst_idx := SUC t.vs_inst_idx`] >> simp[] >>
      `get_instruction bb4 t.vs_inst_idx = SOME i` by
        (`t.vs_inst_idx < LENGTH bb4.bb_instructions` by
           (CCONTR_TAC >> fs[DROP_LENGTH_TOO_LONG]) >>
         fs[Once DROP_EL_CONS, get_instruction_def]) >>
      gen_tac >>
      simp[gas_events_step_plain] >>
      metis_tac[blockSimHelpersTheory.exec_block_step, gas_events_block_nonterminator,
                gas_events_step_plain])
  >- (rpt strip_tac >>
      rename1 `decode_invoke i = SOME (nm,ops)` >>
      rename1 `lookup_function nm C.ctx_functions = SOME callee` >>
      gvs[decoration_at_def, joint_transition_call_iff] >>
      rename1 `enters_block callee cs sc` >>
      qabbrev_tac `qc = JointConfig
        (<|cf_fn := caller; cf_inst := i; cf_state := s; cf_params := PG; cf_prov := G;
            cf_tvar := tn.t_var|> :: stk) (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY)
        callee inst sc (om::oms) FEMPTY (h::hs)
        [OriginCallee cs;
         OriginObserve (OriginSnapshot callee (MAP (op_prov G) ops) FEMPTY FEMPTY inst sc)]` >>
      qabbrev_tac `qs = JointConfig stk PG G tn caller i s oms om hs h` >>
      `joint_transition C qs NONE qc` by simp[Abbr `qs`, Abbr `qc`, joint_transition_call_iff] >>
      drule (cj 3 decorated_execution_segment) >> strip_tac >>
      `joint_transition C qe ev qn` by fs[decoration_consumes_def] >>
      `selected_segment C root path (a+1) qc w qe` by
        (`joint_segment C qs [(NONE,qc)] qc` by simp[joint_segment_def] >>
         qpat_assum `selected_segment C root path a qs _ qn`
           (strip_assume_tac o REWRITE_RULE [selected_segment_def]) >>
         simp[selected_segment_def] >>
         rename1 `joint_segment C root pre qs` >>
         rename1 `path = pre ++ _ ++ suf` >>
         qexistsl [`pre ++ [(NONE,qc)]`, `(ev,qn)::suf`] >>
         simp[APPEND_ASSOC] >> metis_tac[joint_segment_append]) >>
      `finite_run C callee cs (IntRet ret send)` by
        (drule (cj 3 decorated_execution_erases) >> simp[]) >>
      drule_all finite_invoke_return_fuel_inv >> strip_tac >>
      qpat_x_assum `Abbrev (qs = _)` (fn th =>
        RULE_ASSUM_TAC (REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] th])) >>
      `EVERY (o1_fn_row 3) C.ctx_functions` by fs[o1_pre_def] >>
      drule_all fmp_cut_event_cursor >> strip_tac >>
      drule_all fmp_cut_event_point >> strip_tac >>
      `C.ctx_entry <> SOME nm` by (drule_all fmp_invoke_not_entry >> simp[]) >>
      `callee.fn_fmp_signature = NONE` by
        (fs[fmp_free_ctx_def, EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
      drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ F _ _ _ _ _ _ _ _ _`)
        focus_fmp_cut_restore_prefix >>
      disch_then (qspecl_then [`vs`, `rp`, `n`, `i`, `C`] mp_tac) >>
      simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      rename1 `!fuel. fmp_target_run fuel C4 caller.fn_name t d0 u` >>
      drule_all focus_fmp_cut_invoke_push >> strip_tac >>
      `callee.fn_name = nm` by metis_tac[lookup_function_name] >>
      qpat_assum `!k' sm' lo' p t' ts' fn4'. _` (qspec_then `k` mp_tac) >>
      disch_then (drule_at (Pat `enters_block _ _ _`)) >>
      simp[] >> disch_then (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      strip_tac >>
      `local_pending C qe (IntRet ret send)` by
        (drule (cj 3 decorated_execution_intret_endpoint) >> simp[]) >>
      `selected_segment C root path (a+1+LENGTH w) qe [] qe` by
        (qpat_assum `selected_segment C root path (a+1) qc w qe`
           (strip_assume_tac o REWRITE_RULE [selected_segment_def]) >>
         rename1 `joint_segment C root pre qc` >> rename1 `path = pre ++ w ++ suf` >>
         simp[selected_segment_def] >>
         qexistsl [`pre ++ w`, `suf`] >>
         simp[APPEND_ASSOC, joint_segment_def] >> metis_tac[joint_segment_append]) >>
      qpat_x_assum `decoration_consumes _ _ _ _ _ _ _`
        (strip_assume_tac o SRULE [decoration_consumes_def]) >>
      gvs[joint_transition_return, local_pending_def] >>
      `IntRet ret send = IntRet ret' send'` by
        gvs[finite_step_iff, step_inst_non_invoke] >>
      gvs[] >>
      qpat_assum `selected_segment C root path _ _ [] _`
        (mp_then (Pat `selected_segment _ _ _ _ _ _ _`)
          (drule_all_then strip_assume_tac) fmp_cut_event_cursor) >>
      qpat_assum `frame_reachable vs C (_::_) _ _ _ callee ie' sr`
        (mp_then (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)
          (drule_all_then strip_assume_tac) fmp_cut_event_point) >>
      `ie'.inst_opcode = RET` by
        (`MEM ie' (fn_insts callee)` by metis_tac[allocaFrontierBoundTheory.active_inst_mem_fn_insts] >>
         drule step_inst_intret_opcodes >> fs[pre_fmp_ops_def, pre_fmp_opcode_def, EVERY_MEM]) >>
      qpat_assum `fmp_stage_rel D C4 sme _ _ _ T (_::_) _ Ge tne callee sr le te _`
        (mp_then (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
          (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`) o SRULE [])
          focus_fmp_cut_invoke_pop) >>
      disch_then (drule_all_then strip_assume_tac o SRULE []) >>
      `fc' = fn' /\ jr = ret4` by metis_tac[optionTheory.SOME_11, exec_result_11] >>
      gvs[] >>
      `MEM fc' C4.ctx_functions` by
        (irule lookup_function_MEM >> goal_assum (drule_at Any)) >>
      `o1_fn_shape C4 fc'` by fs[o1_ctx_shape_def, EVERY_MEM] >>
      `wf_function fc'` by fs[o1_fn_shape_def] >>
      `ALL_DISTINCT (fn_labels fc') /\ EVERY bb_well_formed fc'.fn_blocks` by
        fs[wf_function_compute] >>
      `get_instruction bb'' u.vs_inst_idx = SOME j` by
        (qpat_assum `active_inst fc' j u` (mp_then Any mp_tac active_inst_block_lookup) >>
         simp[]) >>
      `EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> GAS /\
                  j.inst_opcode <> INVOKE) (TAKE d0 (DROP t.vs_inst_idx bb''.bb_instructions))` by
        (qpat_x_assum `(case FLOOKUP _ _ of NONE => _ | SOME _ => _)` mp_tac >>
         CASE_TAC >> simp[] >> strip_tac >>
         simp[Once DROP_EL_CONS, mk_inst_def, is_terminator_def]) >>

      `t.vs_inst_idx + d0 < LENGTH bb''.bb_instructions` by (gs[] >> decide_tac) >>
      drule_all fmp_cut_event_silent_execution >> strip_tac >>
      qexists `m` >> goal_assum (drule_at Any) >>
      qx_gen_tac `fuel4` >> strip_tac >>
      `run_blocks fuel4 C4 callee' cs' = IntRet jr te /\
       gas_events_blocks fuel4 C4 callee' cs' = gas_events_blocks k C callee cs` by
        (qspecl_then [`m`,`C4`,`callee'`,`cs'`,`fuel4`] mp_tac
           (cj 3 gas_events_fuel_extension) >> simp[]) >>
      `j = EL u.vs_inst_idx bb''.bb_instructions` by
        (qpat_x_assum `get_instruction bb'' u.vs_inst_idx = SOME j` mp_tac >>
         simp[get_instruction_def, EQ_SYM_EQ]) >>
      `decode_invoke j = SOME (callee.fn_name,
          ops ++ if IS_SOME (fmp_stage_root ci cc callee) then [Var r] else [])` by
        (qpat_assum `j = EL _ _` (fn th => simp[th])) >>
      `step_inst fuel4 C4 j u = OK t1'` by simp[Once step_inst_def] >>
      `gas_events_step fuel4 C4 caller.fn_name j u =
       gas_events_step k C caller.fn_name i s` by
        (CONV_TAC (BINOP_CONV (REWR_CONV gas_events_step_def)) >> simp[]) >>
      `~is_terminator j.inst_opcode` by simp[is_terminator_def] >>
      metis_tac[blockSimHelpersTheory.exec_block_step, gas_events_block_nonterminator])
  >- simp[]
  >- simp[]
  >- (Cases_on `post.vs_halted` >> simp[] >> rpt strip_tac >>
      gvs[decoration_at_def] >>
      `finite_step C i s (OK post)` by
        (drule (cj 1 decorated_execution_erases) >> simp[]) >>
      `step_inst k C i s = OK post` by
        (irule finite_block_step_fuel_inv >> reverse conj_tac >- simp[] >>
         qexistsl [`bb`, `OK post`] >> simp[]) >>
      `MEM i.inst_opcode [JMP; JNZ; DJMP]` by
        metis_tac[lowerDloadNormalJumpTheory.ld_successful_terminator_branch] >>
      `EVERY (o1_fn_row 3) C.ctx_functions` by fs[o1_pre_def] >>
      drule_all fmp_cut_event_cursor >> strip_tac >>
      drule_all fmp_cut_event_point >> strip_tac >>
      drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ F _ _ _ _ _ _ _ _ _`)
        focus_fmp_cut_restore_prefix >>
      disch_then (qspecl_then [`vs`, `rp`, `n`, `i`, `C`] mp_tac) >>
      simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      `terminates (OK post)` by simp[terminates_def] >>
      drule_all focus_fmp_jump_point >> strip_tac >>
      `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS` by fs[] >>
      `qe = JointConfig stk PG G tn fn i s oms om hs h` by
        (drule (cj 1 decorated_execution_frame) >> simp[]) >>
      rename1 `!fuel. fmp_target_run fuel C4 fn.fn_name t d0 u` >>
      `(d0 <> 0 ==> d0 = 1 /\ ?id v r. EL t.vs_inst_idx bb4.bb_instructions =
                                     mk_inst id ASSIGN [Var v] [r])` by
        (qpat_x_assum `(case FLOOKUP _ _ of NONE => _ | SOME _ => _)` mp_tac >>
         CASE_TAC >> simp[] >> metis_tac[]) >>
      drule_all fmp_cut_event_restore_fetch >> strip_tac >>
      `~u.vs_halted` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
      `exec_block 0 C4 bb4 t = OK (jump_to lbl u)` by
        (qpat_assum `!fuel. exec_block fuel C4 bb4 t = _ /\ _`
           (qspec_then `0` strip_assume_tac) >>
         simp[Once exec_block_def, venomStepPropsTheory.jump_to_halted]) >>
      `gas_events_block 0 C4 fn.fn_name bb4 t = []` by
        (qpat_assum `!fuel. _ /\ gas_events_block fuel C4 fn.fn_name bb4 t = _`
           (qspec_then `0` strip_assume_tac) >>
         drule gas_events_block_at >> simp[gas_events_step_plain]) >>
      `gas_events_block k C fn.fn_name bb s = []` by
        (qpat_assum `get_instruction bb s.vs_inst_idx = SOME i`
           (mp_then Any mp_tac gas_events_block_at) >> simp[gas_events_step_plain]) >>
      qexistsl [`0`,`G`,`tn`,`i`,`s`,`oms`,`om`,`hs`,`h`] >>
      simp[] >> goal_assum (drule_at Any) >>
      goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ T _ _ _ _ _ _ _ _ _`)) >>
      fs[] >> qexists `lbl` >> fs[])
  >- (disch_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gnvs[decoration_at_def] >>
      qmatch_asmsub_abbrev_tac `decoration_consumes C i q post qe ev q'` >>
      `finite_step C i s (OK post)` by
        (drule (cj 1 decorated_execution_erases) >> simp[]) >>
      qabbrev_tac `rb = exec_block k C bb s` >>
      `!e. rb <> Error e` by
        (qpat_assum `(?v. rb = OK v) \/ _` strip_assume_tac >> simp[]) >>
      `step_inst k C i s = OK post` by
        (irule finite_block_step_fuel_inv >> reverse conj_tac >- simp[] >>
         qexistsl [`bb`, `rb`] >> simp[Abbr `rb`]) >>
      `exec_block k C bb (post with vs_inst_idx := SUC s.vs_inst_idx) = rb` by
        (simp[Abbr `rb`] >> simp[SimpRHS, Once exec_block_def]) >>
      `joint_segment C q w qe` by
        (drule (cj 1 decorated_execution_segment) >> simp[]) >>
      `joint_segment C q' w' qe'` by
        (drule (cj 2 decorated_execution_segment) >> simp[]) >>
      `joint_transition C qe ev q'` by fs[decoration_consumes_def] >>
      `selected_segment C root path a q (w ++ [(ev,q')]) q' /\
       selected_segment C root path (a + LENGTH w + 1) q' w' qe'` by
        (`joint_segment C q (w ++ [(ev,q')]) q'` by
           (irule joint_segment_append >> qexists `qe` >> simp[joint_segment_def]) >>
         drule_all (Q.INST [`u` |-> `w ++ [(ev,q')]`, `v` |-> `w'`] selected_segment_parts) >>
         simp[]) >>
      qpat_assum `!ev' qn k' sm' lo' t' ts' bb4'. _` (drule_all_then strip_assume_tac) >>
      drule_all finite_step_nonterminator_control >> strip_tac >>
      `lookup_block t1.vs_current_bb fn4.fn_blocks = SOME bb4` by
        ((qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ (post with vs_inst_idx := _) _ t1 _`
           (mp_tac o MATCH_MP fmp_cut_event_label) >>
         qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ t _`
           (mp_tac o MATCH_MP fmp_cut_event_label) >> strip_tac >> simp[] >> (gvs[]))) >>
      `lookup_block post.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
      qpat_assum `!k' stk' PG' G' tn' fn'' i'' oms' om' hs' h' sm' lo' t' ts' fn4' bb4'. _`
        (drule_all_then strip_assume_tac o REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
      `!err. exec_block m C4 bb4 t1 <> Error err` by
        (Cases_on `rb` >> gvs[]) >>
      qspecl_then [`m`, `C4`, `fn.fn_name`, `bb4`, `t1`, `m + b`] mp_tac
        (cj 2 gas_events_fuel_extension) >> simp[] >> strip_tac >>
      qexistsl [`m + b`, `sme`, `le`, `te`] >>
      simp[] >> simp[SimpRHS, Once gas_events_block_def])
  >- (disch_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gnvs[decoration_at_def] >>
      qpat_assum `?ret send. exec_block _ _ _ _ = IntRet ret send` strip_assume_tac >>
      rename1 `exec_block k C bb s = IntRet ir sr` >>
      `finite_step C i s (IntRet ir sr)` by
        (drule (cj 1 decorated_execution_erases) >> simp[]) >>
      `step_inst k C i s = IntRet ir sr` by
        (irule finite_block_step_fuel_inv >> simp[] >>
         qexists `bb` >> simp[]) >>
      `EVERY (o1_fn_row 3) C.ctx_functions` by fs[o1_pre_def] >>
      drule_all fmp_cut_event_cursor >> strip_tac >>
      `active_inst fn i s` by fs[] >>
      drule_all fmp_cut_event_point >> strip_tac >>
      `i.inst_opcode = RET` by
        (`MEM i (fn_insts fn)` by metis_tac[allocaFrontierBoundTheory.active_inst_mem_fn_insts] >>
         drule step_inst_intret_opcodes >> fs[pre_fmp_ops_def, pre_fmp_opcode_def, EVERY_MEM]) >>
      drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ F _ _ _ _ _ _ _ _ _`)
        focus_fmp_cut_restore_prefix >>
      disch_then (qspecl_then [`vs`, `rp`, `n`, `i`, `C`] mp_tac) >>
      simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      drule_all fmp_focus_ret_point >> strip_tac >>
      `qe = JointConfig stk PG G tn fn i s oms om hs h` by
        (drule (cj 1 decorated_execution_frame) >> simp[]) >>
      rename1 `!fuel. fmp_target_run fuel C4 fn.fn_name t d0 u` >>
      `(d0 <> 0 ==> d0 = 1 /\ ?id v r. EL t.vs_inst_idx bb4.bb_instructions =
                                     mk_inst id ASSIGN [Var v] [r])` by
        (qpat_x_assum `(case FLOOKUP _ _ of NONE => _ | SOME _ => _)` mp_tac >>
         CASE_TAC >> simp[] >> metis_tac[]) >>
      drule_all fmp_cut_event_restore_fetch >> strip_tac >>
      `exec_block 0 C4 bb4 t = IntRet jr u` by
        (qpat_assum `!fuel. exec_block fuel C4 bb4 t = _ /\ _`
           (qspec_then `0` strip_assume_tac) >> simp[Once exec_block_def]) >>
      `gas_events_block 0 C4 fn.fn_name bb4 t = []` by
        (qpat_assum `!fuel. _ /\ gas_events_block fuel C4 fn.fn_name bb4 t = _`
           (qspec_then `0` strip_assume_tac) >>
         drule gas_events_block_at >> simp[gas_events_step_plain]) >>
      `gas_events_block k C fn.fn_name bb s = []` by
        (qpat_assum `get_instruction bb s.vs_inst_idx = SOME i`
           (mp_then Any mp_tac gas_events_block_at) >> simp[gas_events_step_plain]) >>
      qexistsl [`0`, `G`, `tn`, `i`, `s`, `oms`, `om`, `hs`, `h`] >>
      simp[] >> goal_assum (drule_at Any) >>
      goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ T _ _ _ _ _ _ _ _ _`)) >>
      simp[])
  >- (disch_then SUBST_ALL_TAC >> rpt gen_tac >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      gnvs[decoration_entry_def, decoration_at_def] >>
      rename1 `eval_phis entry bb.bb_instructions = OK phi` >>
      rename1 `decorated_run C3 fn post (IntRet ret send) qn _ wr qend _` >>
      `finite_block C3 bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
         (OK post)` by (drule (cj 2 decorated_execution_erases) >> simp[]) >>
      `?h0. k = SUC h0 /\ exec_block h0 C3 bb
           (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK post` by
        (irule finite_run_block_fuel_inv >> simp[] >> qexists `fn` >> simp[] >>
         qexists `entry` >> simp[]) >>
      gvs[] >>
      `run_blocks h0 C3 fn post = IntRet ret send` by
        (drule_all run_blocks_at >>
         disch_then (qspecl_then [`h0`, `C3`] mp_tac) >> simp[]) >>
      `lookup_block phi.vs_current_bb fn.fn_blocks = SOME bb` by
        metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
      drule (cj 2 decorated_execution_segment) >> strip_tac >>
      `joint_segment C3 qn wr qend` by (drule (cj 3 decorated_execution_segment) >> simp[]) >>
      drule_all (SRULE [] selected_segment_edge) >> strip_tac >>
      drule lowerDloadSafetyAmbientTheory.ld_enters_block_alignment >>
      disch_then (qx_choose_then `bb4` (qx_choose_then `phi4` strip_assume_tac)) >>
      `lookup_block t.vs_current_bb fn4.fn_blocks = SOME bb4` by simp[] >>
      qpat_assum `!kb smb lob tb tsb bb4. _ ==> ?mb smb' lb' tb'. _`
        (drule_all_then strip_assume_tac) >>
      `selected_segment C3 root path (a + LENGTH w)
         (JointConfig stk PG G tn fn i si oms om hs h) []
         (JointConfig stk PG G tn fn i si oms om hs h)` by
        (qpat_assum `selected_segment _ _ _ a _ w _`
           (strip_assume_tac o REWRITE_RULE [selected_segment_def]) >>
         rename1 `path = pre ++ w ++ suffix` >>
         simp[Once selected_segment_def] >> qexistsl [`pre ++ w`, `suffix`] >>
         simp[joint_segment_def, APPEND_ASSOC] >> metis_tac[joint_segment_append]) >>
      `frame_reachable vs C3 stk PG G tn fn i si /\ gas_cut n vs si` by
        (drule_all fmp_cut_event_cursor >> simp[]) >>
      `EVERY (o1_fn_row 3) C3.ctx_functions` by fs[o1_pre_def] >>
      drule_all fmp_cut_event_point >> strip_tac >>
      `fn_inst_wf fn /\ first_block_no_preds fn /\
       (C3.ctx_entry = SOME fn.fn_name ==> entry_fn_no_params fn)` by
        fs[o1_fn_shape_def] >>
      qpat_x_assum `joint_transition _ _ (SOME (OriginBlock _ _)) _`
        (strip_assume_tac o REWRITE_RULE [joint_transition_block_iff]) >>
      gvs[] >>
      `MEM i.inst_opcode [JMP; JNZ; DJMP]` by
        metis_tac[lowerDloadNormalJumpTheory.ld_successful_terminator_branch] >>
      drule_all focus_fmp_cut_jump_entry >> strip_tac >>
      qpat_assum `!k' sm' lo' p' t' ts'. _ ==> ?m ret4 Ge tne ie sx omse ome hse he sme le te. _`
        (drule_all_then strip_assume_tac) >>
      `~(jump_to lbl te).vs_halted` by fs[jump_to_def, fmp_stage_rel_def] >>
      `run_block_non_phis (m + m') C4 bb4
          (phi4 with vs_inst_idx := phi_prefix_length bb4.bb_instructions) = OK (jump_to lbl te) /\
       gas_events_block (m + m') C4 fn.fn_name bb4
          (phi4 with vs_inst_idx := phi_prefix_length bb4.bb_instructions) =
       gas_events_block m C4 fn.fn_name bb4
          (phi4 with vs_inst_idx := phi_prefix_length bb4.bb_instructions)` by
        (qspecl_then [`m`, `C4`, `fn.fn_name`, `bb4`,
            `phi4 with vs_inst_idx := phi_prefix_length bb4.bb_instructions`, `m + m'`] mp_tac
           (cj 2 gas_events_fuel_extension) >> simp[]) >>
      `run_blocks (m + m') C4 fn4 (jump_to lbl te) = IntRet ret4 te' /\
       gas_events_blocks (m + m') C4 fn4 (jump_to lbl te) =
       gas_events_blocks h0 C3 fn (jump_to lbl si)` by
        (qspecl_then [`m'`, `C4`, `fn4`, `jump_to lbl te`, `m + m'`] mp_tac
           (cj 3 gas_events_fuel_extension) >> simp[]) >>
      qexistsl [`SUC (m + m')`, `ret4`, `Ge`, `tne`, `ie'`, `sx`, `omse`, `ome`, `hse`, `he`,
                `sme'`, `le'`, `te'`] >>
      simp[] >> conj_tac
      >- (simp[Once run_blocks_def]) >>
      `fn4.fn_name = fn.fn_name` by metis_tac[lookup_function_name] >>
      CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [gas_events_blocks_def])) >> simp[]) >>
  disch_then SUBST_ALL_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gnvs[decoration_entry_def, decoration_at_def] >>
  rename1 `eval_phis entry bb.bb_instructions = OK phi` >>
  `finite_block C3 bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
     (IntRet ret send)` by (drule (cj 2 decorated_execution_erases) >> simp[]) >>
  `?h0. k = SUC h0 /\ exec_block h0 C3 bb
       (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = IntRet ret send` by
    (irule finite_run_block_fuel_inv >> simp[] >> qexists `fn` >> simp[] >>
     qexists `entry` >> simp[]) >>
  gvs[] >>
  `lookup_block phi.vs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  drule lowerDloadSafetyAmbientTheory.ld_enters_block_alignment >>
  disch_then (qx_choose_then `bb4` (qx_choose_then `phi4` strip_assume_tac)) >>
  `lookup_block t.vs_current_bb fn4.fn_blocks = SOME bb4` by simp[] >>
  qpat_assum `!kb smb lob tb tsb bb4. _ ==> ?mb Ge tne ie se omse ome hse he sme le te. _`
    (drule_all_then strip_assume_tac) >>
  gvs[] >>
  qexistsl [`SUC m`, `ret4`, `sme`, `le`, `te`] >>
  simp[] >> conj_tac
  >- simp[Once run_blocks_def] >>
  `fn4.fn_name = fn.fn_name` by metis_tac[lookup_function_name] >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [gas_events_blocks_def])) >> simp[]
QED

Theorem fmp_cut_event_prefix:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  o1_ctx_shape C3 /\ o1_ctx_shape C4 /\ o1_pre 3 C3 C4 /\
  EVERY ssa_form C3.ctx_functions /\ fmp_free_ctx C3 /\
  callee_first names C3.ctx_functions /\
  (!stk PG G tn fn inst s.
    frame_reachable vs C3 stk PG G tn fn inst s /\ gas_cut n vs s ==>
    access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
    (?P. fn_static_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
         ptr_use_static_ok P (fn_pv P fn) inst)) /\
  taint_within_upto D n C3 vs /\
  eom <= fmp0 /\ raw0 = w2n vs.vs_fmp /\
  (!f i s. raw_reachable vs C3 f i s /\ gas_cut n vs s ==> dalloca_no_wrap i s) /\
  joint_trace vs C3 root (MAP FST path) (MAP SND path) last /\
  gas_cut n vs (joint_state last) /\ ~vs.vs_halted /\
  (?fe ie se. decoration_at fe ie se last /\ ie.inst_opcode = GAS) ==>
  (!C owner bb s q a w qe es. decorated_block_prefix C owner bb s q a w qe es ==>
    C = C3 ==>
    !stk PG G tn fn i oms om hs h sm lo t ts fn4 bb4.
      q = JointConfig stk PG G tn fn i s oms om hs h /\ owner = fn.fn_name /\
      selected_segment C root path a q w qe /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      lookup_function fn.fn_name C4.ctx_functions = SOME fn4 /\
      lookup_block t.vs_current_bb fn4.fn_blocks = SOME bb4 /\
      fmp_stage_rel D C4 sm fmp0 raw0 eom F stk PG G tn fn s lo t ts ==>
      finite_block_prefix C4 owner bb4 t es) /\
  (!C fn s q a w qe es. decorated_run_prefix C fn s q a w qe es ==>
    C = C3 ==>
    !stk PG G tn i se oms om hs h sm lo p t ts fn4.
      q = JointConfig stk PG G tn fn i se oms om hs h /\
      selected_segment C root path a q w qe /\
      lookup_function fn.fn_name C4.ctx_functions = SOME fn4 /\
      (?u. enters_block fn4 p u /\ t.vs_current_bb = u.vs_current_bb /\
           !bb k. lookup_block p.vs_current_bb fn4.fn_blocks = SOME bb ==>
             exec_block k C4 bb u = exec_block k C4 bb t /\
             gas_events_block k C4 fn.fn_name bb u =
             gas_events_block k C4 fn.fn_name bb t) /\
      fmp_stage_rel D C4 sm fmp0 raw0 eom F stk PG G tn fn se lo t ts ==>
      finite_run_prefix C4 fn4 p es)
Proof
  disch_then (fn th =>
    strip_assume_tac (MATCH_MP fmp_cut_event_completed th) >> strip_assume_tac th) >>
  ho_match_mp_tac decorated_prefix_strongind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (rpt strip_tac >> gvs[decoration_at_def] >>
      drule_all fmp_cut_event_cursor >> strip_tac >>
      `EVERY (o1_fn_row 3) C.ctx_functions` by fs[o1_pre_def] >>
      `active_inst fn i s` by metis_tac[active_inst_def] >>
      drule_all fmp_cut_event_point >> strip_tac >>
      drule_all focus_fmp_gas_pair >> strip_tac >>
      irule finite_prefix_gas >> metis_tac[optionTheory.SOME_11])
  >- suspend "invoke"
  >- suspend "next"
  >- (disch_then SUBST_ALL_TAC >> rpt gen_tac >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      gnvs[decoration_entry_def, decoration_at_def] >>
      `lookup_block phi.vs_current_bb fn.fn_blocks = SOME bb` by
        metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
      qpat_x_assum `?u. enters_block fn4 p u /\ _` (qx_choose_then `u` strip_assume_tac) >>
      drule lowerDloadSafetyAmbientTheory.ld_enters_block_alignment >>
      disch_then (qx_choose_then `bb4` (qx_choose_then `phi4` strip_assume_tac)) >>
      `lookup_block t.vs_current_bb fn4.fn_blocks = SOME bb4` by simp[] >>
      `finite_block_prefix C4 fn.fn_name bb4 t es` by metis_tac[] >>
      `es <> []` by (drule (cj 1 decorated_prefix_end) >> simp[]) >>
      `fn4.fn_name = fn.fn_name` by metis_tac[lookup_function_name] >>
      irule fmp_cut_event_run_here >> qexistsl [`bb4`, `u`] >> simp[] >>
      irule fmp_cut_event_silent_prefix >> simp[] >> qexists `t` >> simp[] >>
      qpat_x_assum `u = _ with vs_inst_idx := _` (SUBST1_TAC o SYM) >> simp[])
  >> suspend "run_next"
QED

Resume fmp_cut_event_prefix[invoke]:
  rpt strip_tac >>
  rename1 `decode_invoke i = SOME (nm,ops)` >>
  rename1 `lookup_function nm C.ctx_functions = SOME callee` >>
  gvs[decoration_at_def] >>
  rename1 `decorated_run_prefix C callee cs qc (a + 1) wc qe es` >>
  `joint_segment C qc wc qe` by (drule (cj 2 decorated_prefix_segment) >> simp[]) >>
  `selected_segment C root path (a+1) qc wc qe` by
    (`joint_segment C (JointConfig stk PG G tn caller i s oms om hs h) [(NONE,qc)] qc` by
       simp[joint_segment_def] >>
     drule_all (SRULE [] (Q.INST [`u` |-> `[(NONE,qc)]`, `v` |-> `wc`] selected_segment_parts)) >>
     simp[]) >>
  qpat_x_assum `joint_transition C _ NONE qc`
    (strip_assume_tac o REWRITE_RULE [joint_transition_call_iff]) >>
  gnvs[] >>
  rename1 `enters_block callee cs sc` >>
  `EVERY (o1_fn_row 3) C.ctx_functions` by fs[o1_pre_def] >>
  `frame_reachable vs C stk PG G tn caller i s /\ gas_cut n vs s /\
    ~in_revert_forward caller s` by
    (irule fmp_cut_event_cursor >> simp[] >> metis_tac[]) >>
  drule_all fmp_cut_event_point >> strip_tac >>
  `C.ctx_entry <> SOME nm` by (drule_all fmp_invoke_not_entry >> simp[]) >>
  `callee.fn_fmp_signature = NONE` by
    (fs[fmp_free_ctx_def, EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ F _ _ _ _ _ _ _ _ _`)
    focus_fmp_cut_restore_prefix >>
  disch_then (qspecl_then [`vs`, `rp`, `n`, `i`, `C`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  rename1 `!fuel. fmp_target_run fuel C4 caller.fn_name t d0 u` >>
  drule_all focus_fmp_cut_invoke_push >> strip_tac >>
  `callee.fn_name = nm` by metis_tac[lookup_function_name] >>
  `finite_run_prefix C4 callee' cs' es` by
    (first_assum irule >> simp[] >> metis_tac[]) >>
  `fn' = fn4` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `fn' = fn4` SUBST_ALL_TAC >>
  `bb'' = bb4` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `bb'' = bb4` SUBST_ALL_TAC >>
  `(d0 <> 0 ==> d0 = 1 /\ ?id v r. EL t.vs_inst_idx bb4.bb_instructions =
                                     mk_inst id ASSIGN [Var v] [r])` by
    (qpat_x_assum `(case FLOOKUP _ _ of NONE => _ | SOME _ => _)` mp_tac >>
     CASE_TAC >> simp[] >> metis_tac[]) >>
  drule_all fmp_cut_event_restore_fetch >> strip_tac >>
  `finite_block_prefix C4 caller.fn_name bb4 u es` by
    (irule finite_prefix_invoke >> metis_tac[]) >>
  irule fmp_cut_event_silent_prefix >> conj_tac
  >- (drule (cj 2 decorated_prefix_end) >> simp[]) >>
  qexists `u` >> simp[]
QED

Resume fmp_cut_event_prefix[next]:
  disch_then SUBST_ALL_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gnvs[decoration_at_def] >>
  qmatch_asmsub_abbrev_tac `decoration_consumes C i q post qm ev qn` >>
  `joint_segment C q ws qm` by
    (drule (cj 1 decorated_execution_segment) >> simp[]) >>
  `joint_segment C qn w qe` by
    (drule (cj 1 decorated_prefix_segment) >> simp[]) >>
  `joint_transition C qm ev qn` by fs[decoration_consumes_def] >>
  `selected_segment C root path a q (ws ++ [(ev,qn)]) qn /\
   selected_segment C root path (a + LENGTH ws + 1) qn w qe` by
    (`joint_segment C q (ws ++ [(ev,qn)]) qn` by
       (irule joint_segment_append >> qexists `qm` >> simp[joint_segment_def]) >>
     drule_all (Q.INST [`u` |-> `ws ++ [(ev,qn)]`, `v` |-> `w`] selected_segment_parts) >>
     simp[]) >>
  simp[Abbr `q`] >>
  first_assum (drule_at_then (Pat `decorated_step _ _ _ _ _ _ _ _ _`) mp_tac) >>
  simp[] >> disch_then (drule_all_then strip_assume_tac) >>
  `finite_step C i s (OK post)` by
    (drule (cj 1 decorated_execution_erases) >> simp[]) >>
  drule_all finite_step_nonterminator_control >> strip_tac >>
  `lookup_block t1.vs_current_bb fn4.fn_blocks = SOME bb4` by
    (qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ (post with vs_inst_idx := _) _ t1 _`
       (mp_tac o MATCH_MP fmp_cut_event_label) >>
     qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ t _`
       (mp_tac o MATCH_MP fmp_cut_event_label) >> strip_tac >> simp[] >> gvs[]) >>
  `lookup_block post.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  `finite_block_prefix C4 fn.fn_name bb4 t1 es` by
    (first_assum (irule o REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ t1 _`))) >>
  drule (cj 1 finite_prefix_realizable) >>
  disch_then (qx_choose_then `c` (qspec_then `b + c` mp_tac)) >>
  simp[] >> strip_tac >>
  `es <> []` by (drule (cj 1 decorated_prefix_end) >> simp[]) >>
  qabbrev_tac `l = gas_events_step k C fn.fn_name i s ++ es` >>
  `gas_events_block (b + c) C4 fn.fn_name bb4 t = l ++ rest` by
    simp[Abbr `l`, APPEND_ASSOC] >>
  qspecl_then [`b + c`, `C4`, `fn.fn_name`, `bb4`, `t`, `LENGTH l`] mp_tac
    (cj 2 gas_events_take_prefix) >>
  `0 < LENGTH es` by (Cases_on `es` >> gvs[]) >>
  simp[TAKE_APPEND1, TAKE_LENGTH_TOO_LONG, Abbr `l`]
QED

Resume fmp_cut_event_prefix[run_next]:
  disch_then SUBST_ALL_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gnvs[decoration_entry_def, decoration_at_def] >>
  `lookup_block phi.vs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  drule (cj 2 decorated_execution_segment) >> strip_tac >>
  drule (cj 2 decorated_prefix_segment) >> strip_tac >>
  drule_all (SRULE [] selected_segment_edge) >> strip_tac >>
  qpat_x_assum `?u. enters_block fn4 p u /\ _` (qx_choose_then `u` strip_assume_tac) >>
  drule lowerDloadSafetyAmbientTheory.ld_enters_block_alignment >>
  disch_then (qx_choose_then `bb4` (qx_choose_then `phi4` strip_assume_tac)) >>
  `lookup_block t.vs_current_bb fn4.fn_blocks = SOME bb4` by simp[] >>
  first_assum (drule_at_then (Pat `decorated_block _ _ _ _ _ _ _ _ _`) mp_tac) >>
  simp[] >> disch_then (drule_all_then strip_assume_tac) >>
  `selected_segment C3 root path (a + LENGTH wb)
     (JointConfig stk PG G tn fn i si oms om hs h) []
     (JointConfig stk PG G tn fn i si oms om hs h)` by
    (qpat_assum `selected_segment _ _ _ a _ wb _`
       (strip_assume_tac o REWRITE_RULE [selected_segment_def]) >>
     rename1 `path = pre ++ wb ++ suffix` >>
     simp[Once selected_segment_def] >> qexistsl [`pre ++ wb`, `suffix`] >>
     simp[joint_segment_def, APPEND_ASSOC] >> metis_tac[joint_segment_append]) >>
  `frame_reachable vs C3 stk PG G tn fn i si /\ gas_cut n vs si` by
    (drule_all fmp_cut_event_cursor >> simp[]) >>
  `EVERY (o1_fn_row 3) C3.ctx_functions` by fs[o1_pre_def] >>
  drule_all fmp_cut_event_point >> strip_tac >>
  `fn_inst_wf fn /\ first_block_no_preds fn /\
   (C3.ctx_entry = SOME fn.fn_name ==> entry_fn_no_params fn)` by fs[o1_fn_shape_def] >>
  qpat_x_assum `joint_transition _ _ (SOME (OriginBlock _ _)) _`
    (strip_assume_tac o REWRITE_RULE [joint_transition_block_iff]) >>
  gvs[] >>
  `MEM i.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[lowerDloadNormalJumpTheory.ld_successful_terminator_branch] >>
  drule_all focus_fmp_cut_jump_entry >> strip_tac >>
  `finite_run_prefix C4 fn4 (jump_to lbl te) es` by
    (first_assum irule >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `~(jump_to lbl te).vs_halted` by fs[jump_to_def, fmp_stage_rel_def] >>
  `fn4.fn_name = fn.fn_name` by metis_tac[lookup_function_name] >>
  qabbrev_tac `pre = phi4 with vs_inst_idx := phi_prefix_length bb4.bb_instructions` >>
  `exec_block m C4 bb4 pre = OK (jump_to lbl te) /\
   gas_events_block m C4 fn4.fn_name bb4 pre = gas_events_block m C4 fn.fn_name bb4 t` by
    (qpat_assum `!k. exec_block k C4 bb4 pre = _ /\ _` (qspec_then `m` mp_tac) >> simp[]) >>
  drule_all fmp_cut_event_run_next >> simp[]
QED

Finalise fmp_cut_event_prefix[local]

(* The root cursor can be one instruction past the actual block entry. *)
Theorem fmp_cut_event_root_slice[local]:
  lookup_function name C.ctx_functions = SOME fn' /\ fn_entry_label fn' = SOME lbl /\
  wf_function fn' /\ first_block_no_phi fn' /\
  p = v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  (!k. fmp_target_run k C name p d t) /\
  (!bb. lookup_block lbl fn'.fn_blocks = SOME bb ==> t.vs_inst_idx < LENGTH bb.bb_instructions) /\
  ((d = 0 /\ t = p) \/
   (d = 1 /\ ?bb id runner tail.
     lookup_block lbl fn'.fn_blocks = SOME bb /\
     bb.bb_instructions = mk_inst id INITIAL_FMP [] [runner]::tail /\
     t = (update_var runner v.vs_initial_fmp v) with
         <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 1|>)) ==>
  ?u. enters_block fn' p u /\ t.vs_current_bb = u.vs_current_bb /\
      !bb k. lookup_block p.vs_current_bb fn'.fn_blocks = SOME bb ==>
        exec_block k C bb u = exec_block k C bb t /\
        gas_events_block k C owner bb u = gas_events_block k C owner bb t
Proof
  strip_tac >> qexists `p` >> gvs[o1LowerDloadSourceEntryTheory.dload_no_phi_entry] >>
  irule fmp_cut_event_silent_execution >>
  qexistsl [`1`, `fn'`, `name`] >> simp[] >>
  fs[wf_function_def, EVERY_MEM, mk_inst_def, is_terminator_def]
QED

Theorem focus_fmp_cut_prefix_events_fields:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  o1_ctx_shape C3 /\ o1_ctx_shape C4 /\ o1_pre 3 C3 C4 /\
  EVERY ssa_form C3.ctx_functions /\ fmp_free_ctx C3 /\
  callee_first names C3.ctx_functions /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  o1_initial_state_ok v /\ v.vs_fmp = v.vs_initial_fmp /\ code_layout_valid v /\
  eom <= w2n v.vs_initial_fmp /\ w2n v.vs_initial_fmp <= w2n fmp /\
  vs = v with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  (!stk PG G tn fn inst s.
    frame_reachable vs C3 stk PG G tn fn inst s /\ gas_cut n vs s ==>
    access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
    (?P. fn_static_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
         ptr_use_static_ok P (fn_pv P fn) inst)) /\
  taint_within_upto D n C3 vs /\
  (!f i s. raw_reachable vs C3 f i s /\ gas_cut n vs s ==> dalloca_no_wrap i s) /\
  s3 = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  s4 = v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  n <= LENGTH (gas_events_blocks fuel C3 fn s3) ==>
  ?fn4. lookup_function name C4.ctx_functions = SOME fn4 /\
    fn_entry_label fn4 = SOME lbl /\
    ?fuel4. n <= LENGTH (gas_events_blocks fuel4 C4 fn4 s4) /\
      TAKE n (gas_events_blocks fuel4 C4 fn4 s4) =
      TAKE n (gas_events_blocks fuel C3 fn s3)
Proof
  strip_tac >>
  `fn.fn_name = name /\ MEM fn C3.ctx_functions` by metis_tac[lookup_function_name,lookup_function_MEM] >>
  `EVERY (o1_fn_shape C3) C3.ctx_functions` by fs[o1_ctx_shape_def] >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f)) C3.ctx_functions` by
    (simp[EVERY_MEM] >> qx_gen_tac `f` >> strip_tac >>
     `o1_fn_shape C3 f` by fs[EVERY_MEM] >> fs[o1_fn_shape_def, wf_function_def]) >>
  `o1_fn_shape C3 fn` by fs[EVERY_MEM] >>
  `wf_function fn /\ entry_fn_no_params fn /\ first_block_no_phi fn` by
    fs[o1_fn_shape_def] >>
  `ALL_DISTINCT (fn_labels fn) /\ fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn` by
    fs[wf_function_def, fmp_free_ctx_def, EVERY_MEM] >>
  drule_all focus_fmp_selected_root_pin >>
  disch_then (qx_choose_then `fn4` (qx_choose_then `infos` (qx_choose_then `ctx`
    (qx_choose_then `runner` strip_assume_tac)))) >>
  qexists `fn4` >> simp[] >>
  Cases_on `n = 0` >- (qexists `0` >> simp[]) >>
  qabbrev_tac `es = TAKE n (gas_events_blocks fuel C3 fn s3)` >>
  `0 < n /\ LENGTH es = n` by simp[Abbr `es`, LENGTH_TAKE] >>
  `es = TAKE n (gas_events_blocks fuel C3 fn s3)` by simp[Abbr `es`] >>
  drule_all fmp_cut_event_source_path >>
  disch_then (qx_choose_then `p` (qx_choose_then `i` (qx_choose_then `q0`
    (qx_choose_then `w` (qx_choose_then `qe` strip_assume_tac))))) >>
  `selected_segment C3 q0 w 0 q0 w qe` by
    (simp[selected_segment_def, joint_segment_def] >>
     metis_tac[cj 2 decorated_prefix_segment]) >>
  `enters_block fn (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                               vs_inst_idx := 0|>) p` by metis_tac[] >>
  drule_all focus_fmp_cut_entry_static >>
  disch_then (qspecl_then [`eom`, `D`]
    (qx_choose_then `fn4'` (qx_choose_then `d` (qx_choose_then `t`
      (map_every assume_tac o CONJUNCTS))))) >>
  `fn4' = fn4` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `fn4' = fn4` SUBST_ALL_TAC >>
  `MEM fn4 C4.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `o1_fn_shape C4 fn4` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `wf_function fn4 /\ first_block_no_phi fn4` by fs[o1_fn_shape_def] >>
  `t.vs_current_bb = lbl` by
    (qpat_x_assum `d = 0 /\ _ \/ _` strip_assume_tac >>
     qpat_assum `t = _` SUBST1_TAC >> simp[NoAsms]) >>
  `lookup_function fn.fn_name C4.ctx_functions = SOME fn4` by simp[] >>
  `!bb. lookup_block lbl fn4.fn_blocks = SOME bb ==> t.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qx_gen_tac `bb` >> strip_tac >>
     `lookup_block t.vs_current_bb fn4.fn_blocks = SOME bb` by simp[] >>
     drule_all (cj 1 fmp_cut_event_active_index) >> simp[]) >>
  `!k. fmp_target_run k C4 name s4 d t` by simp[] >>
    Q.SUBGOAL_THEN
    `?u. enters_block fn4 s4 u /\ t.vs_current_bb = u.vs_current_bb /\
       !bb k. lookup_block s4.vs_current_bb fn4.fn_blocks = SOME bb ==>
         exec_block k C4 bb u = exec_block k C4 bb t /\
         gas_events_block k C4 fn.fn_name bb u = gas_events_block k C4 fn.fn_name bb t`
    assume_tac
  >- (irule fmp_cut_event_root_slice >>
      simp[] >> qexistsl [`d`, `name`, `v`] >> simp[] >>
      qpat_assum `d = 0 /\ _ \/ _` ACCEPT_TAC) >>
  `~vs.vs_halted /\ w2n fmp = w2n vs.vs_fmp` by fs[o1_initial_state_ok_def] >>
  Q.SUBGOAL_THEN `?fe ie se. decoration_at fe ie se qe /\ ie.inst_opcode = GAS` assume_tac
  >- (drule (cj 2 decorated_prefix_end) >> metis_tac[]) >>
  `finite_run_prefix C4 fn4 s4 es` by
    (drule_all (Q.INST [`fmp0` |-> `w2n v.vs_initial_fmp`, `raw0` |-> `w2n fmp`]
      fmp_cut_event_prefix) >>
     disch_then (drule_then (irule o REWRITE_RULE []) o CONJUNCT2) >>
     (conj_tac >- first_assum ACCEPT_TAC) >> (conj_tac >- first_assum ACCEPT_TAC) >>
     goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `q0 = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >>
     asm_rewrite_tac[]) >>
  drule (cj 2 finite_prefix_realizable) >>
  disch_then (qx_choose_then `k`
    (qspec_then `k` (strip_assume_tac o REWRITE_RULE [arithmeticTheory.LESS_EQ_REFL]))) >>
  qexists `k` >>
  qpat_assum `s4 = _` (SUBST1_TAC o SYM) >>
  qpat_assum `s3 = _` (SUBST1_TAC o SYM o REWRITE_RULE [ASSUME ``vs = v with <|vs_fmp := fmp; vs_initial_fmp := fmp|>``]) >>
  qpat_assum `gas_events_blocks k C4 fn4 s4 = _` SUBST1_TAC >>
  qpat_assum `es = TAKE n _` (SUBST1_TAC o SYM) >>
  qpat_assum `LENGTH es = n` (SUBST1_TAC o SYM) >>
  simp[NoAsms, TAKE_APPEND1]
QED
