Theory requestCutSelectedReplay
Ancestors
  gasFocusWalkInventoryReplay gasFocusJointProgress gasFocusOptLabelFlow
  gasFocusStaticReplay requestCutStoppedAssert requestCutHistoricalRecording
  requestCutFrontierCases requestCutFrontierGuards requestCutFrontierObservation
  frameRawProjection stepWriteFootprintBase jointRequestCut stateFrame
  requestCutEntryFacts requestCutReplayJoin requestCutClippedPipeline requestCutStageFacts
  requestCutPacketOracle requestCutPacketFrontierKeys requestCutRootOracle
  requestCutPacketNativeVisit requestCutRecordingFrontier requestCutRetainedRow
  requestCutPacketVisitGeometry requestCutDftPacketVisit requestCutReplaySuffix
  requestCutStaticFrontier contextPlanLayoutProps
  stackPlanTypes lowerDloadOracleCallAssembly dretDesugarDefs
  dftGasInvForwardActive dftGasInvMemoryObservation dftWf dftDefs dftRunRel
  requestCutStaticCrossing requestCutStoppedTerminal requestCutTerminalPrefix
  e2eRequestCutDefs o1PipelineCorrect o1SafeUpto o1PassContract o1PassLift
  o1RequestContract unitTransformDefs o1ComposeSupport o1PipelineCompose
  dftFinitePacket dftGasFromListTraceDefs dftGasOracleDefs contextCodegenRel
  fnFramePrefixDriver fnFrameSymbolicPrefix frameJointTrace frameJointTransition
  o1ContractCfgNormJointCursors codegenEntryRel codegenEntrySim unitMemInv
  venomPipelineRunner venomPassSchedule venomState venomInst venomWf unitShapeDefs
  venomExecSemantics venomCompilerWf asmSem asmSymSem asmFrameRel asmOptimizer
  codegenSymRel asmIR extCallOracle vfmExecution finite_map words list alist
  gasFocusOwnSetup gasFocusPrefixDriver gasFocusUniformStop
  fnPlanPlaceRevertPostamble asmRelocDataEnv asmSpliceOwn
  asmSymBridge codegenLabelDisciplined symbolResolve

fun choose_named [] use th = use th
  | choose_named (name::names) use th =
      let val (bound,_) = dest_exists (concl th)
      in X_CHOOSE_THEN (mk_var (name,type_of bound)) (choose_named names use) th end

fun fixed_native_tape path block =
  `!cut_fuel. N <= cut_fuel ==>
    ?extra. keys = MAP FST (trace_gas (trace_blocks [] 0 cut_fuel (stage 7) root_sf
      (root_entry with vs_gas_readings := raw ++ [0w]))) ++ extra` by
    (qx_gen_tac `cut_fuel` >> strip_tac >>
     `~(?u. SND (rooted_eval cut_fuel (stage 7) levels
       (root_entry with vs_gas_readings := gs ++ (gr ++ [0w]))) = OK u)` by
       (strip_tac >>
        qpat_assum `!cut_fuel gs tail. N <= cut_fuel /\ LIST_REL _ Mcut gs ==> _`
          (qspecl_then [`cut_fuel`, `gs`, `gr ++ [0w]`] mp_tac) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        qpat_assum `SND (rooted_eval cut_fuel _ _ _) = OK _`
          (fn eq => PURE_REWRITE_TAC [eq]) >>
        simp[NoAsms] >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        qpat_assum `~(?native_fuel u. N <= native_fuel /\ rooted_eval native_fuel _ _ _ = (Ecut,OK u))` mp_tac >>
        simp_tac bool_ss [NOT_EXISTS_THM] >>
        disch_then (qspecl_then [`cut_fuel`, `u`] mp_tac) >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`N <= cut_fuel`, `gs ++ (gr ++ [0w]) = raw ++ [0w]`,
           `SND (rooted_eval cut_fuel _ _ _) = OK u`,
           `FST (rooted_eval cut_fuel _ _ _) = Ecut`] >>
        POP_ASSUM_LIST (K all_tac) >>
        simp_tac (srw_ss()) [APPEND_ASSOC] >> metis_tac[pairTheory.PAIR]) >>
     mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`,
       `packet` |-> `(j,obs)`, `a` |-> path, `e` |-> block,
       `q8` |-> `JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8`,
       `fuel` |-> `cut_fuel`, `tail` |-> `gr ++ [0w]`,
       `paths` |-> `MAP (\(ai,ds,ei,qi,zi). ai) cuts`,
       `r` |-> `SND (rooted_eval cut_fuel (stage 7) levels
           (root_entry with vs_gas_readings := gs ++ (gr ++ [0w])))`]
        (INST [mk_var ("row_order", ``:num list``) |-> mk_var ("retained_order", ``:num list``),
          mk_var ("hin", ``:venom_state``) |-> mk_var ("in_state", ``:venom_state``),
          mk_var ("row_count", ``:num``) |-> mk_var ("retained_count", ``:num``)]
          request_cut_packet_frontier_keys)) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
       disj1_tac >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (CONJUNCTS_THEN2 (K all_tac)
       (CONJUNCTS_THEN2 (K all_tac) (qx_choose_then `native_extra` assume_tac))) >>
     qexists_tac `native_extra ++ kr` >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`keys = Kcut ++ kr`, `Kcut = _ ++ native_extra`, `gs ++ (gr ++ [0w]) = raw ++ [0w]`] >>
     POP_ASSUM_LIST (K all_tac) >> simp_tac (srw_ss()) [APPEND_ASSOC]) >>
  mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `v` |-> `vs0`,
    `lbl` |-> `lbl7`, `success` |-> `F`, `tail` |-> `[0w]`,
    `q8` |-> `JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8`]
    request_cut_packet_root_oracle) >>
  (impl_tac >- (simp_tac bool_ss [] >>
    rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[Abbr `keys`]))) >>
  qpat_assum `Abbrev (orc = _)` (fn th =>
    PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  simp_tac bool_ss [] >> strip_tac

fun finish_recording source_fn =
  `LENGTH s7.vs_requests = k /\ k < LENGTH u.vs_requests /\
   t9.vs_outcomes = s7.vs_outcomes /\ u9.vs_requests = u.vs_requests` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`s7.vs_requests = t8.vs_requests`, `LENGTH t8.vs_requests = k`,
       `u.vs_requests = u8.vs_requests`, `u8.vs_requests = u9.vs_requests`,
       `s7.vs_outcomes = t8.vs_outcomes`, `t8.vs_outcomes = t9.vs_outcomes`,
       `k < LENGTH u9.vs_requests`] >>
     POP_ASSUM_LIST (K all_tac) >> simp_tac (srw_ss()) []) >>
  `!fn i t. raw_reachable vs0 (stage 8) fn i t /\ LENGTH t.vs_requests <= k /\
    ~in_static_abort_prefix fn t ==> ?p d. ev_reachable orc vs0 (stage 8) p d fn i
      (t with vs_gas_readings := vs0.vs_gas_readings)` by
    (qpat_assum `!fn i s. raw_reachable vs0 (stage 8) fn i s /\ LENGTH s.vs_requests <= k ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `clip = (vs with vs_outcomes := TAKE (k - LENGTH vs.vs_requests) vs.vs_outcomes) /\
   clip7 = (v7 with vs_outcomes := TAKE (k - LENGTH v7.vs_requests) v7.vs_outcomes)` by
    (map_every (fn pat => qpat_assum pat (fn eq => PURE_REWRITE_TAC [eq]))
      [`clip = (vs with vs_outcomes := short)`,
       `clip7 = (v7 with vs_outcomes := short)`,
       `short = TAKE (k - LENGTH vs0.vs_requests) vs0.vs_outcomes`,
       `vs = _`, `v7 = _`] >>
     simp_tac (srw_ss()) []) >>
  `EVERY wf_function (stage 9).ctx_functions` by
    (qpat_assum `!i. i <= 9 ==> EVERY wf_function (stage i).ctx_functions`
      (qspec_then `9` mp_tac) >> simp_tac (srw_ss()) []) >>
  `max_live_eom (stage 9) = SOME eom` by
    (qpat_assum `max_live_eom (stage 9) = max_live_eom (stage 7)`
       (fn eq => PURE_REWRITE_TAC [eq]) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `supply` |-> `t`, `entry` |-> `nm`,
    `filling` |-> `raw ++ [0w]`, `vi` |-> `vs`, `i` |-> `inst`, `u` |-> `post`,
    `f7` |-> source_fn, `i7` |-> `i8`, `fuel7` |-> `0`, `u7` |-> `u`,
    `s9` |-> `t9`, `fuel9` |-> `record_fuel`, `guarded` |-> `fin = asm_opt_finalizer`]
    request_cut_recording_through_o1) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `stage 9 = out.po_unit.cu_context` (fn eq => PURE_REWRITE_TAC [eq]) >>
  disch_then ACCEPT_TAC

Theorem request_cut_joint_trace_raw[local]:
  EVERY wf_function C.ctx_functions /\
  joint_trace vs0 C q0 evs qs (JointConfig stk PG G tn fn inst s oms om hs hist) ==>
  raw_reachable vs0 C fn inst s
Proof
  strip_tac >> drule_then strip_assume_tac joint_trace_reachable >>
  metis_tac[joint_config_raw]
QED

val request_cut_setup_own =
  mp_tac focus_own_finalizer_setup >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
    disch_tac >> qpat_assum `fin = asm_opt_finalizer ==> label_flow_own_ok _ /\ _`
      (drule_then (fn th =>
        ACCEPT_TAC (LIST_CONJ (List.take (CONJUNCTS th, 4))))))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vs0.vs_initial_fmp = n2w cpl.cp_initial_fmp /\
    (!l. FLOOKUP vs0.vs_labels l = OPTION_MAP n2w (FLOOKUP (lo_reloc prog prog') l))` by
    fs[codegen_asm_entry_rel_reloc_def] >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  `code_labels_agree prog (lo_reloc prog prog')` by simp[lo_reloc_code_labels_agree] >>
  `!l. MEM (AsmDataHeader l) prog ==> IS_SOME (FLOOKUP (lo_reloc prog prog') l)` by
    (`fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     pop_assum strip_assume_tac
     >- (`prog' = prog` by fs[combinTheory.K_THM] >>
         qpat_assum `prog' = prog` SUBST1_TAC >> rpt strip_tac >>
         simp[lo_reloc_refl, FLOOKUP_DEF, compute_label_offsets_def,
              asmToBytecodeProofsTheory.clo_step_eq] >>
         irule asmSymBridgeTheory.clo_FDOM >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `fin = asm_opt_finalizer ==> focus_s7_symbolic_context_own _ _ _ /\ _`
       (drule_then (qspec_then `l` mp_tac o REWRITE_RULE [asm_data_env_lo_ok_def] o cj 3)) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> simp[]) >>
  `fin = asm_opt_finalizer ==>
    focus_s7_symbolic_context_own T out.po_unit prog /\
    asm_data_env_lo_ok (lo_reloc prog prog') prog (asm_data_env prog' vs0.vs_code)
      vs0.vs_code` by
    (disch_tac >>
     qpat_assum `fin = asm_opt_finalizer ==> focus_s7_symbolic_context_own _ _ _ /\ _`
       (drule_then (fn th => ACCEPT_TAC (CONJ (cj 1 th) (cj 3 th))))) >>
  `fin = asm_opt_finalizer ==> focus_s7_symbolic_context_own T out.po_unit prog` by
    (disch_tac >> first_x_assum (drule_then (ACCEPT_TAC o cj 1))) >>
  mp_tac focus_own_prefix_budget >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (fn th => assume_tac th >> qx_choose_then `B` assume_tac th) >>
  `fin = asm_opt_finalizer ==>
    !j a. asm_steps (lo_reloc prog prog') (build_offset_to_pc prog)
      prog j (entry_asm_state vs0 es0) = AsmOK a /\
      (?sr. sym_steps_own prog (asm_data_env prog' vs0.vs_code) vs0.vs_code j
        (sym_init (entry_asm_state vs0 es0)) = SymOK sr) ==>
      j <= B /\
      (a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "GAS" ==>
        a.as_gas_readings <> [])` by
    (disch_tac >> rpt gen_tac >> strip_tac >>
     qpat_assum `!n ast. _ ==> n <= B /\ _` (qspecl_then [`j`,`a`] mp_tac) >> simp[]) >>
  mp_tac (Q.INST [`max_cost` |-> `B`] focus_own_gas_callback) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then assume_tac >>
  `fin = asm_opt_finalizer ==>
     (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                ~MEM (Label "code_end") inst.inst_operands) /\
     EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                       ds.ds_items) unit.cu_data_segment /\
     ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                 MEM inst (fn_insts fn) /\
                 MEM (Label "runtime_begin") inst.inst_operands) ==>
      EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
     LENGTH vs0.vs_data_section < dimword (:256) DIV 2` by
    (disch_tac >>
     qpat_assum `fin = asm_opt_finalizer ==> label_flow_own_ok _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2)));

val request_cut_symbolic_plan_own =
  `fin = asm_opt_finalizer ==>
    sym_steps_own prog (asm_data_env prog' vs0.vs_code) vs0.vs_code asm_fuel
      (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan_own T (lo_reloc prog prog')
      (asm_data_env prog' vs0.vs_code) vs0.vs_code rpolicy out.po_unit cpl prog vs0 es0
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss /\
    focus_s7_symbolic_context_own T out.po_unit prog /\
    asm_data_env_lo_ok (lo_reloc prog prog') prog (asm_data_env prog' vs0.vs_code)
      vs0.vs_code` by
    (qpat_assum `fin = asm_opt_finalizer ==> sym_steps_own _ _ _ _ _ = _ /\ _` mp_tac >>
     qpat_assum `fin = asm_opt_finalizer ==> focus_s7_symbolic_context_own T _ _ /\ asm_data_env_lo_ok _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]);

fun own_steps th = PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES] th;

val request_cut_entry_facts_own_tac =
  drule_all_then strip_assume_tac request_cut_entry_facts_own;

val request_cut_replay_own =
  BETA_RULE (Q.INST
    [`asm_lo` |-> `lo_reloc prog prog'`,
     `symbolic` |-> `sym_steps_own prog (asm_data_env prog' vs0.vs_code) vs0.vs_code`,
     `frame` |-> `normal_frame_symbolic_plan_own T (lo_reloc prog prog')
       (asm_data_env prog' vs0.vs_code) vs0.vs_code rpolicy out.po_unit cpl prog vs0 es0`]
    focus_stopped_filling_replay_for);

val request_cut_frame_projection_own =
  let
    val projection = valOf (List.find (fn tm =>
      let val (arguments, implication) = strip_forall tm in
        length arguments = 13 andalso is_imp_only implication andalso
        is_exists (rand implication)
      end) (strip_conj (lhand (concl request_cut_replay_own))))
  in
    SUBGOAL_THEN projection assume_tac
    >- (rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC focus_own_frame_projection)
  end;

fun replay_begin selector entry_facts =
  mp_tac selector >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  PURE_REWRITE_TAC [LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  disch_then (qx_choosel_then
    [`raw_slots`, `sites`, `unused`, `N`, `root_sf`, `root_tf`, `root_entry`, `lbl7`,
     `q80`, `q90`, `evs8`, `qs8`, `evs9`, `qs9`, `schedules`, `current`, `saved`,
     `asm_fuel`, `ast`, `ss`, `j`, `obs`, `acts`, `blocks`, `calls`, `ms_tab`, `es_tab`, `ks_tab`,
     `rooted_eval`, `p`, `d`,
     `stk8`, `PG8`, `G8`, `tn8`, `fn8`, `inst8`, `s8`, `oms8`, `om8`, `hs8`, `hist8`,
     `stk9`, `PG9`, `G9`, `tn9`, `fn9`, `inst9`, `s9`, `oms9`, `om9`, `hs9`, `hist9`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`raw_slots`, `sites`, `unused`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `raw` >> strip_tac >>
  conj_tac >- (qpat_assum `!raw. LIST_REL _ raw_slots raw ==> _` drule >> simp[]) >>
  conj_tac >- suspend "exit" >>
  qx_genl_tac [`D`, `k`, `vs`, `fn`, `inst`, `s`, `fuel`, `post`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!rq rqs. record_request rq rqs = rqs ++ [rq]` by simp[record_request_def] >>
  `raw_variant fmp vs vs0` by simp[raw_variant_def, gas_variant_def, venom_state_component_equality] >>
  `unit_wf unit` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ _ = _`
       (mp_tac o MATCH_MP o1_driver_runs o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
     simp[]) >>
  `EVERY wf_function unit.cu_context.ctx_functions` by
    (drule o1_source_unit_ok_ctx_shape >> simp[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
     metis_tac[]) >>
  drule_all_then strip_assume_tac request_cut_stage_facts >>
  entry_facts >>
  `LENGTH vs0.vs_requests <= k` by
    (`vs.vs_requests = vs0.vs_requests` by fs[] >>
     drule_all raw_reachable_recorded_oracle_drop >> simp[]) >>
  qabbrev_tac `v7 = vs0 with vs_gas_readings := raw ++ [0w]` >>
  qabbrev_tac `short = TAKE (k - LENGTH vs0.vs_requests) vs0.vs_outcomes` >>
  qabbrev_tac `clip = vs with vs_outcomes := short` >>
  qabbrev_tac `clip7 = v7 with vs_outcomes := short` >>
  qpat_assum `!gs. ?D f extra. _` (qspec_then `raw ++ [0w]` mp_tac) >>
  disch_then (qx_choosel_then [`Ds`, `source_fuel`, `extra`] strip_assume_tac) >>
  suspend "clipped";

val replay_clipped =
  `LENGTH o1_fn_passes = 9` by simp[o1_fn_passes_def] >>
  `stage (LENGTH o1_fn_passes) = out.po_unit.cu_context` by
    (qpat_assum `LENGTH o1_fn_passes = 9` (fn eq => PURE_REWRITE_TAC [eq]) >>
     first_assum ACCEPT_TAC) >>
  `fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) vs0` by
    (qpat_assum `stage (LENGTH o1_fn_passes) = out.po_unit.cu_context`
       (fn eq => PURE_REWRITE_TAC [eq]) >>
     first_assum ACCEPT_TAC) >>
  `!i. i < LENGTH o1_fn_passes ==> ctx_pass_stage rpolicy (EL i o1_fn_passes)
      (o1_walk_view rpolicy i) (stage i) (stage (SUC i))` by simp[] >>
  `!i. i <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage i)` by
    (qpat_assum `LENGTH o1_fn_passes = 9` (fn eq => PURE_REWRITE_TAC [eq]) >>
     qpat_assum `!i. i <= 9 ==> o1_ctx_shape (stage i) /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!i. i <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row i) (stage i).ctx_functions` by
    (qpat_assum `LENGTH o1_fn_passes = 9` (fn eq => PURE_REWRITE_TAC [eq]) >>
     qpat_assum `!i. i <= 9 ==> o1_ctx_shape (stage i) /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `v7 = vs0 with vs_gas_readings := raw ++ [0w]` by simp[Abbr `v7`] >>
  `vs = v7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` by
    (qpat_assum `vs = _` (fn eq => PURE_REWRITE_TAC [eq]) >>
     qpat_assum `v7 = _` (fn eq => PURE_REWRITE_TAC [eq]) >>
     simp_tac (srw_ss()) [venom_state_component_equality]) >>
  `o1_safe_upto Ds lo (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w])))
    unit.cu_context vs` by
    (qpat_assum `vs = (vs0 with <|vs_gas_readings := raw ++ [0w];
      vs_fmp := fmp; vs_initial_fmp := fmp|>)` (fn eq => PURE_REWRITE_TAC [eq]) >>
     first_assum ACCEPT_TAC) >>
  `short = TAKE (k - LENGTH vs0.vs_requests) vs0.vs_outcomes /\
   clip = (vs with vs_outcomes := short) /\ clip7 = (v7 with vs_outcomes := short)` by
    simp[Abbr `short`, Abbr `clip`, Abbr `clip7`] >>
  `fin = asm_opt_finalizer ==>
    LENGTH vs0.vs_data_section < dimword (:256) DIV 2 /\
    !fn i. MEM fn unit.cu_context.ctx_functions /\ MEM i (fn_insts fn) ==>
      ~MEM (Label "code_end") i.inst_operands` by
    (qpat_assum `fin = asm_opt_finalizer ==> label_flow_own_ok unit.cu_context /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `supply` |-> `t`, `entry` |-> `nm`,
    `rds` |-> `raw ++ [0w]`, `w7` |-> `v7`, `w` |-> `vs`,
    `i` |-> `inst`, `vi` |-> `clip`, `v7` |-> `clip7`, `reserve` |-> `lo`,
    `n` |-> `MIN (LENGTH ((markf:256 word list -> 'a list) (raw ++ [0w]))) (LENGTH (raw ++ [0w]))`,
    `guarded` |-> `fin = asm_opt_finalizer`] request_cut_pre_dft) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (qx_choose_then `eom` (map_every assume_tac o CONJUNCTS)) assume_tac))) >>
  qabbrev_tac `keys = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))` >>
  qabbrev_tac `orc = \key. case ALOOKUP (obs ++ ZIP (keys,raw)) key of NONE => 0w | SOME w => w` >>
  qabbrev_tac `trace8 = trace_blocks [] 0 N (stage 8) root_tf root_entry` >>
  suspend "stopped";

val replay_stopped =
  `o1_ctx_shape (stage 7) /\ o1_ctx_shape (stage 8)` by
    (qpat_assum `!i. i <= 9 ==> o1_ctx_shape (stage i) /\ _`
      (fn th => simp_tac (srw_ss()) [Q.SPEC `7` th, Q.SPEC `8` th])) >>
  `EVERY wf_function (stage 7).ctx_functions /\
   EVERY wf_function (stage 8).ctx_functions /\ EVERY wf_function (stage 9).ctx_functions` by
    (qpat_assum `!i. i <= 9 ==> EVERY wf_function (stage i).ctx_functions`
       (fn wf => simp[Q.SPEC `7` wf, Q.SPEC `8` wf, Q.SPEC `9` wf])) >>
  qpat_x_assum `?align old_cursors old_asm old_sym costs. LENGTH costs = LENGTH evs9 /\ _`
    (qx_choosel_then [`align`, `old_cursors`, `old_asm`, `old_sym`, `costs`]
       (map_every assume_tac o CONJUNCTS)) >>
  `!h. h < LENGTH evs9 ==> align h <= LENGTH evs8 /\
      ?packet. cfg_norm_joint_cursors (stage 8) (stage 9) packet
        (EL (align h) (q80::qs8)) (EL h (q90::qs9))` by
    (qx_gen_tac `h` >> strip_tac >>
     qpat_assum `!k. k < LENGTH evs9 ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     conj_tac >- (qpat_assum `j = LENGTH evs8` (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
                  first_assum ACCEPT_TAC) >>
     qexists_tac `old_cursors h` >> first_assum ACCEPT_TAC) >>
  `keys = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))` by simp[Abbr `keys`] >>
  `ALL_DISTINCT (MAP FST obs)` by
    (drule_all request_cut_packet_mask_observations >>
     disch_then (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2)) >>
  `trace8 = trace_context N (stage 8) vs0` by
    simp[Abbr `trace8`, trace_context_def, trace_function_def] >>
  `LENGTH evs8 < LENGTH trace8 /\
   obs = trace_gas (TAKE (LENGTH evs8) trace8)` by
    (qpat_assum `j = LENGTH evs8` (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!i. i < LENGTH evs8 ==>
    ?p d f inst u stk PG G tn oms om hs hist.
      EL i trace8 = ((p,d,inst.inst_id),f,inst,u) /\
      EL i (q80::qs8) = JointConfig stk PG G tn f inst u oms om hs hist` by
    (qx_gen_tac `h_idx` >> strip_tac >>
     qpat_assum `j = LENGTH evs8` (fn eq =>
       qpat_assum `!h. h < j ==> ?a e tf inst visit_state stk PG G tn oms om hs hist. _`
         (mp_tac o Q.SPEC `h_idx` o PURE_REWRITE_RULE [eq])) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (qx_choosel_then
       [`hh_p`, `hh_d`, `hh_f`, `hh_i`, `hh_u`, `hh_stk`, `hh_PG`, `hh_G`,
        `hh_tn`, `hh_oms`, `hh_om`, `hh_hs`, `hh_hist`]
       (map_every assume_tac o CONJUNCTS)) >>
     qexistsl_tac [`hh_p`, `hh_d`, `hh_f`, `hh_i`, `hh_u`, `hh_stk`, `hh_PG`,
       `hh_G`, `hh_tn`, `hh_oms`, `hh_om`, `hh_hs`, `hh_hist`] >>
     conj_tac >- (
       qpat_assum `EL h_idx (TAKE (LENGTH evs8) trace8) = _` mp_tac >>
       qpat_assum `h_idx < LENGTH evs8` mp_tac >>
       simp_tac (srw_ss()) [EL_TAKE]) >>
     first_assum ACCEPT_TAC) >>
  `k < LENGTH s9.vs_requests` by
    (Cases_on `?a post8. MEM inst8.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\
      step_inst (N - d) (stage 8) inst8 s8 = Abort a post8`
     >- (qpat_x_assum `?a post8. MEM _ _ /\ _`
          (qx_choosel_then [`ab`, `post8`] strip_assume_tac) >>
         request_cut_symbolic_plan_own >>
         mp_tac (Q.INST [`rp` |-> `rpolicy`, `unit` |-> `out.po_unit`, `es` |-> `es0`,
           `C` |-> `unit.cu_context`, `C8` |-> `stage 8`, `n` |-> `asm_fuel`,
           `m` |-> `N - d`, `s8'` |-> `post8`, `fuel` |-> `fuel`,
           `q9` |-> `JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9`,
           `planner_base` |-> `vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                                       vs_return_pc_token := 0w; vs_inst_idx := 0|>`]
           (own_steps request_cut_stopped_assert_crossed_own)) >>
         (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
            qpat_assum `stage 9 = out.po_unit.cu_context` (SUBST1_TAC o SYM) >>
            first_assum ACCEPT_TAC)) >>
         disch_then ACCEPT_TAC) >>
     suspend "other_stop") >>
  `k < LENGTH s8.vs_requests` by
    (drule cfg_norm_joint_cursor_execution_frame >> strip_tac >>
     qpat_assum `execution_frame s8 = execution_frame s9`
       (mp_tac o Q.AP_TERM `\s. s.vs_requests`) >> simp[execution_frame_def]) >>
  mp_tac (Q.INST [`C8` |-> `stage 8`, `v` |-> `vs0`, `q0` |-> `q80`,
    `evs` |-> `evs8`, `qs` |-> `qs8`, `tr` |-> `trace8`, `end8` |-> `s8`,
    `f` |-> `fn8`, `inst` |-> `inst8`, `stk` |-> `stk8`, `PG` |-> `PG8`,
    `G` |-> `G8`, `tn` |-> `tn8`, `oms` |-> `oms8`, `om` |-> `om8`,
    `hs` |-> `hs8`, `hist` |-> `hist8`, `filling` |-> `ZIP (keys,raw)`]
    request_cut_observed_cover) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `Abbrev (orc = _)` (fn eq =>
    PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)]) >>
  disch_then assume_tac >>
  mp_tac (Q.INST [`C8` |-> `stage 8`, `C9` |-> `stage 9`,
    `f8` |-> `fn8`, `i8` |-> `inst8`, `end8` |-> `s8`,
    `f9` |-> `fn9`, `i9` |-> `inst9`, `end9` |-> `s9`]
    request_cut_cfg_retained_row) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then
    [`cross`, `stk`, `PG`, `G`, `tn`, `f8`, `i8`, `t8`, `oms`, `om`, `hs`,
     `hist`, `record_fuel`, `u8`, `f9`, `i9`, `t9`, `u9`] strip_assume_tac) >>
  `align cross < j` by simp[] >>
  qpat_assum `!h. h < j ==> ?a e tf inst visit_state stk PG G tn oms om hs hist. _`
    (qspec_then `align cross` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`a`, `e`, `tf`, `visit_inst`, `visit_state`, `visit_stk`,
    `visit_PG`, `visit_G`, `visit_tn`, `visit_oms`, `visit_om`, `visit_hs`, `visit_hist`]
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (choose_named
        ["sf", "inc", "entry", "order", "res", "nrest", "bb", "bt", "ps", "xs", "ys",
         "retained_order", "in_state", "h0", "body_entry", "retained_count", "front", "closed", "brest"]
        (map_every assume_tac o CONJUNCTS))))) >>
  `tf = f8 /\ visit_inst = i8 /\ visit_state = t8` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`EL (align cross) (q80::qs8) = JointConfig stk PG G tn f8 i8 t8 oms om hs hist`,
       `EL (align cross) (q80::qs8) =
        JointConfig visit_stk visit_PG visit_G visit_tn tf visit_inst visit_state
          visit_oms visit_om visit_hs visit_hist`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [joint_config_11] >> metis_tac[]) >>
  `EL (align cross) trace8 =
    ((a,e,i8.inst_id),f8,i8,t8)` by
    (qpat_assum `EL (align cross) (TAKE j trace8) = _` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`align cross < j`, `tf = f8`, `visit_inst = i8`, `visit_state = t8`] >>
     POP_ASSUM_LIST (K all_tac) >> simp_tac (srw_ss()) [EL_TAKE]) >>
  `align cross < LENGTH trace8 /\ k < LENGTH u8.vs_requests` by
    (conj_tac >-
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`align cross < j`, `j < LENGTH trace8`] >>
        POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     qpat_assum `u8.vs_requests = u9.vs_requests` (fn eq => PURE_REWRITE_TAC [eq]) >>
     first_assum ACCEPT_TAC) >>
  suspend "historical_root";

val replay_historical_root =
  qpat_x_assum `(inv_memory_observation visit_inst.inst_opcode \/ _) /\
    ~in_revert_forward tf visit_state ==> _` mp_tac >>
  (impl_tac >-
    (conj_tac >- (disj1_tac >> simp[]) >> simp[])) >>
  disch_then (qx_choosel_then [`q`, `z`, `src_inst`, `cuts`, `levels`, `Mcut`, `Ecut`,
    `Kcut`, `mr`, `er`, `kr`] (map_every assume_tac o CONJUNCTS)) >>
  `FLOOKUP acts a = SOME (sf,f8,inc,entry,order,res,nrest)` by
    (qpat_assum `tf = f8` (fn eq =>
      first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  `visit_state <> s8` by
    (strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
      [`visit_state = t8`, `visit_state = s8`, `LENGTH t8.vs_requests = k`,
       `k < LENGTH s8.vs_requests`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[prim_recTheory.LESS_REFL]) >>
  `q < LENGTH xs /\ EL q xs = i8 /\
   z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs` by
    (qpat_assum `(IS_SOME body_entry /\ _) \/ _`
       (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS))
     >- simp[] >>
     qpat_assum `visit_state <> s8` mp_tac >>
     qpat_assum `visit_state = s8` (fn eq => simp_tac bool_ss [eq])) >>
  `!cut_fuel gs tail u. N <= cut_fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
    rooted_eval cut_fuel (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) = (Ecut,OK u) ==>
    ?before after.
      trace_blocks [] 0 cut_fuel (stage 7) root_sf (root_entry with vs_gas_readings := gs ++ tail) =
      before ++ [((a,e,(EL (LENGTH z)
        (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
        EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
      trace_gas before = ZIP (Kcut,gs)` by
    (qx_genl_tac [`cut_fuel`, `gs`, `tail`, `u`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!cut_fuel gs tail. N <= cut_fuel /\ LIST_REL _ Mcut gs ==> _`
       (qspecl_then [`cut_fuel`, `gs`, `tail`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `rooted_eval cut_fuel _ _ _ = _` (fn eq => PURE_REWRITE_TAC [eq]) >>
     simp[NoAsms] >> metis_tac[]) >>
  Cases_on `?native_fuel u. N <= native_fuel /\
    rooted_eval native_fuel (stage 7) levels (root_entry with vs_gas_readings := raw ++ [0w]) = (Ecut,OK u)`
  >- (qpat_x_assum `?native_fuel u. N <= native_fuel /\ rooted_eval native_fuel _ _ _ = _`
       (qx_choosel_then [`native_fuel`, `s7`] strip_assume_tac) >>
      mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`,
        `stopped` |-> `j`, `initial` |-> `vs0`, `lbl` |-> `lbl7`,
        `h` |-> `(align:num -> num) (cross:num)`, `inst` |-> `i8`, `tf` |-> `f8`,
        `t` |-> `t8`, `post8` |-> `u8`, `fuel` |-> `record_fuel`,
        `fuel7` |-> `native_fuel`, `s` |-> `s7`,
        `v7` |-> `vs0 with vs_gas_readings := raw ++ [0w]`,
        `trace8` |-> `trace_blocks [] 0 N (stage 8) root_tf root_entry`,
        `q8` |-> `JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8`]
        (INST [mk_var ("row_order", ``:num list``) |-> mk_var ("retained_order", ``:num list``),
          mk_var ("hin", ``:venom_state``) |-> mk_var ("in_state", ``:venom_state``),
          mk_var ("nseen", ``:num``) |-> mk_var ("retained_count", ``:num``)]
          request_cut_historical_recording)) >>
      (impl_tac >- (
        qpat_assum `Abbrev (trace8 = _)` (fn eq =>
          PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)]) >>
        qpat_assum `keys = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e)))) _)`
          (SUBST1_TAC o SYM) >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        (REFL_TAC ORELSE (SIMP_TAC bool_ss [record_request_def] >> NO_TAC)))) >>
      disch_then (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 (qx_choose_then `u` (map_every assume_tac o CONJUNCTS)) assume_tac)) >>
      suspend "join_recording") >>
  suspend "earlier_native_stop";

val replay_join_recording =
  `raw_reachable v7 (stage 7) sf i8 s7` by
    (simp_tac bool_ss [Abbr `v7`] >> first_assum ACCEPT_TAC) >>
  `!p d fn i t. ev_reachable orc vs0 (stage 7) p d fn i t /\ LENGTH t.vs_requests <= k ==>
     ?ws. raw_reachable v7 (stage 7) fn i (t with vs_gas_readings := ws)` by
    (simp_tac bool_ss [Abbr `orc`, Abbr `v7`] >>
     qpat_assum `keys = Kcut ++ kr` (fn eq => PURE_REWRITE_TAC [eq]) >>
     first_assum ACCEPT_TAC) >>
  finish_recording `sf`;

val replay_earlier_native_stop =
  `IS_SOME body_entry /\ LENGTH ps <= visit_state.vs_inst_idx /\
   visit_state.vs_inst_idx - LENGTH ps < LENGTH (retained_order:num list) /\
   q = EL (visit_state.vs_inst_idx - LENGTH ps) (retained_order:num list)` by
    (qpat_assum `(IS_SOME body_entry /\ _) \/ _`
       (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS))
     >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `visit_state <> s8` mp_tac >>
     qpat_assum `visit_state = s8` (fn eq => simp_tac bool_ss [eq])) >>
  mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `R` |-> `trace8`,
    `stk` |-> `stk8`, `PG` |-> `PG8`, `G` |-> `G8`, `tn` |-> `tn8`,
    `fn` |-> `fn8`, `inst` |-> `inst8`, `st` |-> `s8`, `oms` |-> `oms8`,
    `om` |-> `om8`, `hs` |-> `hs8`, `hist` |-> `hist8`,
    `h` |-> `(align:num -> num) (cross:num)`, `i` |-> `i8`, `tf` |-> `f8`, `t` |-> `t8`]
    focus_packet_visit_row) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[Abbr `trace8`]))) >>
  disch_then (qx_choosel_then
    [`row_sf`, `row_inc`, `row_entry`, `row_order`, `row_res`, `row_nrest`, `row_bb`,
     `row_bt`, `row_ps`, `row_xs`, `row_ys`, `row_rho`, `row_in`, `row_h0`, `row_body`,
     `row_count`, `row_front`, `row_closed`, `row_rest`]
    (map_every assume_tac o CONJUNCTS)) >>
  `row_ps = ps /\ row_xs = xs /\ row_rho = (retained_order:num list) /\ row_count = retained_count` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,(retained_order:num list),in_state,h0,body_entry,retained_count,front,closed,brest)`,
       `FLOOKUP blocks (a,e) =
         SOME (row_bb,row_bt,row_ps,row_xs,row_ys,row_rho,row_in,row_h0,row_body,row_count,
           row_front,row_closed,row_rest)`] >>
     simp_tac (srw_ss()) [] >> metis_tac[]) >>
  qpat_x_assum `(inv_memory_observation i8.inst_opcode \/ _) ==> _` mp_tac >>
  (impl_tac >- (disj1_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`history_entry`, `history_entry_count`, `history_pos`, `retained_q`]
    (map_every assume_tac o CONJUNCTS)) >>
  `retained_q = EL (t8.vs_inst_idx - LENGTH row_ps) row_rho` by
    (qpat_assum `history_pos = t8.vs_inst_idx - LENGTH row_ps`
       (fn eq => PURE_REWRITE_TAC [GSYM eq]) >> first_assum ACCEPT_TAC) >>
  `EVERY (\x. ~is_terminator x.inst_opcode) (TAKE q xs) /\
   (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE retained_count (retained_order:num list)))` by
    (`retained_q = q` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`row_rho = (retained_order:num list)`, `row_ps = ps`, `visit_state = t8`,
          `q = EL (visit_state.vs_inst_idx - LENGTH ps) (retained_order:num list)`,
          `retained_q = EL (t8.vs_inst_idx - LENGTH row_ps) row_rho`] >>
        POP_ASSUM_LIST (K all_tac) >> simp_tac (srw_ss()) []) >>
     map_every (fn pat => qpat_assum pat (fn eq => PURE_REWRITE_TAC [GSYM eq]))
       [`row_xs = xs`, `retained_q = q`, `row_count = retained_count`, `row_rho = (retained_order:num list)`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `LIST_REL _ raw_slots raw`
    (fn rel => qpat_assum `raw_slots = Mcut ++ mr`
       (fn eq => strip_assume_tac (REWRITE_RULE [eq, LIST_REL_SPLIT1] rel))) >>
  rename1 `raw = gs ++ gr` >>
  `gs ++ (gr ++ [0w]) = raw ++ [0w]` by
    (qpat_assum `raw = gs ++ gr` (fn eq => PURE_REWRITE_TAC [eq]) >>
     simp_tac (srw_ss()) [APPEND_ASSOC]) >>
  fixed_native_tape `a` `e` >>
  `align cross <= j /\ align cross < LENGTH trace8` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`align cross < j`, `j < LENGTH trace8`] >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`,
    `v` |-> `vs0`, `lbl` |-> `lbl7`, `tr` |-> `trace8`,
    `id` |-> `i8.inst_id`, `h` |-> `(align:num -> num) (cross:num)`, `fn` |-> `f8`,
    `q8` |-> `JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8`,
    `inst` |-> `i8`, `s` |-> `t8`] request_cut_packet_observed_visit) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[Abbr `keys`, Abbr `trace8`]))) >>
  qpat_assum `Abbrev (orc = _)` (fn th => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  strip_tac >>
  mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `initial` |-> `vs0`,
    `fn8` |-> `f8`, `inst` |-> `i8`, `s8` |-> `t8`, `n` |-> `record_fuel`,
    `p` |-> `a`, `d` |-> `e`, `filling` |-> `raw ++ [0w]`]
    request_cut_recording_frontier) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[Abbr `orc`]))) >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`record_fn`, `s7`, `u`] strip_assume_tac)
    assume_tac) >>
  `raw_reachable v7 (stage 7) record_fn i8 s7` by
    (simp_tac bool_ss [Abbr `v7`] >> first_assum ACCEPT_TAC) >>
  `!p d fn i t. ev_reachable orc vs0 (stage 7) p d fn i t /\ LENGTH t.vs_requests <= k ==>
     ?ws. raw_reachable v7 (stage 7) fn i (t with vs_gas_readings := ws)` by
    (simp_tac bool_ss [Abbr `v7`] >>
     qpat_assum `!p d fn i t. ev_reachable orc vs0 (stage 7) p d fn i t ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  finish_recording `record_fn`;

val replay_other_stop =
  `raw_reachable vs0 (stage 8) fn8 inst8 s8 /\
   raw_reachable vs0 (stage 9) fn9 inst9 s9` by
    (conj_tac
     >- (qpat_assum `EVERY wf_function (stage 8).ctx_functions` (fn wf =>
           qpat_assum `joint_trace vs0 (stage 8) _ _ _ _`
             (ACCEPT_TAC o MATCH_MP request_cut_joint_trace_raw o CONJ wf))) >>
     qpat_assum `EVERY wf_function (stage 9).ctx_functions` (fn wf =>
       qpat_assum `joint_trace vs0 (stage 9) _ _ _ _`
         (ACCEPT_TAC o MATCH_MP request_cut_joint_trace_raw o CONJ wf))) >>
  `MEM inst8 (fn_insts fn8) /\ MEM inst9 (fn_insts fn9)` by
    (conj_tac
     >- qpat_assum `raw_reachable vs0 (stage 8) fn8 inst8 s8`
        (ACCEPT_TAC o MATCH_MP ld_active_inst_member o MATCH_MP (SPEC_ALL raw_reachable_active)) >>
     qpat_assum `raw_reachable vs0 (stage 9) fn9 inst9 s9`
       (ACCEPT_TAC o MATCH_MP ld_active_inst_member o MATCH_MP (SPEC_ALL raw_reachable_active))) >>
  `MEM fn8 (stage 8).ctx_functions` by
    (qpat_assum `raw_reachable vs0 (stage 8) fn8 inst8 s8`
      (ACCEPT_TAC o MATCH_MP (SPEC_ALL raw_visit_function_member))) >>
  `inst_shape_ok inst8 /\ inst8.inst_opcode <> DRET` by
    (qpat_assum `!i. i <= 9 ==> o1_ctx_shape (stage i) /\ _`
       (qspec_then `8` mp_tac) >>
     simp[NoAsms, o1_ctx_shape_def, EVERY_MEM] >> strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`!f. MEM f (stage 8).ctx_functions ==> o1_fn_shape (stage 8) f`,
        `MEM inst8 (fn_insts fn8)`, `MEM fn8 (stage 8).ctx_functions`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac (srw_ss()) [o1_fn_shape_def,fn_shape_ok_def,no_dret_def,EVERY_MEM] >> metis_tac[]) >>
  `(inst9.inst_opcode <> PHI ==>
    !l. MEM (Label l) (compute_operands inst9) ==> IS_SOME (FLOOKUP s9.vs_labels l))` by
    (rpt strip_tac >>
     qpat_assum `stage 9 = out.po_unit.cu_context` (fn eq =>
       qpat_assum `raw_reachable vs0 (stage 9) fn9 inst9 s9`
         (assume_tac o REWRITE_RULE [eq])) >>
     qpat_assum `!fn inst s i l. raw_reachable vs0 out.po_unit.cu_context fn inst s /\
          MEM i (fn_insts fn) /\ i.inst_opcode <> PHI /\
          MEM (Label l) (compute_operands i) ==> IS_SOME (FLOOKUP s.vs_labels l)`
        (drule_all_then ACCEPT_TAC)) >>
  `o1_ctx_shape out.po_unit.cu_context` by
    (qpat_assum `!i. i <= 9 ==> o1_ctx_shape (stage i) /\ _` (qspec_then `9` mp_tac) >>
     qpat_assum `stage 9 = out.po_unit.cu_context` (fn eq =>
       simp_tac (srw_ss()) [eq])) >>
  request_cut_symbolic_plan_own >>
  (qpat_assum `fin = asm_opt_finalizer ==> sym_steps_own _ _ _ _ _ = _ /\ _`
       (fn plan =>
         qpat_assum `fin = asm_opt_finalizer ==> !j a. _ ==> j <= B /\ _`
           (fn bound =>
             let
               val enabled = ASSUME ``fin = asm_opt_finalizer``
             in
               assume_tac (DISCH (concl enabled)
                 (LIST_CONJ (CONJUNCTS (MP plan enabled) @ [MP bound enabled])))
             end))) >>
  PairCases_on `current` >>
  mp_tac (Q.INST [`C8` |-> `stage 8`, `unit` |-> `out.po_unit`, `rp` |-> `rpolicy`,
    `es` |-> `es0`, `n` |-> `asm_fuel`, `m` |-> `N - d`,
    `C` |-> `unit.cu_context`, `rounds` |-> `current0`, `cells` |-> `current1`,
    `q8` |-> `JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8`,
    `q9` |-> `JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9`]
    (own_steps (Q.INST [`max_cost` |-> `B`] request_cut_frontier_cases_own))) >>
  (impl_tac >- (rpt conj_tac >>
    TRY (REFL_TAC ORELSE first_assum ACCEPT_TAC) >>
    qpat_assum `stage 9 = out.po_unit.cu_context`
      (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
    TRY (first_assum ACCEPT_TAC) >>
    qpat_assum `(?r r8. step_inst (N-d) (stage 8) inst8 s8 = r /\ _) \/ _`
      (DISJ_CASES_THEN2 (qx_choosel_then [`stop8`,`root_stop8`]
                        (map_every assume_tac o CONJUNCTS)) assume_tac)
    >- (disj1_tac >> conj_tac >- first_assum ACCEPT_TAC >>
        qexists_tac `stop8` >> conj_tac >> first_assum ACCEPT_TAC) >>
    disj2_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (DISJ_CASES_THEN2 ACCEPT_TAC (CONJUNCTS_THEN assume_tac)) >>
  Cases_on `k < LENGTH s9.vs_requests` >> simp[] >>
  `LENGTH s9.vs_requests <= k` by decide_tac >>
  suspend "endpoint_observation";

val replay_endpoint_observation =
  `!r. MEM r cpl.cp_regions ==> eom <= r.sr_spill_base /\ r.sr_spill_end <= w2n s9.vs_initial_fmp` by
    (drule generate_context_plan_spill_gap >> strip_tac >>
     `s9.vs_initial_fmp = vs0.vs_initial_fmp` by
       (qpat_assum `raw_reachable vs0 (stage 9) fn9 inst9 s9`
         (ACCEPT_TAC o MATCH_MP (SPEC_ALL ctxLookupAgreeTheory.raw_reachable_initial_fmp))) >>
     `vs0.vs_initial_fmp = n2w cpl.cp_initial_fmp` by
       first_assum ACCEPT_TAC >>
     `cpl.cp_max_static_eom = eom` by
       (qpat_assum `max_live_eom (stage 7) = SOME eom` (fn cut_eom =>
        qpat_assum `max_live_eom (stage 9) = max_live_eom (stage 7)` (fn stages =>
        qpat_assum `stage 9 = out.po_unit.cu_context` (fn ctx =>
        qpat_assum `max_live_eom out.po_unit.cu_context = SOME cpl.cp_max_static_eom`
          (fn plan_eom => mp_tac (TRANS (SYM plan_eom)
            (PURE_REWRITE_RULE [ctx] (TRANS stages cut_eom))))))) >>
        simp_tac (srw_ss()) []) >>
     qpat_assum `!r. MEM r cpl.cp_regions ==> _` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`s9.vs_initial_fmp = vs0.vs_initial_fmp`,
        `vs0.vs_initial_fmp = n2w cpl.cp_initial_fmp`,
        `cpl.cp_max_static_eom = eom`, `cpl.cp_initial_fmp < dimword (:256)`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac (srw_ss()) [wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  qpat_assum `mem_inv _ (stage 7) v7` (assume_tac o REWRITE_RULE [request_cut_def]) >>
  qpat_assum `fin = asm_opt_finalizer ==> code_end_offset_ok _ (stage 7)`
    (assume_tac o REWRITE_RULE [request_cut_def]) >>
  `inv_memory_observation inst8.inst_opcode /\ ~in_revert_forward fn8 s8 ==>
    ((?fn7 u ws. raw_reachable v7 (stage 7) fn7 inst8 (u with vs_gas_readings := ws) /\
      ~in_revert_forward fn7 u /\ fn8 = dft_fn fn7 /\
      u.vs_current_bb = s8.vs_current_bb /\ ev_reachable orc vs0 (stage 7) p d fn7 inst8 u) \/
     (in_static_abort_prefix fn8 s8 /\ !p d fn i t. ev_reachable orc vs0 (stage 7) p d fn i t ==>
       ?ws. raw_reachable v7 (stage 7) fn i (t with vs_gas_readings := ws))) /\
    ev_reachable orc vs0 (stage 8) p d fn8 inst8 (s8 with vs_gas_readings := vs0.vs_gas_readings)` by
    suspend "endpoint_visit" >>
  mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `C9` |-> `stage 9`,
    `initial` |-> `vs0`, `p` |-> `p`, `d` |-> `d`,
    `h8` |-> `hist8`, `h9` |-> `hist9`, `current` |-> `(current0,current1)`,
    `guarded` |-> `fin = asm_opt_finalizer`]
    (Q.INST [`lo` |-> `lo_reloc prog prog'`] request_cut_frontier_guards_reloc)) >>
  (impl_tac >- (rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
    TRY (rpt strip_tac >>
      qpat_assum `!l. FLOOKUP vs0.vs_labels l = OPTION_MAP n2w _`
        (qspec_then `"code_end"` mp_tac) >> simp[] >> NO_TAC) >>
    qpat_assum `(inst9 = inst8 /\ inst8.inst_opcode <> INVOKE /\ _) \/ _` mp_tac >>
    qpat_assum `stage 9 = out.po_unit.cu_context` (fn eq => PURE_REWRITE_TAC [eq]) >>
    POP_ASSUM_LIST (K all_tac) >> metis_tac[])) >>
  disch_then (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS)
     (CONJUNCTS_THEN2 assume_tac
       (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
         (qx_choose_then `terminal` assume_tac)))))
  >- suspend "static_crossing" >>
  `active_inst fn9 inst9 s9` by
    (qpat_assum `raw_reachable vs0 (stage 9) fn9 inst9 s9`
      (ACCEPT_TAC o MATCH_MP (SPEC_ALL raw_reachable_active))) >>
  request_cut_symbolic_plan_own >>
  mp_tac (Q.INST [`unit` |-> `out.po_unit`, `rp` |-> `rpolicy`, `es` |-> `es0`,
    `q9` |-> `JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9`,
    `stk` |-> `stk9`, `PG` |-> `PG9`, `G` |-> `G9`, `tn` |-> `tn9`,
    `oms` |-> `oms9`, `om` |-> `om9`, `hs` |-> `hs9`, `hist` |-> `hist9`,
    `planner_base` |-> `vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
       vs_return_pc_token := 0w; vs_inst_idx := 0|>`,
    `C` |-> `unit.cu_context`, `n` |-> `asm_fuel`, `m` |-> `0`, `post9` |-> `terminal`]
    (own_steps request_cut_stopped_terminal_crossed_own)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
    qpat_assum `stage 9 = out.po_unit.cu_context`
      (fn eq => first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [eq])))) >>
  qpat_assum `~(k < LENGTH s9.vs_requests)` (fn no_cross => simp_tac bool_ss [no_cross]);

val replay_static_crossing =
  `ALL_DISTINCT (fn_labels fn8)` by
    (qpat_assum `EVERY wf_function (stage 8).ctx_functions` mp_tac >>
     qpat_assum `MEM fn8 (stage 8).ctx_functions` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM, wf_function_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`C8` |-> `stage 8`, `v` |-> `vs0`, `q0` |-> `q80`,
    `evs` |-> `evs8`, `qs` |-> `qs8`,
    `tr` |-> `trace8`,
    `stopfn` |-> `fn8`, `stopinst` |-> `inst8`, `end8` |-> `s8`,
    `stk` |-> `stk8`, `PG` |-> `PG8`, `G` |-> `G8`, `tn` |-> `tn8`,
    `oms` |-> `oms8`, `om` |-> `om8`, `hs` |-> `hs8`, `hist` |-> `hist8`,
    `filling` |-> `ZIP (keys,raw)`] request_cut_observed_cover_before_static) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `Abbrev (orc = _)`
    (fn th => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  disch_then assume_tac >>
  `!p d fn i t. ev_reachable orc vs0 (stage 7) p d fn i t /\ LENGTH t.vs_requests <= k ==>
     ?ws. raw_reachable v7 (stage 7) fn i (t with vs_gas_readings := ws)` by
    (qpat_assum `!p d fn i t. ev_reachable orc vs0 (stage 7) p d fn i t ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `max_live_eom (stage 9) = SOME eom` by
    (qpat_assum `max_live_eom (stage 9) = max_live_eom (stage 7)`
       (fn eq => PURE_REWRITE_TAC [eq]) >>
     first_assum ACCEPT_TAC) >>
  `fin = asm_opt_finalizer ==> label_flow_own_ok (stage 9) /\ sym_unit_static_ok out.po_unit` by
    (qpat_assum `stage 9 = out.po_unit.cu_context` (fn eq => PURE_REWRITE_TAC [eq]) >>
     qpat_assum `fin = asm_opt_finalizer ==> focus_s7_symbolic_context_own T out.po_unit prog` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [focus_s7_symbolic_context_own_def] >> metis_tac[]) >>
  `!i l. MEM i (fn_insts fn9) /\ i.inst_opcode <> PHI /\
    MEM (Label l) (compute_operands i) ==> IS_SOME (FLOOKUP s9.vs_labels l)` by
    (rpt strip_tac >>
     qpat_assum `stage 9 = out.po_unit.cu_context` (fn eq =>
       qpat_assum `raw_reachable vs0 (stage 9) fn9 inst9 s9`
         (assume_tac o REWRITE_RULE [eq])) >>
     qpat_assum `!fn inst s i l. raw_reachable vs0 out.po_unit.cu_context fn inst s /\
          MEM i (fn_insts fn) /\ i.inst_opcode <> PHI /\
          MEM (Label l) (compute_operands i) ==> IS_SOME (FLOOKUP s.vs_labels l)`
        (drule_all_then ACCEPT_TAC)) >>
  mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `C9` |-> `stage 9`,
    `rp` |-> `rpolicy`, `src_unit` |-> `unit`, `unit` |-> `out.po_unit`, `es` |-> `es0`,
    `dft_view` |-> `o1_walk_view rpolicy 7`, `cfg_view` |-> `o1_walk_view rpolicy 8`,
    `source` |-> `v7`, `rounds` |-> `current0`, `cells` |-> `current1`,
    `h8` |-> `hist8`, `h9` |-> `hist9`] request_cut_static_crossing_own) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
    qpat_assum `stage 9 = out.po_unit.cu_context` (fn eq => PURE_REWRITE_TAC [eq]) >>
    first_assum ACCEPT_TAC)) >>
  qpat_assum `~(k < LENGTH s9.vs_requests)` (fn no_cross => simp_tac bool_ss [no_cross]);

val replay_endpoint_visit =
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?sf inc entry order res nrest bb bt ps xs ys (retained_order:num list) in_state h0
      body_entry retained_count front closed brest. FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\ _`
    (qx_choosel_then [`sf`, `inc`, `entry`, `order`, `res`, `nrest`, `bb`, `bt`, `ps`, `xs`,
      `ys`, `(retained_order:num list)`, `in_state`, `h0`, `body_entry`, `retained_count`, `front`, `closed`, `brest`]
      (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?q z src_inst cuts levels Mcut Ecut Kcut mr er kr. src_inst = _ /\ _`
    (qx_choosel_then [`q`, `z`, `src_inst`, `cuts`, `levels`, `Mcut`, `Ecut`, `Kcut`,
      `mr`, `er`, `kr`] (map_every assume_tac o CONJUNCTS)) >>
  `q < LENGTH xs /\ EL q xs = inst8 /\
   z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\ src_inst = inst8 /\
   EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst8` by
    (mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `packet` |-> `(j,obs)`,
       `q8` |-> `JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8`,
       `a` |-> `p`, `e` |-> `d`, `tf` |-> `fn8`, `inst` |-> `inst8`, `t` |-> `s8`,
       `row_order` |-> `(retained_order:num list)`, `hin` |-> `in_state`, `nseen` |-> `retained_count`]
       request_cut_packet_observation_body) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       qpat_assum `(IS_SOME body_entry /\ _) \/ _`
         (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS)) >>
       simp[])) >> simp[]) >>
  `keys = Kcut ++ kr` by simp[Abbr `keys`] >>
  qpat_assum `LIST_REL _ raw_slots raw`
    (fn rel => qpat_assum `raw_slots = Mcut ++ mr`
      (fn eq => strip_assume_tac (REWRITE_RULE [eq, LIST_REL_SPLIT1] rel))) >>
  rename1 `raw = (gs:bytes32 list) ++ (gr:bytes32 list)` >>
  `LENGTH Kcut = LENGTH gs` by
    (qpat_assum `LIST_REL _ Mcut gs` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     qpat_assum `LENGTH Mcut = LENGTH Kcut` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp_tac bool_ss []) >>
  `gs ++ (gr ++ [0w]) = raw ++ [0w]` by
    (qpat_assum `raw = gs ++ gr` (fn eq => PURE_REWRITE_TAC [eq]) >>
     simp_tac (srw_ss()) [APPEND_ASSOC]) >>
  Cases_on `?native_fuel u. N <= native_fuel /\
    rooted_eval native_fuel (stage 7) levels (root_entry with vs_gas_readings := raw ++ [0w]) = (Ecut,OK u)`
  >- suspend "endpoint_native_success" >>
  suspend "endpoint_native_stop";

val replay_endpoint_native_stop =
  `~is_pseudo inst8.inst_opcode` by
    (irule inv_memory_observation_nonpseudo >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `packet` |-> `(j,obs)`,
    `stk` |-> `stk8`, `PG` |-> `PG8`, `G` |-> `G8`, `tn` |-> `tn8`,
    `fn` |-> `fn8`, `inst` |-> `inst8`, `s` |-> `s8`, `oms` |-> `oms8`,
    `om` |-> `om8`, `hs` |-> `hs8`, `h` |-> `hist8`] dft_packet_return_data) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (choose_named
    ["ep_f","ep_inc","ep_ent","ep_order","ep_bb","ep_bt","ep_ps","ep_xs","ep_ys",
     "ep_rho","ep_in","ep_h0","ep_body","ep_at","ep_count"]
    (map_every assume_tac o CONJUNCTS)) >>
  `IS_SOME body_entry` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,(retained_order:num list),in_state,h0,body_entry,retained_count,front,closed,brest)`,
       `FLOOKUP blocks (p,d) =
         SOME (ep_bb,ep_bt,ep_ps,ep_xs,ep_ys,ep_rho,ep_in,ep_h0,SOME (ep_body,ep_at),
           ep_count,OK s8,F,NONE)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp_tac (srw_ss()) [] >>
     rpt strip_tac >> gvs[]) >>
  `EVERY (\x. ~is_terminator x.inst_opcode) (TAKE q xs) /\
    (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE retained_count (retained_order:num list)))` by
    (qpat_assum `(IS_SOME body_entry /\ _) \/ _` (DISJ_CASES_THEN mp_tac) >>
     qpat_assum `IS_SOME body_entry` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
  fixed_native_tape `p` `d` >>
  mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `v` |-> `vs0`,
    `lbl` |-> `lbl7`, `tr` |-> `trace8`,
    `q8` |-> `JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8`,
    `a` |-> `p`, `e` |-> `d`, `h` |-> `j`, `id` |-> `inst8.inst_id`,
    `fn` |-> `fn8`, `inst` |-> `inst8`, `s` |-> `s8`] request_cut_packet_observed_visit) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    (REFL_TAC ORELSE (simp_tac (srw_ss()) [Abbr `trace8`] >> NO_TAC)))) >>
  qpat_assum `Abbrev (orc = _)`
    (fn th => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  disch_then assume_tac >>
  conj_tac >- (
    mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `initial` |-> `vs0`,
      `inst` |-> `inst8`, `t` |-> `s8`, `v7` |-> `v7`, `filling` |-> `raw ++ [0w]`]
      request_cut_frontier_observation) >>
    (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      disj2_tac >> simp_tac bool_ss [Abbr `v7`] >> first_assum ACCEPT_TAC)) >>
    disch_then ACCEPT_TAC) >>
  first_assum ACCEPT_TAC;

val replay_endpoint_native_success =
  qpat_x_assum `?native_fuel u. N <= native_fuel /\ rooted_eval native_fuel _ _ _ = _`
    (qx_choosel_then [`native_fuel`, `u7`] strip_assume_tac) >>
  `rooted_eval native_fuel (stage 7) levels
    (root_entry with vs_gas_readings := gs ++ (gr ++ [0w])) = (Ecut,OK u7)` by
    (qpat_assum `gs ++ (gr ++ [0w]) = raw ++ [0w]`
       (fn eq => PURE_REWRITE_TAC [eq]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!F gs tail. N <= F /\ LIST_REL _ Mcut gs ==> _`
    (qspecl_then [`native_fuel`, `gs`, `gr ++ [0w]`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC [th]))
    [`rooted_eval native_fuel (stage 7) levels
      (root_entry with vs_gas_readings := gs ++ (gr ++ [0w])) = (Ecut,OK u7)`,
     `gs ++ (gr ++ [0w]) = raw ++ [0w]`] >>
  simp_tac (srw_ss()) [NoAsms, APPEND] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?before after. trace_blocks [] 0 native_fuel _ _ _ = _ /\ _`
    (qx_choosel_then [`before`, `after`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst8`
    (fn row => qpat_assum `trace_blocks [] 0 native_fuel _ _ _ = _`
      (assume_tac o SIMP_RULE bool_ss [row,APPEND])) >>
  `EVERY (\fn. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
      fn.fn_blocks) (stage 7).ctx_functions` by
    (qpat_assum `EVERY wf_function (stage 7).ctx_functions` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM] >>
     metis_tac[wf_fn_block_inst_ids_distinct]) >>
  `j < LENGTH trace8 /\ EL j trace8 = ((p,d,inst8.inst_id),fn8,inst8,s8)`
    by simp[Abbr `trace8`] >>
  mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `v` |-> `vs0`,
    `lbl` |-> `lbl7`, `fuel7` |-> `native_fuel`, `h` |-> `j`, `t` |-> `s8`,
    `a` |-> `p`, `e` |-> `d`, `inst` |-> `inst8`, `fn7` |-> `sf`, `s` |-> `u7`,
    `pre` |-> `before`, `q8` |-> `JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8`]
    request_cut_packet_native_visit) >>
  (impl_tac >- (rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE simp[Abbr `keys`, Abbr `orc`, Abbr `trace8`]))) >>
  strip_tac >>
  `raw_reachable v7 (stage 7) sf inst8 u7` by simp[Abbr `v7`] >>
  `active_inst sf inst8 u7 /\ active_inst fn8 inst8 s8` by
    (conj_tac
     >- qpat_assum `raw_reachable v7 (stage 7) sf inst8 u7`
          (ACCEPT_TAC o MATCH_MP (SPEC_ALL raw_reachable_active)) >>
     qpat_assum `raw_reachable vs0 (stage 8) fn8 inst8 s8`
       (ACCEPT_TAC o MATCH_MP (SPEC_ALL raw_reachable_active))) >>
  mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `packet` |-> `(j,obs)`,
    `a` |-> `p`, `e` |-> `d`, `tf` |-> `fn8`, `inst` |-> `inst8`,
    `t` |-> `s8`, `u` |-> `u7`, `row_order` |-> `(retained_order:num list)`, `hin` |-> `in_state`,
    `nseen` |-> `retained_count`, `q8` |-> `JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8`]
    request_cut_packet_visit_geometry) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `MEM sf (stage 7).ctx_functions` by
    (qpat_assum `raw_reachable v7 (stage 7) sf inst8 u7`
      (ACCEPT_TAC o MATCH_MP (SPEC_ALL raw_visit_function_member))) >>
  `dft_fn_rel sf fn8` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`MEM sf (stage 7).ctx_functions`, `fn8 = dft_fn sf`,
       `LIST_REL (\f g. g = dft_fn f) (stage 7).ctx_functions (stage 8).ctx_functions`,
       `LIST_REL dft_fn_rel (stage 7).ctx_functions (stage 8).ctx_functions`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[LIST_REL_EL_EQN,MEM_EL] >> metis_tac[]) >>
  `~in_revert_forward sf u7` by
    (strip_tac >>
     mp_tac (Q.INST [`C` |-> `stage 7`, `fn` |-> `sf`, `inst` |-> `inst8`,
       `a` |-> `u7`, `b` |-> `s8`] inv_forward_active) >>
     qpat_assum `fn8 = dft_fn sf` (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  conj_tac
  >- (disj1_tac >>
      qexistsl_tac [`sf`, `u7 with vs_gas_readings := vs0.vs_gas_readings`, `u7.vs_gas_readings`] >>
      `(u7 with vs_gas_readings := vs0.vs_gas_readings)
          with vs_gas_readings := u7.vs_gas_readings = u7` by
        simp_tac (srw_ss()) [venom_state_component_equality] >>
      qpat_assum `(u7 with vs_gas_readings := _) with vs_gas_readings := _ = u7`
        (fn eq => PURE_REWRITE_TAC [eq]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (
        qpat_assum `~in_revert_forward sf u7` mp_tac >>
        simp_tac (srw_ss()) [in_revert_forward_def]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      simp_tac (srw_ss()) [] >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC;

val replay_exit =
  qx_gen_tac `D` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  request_cut_frame_projection_own >>
  mp_tac (CONV_RULE (DEPTH_CONV BETA_CONV)
    (PURE_REWRITE_RULE [LET_THM]
      request_cut_replay_own)) >>
  (impl_tac >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac))) >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `orc` (map_every assume_tac o CONJUNCTS))
    (map_every assume_tac o CONJUNCTS))
  >- (conj_tac
      >- (disj1_tac >> qexists_tac `orc` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >>
      `fin = asm_opt_finalizer ==>
        (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
          ~MEM (Label "code_end") inst.inst_operands) /\
        LENGTH vs0.vs_data_section < dimword (:256) DIV 2` by
        (qpat_assum `fin = asm_opt_finalizer ==> label_flow_own_ok unit.cu_context /\ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
      mp_tac focus_static_replay_exit_for >>
      (impl_tac >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac))) >>
      disch_then ACCEPT_TAC) >>
  conj_tac >- (disj2_tac >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
  strip_tac >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac ORELSE disj2_tac);

Theorem focus_finalizer_selected_request_replay_own:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
  code_layout_valid vs0 /\
  unit_shape_ok out.po_unit /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy out.po_unit = SOME prog /\
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  (fin = asm_opt_finalizer ==>
     label_flow_own_ok unit.cu_context /\
     (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                ~MEM (Label "code_end") inst.inst_operands) /\
     EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                       ds.ds_items) unit.cu_data_segment /\
     ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                 MEM inst (fn_insts fn) /\
                 MEM (Label "runtime_begin") inst.inst_operands) ==>
      EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
     LENGTH vs0.vs_data_section < dimword (:256) DIV 2) /\
  (vs0.vs_call_ctx.cc_static ==>
     !fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
               ~MEM (Label "runtime_begin") inst.inst_operands) /\
  vs0.vs_code = assemble prog' ++ vs0.vs_data_section /\
  codegen_asm_entry_rel_reloc (lo_reloc prog prog') cpl prog vs0
    (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es0
    (entry_asm_state vs0 es0) es0 /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
  unit_alloca_budget unit.cu_context +
    32 * ctx_dload_count unit.cu_context <= w2n fmp /\
  (!gs. ?D f extra.
    dead_wf D /\
    (fin = asm_opt_finalizer ==>
       !fn inst s.
         raw_reachable (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
           unit.cu_context fn inst s /\
         gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs))
           (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) s ==>
         inst_dload_in_section inst s) /\
    o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
      unit.cu_context (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
    MAP project
      (gas_events_blocks f unit.cu_context entryfn
        (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp;
                    vs_prev_bb := NONE;
                    vs_current_bb := lbl; vs_inst_idx := 0|>)) =
      markf gs ++ extra) /\
  run_call es0 = SOME (result,final) /\
  ~frame_resource_starved es0 result final /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  run_callee_first rpolicy o1_fn_passes
    (fcg_postorder (fcg_analyze pre.cu_context) nm)
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
    SOME (out.po_unit,t') /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage 9 = out.po_unit.cu_context /\
  (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
    (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
    EVERY (o1_fn_row k) (stage k).ctx_functions) ==>
  ?raw_slots sites unused.
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
    !raw.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
      (?rest. MAP project sites = markf (raw ++ [0w]) ++ rest) /\
      (!D.
        (?fr. terminates (run_context fr unit.cu_context
           (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>))) /\
        dead_wf D /\
        o1_pre_walk_inv D unit.cu_context
          (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
        (fin = asm_opt_finalizer ==>
           mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                     s.vs_code = vs0.vs_code /\ s.vs_data_section = vs0.vs_data_section)
             unit.cu_context (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
        (((?orc.
          (!fuel. gas_res_rel (run_context fuel (stage 7)
            (vs0 with vs_gas_readings := raw ++ [0w]))
            (ev_context orc fuel (stage 7) vs0)) /\
          (!fuel. gas_res_rel (run_context fuel (stage 8) vs0)
            (ev_context orc fuel (stage 8) vs0)) /\
          (!p d fn inst s. ev_reachable orc vs0 (stage 7) p d fn inst s ==>
            ?ws. raw_reachable (vs0 with vs_gas_readings := raw ++ [0w])
                 (stage 7) fn inst (s with vs_gas_readings := ws)) /\
          (!fn inst s. raw_reachable vs0 (stage 8) fn inst s ==>
            ?p d. ev_reachable orc vs0 (stage 8) p d fn inst
              (s with vs_gas_readings := vs0.vs_gas_readings))) \/
         (vs0.vs_call_ctx.cc_static /\
          ctx_sim D unit.cu_context out.po_unit.cu_context
            (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
          ctx_abort_rq D unit.cu_context out.po_unit.cu_context
            (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
          (fin = asm_opt_finalizer ==>
             code_end_offset_ok
               (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
                 ~in_static_abort_prefix fn s) out.po_unit.cu_context) /\
          (?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
            mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                      lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
              out.po_unit.cu_context vs0) /\
          (!fuel. terminates (run_context fuel unit.cu_context
                    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
                  ?u. run_context fuel unit.cu_context
                        (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) =
                      Abort ExHalt_abort u))) /\
        ((!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
           ~MEM (Label "runtime_begin") inst.inst_operands) ==>
        ctx_sim D unit.cu_context out.po_unit.cu_context
          (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
        ctx_abort_rq D unit.cu_context out.po_unit.cu_context
          (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
        (fin = asm_opt_finalizer ==>
           code_end_offset_ok
             (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
               ~in_static_abort_prefix fn s) out.po_unit.cu_context) /\
        ((o1_lowered_inv out.po_unit.cu_context vs0 /\
          (fin = asm_opt_finalizer ==>
             code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context)) \/
         ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
            mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                      lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
              out.po_unit.cu_context vs0) /\
          !fuel. terminates (run_context fuel unit.cu_context
                    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
                 ?u. run_context fuel unit.cu_context
                       (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) =
                     Abort ExHalt_abort u))))) /\
      (!D k vs fn inst s fuel s'.
        (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
           ~MEM (Label "runtime_begin") inst.inst_operands) /\
        vs = (vs0 with <|vs_gas_readings := raw ++ [0w];
                         vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
        dead_wf D /\ raw_safe_rq_upto D 0 k unit.cu_context vs /\
        raw_reachable vs unit.cu_context fn inst s /\
        inst.inst_opcode <> INVOKE /\ LENGTH s.vs_requests = k /\
        step_inst fuel unit.cu_context inst s = OK s' /\
        k < LENGTH s'.vs_requests ==>
        (?fn' inst' t fuel' t'.
          raw_reachable vs0 out.po_unit.cu_context fn' inst' t /\
          inst'.inst_opcode <> INVOKE /\ LENGTH t.vs_requests = k /\
          step_inst fuel' out.po_unit.cu_context inst' t = OK t' /\
          k < LENGTH t'.vs_requests /\
          request_agree_except D (EL k s'.vs_requests) (EL k t'.vs_requests) /\
          t.vs_outcomes = s.vs_outcomes) /\
        ctx_rq_upto D k unit.cu_context out.po_unit.cu_context vs vs0 /\
        (?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
          mem_inv (\ctx fn inst t. (request_cut k t /\ ~in_static_abort_prefix fn t) ==>
            lowered_mem_ok eom (w2n t.vs_initial_fmp) ctx fn inst t)
            out.po_unit.cu_context vs0) /\
        (fin = asm_opt_finalizer ==>
          code_end_offset_ok (\ctx fn inst t.
            raw_reachable vs0 ctx fn inst t /\ request_cut k t /\
            ~in_static_abort_prefix fn t) out.po_unit.cu_context))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  request_cut_setup_own >>
  replay_begin focus_walk_stopped_selection_own request_cut_entry_facts_own_tac
QED

Resume focus_finalizer_selected_request_replay_own[clipped]:
  replay_clipped
QED

Resume focus_finalizer_selected_request_replay_own[stopped]:
  replay_stopped
QED

Resume focus_finalizer_selected_request_replay_own[historical_root]:
  replay_historical_root
QED

Resume focus_finalizer_selected_request_replay_own[join_recording]:
  replay_join_recording
QED

Resume focus_finalizer_selected_request_replay_own[earlier_native_stop]:
  replay_earlier_native_stop
QED

Resume focus_finalizer_selected_request_replay_own[other_stop]:
  replay_other_stop
QED

Resume focus_finalizer_selected_request_replay_own[endpoint_observation]:
  replay_endpoint_observation
QED

Resume focus_finalizer_selected_request_replay_own[static_crossing]:
  replay_static_crossing
QED

Resume focus_finalizer_selected_request_replay_own[endpoint_visit]:
  replay_endpoint_visit
QED

Resume focus_finalizer_selected_request_replay_own[endpoint_native_stop]:
  replay_endpoint_native_stop
QED

Resume focus_finalizer_selected_request_replay_own[endpoint_native_success]:
  replay_endpoint_native_success
QED

Resume focus_finalizer_selected_request_replay_own[exit]:
  replay_exit
QED

Finalise focus_finalizer_selected_request_replay_own
