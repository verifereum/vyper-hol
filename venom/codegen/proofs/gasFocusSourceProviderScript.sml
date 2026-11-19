Theory gasFocusSourceProvider
Ancestors
  lowerDloadSafetyKernel[qualified,ignore_grammar] gasFocusSourceStages
  dftFinitePacket dftGasFromListTraceDefs
  o1ContractCfgNormJointCursors frameJointTrace frameJointTransition
  fnFramePrefixDriver fnFrameSymbolicPrefix codegenEntryRel
  o1PipelineCorrect o1SafeUpto o1PassContract o1PassLift unitMemInv
  venomPipelineRunner venomPassSchedule irSupply fcgDefs
  dftGasOracleDefs gasEvents contextRawReachable memSafeRun
  venomExecSemantics venomWf venomInst venomState unitShapeDefs
  codegenSymRel asmDataEnv asmFrameRel asmOptimizer asmSem asmSymSem symbolResolve
  contextCodegenRel lowerDloadDefs staticAbortDefs frameOutcome callTrace
  o1RequestContract unitTransformDefs ptrDiscipline passSimulationDefs
  vfmExecution codegen asmIR
  finite_map list rich_list words arithmetic
  o1CodeEndSourceCutTransport o1ComposeSupport o1PipelineCompose simplifyCfgDefs
  makeSsaDefs o1ContractSimplifyCfg
  gasFocusFmpCutEntryStatic gasFocusFmpStagePin o1LowerDloadSourceEntry
  fmpStageCoverInv fmpStageCoverMem fmpStageRel fmpLowerDefs fmpStepLayout
  fmpStepStructural fmpAnalysisProps fmpStageFmpStepsEntryLayout
  ctxLookupAgreeHelpers gasFocusFmpCutResidual concretizeLayoutCutSafe
  gasFocusLowerDloadCodecopyPoint lowerDloadSafetyRelation lowerDloadSafetyAmbient o1LowerDloadPtrDiscipline lowerDloadPtrSupport
  o1ContractSimplifyCfgSrcFrame simplifyCfgAvailability ptrStaticDiscipline
  allocaFrontierBound fmpStageControl fmpStageCallArity fmpStageCoverBackParam
  fmpStageCoverBackKeptOps fmpCoverInvokeIndex lowerDloadPtrRawReachable
  gasFocusFmpCutSites gasFocusFmpCutSegments gasFocusFmpCutRestorePrefix
  fmpStageFmpStepsRestoreControl fmpStepReclaim analysisSimDefs
  gasFocusFmpCutForwardLayout gasFocusFmpRetpcPoint
  lowerDloadNormalDispatch o1LowerDloadJointRetpc gasFocusFmpCutSourceJump
  gasFocusFmpCutJumpEntry gasFocusFmpJumpPoint fmpStageRunnerFacts
  gasFocusFmpCutSourceCall gasFocusFmpCutInvokePush gasFocusFmpCutInvokeOutputs
  gasFocusFmpCutSourceReturn gasFocusFmpCutInvokePop
  concretizePtrCoverageStaticMemReachability frameAllocationOwnership
  fmpStepPredicateTransport fmpStepRewrite fmpStepRestrictionClosure fmpStepBridge
  concretizeAllocationFree o1MakeSsaStructuralShape o1ContractMakeSsaReplay
  simplifyCfgInvariant o1ContractSue singleUseExpansionSupplySim callLayoutDefs gasFocusConcretizeEndpointCut gasFocusConcretizeHistoricalCut o1CodeEndConcretizeRead o1LabelFlowMiddleConcretize o1LabelFlowMiddleFmp concretizePtrChronologicalHistory concretizePtrPairedPrefix concretizePtrStructuralTranscript concretizePtrStructuralTrace concretizePtrSourceOwnership concretizePtrParamSupport concretizePtrRequestHistory concretizePtrOperationalOpcodes concretizePtrChronologicalDemand lowerDloadReachability lowerDloadRevertSuffix concretizeMemLocDefs venomExecProofs pred_set passSharedDefs concretizeStepStructure concretizePtrPairedFields unitLabelMapIdentity stepWriteFootprintBase

(* Entry and source-point facts for the bounded FMP frame induction. *)
Theorem focus_fmp_src_active[local]:
  wf_function fn /\ first_block_no_phi fn /\ fn_entry_label fn = SOME lbl ==>
  ?inst. active_inst fn inst
    (root with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
Proof
  Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >>
  strip_tac >> rename1 `fn.fn_blocks = bb::bbs` >>
  `bb.bb_instructions <> []` by metis_tac[wf_function_def, bb_well_formed_def, MEM] >>
  Cases_on `bb.bb_instructions` >>
  gvs[active_inst_def, get_instruction_def, lookup_block_def, FIND_thm] >>
  qexists `bb` >> simp[]
QED

Theorem focus_fmp_target_entry[local]:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\ wf_function fn /\ entry_fn_no_params fn /\
  first_block_no_phi fn /\ fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn /\
  o1_initial_state_ok v /\ v.vs_fmp = v.vs_initial_fmp /\ code_layout_valid v /\
  w2n v.vs_initial_fmp <= w2n fmp ==>
  ?fn' bb p u inst s t.
    lookup_function name C4.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\ first_block_no_phi fn' /\
    lookup_block lbl fn'.fn_blocks = SOME bb /\
    s = (v with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                  vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
    t = (v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
    frame_reachable (v with <|vs_fmp := fmp; vs_initial_fmp := fmp|>)
      C3 [] [] FEMPTY entry_taint fn inst s /\ active_inst fn inst s /\ ~s.vs_halted /\
    fmp_stage_rel D C4 FEMPTY (w2n v.vs_initial_fmp) (w2n fmp) eom F
      [] [] FEMPTY entry_taint fn s (w2n v.vs_initial_fmp) u [] /\
    u.vs_current_bb = lbl /\ u.vs_inst_idx = p /\
    u.vs_gas_readings = v.vs_gas_readings /\
    (!k. fmp_target_run k C4 name t p u) /\
    (!i. i < p ==> i < LENGTH bb.bb_instructions /\
                   fmp_inserted_op (EL i bb.bb_instructions).inst_opcode)
Proof
  strip_tac >> drule_all focus_fmp_selected_root_pin >> strip_tac >>
  `?ctx1 sp sp'. fmp_lower_function ctx1 sp fn = SOME (fn',sp')` by
    (fs[fmp_stage_lowered_def] >>
     rename1 `fmp_lower_function_with_info info0 ctx0 supply fn = SOME (fn',supply')` >>
     qexistsl [`ctx0`, `supply`, `supply'`] >> simp[fmp_lower_function_def]) >>
  `first_block_no_phi fn'` by metis_tac[fmp_lower_function_first_block_no_phi] >>
  `?bb. lookup_block lbl fn'.fn_blocks = SOME bb` by
    metis_tac[fmp_entry_target_block] >>
  qabbrev_tac `root = v with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  qabbrev_tac `s = root with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` >>
  `enters_block fn s s` by
    (simp[Abbr `s`] >> metis_tac[dload_no_phi_entry]) >>
  `?inst. active_inst fn inst s` by
    (simp[Abbr `s`] >> metis_tac[focus_fmp_src_active]) >>
  `frame_reachable root C3 [] [] FEMPTY entry_taint fn inst s` by
    (irule frame_reachable_entry >> metis_tac[Abbr `s`]) >>
  mp_tac (Q.INST [`u` |-> `root`, `s` |-> `s`, `v` |-> `v`,
                   `rpolicy` |-> `rp`, `D` |-> `D`, `eom` |-> `eom`]
                 focus_fmp_cut_entry_static) >>
  impl_tac >- (simp[Abbr `root`] >> metis_tac[Abbr `s`]) >>
  disch_then (qx_choose_then `f4` (qx_choose_then `p` (qx_choose_then `u4` strip_assume_tac))) >>
  qexistsl [`f4`, `bb`, `p`, `u4`, `inst`, `s`,
            `v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`] >>
  gvs[Abbr `root`, Abbr `s`, o1_initial_state_ok_def, fmp_inserted_op_def,
      update_var_def, mk_inst_def]
QED

(* These quotations are the three recurrent formulas of the induction;
   they introduce no new predicates. *)
val focus_fmp_matched = ``
  ?stk PG G tn fn inst s sm lo u ts restored bb.
    frame_reachable root3 C3 stk PG G tn fn inst s /\
    active_inst fn inst s /\ ~s.vs_halted /\ gas_cut n root3 s /\
    (restored ==> MEM inst.inst_opcode [DALLOCA; INVOKE] \/
                  is_terminator inst.inst_opcode) /\
    fmp_stage_rel D C4 sm (w2n root4.vs_initial_fmp) (w2n (fmp:256 word)) eom restored
      stk PG G tn fn s lo u ts /\
    lookup_function fn.fn_name C4.ctx_functions = SOME fn' /\
    fmp_cov_stack C4 stk ts stk' /\
    LIST_REL (\f g. g.cf_inst.inst_outputs = f.cf_inst.inst_outputs) stk stk' /\
    t.vs_current_bb = u.vs_current_bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
    t.vs_inst_idx <= u.vs_inst_idx /\
    s.vs_gas_readings = u.vs_gas_readings /\ u.vs_gas_readings = t.vs_gas_readings /\
    (!k. fmp_target_run k C4 fn.fn_name t (u.vs_inst_idx - t.vs_inst_idx) u) /\
    (!i. t.vs_inst_idx <= i /\ i < u.vs_inst_idx ==>
         i < LENGTH bb.bb_instructions /\
         fmp_inserted_op (EL i bb.bb_instructions).inst_opcode)``;

val focus_fmp_tail = ``
  ?bb p j. ALL_DISTINCT (fn_labels fn') /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
    revert_forward_pair bb p j /\ p < t.vs_inst_idx /\ t.vs_inst_idx <= j``;

val focus_fmp_fields = ``
  !stk PG G tn fn inst s.
    frame_reachable root3 C3 stk PG G tn fn inst s /\ gas_cut n root3 s ==>
    access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
    allocas_from eom s /\ (ctx_has_dalloca C3 ==> allocas_below_fmp s) /\
    (?P. fn_static_ptr_ok P fn /\ ptr_use_static_ok P (fn_pv P fn) inst /\
         FDOM G SUBSET fn_pv P fn)``;

Theorem focus_fmp_matched_entry[local]:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME src /\
  fn_entry_label src = SOME src_lbl /\ o1_ctx_shape C3 /\ fmp_free_ctx C3 /\
  o1_initial_state_ok root4 /\ root4.vs_fmp = root4.vs_initial_fmp /\
  code_layout_valid root4 /\ w2n root4.vs_initial_fmp <= w2n fmp /\
  root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  C4.ctx_entry = SOME name' /\ lookup_function name' C4.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  enters_block fn' (root4 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  gas_cut n root4 t ==>
  ^(subst [``stk':call_frame list`` |-> ``[]:call_frame list``] focus_fmp_matched)
Proof
  strip_tac >>
  `name' = name` by fs[ctx_pass_stage_def] >>
  `MEM src C3.ctx_functions /\ src.fn_name = name` by
    metis_tac[lookup_function_MEM, lookup_function_selected_name] >>
  `wf_function src /\ first_block_no_phi src /\ entry_fn_no_params src /\
   src.fn_fmp_signature = NONE /\ pre_fmp_ops src` by
    (fs[o1_ctx_shape_def, fmp_free_ctx_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  drule_all focus_fmp_target_entry >>
  disch_then (qspecl_then [`eom`, `D`] strip_assume_tac) >> gvs[] >>
  qpat_x_assum `enters_block _ _ _` mp_tac >> simp[dload_no_phi_entry] >>
  disch_then SUBST_ALL_TAC >>
  qexistsl [`[]`, `FEMPTY`, `entry_taint`, `src`, `inst`,
    `root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp; vs_prev_bb := NONE;
                  vs_current_bb := u.vs_current_bb; vs_inst_idx := 0|>`,
    `FEMPTY`, `w2n root4.vs_initial_fmp`, `u`, `[]`, `F`] >>
  gvs[fmp_cov_stack_def, gas_cut_def]
QED

Theorem focus_fmp_source_points[local]:
  o1_ctx_shape C3 /\ EVERY (o1_fn_row 3) C3.ctx_functions /\
  fmp_free_ctx C3 /\ root3.vs_vars = FEMPTY /\ ~root3.vs_halted /\
  frame_reachable root3 C3 stk PG G tn fn inst s /\ active_inst fn inst s /\
  ^focus_fmp_fields /\ gas_cut n root3 s ==>
  lookup_function fn.fn_name C3.ctx_functions = SOME fn /\
  o1_fn_shape C3 fn /\ o1_fn_row 3 fn /\ fn_inst_wf fn /\ wf_function fn /\
  make_ssa_input_ok fn /\ pre_fmp_ops fn /\ fn.fn_fmp_signature = NONE /\
  (!v. inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
       IS_SOME (lookup_var v s)) /\
  access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
  allocas_from eom s /\ (ctx_has_dalloca C3 ==> allocas_below_fmp s) /\
  (?P. fn_static_ptr_ok P fn /\ ptr_use_static_ok P (fn_pv P fn) inst /\
       FDOM G SUBSET fn_pv P fn)
Proof
  strip_tac >>
  `!nm f. lookup_function nm C3.ctx_functions = SOME f ==> wf_function f` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  drule_all scfg_frame_reachable_entry_root >> strip_tac >>
  `lookup_function fn.fn_name C3.ctx_functions = SOME fn` by
    (drule_all scfg_frame_reachable_rooted >>
     disch_then (strip_assume_tac o MATCH_MP scfg_rooted_elim) >>
     metis_tac[lookup_function_selected_name]) >>
  `MEM fn C3.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `o1_fn_shape C3 fn /\ o1_fn_row 3 fn /\ fn.fn_fmp_signature = NONE` by
    (fs[o1_ctx_shape_def, fmp_free_ctx_def, EVERY_MEM] >> metis_tac[]) >>
  `wf_function fn /\ fn_inst_wf fn /\ make_ssa_input_ok fn /\ pre_fmp_ops fn` by
    fs[o1_fn_shape_def, o1_fn_row_def] >>
  `!v. inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
       IS_SOME (lookup_var v s)` by
    (fs[make_ssa_input_ok_def] >> metis_tac[scfg_frame_operand_defined]) >>
  qpat_assum `!stk PG G tn fn inst s. frame_reachable _ _ _ _ _ _ _ _ _ /\ _ ==> _`
    drule_all >> simp[]
QED

Theorem focus_fmp_source_call_arity[local]:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  o1_ctx_shape C3 /\ fmp_free_ctx C3 ==>
  !stk PG G tn caller ivk st nm args callee.
    frame_reachable vs C3 stk PG G tn caller ivk st /\
    active_inst caller ivk st /\ ivk.inst_opcode = INVOKE /\
    ivk.inst_operands = Label nm::args /\
    lookup_function nm C3.ctx_functions = SOME callee ==>
    LENGTH (fn_user_param_insts callee) <= LENGTH args
Proof
  rpt strip_tac >>
  `MEM caller C3.ctx_functions` by metis_tac[frame_reachable_raw_certificate] >>
  `caller.fn_fmp_signature = NONE` by fs[fmp_free_ctx_def, EVERY_MEM] >>
  `lookup_function caller.fn_name C3.ctx_functions = SOME caller` by
    (irule fmpLowerPropsTheory.fmp_lookup_function_self >>
     fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  `MEM ivk (fn_insts caller)` by metis_tac[active_inst_mem_fn_insts] >>
  `decode_invoke ivk = SOME (nm,args)` by simp[decode_invoke_def] >>
  drule_all fmp_stage_invoke_arity_static >> simp[]
QED

Theorem focus_fmp_aligned_layout[local]:
  wf_function fn /\ ALL_DISTINCT (fn_labels fn') /\
  active_inst fn inst s /\ active_inst fn' ti t /\
  fmp_stage_rel D C4 sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C4.ctx_functions = SOME fn' ==>
  ?infos ctx runner bs bt.
    fmp_stage_lowered infos ctx runner fn fn' /\
    t.vs_current_bb = s.vs_current_bb /\ w2n t.vs_initial_fmp = fmp0 /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bs /\
    s.vs_inst_idx < LENGTH bs.bb_instructions /\
    inst = EL s.vs_inst_idx bs.bb_instructions /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
    get_instruction bt t.vs_inst_idx = SOME ti /\
    t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) s.vs_current_bb bs.bb_instructions s.vs_inst_idx +
      (if restored /\ (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
       then 1 else 0)
Proof
  strip_tac >> drule_all fmp_cov_frame_pos >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  `?bs. lookup_block s.vs_current_bb fn.fn_blocks = SOME bs /\
        get_instruction bs s.vs_inst_idx = SOME inst` by
    metis_tac[active_inst_block_lookup] >>
  `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
        get_instruction bt t.vs_inst_idx = SOME ti` by
    metis_tac[active_inst_block_lookup] >>
  first_x_assum drule >> strip_tac >>
  qexistsl [`infos`, `ctx`, `runner`, `bs`, `bt`] >> fs[get_instruction_def]
QED

Theorem focus_opt_lower_inst_no_dload[local]:
  lower_dload_inst_supply s i = (xs,t) /\ inst_wf i ==>
  EVERY (\j. j.inst_opcode <> DLOAD /\ j.inst_opcode <> DLOADBYTES) xs
Proof
  strip_tac >> Cases_on `i.inst_opcode = DLOAD`
  >- (fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      gvs[lower_dload_inst_supply_def, AllCaseEqs()]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      gvs[lower_dload_inst_supply_def, AllCaseEqs()]) >>
  gvs[lower_dload_inst_supply_def]
QED

(* Neither source DLOAD opcode survives expansion in a well-formed stage. *)
Theorem focus_opt_lower_no_dload[local]:
  ctx_pass_stage rp (CFP_Simple VP_LowerDload) view C C' /\
  o1_ctx_shape C /\ MEM g C'.ctx_functions /\ MEM j (fn_insts g) ==>
  j.inst_opcode <> DLOAD /\ j.inst_opcode <> DLOADBYTES
Proof
  strip_tac >>
  `?f s t. MEM f C.ctx_functions /\ lower_dload_function_supply s f = (g,t)` by
    (qpat_x_assum `MEM j (fn_insts g)` kall_tac >>
     fs[ctx_pass_stage_def, LIST_REL_EL_EQN] >>
     qpat_x_assum `MEM g C'.ctx_functions` mp_tac >> simp[MEM_EL] >>
     strip_tac >> first_x_assum (qspec_then `n` mp_tac) >>
     impl_tac >- fs[] >> strip_tac >>
     gvs[fn_pass_step_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all o1ContractLowerDloadTheory.lower_dload_function_supply_member >>
  strip_tac >>
  `inst_wf i` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, fn_inst_wf_def,
        fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  drule_all focus_opt_lower_inst_no_dload >> simp[EVERY_MEM] >>
  disch_then drule >> simp[]
QED

(* Induct on the observed C4 history, keeping the independent C3
   reachability and the gas-reading alignment in the motive. *)
Theorem focus_opt_fmp_cut_cover:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  o1_pre 3 C3 C4 /\ o1_ctx_shape C3 /\ o1_ctx_shape C4 /\
  EVERY (o1_fn_row 3) C3.ctx_functions /\ EVERY ssa_form C3.ctx_functions /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME src /\
  fn_entry_label src = SOME src_lbl /\
  o1_initial_state_ok root4 /\ root4.vs_fmp = root4.vs_initial_fmp /\
  code_layout_valid root4 /\ w2n root4.vs_initial_fmp <= w2n fmp /\
  root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  dead_wf D /\ fmp_free_ctx C3 /\ taint_within_upto D n C3 root3 /\
  (!g i v. raw_reachable root3 C3 g i v /\ gas_cut n root3 v ==> dalloca_no_wrap i v) /\
  ^focus_fmp_fields /\
  eom <= w2n root4.vs_initial_fmp /\ fmp_variant_room (SOME fmp) C4 root4 /\
  callee_first names C3.ctx_functions ==>
  !stk' PG' G' tn' fn' ti t.
    frame_reachable root4 C4 stk' PG' G' tn' fn' ti t /\ gas_cut n root4 t ==>
    ^focus_fmp_matched \/ ^focus_fmp_tail
Proof
  strip_tac >>
  `!vs ctx stk' PG' G' tn' fn' ti t.
     frame_reachable vs ctx stk' PG' G' tn' fn' ti t ==>
     vs = root4 /\ ctx = C4 /\ gas_cut n root4 t ==> ^focus_fmp_matched \/ ^focus_fmp_tail`
    suffices_by
      (disch_then (qspecl_then [`root4`, `C4`] mp_tac) >>
       rewrite_tac[] >> disch_then (fn th => rpt gen_tac >> strip_tac >>
         drule th >> simp[]) >> simp[]) >>
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac >>
  rpt strip_tac >> gvs[]
  >- (disj1_tac >>
      irule (SRULE [] (Q.INST
        [`root3` |-> `root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>`]
        focus_fmp_matched_entry)) >> metis_tac[])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume focus_opt_fmp_cut_cover[block]:
  `MEM ti.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[fnBlockBodyHelpersTheory.step_ok_terminator_jump, MEM] >>
  `ti.inst_opcode <> INVOKE` by (fs[MEM] >> simp[]) >>
  `gas_cut n root4 t` by
    (irule gas_cut_readings_mono >> first_assum (irule_at Any) >>
     drule enters_block_readings >> strip_tac >> simp[] >>
     irule step_inst_noninvoke_readings_le >> metis_tac[]) >>
  qpat_x_assum `gas_cut n root4 t ==> _` drule >>
  reverse (disch_then (DISJ_CASES_THEN strip_assume_tac))
  >- (drule_all (Q.INST [`eom` |-> `eom`, `C4` |-> `C4`] focus_fmp_cut_tail_observation) >>
      strip_tac >> gvs[MEM]) >>
  `ALL_DISTINCT (fn_labels fn')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  `get_instruction bb t.vs_inst_idx = SOME ti` by
    (qpat_assum `active_inst fn' ti t` (mp_then Any drule_all active_inst_block_lookup) >>
     strip_tac >> metis_tac[optionTheory.SOME_11]) >>
  `u = t` by
    (Cases_on `t.vs_inst_idx < u.vs_inst_idx`
     >- (qpat_assum `!i. _ <= i /\ _ ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
         gvs[get_instruction_def, fmp_inserted_op_def, MEM]) >>
     `u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
     metis_tac[fmp_target_run_zero]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  `(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_vars = FEMPTY /\
   ~(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_halted` by
    fs[o1_initial_state_ok_def] >>
  drule_all focus_fmp_source_points >> strip_tac >>
  `ssa_form fn` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  qabbrev_tac `root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `w2n root3.vs_fmp = w2n fmp` by simp[Abbr `root3`] >>
  `?m l. fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n fmp) eom T
           stk PG G tn fn s l t ts` by
    (`ti.inst_opcode <> ASSIGN` by (fs[MEM] >> simp[]) >>
     qpat_x_assum `MEM ti.inst_opcode _` kall_tac >>
     Cases_on `restored` >- metis_tac[] >> gvs[] >>
     drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_restore_prefix)) >>
     disch_then (qx_choosel_then
       [`rest_fn`, `rest_src`, `rest_bb`, `rest_infos`, `rest_ctx`,
        `rest_runner`, `rest_len`, `rest_post`, `rest_cut`] strip_assume_tac) >>
     Cases_on `FLOOKUP (fmp_stage_plan rest_infos rest_ctx fn) (s.vs_current_bb,s.vs_inst_idx)`
     >- (gvs[] >> metis_tac[]) >>
     gvs[get_instruction_def, mk_inst_def]) >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ restored _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all focus_fmp_aligned_layout >> strip_tac >>
  `pre_fmp_opcode inst.inst_opcode` by
    (qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
     metis_tac[active_inst_mem_fn_insts]) >>
  `inst = ti` by
    (Cases_on `MEM inst.inst_opcode [DALLOCA; RETPC_PARAM]`
     >- (qabbrev_tac `plan = fmp_stage_plan infos ctx fn` >>
         qabbrev_tac `rt = fmp_stage_root infos ctx fn` >>
         qabbrev_tac `idx = s.vs_inst_idx` >>
         qabbrev_tac `lab = s.vs_current_bb` >>
         `fmp_stage_tidx plan rt lab bs.bb_instructions idx +
            (if (lab,idx) IN FDOM plan then 1 else 0) <
          fmp_stage_tidx plan rt lab bs.bb_instructions (SUC idx)` by
           (simp[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
            Cases_on `rt` >> simp[]
            >- (IF_CASES_TAC >> simp[]) >>
            rename1 `SOME r = fmp_stage_root _ _ _` >> PairCases_on `r` >> simp[] >>
            rpt (IF_CASES_TAC >> simp[]) >> decide_tac) >>
         mp_tac (Q.INST [`P` |-> `fmp_inserted_op`, `infos` |-> `infos`,
                         `ctx` |-> `ctx`, `runner` |-> `runner`, `fn` |-> `fn`,
                         `fn'` |-> `fn'`, `lbl` |-> `lab`, `bb` |-> `bs`,
                         `idx` |-> `idx`, `i` |-> `t.vs_inst_idx`]
             fmpStageCoverMemAssembleTheory.fmp_cover_inserted_from_root_structural) >>
         (impl_tac >- (simp[fmp_inserted_op_def, Abbr `rt`, Abbr `plan`] >>
                       rw[] >> gvs[MEM])) >>
         strip_tac >> gvs[get_instruction_def, fmp_inserted_op_def, MEM]) >>
     Cases_on `inst.inst_opcode = INVOKE`
     >- (`(EL s.vs_inst_idx bs.bb_instructions).inst_opcode = INVOKE` by metis_tac[] >>
         drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                           `idx` |-> `s.vs_inst_idx`] fmp_stage_invoke_inst) >>
         strip_tac >> gvs[get_instruction_def]) >>
     `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by fs[MEM] >>
     drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                       `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
     strip_tac >> gvs[get_instruction_def]) >>
  qpat_x_assum `inst = ti` SUBST_ALL_TAC >>
  `inst_wf ti /\ inst_shape_ok ti /\ opaque_use_ok fn /\ first_block_no_preds fn /\
   (C3.ctx_entry = SOME fn.fn_name ==> entry_fn_no_params fn)` by
    (`MEM ti (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
     conj_tac >- metis_tac[fn_inst_wf_def, fn_insts_def,
                            unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def, EVERY_MEM]) >>
  `s.vs_labels = t.vs_labels` by
    (qpat_assum `fmp_stage_rel _ _ m _ _ _ T _ _ _ _ _ _ _ t _` mp_tac >>
     simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `~MEM ti.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI; PARAM] /\
   ti.inst_opcode <> PHI` by (fs[MEM] >> simp[]) >>
  `!v. MEM (Var v) ti.inst_operands ==> IS_SOME (lookup_var v s)` by simp[] >>
  `terminates (step_inst fuel C4 ti t)` by simp[passSimulationDefsTheory.terminates_def] >>
  `terminates (step_inst fuel C3 ti s)` by
    (drule_all fmp_stage_back_kept_nonparam_point >> simp[NoAsms]) >>
  `step_inst fuel C3 ti s = step_inst fuel C3 ti s` by simp[] >>
  drule_all focus_fmp_jump_point >>
  disch_then (CONJUNCTS_THEN2 (K ALL_TAC) (qx_choose_then `dst` strip_assume_tac)) >>
  `s' = jump_to dst t` by metis_tac[exec_result_11] >>
  qpat_x_assum `s' = jump_to dst t` SUBST_ALL_TAC >>
  `fn_labels fn' = fn_labels fn` by metis_tac[fmp_stage_lowered_shape] >>
  `MEM dst (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (`?b. lookup_block dst fn'.fn_blocks = SOME b` by fs[enters_block_def, jump_to_def] >>
     drule stackPlanGenTheory.lookup_block_mem_fn_labels >>
     fs[fn_labels_def]) >>
  drule_all focus_fmp_cut_source_jump_entry >>
  disch_then (qx_choosel_then [`s1`, `si1`] strip_assume_tac) >>
  drule_all focus_fmp_cut_jump_entry >>
  disch_then (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (qx_choose_then `t1` strip_assume_tac))) >>
  `t1 = t'` by (fs[enters_block_def] >> gvs[]) >>
  qpat_x_assum `t1 = t'` SUBST_ALL_TAC >>
  `frame_reachable root3 C3 stk PG (entry_prov fn (jump_to dst s) G)
      (entry_taint_vars fn (jump_to dst s) tn) fn si1 s1` by
    (irule (cj 3 frame_reachable_rules) >>
     goal_assum (drule_at Any) >>
     `~(jump_to dst s).vs_halted` by simp[jump_to_def] >>
     simp[] >> qexistsl [`fuel`, `ti`, `s`] >> simp[]) >>
  `s1.vs_gas_readings = s.vs_gas_readings /\ ~s1.vs_halted` by
    (qpat_assum `enters_block fn _ s1` (mp_then Any assume_tac enters_block_readings) >>
     qpat_assum `enters_block fn _ s1`
       (mp_then Any assume_tac o1LowerDloadRunnerBoundaryTheory.ld_enters_block_halted) >>
     fs[jump_to_def]) >>
  qpat_assum `active_inst fn' ti' t'` (mp_then Any drule_all active_inst_block_lookup) >>
  disch_then (qx_choose_then `bb1` strip_assume_tac) >>
  `s1.vs_gas_readings = t'.vs_gas_readings` by
    (qpat_assum `enters_block fn' _ t'` (mp_then Any assume_tac enters_block_readings) >>
     fs[jump_to_def]) >>
  disj1_tac >>
  qexistsl [`stk`, `PG`, `entry_prov fn (jump_to dst s) G`,
    `entry_taint_vars fn (jump_to dst s) tn`, `fn`, `si1`, `s1`, `m`, `l`, `t'`, `ts`, `F`, `bb1`] >>
  simp[] >> conj_tac
  >- (irule gas_cut_readings_mono >>
      qpat_assum `gas_cut n root3 s` (irule_at Any) >>
      gvs[]) >>
  fs[fmp_target_run_def, run_insts_def, get_instruction_def] >> gvs[]
QED

Resume focus_opt_fmp_cut_cover[next]:
  `gas_cut n root4 t` by
    (irule gas_cut_readings_mono >> qexists `s'` >>
     conj_tac >- metis_tac[step_inst_noninvoke_readings_le] >>
     fs[gas_cut_def]) >>
  qpat_x_assum `gas_cut n root4 t ==> _` drule >>
  reverse (disch_then strip_assume_tac)
  >- (disj2_tac >> drule_all focus_fmp_cut_tail_observation >>
      disch_then (qspecl_then [`eom`, `C4`] strip_assume_tac) >>
      first_x_assum drule_all >> simp[] >> strip_tac >>
      qexistsl [`p`, `j`] >> simp[] >> decide_tac) >>
  `ALL_DISTINCT (fn_labels fn')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  Cases_on `t.vs_inst_idx < u.vs_inst_idx`
  >- (disj1_tac >> drule_all focus_fmp_cut_inserted_residual >> strip_tac >>
      first_x_assum drule >> simp[] >> strip_tac >>
      qexistsl [`stk`, `PG`, `G`, `tn`, `fn`, `inst`, `s`, `sm`, `lo`, `u`, `ts`,
                `restored`, `bb`] >> gvs[] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `u = t` by
    (`u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
     metis_tac[fmp_target_run_zero]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  `(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_vars = FEMPTY /\
   ~(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_halted` by
    fs[o1_initial_state_ok_def] >>
  drule_all focus_fmp_source_points >> strip_tac >>
  drule_all focus_fmp_aligned_layout >> strip_tac >>
  `opaque_use_ok fn /\ all_reachable fn` by
    fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def, make_ssa_input_ok_def] >>
  `ssa_form fn` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  qabbrev_tac `root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `w2n root3.vs_fmp = w2n fmp` by simp[Abbr `root3`] >>
  `inst.inst_opcode = DALLOCA ==> ?post. step_inst fuel C3 inst s = OK post` by
    (strip_tac >>
     `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
     `MEM bs fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
     `MEM inst bs.bb_instructions` by
       (simp[MEM_EL] >> qexists `s.vs_inst_idx` >> simp[]) >>
     `inst_wf inst` by
       (qpat_assum `fn_inst_wf fn` (mp_tac o REWRITE_RULE [fn_inst_wf_def]) >>
        disch_then (qspecl_then [`bs`, `inst`] mp_tac) >> simp[]) >>
     `inst_shape_ok inst` by
       fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def, EVERY_MEM] >>
     qpat_x_assum `inst_wf inst` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> strip_tac >>
     rename1 `_.inst_operands = [szop]` >>
     `?sz. eval_operand szop s = SOME sz` by
       (Cases_on `szop` >> gvs[eval_operand_def, unitShapeDefsTheory.inst_shape_ok_def,
          unitShapeDefsTheory.label_positions_ok_def, stackPlanTypesTheory.is_label_operand_def] >>
        metis_tac[optionTheory.IS_SOME_EXISTS]) >>
     metis_tac[lowerDloadPtrDallocaTheory.dalloca_step_success]) >>
  Cases_on `inst.inst_opcode = DALLOCA /\
    ?m l. fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n fmp) eom T stk PG G tn fn s l t ts`
  >- (qpat_x_assum `inst.inst_opcode = DALLOCA /\ _` strip_assume_tac >>
      rename1 `fmp_stage_rel D C4 m _ _ eom T stk PG G tn fn s l t ts` >>
      qpat_x_assum `inst.inst_opcode = DALLOCA ==> _` drule >>
      disch_then (qx_choose_then `post` assume_tac) >>
      `terminates (OK post)` by simp[passSimulationDefsTheory.terminates_def] >>
      `w2n fmp = w2n root3.vs_fmp` by simp[NoAsms, Abbr `root3`] >>
      qpat_assum `fmp_stage_rel D C4 m _ _ eom T stk PG G tn fn s l t ts`
        (mp_then Any drule_all focus_fmp_cut_dalloca_segment) >>
      disch_then (qx_choosel_then [`s1`, `t1`, `m1`, `sz`, `seg_fn`, `seg_bb`, `code`, `tail`,
        `op`, `out`, `runner'`, `plus31`, `mask`, `aligned`, `ai`, `ni`, `mi`, `bi`]
        (strip_assume_tac o SRULE [LET_THM])) >>
      `s1 = post /\ seg_fn = fn' /\ seg_bb = bb` by metis_tac[optionTheory.SOME_11] >>
      qpat_x_assum `s1 = post` SUBST_ALL_TAC >>
      qpat_x_assum `seg_bb = bb` SUBST_ALL_TAC >>
      `t1.vs_inst_idx = t.vs_inst_idx + 4` by
        (qpat_assum `!k. fmp_target_run k C4 _ t 4 t1`
           (qspec_then `fuel` mp_tac) >> simp[NoAsms, fmp_target_run_def] >>
         strip_tac >> simp[]) >>
      `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\ ~is_terminator inst.inst_opcode` by
        simp[is_terminator_def] >>
      `post.vs_current_bb = s.vs_current_bb /\
       post.vs_gas_readings = s.vs_gas_readings /\ ~post.vs_halted` by
        (`step_inst_base inst s = OK post` by
           (qpat_assum `step_inst fuel C3 inst s = OK post` mp_tac >>
            qpat_assum `inst.inst_opcode <> INVOKE`
              (fn th => simp[NoAsms, step_inst_non_invoke, th])) >>
         drule venomExecPropsTheory.step_inst_OK_preserves_halted >>
         drule_all venomInstPropsTheory.step_preserves_control_flow >>
         drule_all oracleExecPropsTheory.step_inst_noninvoke_gas_readings >> simp[]) >>
      `t1.vs_current_bb = t.vs_current_bb /\ post.vs_gas_readings = t1.vs_gas_readings` by
        (qpat_assum `fmp_stage_rel _ _ m1 _ _ _ F _ _ _ _ _ _ _ t1 _` mp_tac >>
         simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def,
              o1LowerDloadSharedTheory.ld_shared_agree_def] >>
         strip_tac >> metis_tac[]) >>
      `!i. t.vs_inst_idx <= i /\ i < t1.vs_inst_idx ==>
           i < LENGTH bb.bb_instructions /\
           fmp_inserted_op (EL i bb.bb_instructions).inst_opcode` by
        (qx_gen_tac `i` >> strip_tac >>
         `i - t.vs_inst_idx < 4 /\ i - t.vs_inst_idx + t.vs_inst_idx = i` by decide_tac >>
         `DROP t.vs_inst_idx bb.bb_instructions =
            mk_inst ai ADD [op; Lit 31w] [plus31]::mk_inst ni NOT [Lit 31w] [mask]::
            mk_inst mi AND [Var plus31; Var mask] [aligned]::
            mk_inst bi BUMP [Var runner'; Var aligned] [out; runner']::tail` by simp[] >>
         `i < LENGTH bb.bb_instructions` by
           (pop_assum (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
            simp[NoAsms, LENGTH_DROP] >> decide_tac) >>
         `EL i bb.bb_instructions = EL (i - t.vs_inst_idx) (DROP t.vs_inst_idx bb.bb_instructions)` by
           (qpat_assum `i - t.vs_inst_idx + t.vs_inst_idx = i` (fn idx =>
              qpat_assum `i < LENGTH bb.bb_instructions` (fn bound =>
                simp[NoAsms, EL_DROP, idx, bound]))) >>
         qpat_x_assum `EL i bb.bb_instructions = _` SUBST1_TAC >>
         `i - t.vs_inst_idx = 0 \/ i - t.vs_inst_idx = 1 \/
          i - t.vs_inst_idx = 2 \/ i - t.vs_inst_idx = 3` by decide_tac >>
         simp[fmp_inserted_op_def, mk_inst_def]) >>
      `t1.vs_inst_idx - t.vs_inst_idx = 4 /\ t.vs_inst_idx < t1.vs_inst_idx` by decide_tac >>
      `t.vs_current_bb = t1.vs_current_bb /\
       (!k. fmp_target_run k C4 fn.fn_name t (t1.vs_inst_idx - t.vs_inst_idx) t1)` by
        (conj_tac >- metis_tac[] >>
         qpat_assum `t1.vs_inst_idx - t.vs_inst_idx = 4` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      drule_all (Q.INST [`u` |-> `t1`] focus_fmp_cut_inserted_residual) >>
      strip_tac >> first_x_assum drule >>
      disch_then (strip_assume_tac o SRULE [LET_THM]) >>
      drule_all o1LowerDloadReadinessTheory.ld_nonterminator_successor >>
      disch_then (qx_choose_then `next` assume_tac) >>
      `gas_cut n root3 (post with vs_inst_idx := SUC s.vs_inst_idx)` by
        (qpat_assum `gas_cut n root3 s` mp_tac >>
         qpat_assum `post.vs_gas_readings = s.vs_gas_readings`
           (fn th => simp[NoAsms, gas_cut_def, th])) >>
      `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME bb /\
       t1.vs_gas_readings = s'.vs_gas_readings` by metis_tac[] >>
      disj1_tac >>
      qexistsl [`stk`, `PG`, `step_prov PG G inst post`, `step_taint inst s post tn`,
        `fn`, `next`, `post with vs_inst_idx := SUC s.vs_inst_idx`, `m1`,
        `l + venomLayout$ceil32 (w2n sz)`, `t1`, `ts`, `F`, `bb`] >>
      conj_tac >- (irule frame_reachable_next >> metis_tac[]) >>
      rpt conj_tac >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  reverse (Cases_on `restored`)
  >- (gvs[] >>
      drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`]
                             focus_fmp_cut_restore_prefix)) >>
      disch_then (qx_choosel_then
        [`rest_fn`, `rest_src`, `rest_bb`, `rest_infos`, `rest_ctx`,
         `rest_runner`, `rest_len`, `rest_post`, `rest_cut`] strip_assume_tac) >>
      (* Dispatch on the layout returned by this run certificate. *)
      reverse (Cases_on `FLOOKUP (fmp_stage_plan rest_infos rest_ctx fn)
                                    (s.vs_current_bb,s.vs_inst_idx)`) >>
      PRED_ASSUM (can optionSyntax.dest_option_case) mp_tac >> simp[] >> strip_tac
      >- (`rest_src = bs /\ rest_fn = fn' /\ rest_bb = bb` by
            metis_tac[optionTheory.SOME_11] >>
          `(s.vs_current_bb,s.vs_inst_idx) IN FDOM
             (fmp_stage_plan rest_infos rest_ctx fn)` by fs[FLOOKUP_DEF] >>
          `fmp_is_reclaim_point rest_infos (EL s.vs_inst_idx bs.bb_instructions)` by
            metis_tac[fmp_stage_plan_point] >>
          (SUBGOAL_THEN
             ``MEM (EL s.vs_inst_idx bs.bb_instructions).inst_opcode [DALLOCA; INVOKE] \/
               is_terminator (EL s.vs_inst_idx bs.bb_instructions).inst_opcode`` assume_tac >-
           (drule fmp_reclaim_point_opcodes >> simp[] >> strip_tac >> simp[is_terminator_def])) >>
          `rest_post = s' with vs_inst_idx := SUC t.vs_inst_idx` by
            (qpat_assum `!k. fmp_target_run k _ _ t _ rest_post`
              (qspec_then `fuel` mp_tac) >>
             gvs[fmp_target_run_def, TAKE1_DROP, run_insts_def, get_instruction_def,
                 arithmeticTheory.ADD1]) >>
          `s'.vs_current_bb = t.vs_current_bb /\ s'.vs_gas_readings = t.vs_gas_readings` by
            (qpat_assum `rest_post = update_var _ _ _ with vs_inst_idx := _`
               (mp_tac o AP_TERM ``\v:venom_state. (v.vs_current_bb,v.vs_gas_readings)``) >>
             qpat_assum `rest_post = s' with vs_inst_idx := _`
               (mp_tac o AP_TERM ``\v:venom_state. (v.vs_current_bb,v.vs_gas_readings)``) >>
             simp[NoAsms, update_var_def]) >>
          `!k. fmp_target_run k C4 fn.fn_name rest_post 0 rest_post` by
            (irule fmp_restore_target_run_zero >> metis_tac[]) >>
          disj1_tac >>
          qpat_assum `t.vs_inst_idx = fmp_stage_tidx _ _ _ _ _`
            (fn th => once_rewrite_tac [GSYM th]) >>
          qexistsl [`stk`, `PG`, `G`, `tn`, `fn`, `EL s.vs_inst_idx bs.bb_instructions`,
            `s`, `DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < rest_cut}`,
            `rest_cut`, `rest_post`, `ts`, `T`, `bb`] >>
          gvs[arithmeticTheory.ADD1]) >>
      `rest_src = bs /\ rest_fn = fn' /\ rest_bb = bb` by
        metis_tac[optionTheory.SOME_11] >>
      `~((s.vs_current_bb,s.vs_inst_idx) IN FDOM
            (fmp_stage_plan rest_infos rest_ctx fn))` by fs[FLOOKUP_DEF] >>
      `((EL s.vs_inst_idx bs.bb_instructions).inst_opcode <> INVOKE /\
        ~is_terminator (EL s.vs_inst_idx bs.bb_instructions).inst_opcode)` by
        (conj_tac
         >- (strip_tac >>
             drule_all (Q.INST [`infos` |-> `rest_infos`, `ctx` |-> `rest_ctx`,
                               `idx` |-> `s.vs_inst_idx`] fmp_stage_invoke_inst) >>
             gvs[get_instruction_def]) >>
         strip_tac >>
         `pre_fmp_opcode (EL s.vs_inst_idx bs.bb_instructions).inst_opcode` by
           (drule active_inst_mem_fn_insts >> disch_tac >>
            qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
            simp[]) >>
         `~MEM (EL s.vs_inst_idx bs.bb_instructions).inst_opcode
                [DALLOCA; INVOKE; RETPC_PARAM]` by
           (simp[] >> rpt conj_tac >> strip_tac >> fs[is_terminator_def]) >>
         `?bt. lookup_block s.vs_current_bb fn'.fn_blocks = SOME bt /\
                get_instruction bt t.vs_inst_idx = SOME (EL s.vs_inst_idx bs.bb_instructions)` by
           (mp_tac (Q.INST
              [`infos` |-> `rest_infos`, `ctx` |-> `rest_ctx`, `runner` |-> `rest_runner`,
               `lbl` |-> `s.vs_current_bb`, `idx` |-> `s.vs_inst_idx`, `bb` |-> `bs`,
               `inst` |-> `EL s.vs_inst_idx bs.bb_instructions`] fmp_stage_kept_inst) >>
            simp[get_instruction_def] >> metis_tac[]) >>
         `ti = EL s.vs_inst_idx bs.bb_instructions` by
           metis_tac[optionTheory.SOME_11] >> fs[]) >>
      Cases_on `(EL s.vs_inst_idx bs.bb_instructions).inst_opcode = DALLOCA`
      >- (qpat_x_assum `rest_post = t` SUBST_ALL_TAC >>
          qpat_x_assum `rest_cut = lo` SUBST_ALL_TAC >>
          gvs[]) >>
      rename1 `active_inst fn (EL s.vs_inst_idx bs.bb_instructions) s` >>
      qabbrev_tac `si = EL s.vs_inst_idx bs.bb_instructions` >>
      reverse (Cases_on `si.inst_opcode = RETPC_PARAM`)
      >- (`pre_fmp_opcode si.inst_opcode` by
            (drule active_inst_mem_fn_insts >> disch_tac >>
             qpat_assum `pre_fmp_ops fn`
               (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >> simp[]) >>
          `~MEM si.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by simp[] >>
          `si = EL s.vs_inst_idx bs.bb_instructions` by simp[Abbr `si`] >>
          drule_all (Q.INST [`infos` |-> `rest_infos`, `ctx` |-> `rest_ctx`,
                             `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
          disch_then (qx_choose_then `kept_bb` strip_assume_tac) >>
          `kept_bb = bb` by metis_tac[optionTheory.SOME_11] >>
          qpat_x_assum `kept_bb = bb` SUBST_ALL_TAC >>
          `get_instruction bb t.vs_inst_idx = SOME si` by
            ((qpat_assum `~(_ IN FDOM (fmp_stage_plan rest_infos rest_ctx fn))` (fn absent =>
             qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan rest_infos rest_ctx fn) _ _ _ _`
              (fn idx =>
               qpat_x_assum `_ < LENGTH bb.bb_instructions` (mp_tac o SRULE [NoAsms, absent, GSYM idx]) >>
               qpat_x_assum `EL _ bb.bb_instructions = si` (mp_tac o SRULE [NoAsms, absent, GSYM idx]) >>
               simp[NoAsms, get_instruction_def]))) >> (metis_tac[NoAsms, get_instruction_def])) >>
          `ti = si` by metis_tac[optionTheory.SOME_11] >>
          qpat_x_assum `ti = si` SUBST_ALL_TAC >>
          `s'.vs_current_bb = t.vs_current_bb` by
            metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
          Cases_on `in_revert_forward fn s`
          >- (`?j. revert_forward_pair bs s.vs_inst_idx j` by
                (`get_instruction bs s.vs_inst_idx = SOME si` by
                   simp[get_instruction_def, Abbr `si`] >>
                 qpat_assum `in_revert_forward fn s` (mp_tac o REWRITE_RULE [in_revert_forward_def]) >>
                 disch_then (qx_choose_then `fwd_bb` strip_assume_tac) >>
                 `fwd_bb = bs` by metis_tac[optionTheory.SOME_11] >>
                 qpat_x_assum `fwd_bb = bs` SUBST_ALL_TAC >>
                 qpat_x_assum `revert_forward_at bs _`
                   (qx_choose_then `j` strip_assume_tac o REWRITE_RULE [revert_forward_at_def])
                 >- (qexists `j` >> first_assum ACCEPT_TAC) >>
                 qpat_x_assum `revert_forward_pair bs j _` mp_tac >>
                 simp[NoAsms, revert_forward_pair_def] >> strip_tac >>
                 `inst2 = si` by metis_tac[optionTheory.SOME_11] >> fs[is_terminator_def]) >>
              drule_all (SRULE [LET_THM] (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                                `p` |-> `s.vs_inst_idx`] focus_fmp_cut_forward_layout)) >>
              disch_then (qx_choose_then `target_fwd` strip_assume_tac) >>
              `s.vs_inst_idx < j` by metis_tac[revert_forward_pair_def] >>
              `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME target_fwd` by metis_tac[] >>
              `revert_forward_pair target_fwd t.vs_inst_idx (t.vs_inst_idx + (j - s.vs_inst_idx))` by
                metis_tac[] >>
              disj2_tac >>
              qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn) _ _ _ _`
                (SUBST1_TAC o SYM) >>
              qexistsl [`target_fwd`, `t.vs_inst_idx`, `t.vs_inst_idx + (j - s.vs_inst_idx)`] >>
              conj_tac >- first_assum ACCEPT_TAC >>
              conj_tac >- first_assum ACCEPT_TAC >> decide_tac) >>
          `si.inst_opcode <> PHI` by
            (strip_tac >>
             qpat_assum `si.inst_opcode = PHI` (fn opc =>
               qpat_assum `step_inst fuel C4 si t = OK s'`
                 (mp_tac o SRULE [NoAsms, opc, step_inst_non_invoke,
                                  step_inst_base_opcode_eqs])) >> simp[]) >>
          `MEM si (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
          `inst_wf si /\ inst_shape_ok si` by
            (conj_tac >- metis_tac[fn_inst_wf_def, fn_insts_def,
                                   unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
             qpat_assum `o1_fn_shape C3 fn`
               (mp_tac o REWRITE_RULE [o1_fn_shape_def,
                                       unitShapeDefsTheory.fn_shape_ok_def, EVERY_MEM]) >>
             strip_tac >>
             qpat_assum `!i. MEM i (fn_insts fn) ==> inst_shape_ok i` irule >>
             first_assum ACCEPT_TAC) >>
          `s.vs_labels = t.vs_labels` by
            (qpat_assum `fmp_stage_rel _ _ sm _ _ _ F _ _ _ _ _ _ _ t _` mp_tac >>
             simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def] >>
             strip_tac >> first_assum ACCEPT_TAC) >>
          `terminates (step_inst fuel C4 si t)` by simp[passSimulationDefsTheory.terminates_def] >>
          `terminates (step_inst fuel C3 si s)` by
            (Cases_on `si.inst_opcode = PARAM`
             >- (mp_tac (Q.INST [`vs` |-> `root3`] focus_fmp_source_call_arity) >>
                 (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
                 disch_then assume_tac >>
                 drule_all fmp_stage_back_param_point >> simp[NoAsms]) >>
             `~MEM si.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI; PARAM]` by simp[] >>
             `!v. MEM (Var v) si.inst_operands ==> IS_SOME (lookup_var v s)` by
               (rpt strip_tac >> qpat_assum `!v. _ /\ _ ==> IS_SOME (lookup_var v s)` irule >>
                conj_tac >> first_assum ACCEPT_TAC) >>
             drule_all fmp_stage_back_kept_nonparam_point >> simp[NoAsms]) >>
          drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_frame_sites_upto)) >>
          strip_tac >>
          `~MEM si.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI]` by simp[] >>
          `step_inst fuel C3 si s = step_inst fuel C3 si s` by simp[] >>
          drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_ordinary_segment)) >>
          disch_then (qx_choose_then `target_fn` (qx_choose_then `source_bb`
            (qx_choose_then `target_bb` (qx_choose_then `tail`
              (qx_choose_then `r` strip_assume_tac))))) >>
          `r = OK s'` by
            (qpat_assum `!k. step_inst k C4 si t = r` (qspec_then `fuel` mp_tac) >>
             simp[]) >>
          qpat_x_assum `r = OK s'` SUBST_ALL_TAC >>
          qpat_x_assum `(case step_inst fuel C3 si s of OK _ => _ | Halt _ => _ |
                         Abort _ _ => _ | IntRet _ _ => _ | Error _ => _)` mp_tac >>
          Cases_on `step_inst fuel C3 si s` >>
          simp[NoAsms, dead_result_rel_def] >>
          disch_then strip_assume_tac >>
          rename1 `step_inst fuel C3 si s = OK post` >>
          `post.vs_current_bb = s.vs_current_bb /\ ~post.vs_halted` by
            (drule_all venomInstPropsTheory.step_preserves_control_flow >> strip_tac >>
             `step_inst_base si s = OK post` by
               (qpat_assum `si.inst_opcode <> INVOKE` (fn opc =>
                qpat_assum `step_inst fuel C3 si s = OK post` mp_tac >>
                simp[NoAsms, step_inst_non_invoke, opc])) >>
             drule venomExecPropsTheory.step_inst_OK_preserves_halted >> simp[]) >>
          drule_all o1LowerDloadReadinessTheory.ld_nonterminator_successor >>
          disch_then (qx_choose_then `next` assume_tac) >>
          `post.vs_gas_readings = s'.vs_gas_readings` by
            (qpat_assum `fmp_stage_rel _ _ sm _ _ _ F _ _ _ _ _
                         (post with vs_inst_idx := _) lo (s' with vs_inst_idx := _) ts` mp_tac >>
             simp[NoAsms, fmp_stage_rel_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
          `root3.vs_gas_readings = root4.vs_gas_readings` by simp[NoAsms, Abbr `root3`] >>
          `gas_cut n root3 (post with vs_inst_idx := SUC s.vs_inst_idx)` by
            (qpat_assum `gas_cut n root4 (s' with vs_inst_idx := _)` mp_tac >>
             qpat_assum `post.vs_gas_readings = _` (fn readings =>
             qpat_assum `root3.vs_gas_readings = _` (fn roots =>
               simp[NoAsms, gas_cut_def, readings, roots]))) >>
          `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME bb` by metis_tac[] >>
          `!k. fmp_target_run k C4 fn.fn_name
                     (s' with vs_inst_idx := SUC t.vs_inst_idx) 0
                     (s' with vs_inst_idx := SUC t.vs_inst_idx)` by
            (`SUC t.vs_inst_idx < LENGTH bb.bb_instructions` by
               (qpat_assum `active_inst fn' ti' (s' with vs_inst_idx := _)` mp_tac >>
                qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn) _ _ _ _`
                  (fn idx => once_rewrite_tac [GSYM idx]) >>
                disch_tac >> drule_all active_inst_block_lookup >> strip_tac >>
                `bb' = bb` by
                  (qpat_assum `lookup_block (s' with vs_inst_idx := _).vs_current_bb fn'.fn_blocks = SOME bb'` mp_tac >>
                   qpat_assum `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME bb`
                     (fn fetch => simp[NoAsms, fetch])) >>
                qpat_assum `get_instruction bb' _ = SOME ti'` mp_tac >>
                qpat_assum `bb' = bb` (fn eq => simp[NoAsms, eq, get_instruction_def]) >>
                rw[]) >>
             irule fmp_restore_target_run_zero >>
             simp[NoAsms] >> qexistsl [`bb`, `fn'`] >>
             conj_tac
             >- (qpat_assum `SUC t.vs_inst_idx < LENGTH bb.bb_instructions` mp_tac >> decide_tac) >>
             conj_tac >> first_assum ACCEPT_TAC) >>
          disj1_tac >>
          qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn) _ _ _ _`
            (SUBST1_TAC o SYM) >>
          qexistsl [`stk`, `PG`, `step_prov PG G si post`, `step_taint si s post tn`, `fn`,
                    `next`, `post with vs_inst_idx := SUC s.vs_inst_idx`, `sm`, `lo`,
                    `s' with vs_inst_idx := SUC t.vs_inst_idx`, `ts`, `F`, `bb`] >>
          conj_tac >- (irule frame_reachable_next >> metis_tac[]) >>
          rpt conj_tac >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
      `!k. ?post. step_inst k C3 si s = OK post` by
        (`inst_wf si` by
           (qpat_assum `active_inst fn si s` (mp_tac o MATCH_MP active_inst_mem_fn_insts) >>
            REWRITE_TAC[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
            disch_then (qx_choose_then `b0` strip_assume_tac) >>
            qpat_assum `fn_inst_wf fn`
              (qspecl_then [`b0`, `si`] irule o REWRITE_RULE [fn_inst_wf_def]) >>
            qexists `b0` >> conj_tac >> first_assum ACCEPT_TAC) >>
         `MEM si.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]` by simp[] >>
         drule_all ld_normal_parameter_shape >> strip_tac >>
         simp[ld_retpc_success_iff]) >>
      pop_assum (qspec_then `fuel` (qx_choose_then `post` assume_tac)) >>
      drule_all focus_fmp_retpc_point >>
      disch_then (qx_choosel_then [`len`, `t1`, `ret_fn`, `ret_bb`]
        (map_every assume_tac o CONJUNCTS)) >>
      `ret_fn = fn' /\ ret_bb = bb` by metis_tac[optionTheory.SOME_11] >>
      qpat_x_assum `ret_fn = fn'` SUBST_ALL_TAC >>
      qpat_x_assum `ret_bb = bb` SUBST_ALL_TAC >>
      `t1.vs_inst_idx = t.vs_inst_idx + len /\
       t.vs_inst_idx + len <= LENGTH bb.bb_instructions` by
        (qpat_assum `!k. fmp_target_run k C4 _ t len t1`
           (qspec_then `fuel` mp_tac) >> simp[NoAsms, fmp_target_run_def] >>
         disch_then (qx_choosel_then [`run_fn`, `run_bb`, `run_post`] strip_assume_tac) >>
         `run_fn = fn' /\ run_bb = bb` by metis_tac[optionTheory.SOME_11] >>
         qpat_x_assum `run_bb = bb` SUBST_ALL_TAC >>
         conj_tac
         >- (qpat_assum `t1 = run_post with vs_inst_idx := _` (fn th => simp[NoAsms, th, ADD_COMM])) >>
         qpat_assum `_ <= LENGTH bb.bb_instructions`
           (fn th => simp[NoAsms, ADD_COMM, th])) >>
      `EVERY (\i. fmp_inserted_op i.inst_opcode)
         (TAKE len (DROP t.vs_inst_idx bb.bb_instructions))` by
        (qpat_x_assum `len = 1 \/ len = 2` strip_assume_tac >>
         qpat_assum `if len = 1 then _ else _` mp_tac >>
         qpat_assum `len = _` (fn th => simp[NoAsms, th, Excl "TAKE1_DROP"]) >>
         strip_tac >> simp[fmp_inserted_op_def, mk_inst_def, set_param_index_def]) >>
      `!i. t.vs_inst_idx <= i /\ i < t1.vs_inst_idx ==>
           i < LENGTH bb.bb_instructions /\
           fmp_inserted_op (EL i bb.bb_instructions).inst_opcode` by
        (qx_gen_tac `i` >> strip_tac >>
         `i < LENGTH bb.bb_instructions /\ i - t.vs_inst_idx < len /\
          i - t.vs_inst_idx + t.vs_inst_idx = i` by decide_tac >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qpat_assum `EVERY _ (TAKE len _)`
           (qspec_then `i - t.vs_inst_idx` mp_tac o REWRITE_RULE [EVERY_EL]) >>
         `len <= LENGTH (DROP t.vs_inst_idx bb.bb_instructions)` by
           (simp[NoAsms, LENGTH_DROP] >> decide_tac) >>
         qpat_assum `len <= LENGTH (DROP _ _)` (fn lim =>
           qpat_assum `i - t.vs_inst_idx < len` (fn off =>
           qpat_assum `i - t.vs_inst_idx + t.vs_inst_idx = i` (fn idx =>
           qpat_assum `i < LENGTH bb.bb_instructions` (fn hi =>
             simp[NoAsms, lim, off, idx, hi, LENGTH_TAKE, EL_TAKE, EL_DROP]))))) >>
      `post.vs_current_bb = s.vs_current_bb /\
       post.vs_gas_readings = s.vs_gas_readings /\ ~post.vs_halted` by
        (`step_inst_base si s = OK post` by
           (qpat_assum `step_inst fuel C3 si s = OK post` mp_tac >>
            qpat_assum `si.inst_opcode <> INVOKE`
              (fn th => simp[NoAsms, step_inst_non_invoke, th])) >>
         `si.inst_opcode <> GAS` by simp[] >>
         drule venomExecPropsTheory.step_inst_OK_preserves_halted >>
         drule_all venomInstPropsTheory.step_preserves_control_flow >>
         drule_all oracleExecPropsTheory.step_inst_noninvoke_gas_readings >>
         simp[NoAsms] >> metis_tac[]) >>
      `t1.vs_current_bb = t.vs_current_bb /\ post.vs_gas_readings = t1.vs_gas_readings` by
        (qpat_assum `fmp_stage_rel _ _ sm _ _ _ F _ _ _ _ _
                     (post with vs_inst_idx := _) lo t1 ts` mp_tac >>
         simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def,
              o1LowerDloadSharedTheory.ld_shared_agree_def] >>
         strip_tac >> metis_tac[]) >>
      `t1.vs_inst_idx - t.vs_inst_idx = len /\ t.vs_inst_idx < t1.vs_inst_idx` by
        (qpat_assum `len = 1 \/ len = 2` strip_assume_tac >> decide_tac) >>
      `t.vs_current_bb = t1.vs_current_bb /\
       (!k. fmp_target_run k C4 fn.fn_name t (t1.vs_inst_idx - t.vs_inst_idx) t1)` by
        (conj_tac >- metis_tac[] >>
         qpat_assum `t1.vs_inst_idx - t.vs_inst_idx = len` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      drule_all (Q.INST [`u` |-> `t1`] focus_fmp_cut_inserted_residual) >>
      strip_tac >> first_x_assum drule >>
      disch_then (strip_assume_tac o SRULE [LET_THM]) >>
      drule_all o1LowerDloadReadinessTheory.ld_nonterminator_successor >>
      disch_then (qx_choose_then `next` assume_tac) >>
      `gas_cut n root3 (post with vs_inst_idx := SUC s.vs_inst_idx)` by
        (qpat_assum `gas_cut n root3 s` mp_tac >>
         qpat_assum `post.vs_gas_readings = s.vs_gas_readings`
           (fn th => simp[NoAsms, gas_cut_def, th])) >>
      `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME bb /\
       t1.vs_gas_readings = s'.vs_gas_readings` by metis_tac[] >>
      disj1_tac >>
      qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn) _ _ _ _`
        (SUBST1_TAC o SYM) >>
      qexistsl [`stk`, `PG`, `step_prov PG G si post`, `step_taint si s post tn`,
                `fn`, `next`, `post with vs_inst_idx := SUC s.vs_inst_idx`,
                `sm`, `lo`, `t1`, `ts`, `F`, `bb`] >>
      conj_tac >- (irule frame_reachable_next >> metis_tac[]) >>
      rpt conj_tac >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  reverse (Cases_on `inst.inst_opcode = DALLOCA`)
  >- (Cases_on `inst.inst_opcode = INVOKE`
      >- (`(EL s.vs_inst_idx bs.bb_instructions).inst_opcode = INVOKE` by metis_tac[] >>
          drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                            `idx` |-> `s.vs_inst_idx`] fmp_stage_invoke_inst) >>
          gvs[get_instruction_def]) >>
      `is_terminator inst.inst_opcode` by fs[] >>
      `pre_fmp_opcode inst.inst_opcode` by
        (drule active_inst_mem_fn_insts >> disch_tac >>
         qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
         metis_tac[]) >>
      `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by
        (simp[NoAsms] >> rpt strip_tac >> fs[is_terminator_def]) >>
      drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                        `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
      gvs[get_instruction_def] >> disch_then SUBST_ALL_TAC >> fs[]) >>
  qpat_x_assum `~(inst.inst_opcode = DALLOCA /\ _)` mp_tac >>
  simp[] >> disch_then (qspecl_then [`sm`, `lo`] mp_tac) >> simp[]
QED

Resume focus_opt_fmp_cut_cover[call]:
  `gas_cut n root4 t` by
    (irule gas_cut_readings_mono >>
     qpat_assum `gas_cut n root4 t'` (irule_at Any) >>
     drule enters_block_readings >>
     drule o1LowerDloadSharedTheory.ld_setup_callee_gas_readings >> simp[]) >>
  qpat_x_assum `gas_cut n root4 t ==> _` drule >>
  reverse (disch_then (DISJ_CASES_THEN strip_assume_tac))
  >- (drule_all (Q.INST [`eom` |-> `eom`, `C4` |-> `C4`] focus_fmp_cut_tail_observation) >>
      strip_tac >> gvs[MEM]) >>
  `ALL_DISTINCT (fn_labels fn')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  `get_instruction bb t.vs_inst_idx = SOME ti` by
    (qpat_assum `active_inst fn' ti t` (mp_then Any drule_all active_inst_block_lookup) >>
     strip_tac >> metis_tac[optionTheory.SOME_11]) >>
  `u = t` by
    (Cases_on `t.vs_inst_idx < u.vs_inst_idx`
     >- (qpat_assum `!i. _ <= i /\ _ ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
         gvs[get_instruction_def, fmp_inserted_op_def]) >>
     `u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
     metis_tac[fmp_target_run_zero]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  `(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_vars = FEMPTY /\
   ~(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_halted` by
    fs[o1_initial_state_ok_def] >>
  drule_all focus_fmp_source_points >> strip_tac >>
  `ssa_form fn` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  qabbrev_tac `root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `w2n root3.vs_fmp = w2n fmp` by simp[Abbr `root3`] >>
  `?m l. fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n fmp) eom T
           stk PG G tn fn s l t ts` by
    (Cases_on `restored` >- metis_tac[] >> gvs[] >>
     drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_restore_prefix)) >>
     disch_then (qx_choosel_then
       [`rest_fn`, `rest_src`, `rest_bb`, `rest_infos`, `rest_ctx`,
        `rest_runner`, `rest_len`, `rest_post`, `rest_cut`] strip_assume_tac) >>
     Cases_on `FLOOKUP (fmp_stage_plan rest_infos rest_ctx fn) (s.vs_current_bb,s.vs_inst_idx)`
     >- (gvs[] >> metis_tac[]) >>
     gvs[get_instruction_def, mk_inst_def]) >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ restored _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all focus_fmp_aligned_layout >> strip_tac >>
  `pre_fmp_opcode inst.inst_opcode` by
    (qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
     metis_tac[active_inst_mem_fn_insts]) >>
  `inst.inst_opcode = INVOKE` by
    (CCONTR_TAC >>
     Cases_on `MEM inst.inst_opcode [DALLOCA; RETPC_PARAM]`
     >- (qabbrev_tac `plan = fmp_stage_plan infos ctx fn` >>
         qabbrev_tac `rt = fmp_stage_root infos ctx fn` >>
         qabbrev_tac `idx = s.vs_inst_idx` >>
         qabbrev_tac `lab = s.vs_current_bb` >>
         `fmp_stage_tidx plan rt lab bs.bb_instructions idx +
            (if (lab,idx) IN FDOM plan then 1 else 0) <
          fmp_stage_tidx plan rt lab bs.bb_instructions (SUC idx)` by
           (simp[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
            Cases_on `rt` >> simp[]
            >- (IF_CASES_TAC >> simp[]) >>
            rename1 `SOME r = fmp_stage_root _ _ _` >> PairCases_on `r` >> simp[] >>
            rpt (IF_CASES_TAC >> simp[]) >> decide_tac) >>
         mp_tac (Q.INST [`P` |-> `fmp_inserted_op`, `infos` |-> `infos`,
                         `ctx` |-> `ctx`, `runner` |-> `runner`, `fn` |-> `fn`,
                         `fn'` |-> `fn'`, `lbl` |-> `lab`, `bb` |-> `bs`,
                         `idx` |-> `idx`, `i` |-> `t.vs_inst_idx`]
             fmpStageCoverMemAssembleTheory.fmp_cover_inserted_from_root_structural) >>
         (impl_tac >- (simp[fmp_inserted_op_def, Abbr `rt`, Abbr `plan`] >>
                       rw[] >> gvs[MEM])) >>
         strip_tac >> gvs[get_instruction_def, fmp_inserted_op_def]) >>
     `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by fs[MEM] >>
     drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                       `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
     strip_tac >> gvs[get_instruction_def]) >>
  drule_all focus_fmp_cut_source_call_entry >>
  disch_then (qx_choosel_then [`snm`, `sops`, `callee`, `sargs`, `scs`, `si1`]
    strip_assume_tac) >>
  `C3.ctx_entry <> SOME snm` by (drule_all fmp_invoke_not_entry >> simp[]) >>
  `callee.fn_fmp_signature = NONE` by
    (fs[fmp_free_ctx_def, EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  drule_all focus_fmp_cut_invoke_push >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`tf`, `sb`, `tb`, `tj`, `ti0`, `tc0`, `tr0`, `tf1`,
      `si0`, `sc0`, `sr0`, `extra`, `rr`, `args1`, `cs1`, `t1`] strip_assume_tac)) >>
  `tf = fn'` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tf = fn'` SUBST_ALL_TAC >>
  `tj = ti` by metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique] >>
  qpat_x_assum `tj = ti` SUBST_ALL_TAC >>
  `snm = nm /\ sops ++ extra = ops /\ tf1 = fn'' /\ cs1 = cs /\ t1 = t'` by
    (gvs[enters_block_def] >> metis_tac[]) >>
  qpat_x_assum `t1 = t'` SUBST_ALL_TAC >>
  `callee.fn_name = snm` by metis_tac[lookup_function_selected_name] >>
  `fn_inst_ids_distinct fn` by
    (pure_rewrite_tac [algebraicOptSupplyProofsTheory.ao_fn_inst_ids_distinct_alt] >>
     irule ctx_inst_ids_distinct_fn >>
     qexists `C3` >> fs[o1_ctx_shape_def] >> metis_tac[lookup_function_MEM]) >>
  `MEM inst (fn_insts fn) /\ MEM ti (fn_insts fn')` by
    metis_tac[active_inst_mem_fn_insts] >>
  `ti.inst_outputs = inst.inst_outputs` by
    (qpat_assum `ti.inst_id = inst.inst_id` (mp_then Any drule_all focus_fmp_cut_invoke_outputs) >>
     simp[]) >>
  qabbrev_tac `f = <|cf_fn := fn; cf_inst := inst; cf_state := s;
                     cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>` >>
  `frame_reachable root3 C3 (f::stk) (MAP (op_prov G) sops) FEMPTY
        (tn with t_var := FEMPTY) callee si1 scs` by
    (simp[Abbr `f`] >> irule frame_reachable_call >> metis_tac[]) >>
  `~scs.vs_halted /\ scs.vs_gas_readings = s.vs_gas_readings /\
   t'.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[ld_setup_callee_not_halted, o1LowerDloadSharedTheory.ld_setup_callee_gas_readings,
              enters_block_readings] >>
  `gas_cut n root3 scs` by
    (irule gas_cut_readings_mono >> qpat_assum `gas_cut n root3 s` (irule_at Any) >> gvs[]) >>
  `ALL_DISTINCT (fn_labels fn'')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  qpat_assum `active_inst fn'' ti' t'` (mp_then Any drule_all active_inst_block_lookup) >>
  disch_then (qx_choose_then `bb1` strip_assume_tac) >>
  disj1_tac >>
  qexistsl [`f::stk`, `MAP (op_prov G) sops`, `FEMPTY`, `tn with t_var := FEMPTY`,
    `callee`, `si1`, `scs`, `m`, `l`, `t'`, `(t,l)::ts`, `F`, `bb1`] >>
  simp[Abbr `f`, fmp_cov_stack_def] >>
  gvs[fmp_target_run_def, run_insts_def, get_instruction_def]
QED

Resume focus_opt_fmp_cut_cover[ret]:
  `MEM ti.inst_opcode [RET; RETFMP; DRET]` by metis_tac[step_inst_intret_opcodes] >>
  `gas_cut n root4 t` by
    (irule gas_cut_readings_mono >>
     qpat_assum `gas_cut n root4 (_ with vs_inst_idx := _)` (irule_at Any) >>
     simp[] >> metis_tac[return_readings_le]) >>
  qpat_x_assum `gas_cut n root4 t ==> _` drule >>
  reverse (disch_then (DISJ_CASES_THEN strip_assume_tac))
  >- (drule_all (Q.INST [`eom` |-> `eom`, `C4` |-> `C4`] focus_fmp_cut_tail_observation) >>
      strip_tac >> gvs[MEM]) >>
  `ALL_DISTINCT (fn_labels fn')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  `get_instruction bb t.vs_inst_idx = SOME ti` by
    (qpat_assum `active_inst fn' ti t` (mp_then Any drule_all active_inst_block_lookup) >>
     strip_tac >> metis_tac[optionTheory.SOME_11]) >>
  `u = t` by
    (Cases_on `t.vs_inst_idx < u.vs_inst_idx`
     >- (qpat_assum `!i. _ <= i /\ _ ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
         gvs[get_instruction_def, fmp_inserted_op_def, MEM]) >>
     `u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
     metis_tac[fmp_target_run_zero]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  `(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_vars = FEMPTY /\
   ~(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_halted` by
    fs[o1_initial_state_ok_def] >>
  drule_all focus_fmp_source_points >> strip_tac >>
  `ssa_form fn` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  qabbrev_tac `root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `w2n root3.vs_fmp = w2n fmp` by simp[Abbr `root3`] >>
  `?m l. fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n fmp) eom T
           stk PG G tn fn s l t ts` by
    (Cases_on `restored` >- metis_tac[] >> gvs[] >>
     drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_restore_prefix)) >>
     disch_then (qx_choosel_then
       [`rest_fn`, `rest_src`, `rest_bb`, `rest_infos`, `rest_ctx`,
        `rest_runner`, `rest_len`, `rest_post`, `rest_cut`] strip_assume_tac) >>
     Cases_on `FLOOKUP (fmp_stage_plan rest_infos rest_ctx fn) (s.vs_current_bb,s.vs_inst_idx)`
     >- (qexistsl [`DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < rest_cut}`,
                   `rest_cut`] >> gvs[]) >>
     gvs[get_instruction_def, mk_inst_def, MEM] >>
     metis_tac[get_instruction_def, mk_inst_def, MEM,
               SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_restore_prefix)]) >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ restored _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all focus_fmp_aligned_layout >> strip_tac >>
  `pre_fmp_opcode inst.inst_opcode` by
    (qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
     metis_tac[active_inst_mem_fn_insts]) >>
  `inst = ti` by
    (Cases_on `MEM inst.inst_opcode [DALLOCA; RETPC_PARAM]`
     >- (mp_tac (Q.INST [`P` |-> `fmp_inserted_op`, `infos` |-> `infos`,
                         `ctx` |-> `ctx`, `runner` |-> `runner`, `fn` |-> `fn`,
                         `fn'` |-> `fn'`, `lbl` |-> `s.vs_current_bb`, `bb` |-> `bs`,
                         `idx` |-> `s.vs_inst_idx`, `i` |-> `t.vs_inst_idx`]
             fmpStageCoverMemAssembleTheory.fmp_cover_inserted_from_root_structural) >>
         (impl_tac >- (simp[fmp_inserted_op_def, fmp_cov_tidx_lt] >>
                       rw[] >> gvs[MEM] >>
                       metis_tac[SRULE [] fmp_cov_tidx_lt])) >>
         strip_tac >> gvs[get_instruction_def, fmp_inserted_op_def, MEM]) >>
     Cases_on `inst.inst_opcode = INVOKE`
     >- (qpat_x_assum `inst = EL _ _` SUBST_ALL_TAC >>
         drule_all fmp_stage_invoke_inst >> strip_tac >>
         gvs[get_instruction_def, MEM]) >>
     `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by fs[MEM] >>
     drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                       `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
     strip_tac >> gvs[get_instruction_def]) >>
  `inst.inst_opcode = RET` by fs[pre_fmp_opcode_def, MEM] >>
  qpat_x_assum `inst = ti` SUBST_ALL_TAC >>
  qpat_x_assum `stk = f'::xs` SUBST_ALL_TAC >>
  Cases_on `ts` >- fs[fmp_cov_stack_def] >>
  rename1 `fmp_cov_stack C4 (f'::xs) (p::ps) (f::stk')` >>
  PairCases_on `p` >>
  qpat_x_assum `fmp_cov_stack C4 (f'::xs) _ _`
    (strip_assume_tac o REWRITE_RULE [fmp_cov_stack_def]) >>
  qpat_x_assum `ti = EL _ _` kall_tac >>
  `s.vs_labels = t.vs_labels` by
    (qpat_assum `fmp_stage_rel _ _ m _ _ _ T _ _ _ _ _ _ _ t _` mp_tac >>
     simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!v. MEM (Var v) ti.inst_operands ==> IS_SOME (lookup_var v s)` by fs[] >>
  `opaque_use_ok fn` by fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
  drule_all focus_fmp_cut_source_return >>
  disch_then (qspec_then `fuel`
    (qx_choosel_then [`sr`, `se`, `sb`, `si`] strip_assume_tac)) >>
  `fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n root3.vs_fmp) eom T
     (f'::xs) PG G tn fn s l t ((p0,p1)::ps)` by simp[] >>
  drule_at (Pat `step_inst _ _ _ _ = IntRet _ _`) focus_fmp_cut_invoke_pop >>
  disch_then (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ T _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `taint_ok _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_use_static_ok _ _ _`)) >>
  disch_then (drule_at (Pat `bind_outputs _ _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `active_inst _ _ (_ with vs_inst_idx := _)`)) >>
  disch_then (qspecl_then [`rp`, `n`, `fn'`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> simp[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`jr`, `j`, `t1`] strip_assume_tac))) >>
  qpat_x_assum `!k. step_inst k C4 ti t = _` (qspec_then `fuel` assume_tac) >>
  `ALL_DISTINCT (fn_labels f.cf_fn)` by
    (gs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  `j = f.cf_inst` by metis_tac[active_inst_block_lookup, optionTheory.SOME_11] >>
  gvs[] >>
  qabbrev_tac `b3 = sb with vs_inst_idx := SUC f'.cf_state.vs_inst_idx` >>
  qabbrev_tac `b4 = s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx` >>
  `frame_reachable root3 C3 xs f'.cf_params
       (DRESTRICT f'.cf_prov (COMPL (set f'.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f'.cf_tvar (COMPL (set f'.cf_inst.inst_outputs)))
       f'.cf_fn si b3` by
    (simp[Abbr `b3`] >> irule frame_reachable_ret >> metis_tac[]) >>
  `!nm g. lookup_function nm C3.ctx_functions = SOME g ==> wf_function g` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  `~b3.vs_halted` by
    (qpat_assum `frame_reachable root3 C3 xs _ _ _ _ _ b3`
        (mp_then Any drule_all scfg_frame_reachable_entry_root) >> strip_tac >>
     drule o1PassLiftTheory.supply_frame_reach_not_halted >> fs[o1PassLiftTheory.fn_entry_state_def]) >>
  `b3.vs_gas_readings = b4.vs_gas_readings` by
    (qpat_assum `fmp_stage_rel _ _ _ _ _ _ F xs _ _ _ _ b3 _ b4 _` mp_tac >>
     simp[NoAsms, fmp_stage_rel_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
  `gas_cut n root3 b3` by
    (`root3.vs_gas_readings = root4.vs_gas_readings` by simp[Abbr `root3`] >>
     fs[gas_cut_def, Abbr `b4`]) >>
  qpat_assum `active_inst f.cf_fn ti' b4` (mp_then Any drule_all active_inst_block_lookup) >>
  disch_then (qx_choose_then `bb1` strip_assume_tac) >>
  disj1_tac >>
  qexistsl [`xs`, `f'.cf_params`, `DRESTRICT f'.cf_prov (COMPL (set f'.cf_inst.inst_outputs))`,
    `tn with t_var := DRESTRICT f'.cf_tvar (COMPL (set f'.cf_inst.inst_outputs))`,
    `f'.cf_fn`, `si`, `b3`, `DRESTRICT m {key | FST key < w2n f'.cf_state.vs_fmp}`,
    `p1`, `b4`, `ps`, `F`, `bb1`] >>
  gvs[Abbr `b4`, fmp_target_run_def, run_insts_def, get_instruction_def]
QED

Finalise focus_opt_fmp_cut_cover[local]

Theorem focus_opt_c1_section[local]:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  ctx_pass_stage rp (CFP_Simple VP_MakeSSA) view
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context C1 /\
  EVERY make_ssa_input_ok
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context.ctx_functions /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  o1_initial_state_ok V /\
  (!fn i s. raw_reachable V unit.cu_context fn i s /\ gas_cut n V s ==>
             inst_dload_in_section i s) /\
  (!fn i. MEM fn unit.cu_context.ctx_functions /\ MEM i (fn_insts fn) ==>
           ~MEM (Label "code_end") i.inst_operands) ==>
  mem_inv (\ctx fn i s. (gas_cut n V s ==> inst_dload_in_section i s) /\
    s.vs_code = V.vs_code /\ s.vs_data_section = V.vs_data_section) C1 V /\
  (!fn i. MEM fn C1.ctx_functions /\ MEM i (fn_insts fn) ==>
           ~MEM (Label "code_end") i.inst_operands)
Proof
  strip_tac >> fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn))
    unit.cu_context.ctx_functions` by
    (fs[o1_source_unit_ok_def, EVERY_MEM, raw_opcode_ok_def] >> metis_tac[]) >>
  `EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions` by
    (fs[EVERY_MEM, unit_defs_reach_uses_def, o1_ctx_shape_def] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_no_phi >>
     simp[EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  `mem_inv (\ctx fn i s. (gas_cut n V s ==> inst_dload_in_section i s) /\
    s.vs_code = V.vs_code /\ s.vs_data_section = V.vs_data_section)
    unit.cu_context V` by
    (simp[mem_inv_raw_reachable] >> metis_tac[raw_reachable_code_data]) >>
  gvs[o1_initial_state_ok_def] >>
  irule code_end_source_prefix_transport_upto >>
  metis_tac[init_ir_supply_inst_ok]
QED

(* A synchronized LowerDload expansion has the same unread gas list at
   the selected COPY. Thus bounded source taint and section safety suffice. *)
Theorem focus_opt_lower_row_bound[local]:
  ld_sync lo P C V stk PG G tn fn si s t0 A (f::fs) fuel /\ o1_ctx_shape C /\
  ir_supply_covers_fn f.lf_supply fn /\ fn' = ld_image f /\
  (!g i. MEM g C.ctx_functions /\ MEM i (fn_insts g) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  mem_inv (\ctx g i u. (gas_cut n V u ==> inst_dload_in_section i u) /\
    u.vs_code = V.vs_code /\ u.vs_data_section = V.vs_data_section) C V /\
  o1_safe_upto D lo n C V /\ LENGTH V.vs_data_section < dimword (:256) DIV 2 /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\ ld_prefix C' fn' X p h t0 t /\
  s.vs_gas_readings = t.vs_gas_readings /\ gas_cut n V t /\
  (EL h X).inst_opcode = CODECOPY /\ (EL h X).inst_operands = [dst; Var x; sz] /\
  code_end_var fn' x /\ eval_operand (Var x) t = SOME w /\
  FLOOKUP t.vs_labels "code_end" = SOME bword ==>
  w2n (w - bword) < dimword (:256) DIV 2
Proof
  strip_tac >>
  drule_then strip_assume_tac ld_sync_source >>
  `gas_cut n V s` by fs[gas_cut_def] >>
  `taint_ok fn tn si s` by
    (qpat_x_assum `o1_safe_upto _ _ _ _ _` mp_tac >>
     simp[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >>
     metis_tac[]) >>
  `MEM fn C.ctx_functions` by metis_tac[frameAllocationOwnershipTheory.frame_reachable_functions_member] >>
  `inst_dload_in_section si s /\ s.vs_data_section = V.vs_data_section` by
    (drule_all ld_sync_source_mem_inv >> simp[] >> metis_tac[]) >>
  irule focus_lower_dload_codecopy_point >> simp[] >> metis_tac[]
QED

(* Shared term quotations for the bounded raw-row induction. The transition
   interfaces keep lo, P, C, C', vs, Sigma and names fixed. *)
val focus_opt_ld_stable = ``\lo P Sigma names fs f0 A0 A frames.
  frames <> [] /\ TL frames = fs /\
  (HD frames).lf_serial = f0.lf_serial /\ ld_global lo A frames /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) frames /\
  (!j k. j < k /\ k < LENGTH frames ==>
    list_precedes (EL j frames).lf_fn.fn_name
                  (EL k frames).lf_fn.fn_name names) /\
  (!g. MEM g fs ==> FRANGE g.lf_H SUBSET ld_slots A fs /\
    (!a. MEM (SOME a) g.lf_Q ==> a IN ld_slots A fs)) /\
  (!a. a IN FDOM A0 /\ a IN ld_slots A0 fs ==>
    FLOOKUP A a = FLOOKUP A0 a)``;

val focus_opt_ld_row = ``\lo P C C' vs Sigma names gn ti t
                         stk PG G tn fn inst s t0 A f fs N X p h.
  ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
  ^focus_opt_ld_stable lo P Sigma names fs f A A (f::fs) /\
  gn = ld_image f /\ ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  t0.vs_inst_idx = p /\ ld_prefix C' gn X p h t0 t /\ h < LENGTH X /\
  ti = EL h X /\ s.vs_gas_readings = t0.vs_gas_readings /\
  t0.vs_gas_readings = t.vs_gas_readings /\
  EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (f::fs)``;

val focus_opt_ld_R = ``\lo P C C' vs Sigma names gn ti t.
  ?stk PG G tn fn inst s t0 A f fs N X p h.
    ^focus_opt_ld_row lo P C C' vs Sigma names gn ti t
      stk PG G tn fn inst s t0 A f fs N X p h``;

val focus_opt_ld_forward = ``\(C':venom_context) gn ti t.
  ?bb i j. lookup_block t.vs_current_bb gn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ i <= t.vs_inst_idx /\
    t.vs_inst_idx <= j /\ get_instruction bb t.vs_inst_idx = SOME ti /\
    t.vs_alloca_next < dimword (:256) /\
    w2n t.vs_initial_fmp <= w2n t.vs_fmp /\
    (ctx_has_dalloca C' ==> t.vs_alloca_next <= w2n t.vs_initial_fmp)``;

val focus_opt_ld_W = ``\C' gn ti t. ^focus_opt_ld_forward C' gn ti t /\
  ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)``;

val focus_opt_ld_effect = ``\lo P C vs A f tn PG G inst s t u fuel ss H'.
  step_inst fuel C inst s = OK ss /\
  ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_H := H';
    lf_tv := (step_taint inst s ss tn).t_var|>) /\
  ld_memory lo A (step_taint inst s ss tn) ss u /\
  ld_nonghost (step_taint inst s ss tn) ss u /\
  ld_ghost_ok (dyn_floor C vs) A H' (step_prov PG G inst ss) /\
  ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem ss.vs_memory u.vs_memory /\
  (!a. a IN FRANGE H' ==> a IN FDOM A) /\
  ss.vs_allocas = s.vs_allocas /\ u.vs_allocas = t.vs_allocas /\
  ss.vs_alloca_next = s.vs_alloca_next /\ u.vs_alloca_next = t.vs_alloca_next /\
  ss.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = t.vs_current_bb``;

val focus_opt_ld_advance = ``\lo P C C' vs Sigma names
                             stk PG G tn fn s A f fs N X p Ar g gn q ss j.
  ^focus_opt_ld_stable lo P Sigma names fs f A A (f::fs) /\
  g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\
  g.lf_supply = f.lf_supply /\ g.lf_Q = f.lf_Q /\
  (!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a) /\ ld_global lo Ar (g::fs) /\
  gn = ld_image f /\ gn = FST (lower_dload_function_supply f.lf_supply fn) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = p + LENGTH X /\
  ss.vs_current_bb = s.vs_current_bb /\ active_inst gn j q /\
  g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\ g.lf_tgt = q /\
  ss.vs_gas_readings = q.vs_gas_readings /\
  LENGTH ss.vs_gas_readings <= LENGTH s.vs_gas_readings /\
  EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH k.lf_src.vs_gas_readings) fs /\
  (!ni. active_inst fn ni g.lf_src ==>
    ld_sync lo P C vs stk PG G tn fn ni g.lf_src g.lf_tgt Ar (g::fs) N) ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j q``;

val focus_opt_ld_advance_all = ``\lo P C C' vs Sigma names.
  !stk PG G tn fn s A f fs N X p Ar g gn q ss j.
    ^focus_opt_ld_advance lo P C C' vs Sigma names
      stk PG G tn fn s A f fs N X p Ar g gn q ss j``;

Theorem focus_opt_ld_head_row[local]:
  ld_sync lo P C vs stk PG G tn fn next s1 q A1 (g::fs) N /\
  ^focus_opt_ld_stable lo P Sigma names fs g A1 A1 (g::fs) /\
  gn = ld_image g /\ ld_envelope g.lf_supply fn s1 s1.vs_inst_idx Y q.vs_inst_idx /\
  0 < LENGTH Y /\ j = EL 0 Y /\ s1.vs_gas_readings = q.vs_gas_readings /\
  EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\
    LENGTH s1.vs_gas_readings <= LENGTH k.lf_src.vs_gas_readings) (g::fs) ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j q
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `active_inst gn (EL 0 Y) q` by
    (drule ld_sync_active >> simp[HD] >> strip_tac >>
     drule ld_sync_control >> strip_tac >>
     drule_at (Pat `ld_envelope _ _ _ _ _ _`)
       lowerDloadReturnInteriorTheory.ld_envelope_target_at >>
     disch_then (qspecl_then [`q`,`0`] mp_tac) >> simp[ld_image_def]) >>
  qexistsl [`stk`,`PG`,`G`,`tn`,`fn`,`next`,`s1`,`q`,`A1`,`g`,`fs`,`N`,
    `Y`,`q.vs_inst_idx`,`0`] >>
  simp[lowerDloadSafetyKernelTheory.ld_prefix_zero] >> metis_tac[]
QED

(* ALLOCA changes the allocation map only on a cache miss. *)
Theorem focus_opt_ld_alloca_cached[local]:
  ^focus_opt_ld_advance_all lo P C C' vs Sigma names /\
  ^focus_opt_ld_stable lo P Sigma names fs f A A (f::fs) /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  o1_ctx_shape C /\ gn = ld_image f /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  MEM out (fn_ir_vars fn) /\ out IN fn_pv P fn /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (alloc_base,alloc_size) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] t.vs_inst_idx /\
  step_inst fuel C' inst t = OK u /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH k.lf_src.vs_gas_readings) fs ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  disch_then (map_every (assume_tac o BETA_RULE) o CONJUNCTS) >>
  `ld_global lo A (f::fs)` by metis_tac[] >>
  `t.vs_inst_idx = t.vs_inst_idx` by simp[] >>
  drule_all lowerDloadSafetyAllocationTheory.ld_cached_alloca_endpoint >> strip_tac >>
  drule ld_sync_active >> simp[HD] >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `step_inst fuel C' inst t = OK u` mp_tac >>
     disch_then (mp_tac o MATCH_MP (cj 1 (REWRITE_RULE[GSYM AND_IMP_INTRO]
       venomInstPropsTheory.step_preserves_control_flow))) >> simp[is_terminator_def]) >>
  `ss.vs_current_bb = s.vs_current_bb /\ ss.vs_gas_readings = s.vs_gas_readings` by
    (qpat_assum `step_inst 0 C inst s = OK ss` mp_tac >>
     simp[lowerDloadSafetyAllocationTheory.ld_alloca_step, exec_alloca_def, update_var_def] >>
     rpt strip_tac >> qpat_assum `_ = ss` (SUBST1_TAC o SYM) >> simp[]) >>
  `ss.vs_gas_readings = u.vs_gas_readings` by
    (qpat_assum `ld_nonghost _ ss u` mp_tac >> simp[NoAsms, lowerDloadSafetyKernelTheory.ld_nonghost_def]) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\ g.lf_supply = f.lf_supply /\
   g.lf_Q = f.lf_Q /\ g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
   g.lf_tgt = (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (qpat_assum `g = _` SUBST1_TAC >> simp[NoAsms, ADD1]) >>
  `gn = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  last_x_assum (qspecl_then
    [`stk`,`PG`,`step_prov PG G inst ss`,`step_taint inst s ss tn`,`fn`,`s`,
     `A`,`f`,`fs`,`N`,`[inst]`,`t.vs_inst_idx`,`A`,`g`,`gn`,
     `u with vs_inst_idx := SUC t.vs_inst_idx`,`ss`,`j`] mp_tac) >>
  (impl_tac >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
    simp[NoAsms, GSYM ADD1] >>
    rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
    qpat_assum `ss.vs_gas_readings = s.vs_gas_readings` (rewrite_tac o single) >> simp[NoAsms])) >>
  simp[ld_image_def, CONJ_ASSOC]
QED

Theorem focus_opt_ld_alloca_fresh[local]:
  ^focus_opt_ld_advance_all lo P C C' vs Sigma names /\
  ^focus_opt_ld_stable lo P Sigma names fs f A A (f::fs) /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  o1_ctx_shape C /\ lo <= vs.vs_alloca_next /\ gn = ld_image f /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  MEM out (fn_ir_vars fn) /\ out IN fn_pv P fn /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\ ir_supply_covers_fn f.lf_supply fn /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] t.vs_inst_idx /\
  step_inst fuel C' inst t = OK u /\
  s.vs_gas_readings = t.vs_gas_readings /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH k.lf_src.vs_gas_readings) fs ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  disch_then (map_every (assume_tac o BETA_RULE) o CONJUNCTS) >>
  `ld_global lo A (f::fs)` by metis_tac[] >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_active >> simp[HD] >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  drule_all lowerDloadSafetyAllocationTheory.ld_sync_original_site_fresh >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `s`, `t` |-> `t`, `fuel` |-> `fuel`,
    `ts` |-> `u`] lowerDloadSafetyAllocationTheory.ld_fresh_alloca_dispatch) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `sz` (qx_choose_then `ss` strip_assume_tac)) >>
  `step_inst 0 C inst s = OK ss` by
    (qpat_assum `step_inst fuel C inst s = OK ss` mp_tac >>
     simp[lowerDloadSafetyAllocationTheory.ld_alloca_step]) >>
  `ss.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = s.vs_current_bb /\
   ss.vs_memory = s.vs_memory /\ u.vs_memory = t.vs_memory /\
   ss.vs_gas_readings = s.vs_gas_readings /\ u.vs_gas_readings = t.vs_gas_readings` by
    (qpat_assum `ss = update_var _ _ _` SUBST1_TAC >>
     qpat_assum `u = update_var _ _ _` SUBST1_TAC >> simp[update_var_def]) >>
  `gn = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  qabbrev_tac `sn = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = t.vs_inst_idx + LENGTH [inst]` by
    simp[Abbr `q`, ADD1] >>
  `?i Y. active_inst fn i sn /\ ld_envelope f.lf_supply fn sn sn.vs_inst_idx Y q.vs_inst_idx` by
    (`active_inst gn j q` by (simp[NoAsms, Abbr `q`] >> first_assum ACCEPT_TAC) >>
     drule_at (Pat `ld_envelope _ _ _ _ _ _`)
       lowerDloadSafetyLocationsTheory.ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`gn`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `q.vs_inst_idx = _` SUBST1_TAC >>
     simp[NoAsms, Abbr `sn`] >> metis_tac[NoAsms]) >>
  `frame_reachable vs C stk PG (step_prov PG G inst ss) (step_taint inst s ss tn) fn i sn` by
    (simp[Abbr `sn`] >> irule frame_reachable_next >> simp[is_terminator_def] >> metis_tac[]) >>
  qabbrev_tac `Ar = A |+ ((f.lf_serial,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n sz))` >>
  qabbrev_tac `H' = f.lf_H |+ (out,(f.lf_serial,inst.inst_id))` >>
  qabbrev_tac `tn' = step_taint inst s ss tn` >>
  qabbrev_tac `g = f with <|lf_src := sn; lf_tgt := q; lf_H := H'; lf_tv := tn'.t_var|>` >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_ghosts >> simp[HD] >> strip_tac >>
  `FRANGE f.lf_H SUBSET FDOM A` by
    (simp[pred_setTheory.SUBSET_DEF] >> metis_tac[ld_global_selected, MEM]) >>
  `step_prov PG (ld_erase A o_f f.lf_H) inst ss = ld_erase Ar o_f H' /\
   ld_vars P Ar (f with <|lf_src := ss; lf_tgt := u; lf_H := H'; lf_tv := tn'.t_var|>) /\
   ld_memory lo Ar tn' ss u /\ ld_nonghost tn' ss u /\ FRANGE H' SUBSET FDOM Ar` by
    (`Ar = A |+ ((f.lf_serial,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n sz))` by
       simp[Abbr `Ar`] >>
     qpat_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_fn = fn` (SUBST_ALL_TAC o SYM) >>
     drule_all lowerDloadSafetyAllocationTheory.ld_fresh_alloca_effect >>
     disch_then (qspecl_then [`fuel`,`PG`,`C'`,`C`] strip_assume_tac) >>
     qpat_assum `Abbrev (H' = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     qpat_assum `Abbrev (tn' = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ld_vars P Ar g /\ ld_memory lo Ar tn' sn q /\ ld_nonghost tn' sn q` by
    (conj_tac
     >- (qpat_assum `ld_vars P Ar _` mp_tac >>
         simp[NoAsms, Abbr `g`, Abbr `sn`, Abbr `q`, ld_vars_def]) >>
     conj_tac
     >- (qpat_assum `ld_memory lo Ar tn' ss u` mp_tac >>
         simp[NoAsms, Abbr `sn`, Abbr `q`, lowerDloadSafetyKernelTheory.ld_memory_def] >>
         strip_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `ld_nonghost tn' ss u` mp_tac >>
     simp[NoAsms, Abbr `sn`, Abbr `q`, lowerDloadSafetyKernelTheory.ld_nonghost_def] >>
     strip_tac >> rpt conj_tac >> metis_tac[]) >>
  `ld_ghost_ok (dyn_floor C vs) Ar H' (step_prov PG G inst ss)` by
    (`~MEM inst.inst_opcode [PARAM; ADD; SUB; ASSIGN]` by simp[] >>
     drule_all ld_ghost_ok_step_fixed >> simp[]) >>
  `ld_dyn_agree (dyn_floor C vs) tn'.t_mem sn.vs_memory q.vs_memory` by
    (simp[Abbr `sn`, Abbr `q`, Abbr `tn'`] >>
     `source_memory_write_ranges inst s = []` by simp[codegenRelTheory.source_memory_write_ranges_def] >>
     drule ld_sync_dyn_agree >> strip_tac >> drule_all ld_dyn_agree_unwritten >> simp[]) >>
  `lo <= s.vs_alloca_next /\ lo <= t.vs_alloca_next` by
    (`raw_reachable vs C fn inst s` by metis_tac[lowerDloadReachabilityTheory.ld_frame_reachable_raw] >>
     drule lowerDloadFrontierTheory.ld_raw_reachable_frontier >> strip_tac >>
     drule ld_sync_frontier >> decide_tac) >>
  `Ar = A |+ ((f.lf_serial,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n sz)) /\
   sn = ss with vs_inst_idx := SUC s.vs_inst_idx /\ q = u with vs_inst_idx := SUC t.vs_inst_idx /\
   g = f with <|lf_src := sn; lf_tgt := q; lf_H := H'; lf_tv := tn'.t_var|>` by
    simp[Abbr `Ar`, Abbr `sn`, Abbr `q`, Abbr `g`] >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) tn' fn i sn q Ar (g::fs) N /\
   ld_global lo Ar (g::fs)` by
    (drule_all (SRULE [PULL_EXISTS] lowerDloadSafetyAllocationTheory.ld_sync_fresh_alloca_update) >>
     qpat_assum `g = _` SUBST1_TAC >> qpat_assum `sn = _` SUBST1_TAC >>
     qpat_assum `q = _` SUBST1_TAC >> qpat_assum `Ar = _` SUBST1_TAC >>
     disch_then ACCEPT_TAC) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\ g.lf_supply = f.lf_supply /\
   g.lf_Q = f.lf_Q /\ g.lf_src = sn /\ g.lf_tgt = q` by
    (qpat_assum `g = _` SUBST1_TAC >> simp[NoAsms]) >>
  `!ni. active_inst fn ni g.lf_src ==>
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) tn' fn ni g.lf_src g.lf_tgt Ar (g::fs) N` by
    (qpat_assum `g.lf_src = sn` SUBST1_TAC >> qpat_assum `g.lf_tgt = q` SUBST1_TAC >>
     rpt strip_tac >>
     `ni = i` by metis_tac[REWRITE_RULE[fn_labels_def] fmpStageBlockSimCodeTheory.active_inst_unique] >>
     qpat_assum `ni = i` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a` by
    (qpat_assum `Ar = _` SUBST1_TAC >> simp[NoAsms, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `ss.vs_gas_readings = q.vs_gas_readings` by
    (qpat_assum `q = _` SUBST1_TAC >> simp[NoAsms] >> metis_tac[]) >>
  `LENGTH ss.vs_gas_readings <= LENGTH s.vs_gas_readings` by
    (qpat_assum `ss.vs_gas_readings = s.vs_gas_readings` (rewrite_tac o single) >> simp[NoAsms]) >>
  `g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx)` by metis_tac[] >>
  qpat_assum `q = _` (SUBST1_TAC o SYM) >>
  qpat_x_assum `!stk PG G tn fn s A f fs N X p Ar g gn q ss j. _`
    (qspecl_then [`stk`,`PG`,`step_prov PG G inst ss`,`tn'`,`fn`,`s`,`A`,`f`,
      `fs`,`N`,`[inst]`,`t.vs_inst_idx`,`Ar`,`g`,`gn`,`q`,`ss`,`j`] mp_tac) >>
  (impl_tac >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
    simp[NoAsms, GSYM ADD1] >>
    rpt (first_assum ACCEPT_TAC ORELSE conj_tac))) >>
  `q.vs_gas_readings = t.vs_gas_readings` by metis_tac[] >>
  qpat_assum `gn = ld_image f` (fn image =>
    qpat_assum `q.vs_gas_readings = t.vs_gas_readings` (fn gas =>
      simp[NoAsms, image, gas, CONJ_ASSOC]))
QED

Theorem focus_opt_ld_alloca_next[local]:
  ^focus_opt_ld_advance_all lo P C C' vs Sigma names /\
  o1_ctx_shape C /\ lo <= vs.vs_alloca_next /\
  ^focus_opt_ld_row lo P C C' vs Sigma names gn inst t
    stk PG G tn fn inst s t A f fs N [inst] t.vs_inst_idx 0 /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  inst_wf inst /\ ir_supply_covers_fn f.lf_supply fn /\
  inst.inst_opcode = ALLOCA /\ step_inst fuel C' inst t = OK u /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  qpat_assum `EVERY _ (f::fs)` (strip_assume_tac o REWRITE_RULE[EVERY_DEF]) >>
  drule ld_sync_source >> strip_tac >>
  `?out. inst.inst_outputs = [out]` by
    fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  drule allocaFrontierBoundTheory.active_inst_mem_fn_insts >> strip_tac >>
  `MEM out (fn_ir_vars fn)` by
    (irule lowerDloadSafetyUpdatesTheory.ld_inst_output_ir >> qexists `inst` >> simp[]) >>
  `out IN fn_pv P fn` by
    (mp_tac (Q.INST [`fn` |-> `fn`] o1LowerDloadClosureTheory.ptr_roots_subset_fn_pv) >>
     simp[pred_setTheory.SUBSET_DEF, ptr_roots_def, pointerConfinedDefsTheory.alloca_roots_def] >>
     disch_then irule >> disj1_tac >> disj1_tac >> qexists `inst` >> simp[inst_output_def]) >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >-
    (drule_all (BETA_RULE focus_opt_ld_alloca_fresh) >> simp[CONJ_ASSOC]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME allocation` >>
  PairCases_on `allocation` >> drule_all (BETA_RULE focus_opt_ld_alloca_cached) >> simp[CONJ_ASSOC]
QED

Theorem focus_opt_ld_advance_row[local]:
  ^focus_opt_ld_advance lo P C C' vs Sigma names
    stk PG G tn fn s A f fs N X p Ar g gn q ss j
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `^focus_opt_ld_stable lo P Sigma names fs g Ar Ar (g::fs)` by
    (drule_all (BETA_RULE lowerDloadReturnStableTheory.ld_stable_head_extend) >>
     simp[] >> strip_tac >> metis_tac[]) >>
  drule_all lowerDloadSafetyLocationsTheory.ld_envelope_successor_head >>
  strip_tac >>
  `active_inst fn next g.lf_src` by simp[] >>
  `ld_sync lo P C vs stk PG G tn fn next g.lf_src q Ar (g::fs) N` by
    (qpat_assum `!ni. active_inst fn ni g.lf_src ==> _`
       (qspec_then `next` mp_tac) >> gvs[]) >>
  `EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\
    LENGTH g.lf_src.vs_gas_readings <= LENGTH k.lf_src.vs_gas_readings) (g::fs)` by
    (simp[] >> fs[EVERY_MEM] >> metis_tac[LESS_EQ_TRANS]) >>
  `ld_envelope g.lf_supply fn g.lf_src g.lf_src.vs_inst_idx Y q.vs_inst_idx` by gvs[] >>
  irule (BETA_RULE focus_opt_ld_head_row) >>
  goal_assum (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ld_envelope _ _ _ _ _ _`)) >>
  gvs[ld_image_def] >> metis_tac[]
QED

(* The ordinary effect keeps the allocation map and takes only the given
   step. An active target successor supplies the next source location. *)
Theorem focus_opt_ld_effect_row[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^focus_opt_ld_stable lo P Sigma names fs f A A (f::fs) /\
  o1_ctx_shape C /\ ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  gn = ld_image f /\ gn = FST (lower_dload_function_supply f.lf_supply fn) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] t.vs_inst_idx /\
  step_inst fuel C' inst t = OK u /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  ^focus_opt_ld_effect lo P C vs A f tn PG G inst s t u fuel ss H' /\
  ss.vs_prev_bb = s.vs_prev_bb /\ u.vs_prev_bb = t.vs_prev_bb /\
  s.vs_gas_readings = t.vs_gas_readings /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) fs ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  qabbrev_tac `s1 = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g = f with <|lf_src := s1; lf_tgt := q; lf_H := H';
    lf_tv := (step_taint inst s ss tn).t_var|>` >>
  drule ld_sync_active >> simp[HD] >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  `q.vs_current_bb = s.vs_current_bb /\
   q.vs_inst_idx = t.vs_inst_idx + LENGTH [inst]` by simp[Abbr `q`, ADD1] >>
  `?next Y. active_inst fn next s1 /\
    ld_envelope f.lf_supply fn s1 (SUC s.vs_inst_idx) Y (SUC t.vs_inst_idx)` by
    (drule_at (Pat `ld_envelope _ _ _ _ _ _`)
       lowerDloadSafetyLocationsTheory.ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`gn`] mp_tac) >>
     simp[Abbr `s1`, ADD1, Excl "EL"] >> metis_tac[]) >>
  `ld_vars P A g` by
    (qabbrev_tac `g0 = f with <|lf_src := ss; lf_tgt := u; lf_H := H';
        lf_tv := (step_taint inst s ss tn).t_var|>` >>
     `g = g0 with <|lf_src := g0.lf_src with vs_inst_idx := SUC s.vs_inst_idx;
                    lf_tgt := g0.lf_tgt with vs_inst_idx := SUC t.vs_inst_idx|>` by
       simp[Abbr `g`, Abbr `g0`, Abbr `s1`, Abbr `q`] >>
     simp[lowerDloadSafetyAdvanceTheory.ld_vars_inst_indices]) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
     fn next s1 q A (g::fs) N /\ ld_global lo A (g::fs)` by
    (drule lowerDloadSafetyAdvanceTheory.ld_sync_ordinary_advance >>
     metis_tac[markerTheory.Abbrev_def]) >>
  `ss.vs_gas_readings = q.vs_gas_readings` by fs[lowerDloadSafetyKernelTheory.ld_nonghost_def, Abbr `q`] >>
  `LENGTH ss.vs_gas_readings <= LENGTH s.vs_gas_readings` by
    (qspecl_then [`fuel`,`C`,`inst`,`s`] mp_tac
       (CONJUNCT1 gasCountTheory.gas_count_suffix) >>
     simp[gasCountTheory.gas_count_suffix_def, LENGTH_DROP]) >>
  `!ni. active_inst fn ni g.lf_src ==>
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
      fn ni g.lf_src g.lf_tgt A (g::fs) N` by
    (simp[Abbr `g`] >> rpt strip_tac >>
     `ni = next` by metis_tac[REWRITE_RULE[venomInstTheory.fn_labels_def]
       fmpStageBlockSimCodeTheory.active_inst_unique] >> simp[]) >>
  `^focus_opt_ld_R lo P C C' vs Sigma names gn j q` by
    (BETA_TAC >> irule (BETA_RULE focus_opt_ld_advance_row) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`A`,`A`,`step_prov PG G inst ss`,`N`,`PG`,`[inst]`,
               `f`,`fn`,`fs`,`g`,`t.vs_inst_idx`,`s`,`ss`,`stk`,`step_taint inst s ss tn`] >>
     simp[Abbr `g`, Abbr `s1`] >> metis_tac[]) >>
  pop_assum (mp_tac o BETA_RULE) >> simp[CONJ_ASSOC]
QED

(* These suppliers advance the actual next fetch, including a GAS read
   whose remaining oracle may be shorter than the current row's. *)
Theorem focus_opt_ld_simple_next[local]:
  ^focus_opt_ld_row lo P C C' vs Sigma names gn ti t
    stk PG G tn fn inst s t0 A f fs N [inst] p h /\
  ALL_DISTINCT (fn_labels gn) /\
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  (MEM inst.inst_opcode
     [CALLER;ADDRESS;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;COINBASE;
      TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
      CALLDATASIZE;RETURNDATASIZE;CODESIZE] \/
   (MEM inst.inst_opcode
      [MUL;Div;Mod;SDIV;SMOD;Exp;ADDMOD;MULMOD;SLT;SGT;ISZERO;AND;OR;XOR;
       NOT;SIGNEXTEND;BYTE;OFFSET;ADD;SUB;SHL;SHR;SAR] \/
    MEM inst.inst_opcode [ASSIGN;RETPC_PARAM;PARAM]) \/
   MEM inst.inst_opcode [LOG;SSTORE;TSTORE]) /\
  step_inst fuel C' ti t = OK u /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  gas_cut n vs (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `h = 0` by fs[] >> qpat_x_assum `h = 0` SUBST_ALL_TAC >>
  qpat_x_assum `ld_prefix _ _ _ _ 0 _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [lowerDloadSafetyKernelTheory.ld_prefix_zero]) >>
  `ti = inst` by fs[] >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  qpat_x_assum `t = t0` (SUBST_ALL_TAC o SYM) >>
  `?bb. lookup_block t.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
        get_instruction bb t.vs_inst_idx = SOME inst` by
    (irule lowerDloadPtrRawReachableTheory.active_inst_block_lookup >> metis_tac[]) >>
  `active_inst (ld_image f) j (u with vs_inst_idx := SUC t.vs_inst_idx)` by metis_tac[] >>
  qpat_x_assum `_ \/ _ \/ _` mp_tac >>
  disch_then (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN assume_tac)) >>
  MAP_FIRST (drule_all o BETA_RULE o REWRITE_RULE [LET_THM])
    [gasFocusLowerDloadEnvironmentPointTheory.ld_focus_environment_point_next,
     gasFocusLowerDloadArithmeticBindingPointTheory.ld_focus_arithmetic_binding_point_next,
     gasFocusLowerDloadLogStorePointTheory.ld_focus_log_store_point_next] >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `gn = ld_image g` by (qpat_assum `g = _` (rewrite_tac o single) >> simp[ld_image_def]) >>
  irule (BETA_RULE focus_opt_ld_head_row) >>
  goal_assum (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ld_envelope _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

(* The synchronized frame accounts for the extra LowerDload allocation
   slots within the source instruction's reserved headroom. *)
Theorem focus_opt_ld_access_headroom[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  mem_inv dload_headroom_ok C vs /\ lo <= vs.vs_alloca_next /\
  raw_reachable vs C fn inst s ==>
  lo <= dyn_floor C vs /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
     b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs /\ c+sz < dimword(:256))
Proof
  strip_tac >>
  drule_all lowerDloadDynHeadroomTheory.ld_raw_dyn_headroom >> strip_tac >>
  drule lowerDloadFrontierTheory.ld_raw_reachable_frontier >> strip_tac >>
  drule ld_sync_frontier >> strip_tac >>
  `t.vs_alloca_next <= dyn_floor C vs` by decide_tac >>
  `dload_headroom_ok C fn inst s` by
    (drule_all ld_sync_source_mem_inv >> simp[]) >>
  `t.vs_alloca_next < dimword(:256)` by
    (drule_all ld_sync_target_headroom >> simp[]) >>
  `lo <= dyn_floor C vs` by decide_tac >> simp[] >>
  drule lowerDloadOracleCallAssemblyTheory.ld_sync_slots >> strip_tac >>
  drule lowerDloadOracleCallAssemblyTheory.ld_sync_maps >> strip_tac >>
  drule ld_sync_active >> simp[HD] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule_all lowerDloadSafetyAllocBoundsTheory.ld_alloc_frontiers >>
  simp[] >> decide_tac
QED

(* Point effects for the singleton access opcodes, using only safety up to
   this point and the successful step that has already been taken. *)
Theorem focus_opt_ld_access_effect[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ~in_revert_forward fn s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ s.vs_gas_readings = t.vs_gas_readings /\
  gas_cut n vs t /\ step_inst fuel C' inst t = OK u /\
  (MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ] \/
   MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY] \/
   MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] \/
   inst.inst_opcode = DALLOCA) ==>
  ?ss H'. ^focus_opt_ld_effect lo P C vs A f tn PG G inst s t u fuel ss H' /\
    ss.vs_prev_bb = s.vs_prev_bb /\ u.vs_prev_bb = t.vs_prev_bb
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ld_sync_source >> strip_tac >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  `raw_reachable vs C fn inst s` by
    (drule_all lowerDloadReachabilityTheory.ld_frame_reachable_raw >> simp[]) >>
  qpat_assum `o1_safe_upto _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[o1_safe_upto_def, o1_ptr_safe_upto_def]) >>
  drule_all concretizeLayoutCutSafeTheory.ptr_discipline_upto_at >> strip_tac >>
  `lo <= vs.vs_alloca_next` by fs[ptr_discipline_upto_def] >>
  drule_all focus_opt_ld_access_headroom >> strip_tac >>
  qpat_x_assum `MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ] \/ _` strip_assume_tac
  >- (`MEM inst.inst_opcode [MLOAD;ILOAD] ==> ~in_revert_forward fn s` by simp[] >>
      `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> b+sz <= dyn_floor C vs` by metis_tac[] >>
      `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
      drule_all lowerDloadClassifiedReadPointEffectTheory.ld_sync_classified_read_effect_at >>
      disch_then (qx_choosel_then [`ss`,`H'`] (map_every assume_tac o CONJUNCTS)) >>
      drule_all ld_sync_ghost_step >> strip_tac >>
      `~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
       source_memory_write_ranges inst s = []` by
        (qpat_assum `MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ]` mp_tac >>
         pure_rewrite_tac[MEM] >> strip_tac >>
         qpat_assum `inst.inst_opcode = _` (fn eq =>
           simp[NoAsms, eq, is_alloca_op_def, venomEffectsTheory.write_effects_def,
                venomEffectsTheory.empty_effects_def, codegenRelTheory.source_memory_write_ranges_def])) >>
      drule_all ld_sync_dyn_agree_unwritten >> strip_tac >>
      qexistsl [`ss`,`H'`] >> simp[])
  >- (`fn_shape_ok fn /\ fn_inst_wf fn` by
        (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
      `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
      drule ld_sync_active >> simp[HD] >> strip_tac >>
      drule_all lowerDloadMemoryWritePointEffectTheory.ld_sync_memory_write_effect_at >>
      disch_then (qx_choose_then `ss` (map_every assume_tac o CONJUNCTS)) >>
      `ld_ghost_ok (dyn_floor C vs) A f.lf_H (step_prov PG G inst ss)` by
        (qpat_assum `step_prov PG G inst ss = G` (rewrite_tac o single) >>
         drule ld_sync_ghosts >> simp[HD]) >>
      qexistsl [`ss`,`f.lf_H`] >> simp[] >>
      qpat_assum `ld_vars P A _` mp_tac >> simp[NoAsms, ld_vars_def])
  >- (`!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
          b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs` by metis_tac[] >>
      `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
      drule_all lowerDloadPublicCopyPointEffectTheory.ld_sync_public_copy_effect_at >>
      disch_then (qx_choosel_then [`ss`,`H'`] (map_every assume_tac o CONJUNCTS)) >>
      drule_all ld_sync_ghost_step >> strip_tac >>
      qexistsl [`ss`,`H'`] >> simp[]) >>
  `ctx_has_dalloca C` by
    (simp[NoAsms, ctx_has_dalloca_def, EXISTS_MEM] >>
     metis_tac[lowerDloadOracleCallAssemblyTheory.ld_active_inst_member,
               frameAllocationOwnershipTheory.frame_reachable_functions_member]) >>
  `w2n vs.vs_initial_fmp <= w2n s.vs_fmp` by
    (drule ptrDisciplineEmptyTaintTheory.frame_reachable_initial_fmp >> strip_tac >>
     fs[allocas_below_fmp_def]) >>
  drule_all lowerDloadOrdinaryEndpointTheory.ld_sync_dalloca_effect_at >>
  simp[CONJ_ASSOC]
QED

Theorem focus_opt_ld_block_row[local]:
  ^focus_opt_ld_R lo P C C' vs Sigma names gn ti t /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  callee_first names C.ctx_functions /\
  (!f. MEM f C.ctx_functions ==>
    ir_supply_covers_fn (Sigma f.fn_name) f /\
    lookup_function f.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma f.fn_name) f))) /\
  o1_safe_upto D lo n C vs /\ gas_cut n vs t /\
  is_terminator ti.inst_opcode /\ step_inst fuel C' ti t = OK u /\
  ~u.vs_halted /\ enters_block gn u tp /\ active_inst gn j tp ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j tp
Proof
  BETA_TAC >> disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all lowerDloadSafetyAmbientTheory.ld_sync_fn_shape >> strip_tac >>
     drule o1_fn_shape_components >> simp[]) >>
  drule ld_sync_source >> strip_tac >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (conj_tac >> strip_tac >>
     `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
       simp[is_terminator_def] >>
     drule_all lowerDloadEnvelopeControlTheory.ld_envelope_nonterminal >> strip_tac >>
     fs[EVERY_EL] >> metis_tac[]) >>
  drule_all lowerDloadSafetyLocationsTheory.ld_envelope_ordinary >> strip_tac >>
  `h = 0` by fs[] >>
  `t0 = t /\ ti = inst` by fs[lowerDloadSafetyKernelTheory.ld_prefix_zero] >>
  qpat_x_assum `t0 = t` SUBST_ALL_TAC >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  drule_all o1LowerDloadRunnerBoundaryTheory.ld_terminator_ok_branch >> strip_tac >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  `raw_reachable vs C fn inst s` by
    (irule lowerDloadReachabilityTheory.ld_frame_reachable_raw >> metis_tac[]) >>
  qpat_assum `o1_safe_upto _ _ _ _ _` (strip_assume_tac o REWRITE_RULE[o1_safe_upto_def]) >>
  `raw_mem_ok C fn inst s /\ dload_offset_ok C fn inst s` by metis_tac[] >>
  qpat_x_assum `o1_ptr_safe_upto _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[o1_ptr_safe_upto_def, ptr_discipline_upto_def]) >>
  `taint_ok fn tn inst s` by metis_tac[] >>
  `gn = FST (lower_dload_function_supply (Sigma fn.fn_name) fn)` by
    (drule ld_sync_head >> strip_tac >> fs[ld_image_def]) >>
  `!k. MEM k C.ctx_functions ==> ir_supply_covers_fn (Sigma k.fn_name) k` by metis_tac[] >>
  `!k. MEM k C.ctx_functions ==>
    lookup_function k.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma k.fn_name) k))` by metis_tac[] >>
  drule_all (BETA_RULE gasFocusLowerDloadControlEntryTheory.ld_focus_control_entry) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  irule (BETA_RULE focus_opt_ld_head_row) >>
  goal_assum (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ld_envelope _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[lowerDloadSafetyKernelTheory.ld_prefix_bound]
QED

(* A successful raw expansion step needs no successful suffix. *)
Theorem focus_opt_ld_expansion_next[local]:
  ^focus_opt_ld_row lo P C C' vs Sigma names gn ti t
    stk PG G tn fn inst s t0 A f fs N X p h /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ o1_safe_upto D lo n C vs /\ gas_cut n vs t /\
  ir_supply_covers_fn f.lf_supply fn /\
  ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
  step_inst fuel C' ti t = OK u /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  (SUC h < LENGTH X \/
   (SUC h = LENGTH X /\ ~in_revert_forward fn s /\
    (inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES) /\
    ^focus_opt_ld_advance_all lo P C C' vs Sigma names)) ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  drule ld_sync_source >> strip_tac >>
  `gn = FST (lower_dload_function_supply f.lf_supply fn)` by
    (drule ld_sync_active >> fs[ld_image_def]) >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    metis_tac[lowerDloadReturnInteriorTheory.ld_envelope_source_nonterminal] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) X` by
    (drule_all lowerDloadEnvelopeControlTheory.ld_envelope_nonterminal >> simp[EVERY_MEM]) >>
  `q.vs_current_bb = s.vs_current_bb` by
    (simp[Abbr `q`] >> metis_tac[lowerDloadEnvelopeControlTheory.ld_prefix_control,
       ld_sync_control, venomInstPropsTheory.step_preserves_control_flow]) >>
  `t.vs_inst_idx = p + h` by metis_tac[lowerDloadSafetyKernelTheory.ld_prefix_position] >>
  qpat_x_assum `SUC h < LENGTH X \/ _`
    (DISJ_CASES_THEN2 assume_tac (map_every assume_tac o CONJUNCTS))
  >- suspend "interior" >>
  `gas_cut n vs s` by fs[gas_cut_def, Abbr `q`] >>
  `inst_wf inst` by
    (drule_all ld_sync_fn_shape >>
     metis_tac[o1_fn_shape_components, fmpStepStructuralTheory.fn_inst_wf_fn_insts,
               lowerDloadOracleCallAssemblyTheory.ld_active_inst_member, EVERY_MEM]) >>
  `EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH k.lf_src.vs_gas_readings) fs` by fs[] >>
  `q.vs_inst_idx = p + LENGTH X` by simp[Abbr `q`, ADD1] >>
  Cases_on `inst.inst_opcode = DLOAD`
  >- suspend "scratch" >>
  `inst.inst_opcode = DLOADBYTES` by metis_tac[] >>
  suspend "bytes"
QED

Resume focus_opt_ld_expansion_next[interior]:
  `active_inst gn (EL (SUC h) X) q` by
    (qpat_assum `gn = FST _` SUBST1_TAC >>
     irule lowerDloadReturnInteriorTheory.ld_envelope_target_at >>
     simp[] >> qexistsl [`s.vs_inst_idx`,`p`,`s`] >> simp[Abbr `q`, ADD1]) >>
  `ALL_DISTINCT (fn_labels gn)` by
    (Cases_on `lower_dload_function_supply f.lf_supply fn` >>
     drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >> fs[fn_labels_def]) >>
  `j = EL (SUC h) X` by metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique] >>
  `step_inst 0 C' (EL h X) t = OK u` by metis_tac[step_inst_non_invoke] >>
  `ld_prefix C' gn X p (SUC h) t0 q` by
    (unabbrev_all_tac >> metis_tac[lowerDloadSafetyKernelTheory.ld_prefix_next]) >>
  `q.vs_gas_readings = t0.vs_gas_readings` by
    metis_tac[gasFocusLowerDloadCutGuardsTheory.ld_expansion_prefix_readings] >>
  qexistsl [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`t0`,`A`,`f`,`fs`,`N`,`X`,`p`,`SUC h`] >>
  simp[] >> metis_tac[]
QED

Resume focus_opt_ld_expansion_next[scratch]:
  `?off out. inst.inst_operands = [off] /\ inst.inst_outputs = [out]` by
    fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `ld_prefix C' (ld_image f) X p h t0 t /\
   step_inst fuel C' (EL h X) t = OK u` by metis_tac[] >>
  drule_all gasFocusLowerDloadScratchNextTheory.ld_focus_dload_scratch_next >>
  disch_then (qx_choosel_then [`ss`,`v`,`g`,`c`] (map_every assume_tac o CONJUNCTS)) >>
  `ss.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  qpat_assum `!stk PG G tn fn s A f fs N X p Ar g gn q ss j. _` irule >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`A`,`A`,`step_prov PG G inst ss`,`N`,`PG`,`X`,`f`,`fn`,`fs`,`g`,`p`,
    `s`,`ss`,`stk`,`step_taint inst s ss tn`] >>
  simp[Abbr `q`] >> metis_tac[]
QED

Resume focus_opt_ld_expansion_next[bytes]:
  `?dest off len. inst.inst_operands = [dest;off;len]` by
    fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `LENGTH X = 2` by
    (drule_all lowerDloadPublicTraceTheory.ld_dloadbytes_envelope_temporary >>
     strip_tac >> simp[]) >>
  `h = 1` by decide_tac >>
  `ld_prefix C' gn X p 1 t0 t /\ step_inst fuel C' (EL 1 X) t = OK u` by metis_tac[] >>
  drule_all gasFocusLowerDloadBytesWriteTheory.ld_focus_bytes_classified_write >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `lo <= vs.vs_alloca_next /\ mem_inv dload_headroom_ok C vs` by
    fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >>
  drule_all (REWRITE_RULE [LET_THM] gasFocusLowerDloadBytesNextTheory.ld_focus_bytes_classified_next) >>
  disch_then (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  `ss.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  qpat_x_assum `t = (update_var _ _ _ with vs_inst_idx := _)` kall_tac >>
  qpat_x_assum `ss = write_memory_with_expansion _ _ _` kall_tac >>
  qpat_x_assum `u = write_memory_with_expansion _ _ _` kall_tac >>
  qpat_x_assum `step_taint _ _ _ _ = _` kall_tac >>
  qpat_x_assum `step_prov _ _ _ _ = _` kall_tac >>
  qabbrev_tac `g = f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                            lf_tgt := q|>` >>
  qpat_assum `!stk PG G tn fn s A f fs N X p Ar g gn q ss j. _` irule >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`A`,`A`,`step_prov PG G inst ss`,`N`,`PG`,`X`,`f`,`fn`,`fs`,`g`,`p`,
    `s`,`ss`,`stk`,`step_taint inst s ss tn`] >>
  simp[Abbr `g`, Abbr `q`] >> metis_tac[]
QED

Finalise focus_opt_ld_expansion_next[local]

Theorem focus_row_visit_inverse[local]:
  !xs be.
    DROP be.vs_inst_idx bt.bb_instructions = xs /\
    MEM ((a,e,i.inst_id),tf,i,t)
      (trace_block a e fuel C tf bt be) ==>
    ?pre rest. xs = pre ++ i::rest /\
      t.vs_inst_idx = be.vs_inst_idx + LENGTH pre /\
      EVERY (\x. ~is_terminator x.inst_opcode) pre /\
      FOLDR (dft_exec_cons fuel C) OK pre be = OK t
Proof
  Induct
  >- (rpt strip_tac >>
      `LENGTH bt.bb_instructions <= be.vs_inst_idx` by
        (gvs[GSYM LENGTH_NIL, LENGTH_DROP]) >>
      fs[Once (cj 2 trace_defs), get_instruction_def]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `DROP be.vs_inst_idx bt.bb_instructions = head::xs` >>
  `be.vs_inst_idx < LENGTH bt.bb_instructions` by
    (qpat_assum `DROP _ _.bb_instructions = _::_`
       (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[NoAsms, LENGTH_DROP]) >>
  `get_instruction bt be.vs_inst_idx = SOME head /\
   DROP (SUC be.vs_inst_idx) bt.bb_instructions = xs` by
    (drule DROP_BY_DROP_SUC >> simp[get_instruction_def]) >>
  drule_then assume_tac trace_block_visit >>
  qpat_x_assum `MEM _ (trace_block _ _ _ _ _ _ _)` mp_tac >>
  asm_rewrite_tac[MEM, MEM_APPEND, pairTheory.PAIR_EQ] >> strip_tac
  >- (gvs[] >> qexistsl [`[]`,`xs`] >> simp[])
  >- (`MEM (a,e,i.inst_id) (MAP FST (trace_step a e fuel C tf head be))` by
        (simp[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
      metis_tac[dftGasFromListTraceNamesTheory.trace_step_not_root]) >>
  Cases_on `step_inst fuel C head be` >> gvs[] >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  rename1 `step_inst fuel C head be = OK post` >>
  qpat_x_assum `!s. DROP _ _ = _ /\ MEM _ _ ==> _`
    (qspec_then `post with vs_inst_idx := SUC be.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`head::pre`,`rest`] >> simp[dftIndexedExecTheory.dft_exec_cons_def]
QED

(* A child frame keeps its call site throughout the child's trace. Changing
   the selected instruction ID does not move that frame to another site. *)
Theorem focus_child_row_excludes[local]:
  MEM ((p,d,id),fn,i,t) (trace_step P D fuel C f head s) /\
  ~MEM head.inst_id (MAP (\x. x.inst_id) (DROP post.vs_inst_idx bb.bb_instructions)) ==>
  !id' g j u. ~MEM ((p,d,id'),g,j,u) (trace_block P D fuel C f bb post)
Proof
  rpt strip_tac >>
  drule (REWRITE_RULE [EVERY_MEM] (cj 1 dftGasFromListTraceNamesTheory.trace_regions)) >>
  simp[] >> strip_tac >>
  `block_region P D [head.inst_id] (p,d,id')` by
    (irule dftGasFromListTraceNamesTheory.below_call_region >> simp[] >>
     qexists `head.inst_id` >> simp[]) >>
  drule dftGasFromListTraceNamesTheory.trace_block_region >> simp[] >> strip_tac >>
  metis_tac[dftGasFromListTraceNamesTheory.block_regions_disjoint, MEM]
QED

Theorem focus_later_row_excludes[local]:
  MEM ((p,d,id),fn,i,t) (trace_block P D fuel C f bb s) ==>
  !id' g j u. ~MEM ((p,d,id'),g,j,u) (trace_blocks P D fuel C f post)
Proof
  rpt strip_tac >>
  drule dftGasFromListTraceNamesTheory.trace_blocks_region >> simp[] >> strip_tac >>
  `later_region P D (p,d,id)` by
    fs[dftGasFromListTraceNamesTheory.later_region_def] >>
  drule dftGasFromListTraceNamesTheory.trace_block_region >> simp[] >>
  metis_tac[dftGasFromListTraceNamesTheory.block_later_disjoint]
QED

Theorem focus_row_continuations[local]:
  (!P D fuel C f inst s. !h p d id fn i t.
    EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                     g.fn_blocks) C.ctx_functions /\
    h < LENGTH (trace_step P D fuel C f inst s) /\
    EL h (trace_step P D fuel C f inst s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_step P D fuel C f inst s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest /\
      (!id' g j u. ~MEM ((p,d,id'),g,j,u) rest)) /\
  (!P D fuel C f bb s. !h p d id fn i t.
    EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                     g.fn_blocks) C.ctx_functions /\
    ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions) /\
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    h < LENGTH (trace_block P D fuel C f bb s) /\
    EL h (trace_block P D fuel C f bb s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_block P D fuel C f bb s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest /\
      (!id' g j u. ~MEM ((p,d,id'),g,j,u) rest)) /\
  (!P D fuel C f s. !h p d id fn i t.
    EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                     g.fn_blocks) C.ctx_functions /\
    EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions)) f.fn_blocks /\
    h < LENGTH (trace_blocks P D fuel C f s) /\
    EL h (trace_blocks P D fuel C f s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_blocks P D fuel C f s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest /\
      (!id' g j u. ~MEM ((p,d,id'),g,j,u) rest))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume focus_row_continuations[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[cj 1 trace_defs] >>
  Cases_on `decode_invoke inst` >> gvs[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> gvs[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> gvs[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> gvs[] >>
  first_x_assum irule >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[venomInstTheory.lookup_function_MEM]
QED

Resume focus_row_continuations[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 2 trace_defs)]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME head` >>
  drule_then assume_tac trace_block_visit >>
  Cases_on `h`
  >- (gvs[] >> qexists_tac `bb` >> qexists_tac `[]` >> simp[]) >>
  rename1 `SUC k` >>
  gvs[] >>
  Cases_on `k < LENGTH (trace_step P D fuel C f head s)`
  >- (gvs[EL_APPEND] >>
      qpat_x_assum `!h p d id fn i t. _` drule_all >> strip_tac >>
      qexists_tac `bt` >>
      qmatch_goalsub_abbrev_tac `DROP k (ts ++ tail)` >>
      qexists_tac `rest ++ tail` >>
      simp[DROP_APPEND1, Abbr `ts`, APPEND_ASSOC, MEM_APPEND] >>
      Cases_on `step_inst fuel C head s` >> gvs[Abbr `tail`] >>
      rename1 `step_inst _ _ _ _ = OK post` >>
      Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
      irule focus_child_row_excludes >>
      `ALL_DISTINCT (MAP (\x. x.inst_id) (DROP s.vs_inst_idx bb.bb_instructions))` by
        (rewrite_tac[MAP_DROP] >> irule ALL_DISTINCT_DROP >> simp[]) >>
      qpat_assum `get_instruction bb s.vs_inst_idx = SOME head`
        (mp_tac o MATCH_MP dftGasFromListTraceNamesTheory.remaining_ids_step) >>
      strip_tac >> gvs[] >>
      `MEM ((p,d,i.inst_id),fn,i,t) (trace_step P D fuel C f head s)` by
        (simp[MEM_EL] >> qexists `k` >> simp[]) >>
      goal_assum $ drule_at Any >> simp[]) >>
  Cases_on `step_inst fuel C head s` >> gvs[] >>
  rename1 `step_inst _ _ _ _ = OK post` >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  drule_all venomInstProofsTheory.step_preserves_control_flow >> strip_tac >>
  gvs[EL_APPEND, DROP_APPEND2] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume focus_row_continuations[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- gvs[] >>
  rename1 `trace_blocks P D (SUC n) C f s` >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 3 trace_defs)]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[] >>
  qpat_x_assum `h < _` mp_tac >>
  once_rewrite_tac[cj 3 trace_defs] >> simp[] >> strip_tac >>
  rename1 `eval_phis _ _ = OK sp` >>
  drule_all trace_blocks_enter >> disch_then assume_tac >> gvs[] >>
  `sp.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions)` by
    (gvs[EVERY_MEM] >> metis_tac[venomExecProofsTheory.lookup_block_MEM]) >>
  qmatch_asmsub_abbrev_tac `exec_block n C bb start` >>
  Cases_on `h < LENGTH (trace_block P (SUC D) n C f bb start)`
  >- (gvs[EL_APPEND, Abbr `start`] >>
      qpat_x_assum `!h p d id fn i t. _` drule_all >> strip_tac >>
      qexists_tac `bt` >>
      qmatch_goalsub_abbrev_tac `DROP h (ts ++ tail)` >>
      qexists_tac `rest ++ tail` >>
      simp[DROP_APPEND1, Abbr `ts`, APPEND_ASSOC, ADD_CLAUSES, MEM_APPEND] >>
      Cases_on `exec_block n C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
      gvs[Abbr `tail`] >>
      rename1 `exec_block _ _ _ _ = OK post` >>
      Cases_on `post.vs_halted` >> gvs[] >>
      metis_tac[focus_later_row_excludes, MEM_EL]) >>
  Cases_on `exec_block n C bb start` >> gvs[] >>
  rename1 `exec_block _ _ _ _ = OK post` >>
  Cases_on `post.vs_halted` >> gvs[] >>
  gvs[EL_APPEND, DROP_APPEND2, ADD_CLAUSES] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Finalise focus_row_continuations[local]

Theorem focus_row_continuation[local]:
  !P D fuel C f s h p d id fn i t.
    EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                     g.fn_blocks) C.ctx_functions /\
    EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions)) f.fn_blocks /\
    h < LENGTH (trace_blocks P D fuel C f s) /\
    EL h (trace_blocks P D fuel C f s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_blocks P D fuel C f s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest /\
      (!id' g j u. ~MEM ((p,d,id'),g,j,u) rest)
Proof
  ACCEPT_TAC (cj 3 focus_row_continuations)
QED

(* The later indexed visit belongs to the direct row (not the residual
   continuation), even when child traces intervene between the two visits. *)
Theorem focus_row_visit_between[local]:
  EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                    g.fn_blocks) C.ctx_functions /\
  EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions)) root.fn_blocks /\
  R = trace_blocks [] 0 N C root entry /\
  m <= n /\ n < LENGTH R /\
  EL m R = ((a,e,first.inst_id),tf,first,s) /\
  EL n R = ((a,e,i.inst_id),tf,i,t) ==>
  ?bt rest pre post.
    lookup_block s.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt s.vs_inst_idx = SOME first /\
    R = TAKE m R ++ trace_block a e (N-e) C tf bt s ++ rest /\
    DROP s.vs_inst_idx bt.bb_instructions = pre ++ i::post /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH pre /\
    EVERY (\x. ~is_terminator x.inst_opcode) pre /\
    FOLDR (dftIndexedExec$dft_exec_cons (N-e) C) OK pre s = OK t
Proof
  strip_tac >>
  `?bt rest. lookup_block s.vs_current_bb tf.fn_blocks = SOME bt /\
     get_instruction bt s.vs_inst_idx = SOME first /\ e <= N /\
     DROP m R = trace_block a e (N-e) C tf bt s ++ rest /\
     (!id' g j u. ~MEM ((a,e,id'),g,j,u) rest)` by
    (qpat_x_assum `EL n R = _` kall_tac >> gvs[] >>
     `m < LENGTH (trace_blocks [] 0 N C root entry)` by decide_tac >>
     drule_all focus_row_continuation >> simp[]) >>
  `MEM ((a,e,i.inst_id),tf,i,t) (DROP m R)` by
    (qpat_x_assum `DROP m R = _` kall_tac >>
     qpat_x_assum `R = trace_blocks _ _ _ _ _ _` kall_tac >>
     `n-m + m = n` by decide_tac >>
     simp[MEM_EL] >> qexists `n-m` >>
     conj_tac >- (simp[LENGTH_DROP] >> decide_tac) >>
     dep_rewrite.DEP_REWRITE_TAC[listTheory.EL_DROP] >> simp[]) >>
  `MEM ((a,e,i.inst_id),tf,i,t) (trace_block a e (N-e) C tf bt s)` by
    (qpat_assum `DROP m R = _` (fs o single) >> metis_tac[MEM_APPEND]) >>
  `?pre post. DROP s.vs_inst_idx bt.bb_instructions = pre ++ i::post /\
     t.vs_inst_idx = s.vs_inst_idx + LENGTH pre /\
     EVERY (\x. ~is_terminator x.inst_opcode) pre /\
     FOLDR (dftIndexedExec$dft_exec_cons (N-e) C) OK pre s = OK t` by
    metis_tac[focus_row_visit_inverse] >>
  qexistsl [`bt`,`rest`,`pre`,`post`] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  qpat_x_assum `DROP m R = _` (rewrite_tac o single o GSYM) >> simp[]
QED

Theorem focus_history_target_slice[local]:
  o1_ctx_shape C /\ MEM root C.ctx_functions /\
  R = trace_blocks [] 0 N C root entry /\
  h < j /\ hbe <= j /\ j < LENGTH R /\
  EL hbe R = ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
  EL h R = ((a,e,inst.inst_id),tf,inst,t) /\
  lookup_block be.vs_current_bb tf.fn_blocks = SOME bt /\
  bt.bb_instructions = ps ++ ys /\
  be.vs_inst_idx = LENGTH ps /\ LENGTH ps <= t.vs_inst_idx /\
  k = t.vs_inst_idx - LENGTH ps /\ obs = trace_gas (TAKE j R) ==>
  hbe <= h /\
  (?post. ys = TAKE k ys ++ inst::post) /\
  EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k ys) /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C) OK (TAKE k ys) be = OK t /\
  EVERY (\kw. MEM kw obs)
    (trace_gas (trace_block a e (N-e) C tf
      (bt with bb_instructions := TAKE (LENGTH ps + LENGTH (TAKE k ys)) bt.bb_instructions) be))
Proof
  strip_tac >>
  `EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                    g.fn_blocks) C.ctx_functions` by
    (drule dftContractGasTheory.o1_ctx_shape_wf_functions >>
     simp[EVERY_MEM] >> metis_tac[dftCorrectnessTheory.bb_inst_ids_distinct]) >>
  `EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions)) root.fn_blocks` by
    (qpat_assum `EVERY _ C.ctx_functions`
      (qspec_then `root` mp_tac o PURE_ONCE_REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
  `ALL_DISTINCT (MAP FST R)` by
    (simp[] >> irule (cj 3 dftGasFromListTraceNamesTheory.trace_names_distinct) >> simp[]) >>
  `hbe <= h` by
    (spose_not_then assume_tac >>
     `h <= hbe /\ hbe < LENGTH R` by decide_tac >>
     drule_all focus_row_visit_between >> strip_tac >>
     qpat_x_assum `R = TAKE h R ++ _ ++ _` kall_tac >>
     `LENGTH pre = 0` by decide_tac >>
     `pre = []` by metis_tac[LENGTH_NIL] >>
     `HD ys = inst` by
       (qpat_x_assum `DROP t.vs_inst_idx _ = _` mp_tac >>
        qpat_x_assum `get_instruction _ t.vs_inst_idx = _` mp_tac >>
        simp[get_instruction_def, DROP_CONS_EL]) >>
     qpat_x_assum `R = trace_blocks _ _ _ _ _ _` kall_tac >>
     `h < LENGTH R` by decide_tac >>
     `EL hbe (MAP FST R) = EL h (MAP FST R)` by simp[EL_MAP] >>
     qspecl_then [`MAP FST R`,`hbe`,`h`] mp_tac ALL_DISTINCT_EL_IMP >> simp[]) >>
  `h < LENGTH R` by decide_tac >>
  drule_all focus_row_visit_between >> strip_tac >>
  `bt' = bt` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `bt' = bt` SUBST_ALL_TAC >>
  qpat_x_assum `R = trace_blocks _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `R = TAKE hbe R ++ _ ++ _` (mk_asm "embed") >>
  `ys = pre ++ inst::post /\ k = LENGTH pre` by
    (qpat_x_assum `DROP be.vs_inst_idx _ = _` mp_tac >>
     simp[DROP_LENGTH_APPEND]) >>
  `TAKE k ys = pre` by simp[TAKE_LENGTH_APPEND] >>
  simp[] >>
  `hbe <= LENGTH R /\ be.vs_inst_idx + LENGTH pre < LENGTH bt.bb_instructions` by
    (simp[] >> decide_tac) >>
  `get_instruction bt t.vs_inst_idx = SOME inst` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `TAKE h R = TAKE hbe R ++ trace_block a e (N-e) C tf
      (bt with bb_instructions := TAKE (be.vs_inst_idx + LENGTH pre) bt.bb_instructions) be` by
    (irule dftPacketNativeSliceTheory.native_trace_embedded_prefix_cut >>
     simp[DROP_LENGTH_APPEND, TAKE_LENGTH_APPEND] >>
     asm_x "embed" (fn th => metis_tac[th])) >>
  qmatch_asmsub_abbrev_tac `TAKE h R = TAKE hbe R ++ target` >>
  `TAKE j R = TAKE h R ++ TAKE (j-h) (DROP h R)` by
    simp[rich_listTheory.take_drop_partition] >>
  simp[Abbr `target`, EVERY_MEM, dftGasFromListReadingsTheory.trace_gas_append, MEM_APPEND]
QED

Theorem focus_fmp_inst_no_dload[local]:
  i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES /\
  fmp_lower_inst infos ctx runner s i = SOME (out,t) ==>
  EVERY (\j. j.inst_opcode <> DLOAD /\ j.inst_opcode <> DLOADBYTES) out
Proof
  rpt strip_tac >> gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def]
QED

Theorem focus_fmp_function_no_dload[local]:
  fmp_lower_function ctx s f = SOME (g,t) /\
  EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) (fn_insts g)
Proof
  strip_tac >> drule fmpStepPredicateTransportTheory.fmp_lower_function_every >>
  disch_then (qspec_then `\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES` mp_tac) >>
  simp[] >> impl_tac
  >- (conj_tac
      >- (rpt strip_tac >>
          `i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES` by
            fs[EVERY_MEM] >>
          drule_all focus_fmp_inst_no_dload >> simp[]) >>
      conj_tac
      >- (rpt strip_tac >>
          drule_at (Pat `fmp_emit_restores _ _ _ = _`) fmpStepRewriteTheory.fmp_emit_restores_every >>
          disch_then irule >> simp[mk_inst_def]) >>
      rpt strip_tac >>
      gvs[fmp_make_root_layout_def, AllCaseEqs(), mk_inst_def,
          set_param_index_def, OPTION_TO_LIST_def] >>
      drule fmpStepRestrictionClosureTheory.split_fmp_entry_retpc_restrictions >>
      rw[EVERY_MEM] >> gvs[OPTION_TO_LIST_def]) >>
  simp[]
QED

(* Each of these rows preserves exclusion of the already lowered opcodes. *)
Theorem focus_step_no_dload[local]:
  (pass = CFP_Simple VP_ConcretizeMemLoc \/ pass = CFP_Simple VP_FmpLowering \/
   pass = CFP_Simple VP_MakeSSA \/ pass = CFP_Simple VP_SimplifyCFG \/
   pass = CFP_Simple VP_SingleUseExpansion) /\
  fn_pass_step rp pass observed s f out /\
  EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
    (fn_insts out.fpo_function)
Proof
  disch_then (CONJUNCTS_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC) >> gvs[]
  >- (drule_at (Pat `fn_pass_step _ _ _ _ _ _`)
        (Q.INST [`P` |-> `\op. op <> DLOAD /\ op <> DLOADBYTES`]
          concretize_fn_pass_opcode_property) >> fs[EVERY_MEM])
  >- (drule fmp_fn_pass_step_result >> strip_tac >>
      drule_all focus_fmp_function_no_dload >> simp[])
  >- (drule make_ssa_pass_step_replay >> strip_tac >>
      drule_at (Pat `make_ssa_current_fn _ _ = _`)
        (Q.INST [`P` |-> `\op. op <> DLOAD /\ op <> DLOADBYTES`]
          make_ssa_current_fn_opcode_property) >> simp[])
  >- (drule simplify_cfg_pass_step_function >> disch_then SUBST1_TAC >>
      simp[simplify_cfg_fn_def] >>
      mp_tac (Q.INST [`R` |-> `\op. op <> DLOAD /\ op <> DLOADBYTES`]
        simplify_cfg_fn_with_labels_opcodes) >> simp[]) >>
  drule sue_pass_step_replay >> strip_tac >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  drule_all sue_expand_function_supply_label_projection >>
  strip_tac >> fs[] >> metis_tac[]
QED

Theorem focus_raw_reachable_members[local]:
  !V C f i u. raw_reachable V C f i u ==>
    MEM f C.ctx_functions /\ MEM i (fn_insts f)
Proof
  ho_match_mp_tac raw_reachable_ind >>
  rpt strip_tac >> metis_tac[lookup_function_MEM, active_inst_mem_fn_insts]
QED

Theorem focus_opt_c7_section_from_image[local]:
  (!k. k < 9 ==> ctx_pass_stage rp (EL k o1_fn_passes) (o1_walk_view rp k)
      (stage k) (stage (SUC k))) /\
  (!g j. MEM g (stage 2).ctx_functions /\ MEM j (fn_insts g) ==>
    j.inst_opcode <> DLOAD /\ j.inst_opcode <> DLOADBYTES) /\
  raw_reachable V (stage 7) sf i u ==>
  inst_dload_in_section i u
Proof
  strip_tac >>
  `!k. 2 <= k /\ k <= 7 ==>
    EVERY (\f. EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
      (fn_insts f)) (stage k).ctx_functions` by
    (Induct >- simp[] >> strip_tac >>
     Cases_on `k < 2`
     >- (`SUC k = 2` by decide_tac >> gvs[EVERY_MEM] >> metis_tac[]) >>
     `ctx_pass_stage rp (EL k o1_fn_passes) (o1_walk_view rp k)
          (stage k) (stage (SUC k))` by (first_x_assum irule >> decide_tac) >>
     `2 <= k /\ k <= 7` by decide_tac >>
     drule_at (Pat `ctx_pass_stage _ _ _ _ _`)
       (Q.INST [`P` |-> `\f. EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
                               (fn_insts f)`] ctx_pass_stage_every) >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     drule_at (Pat `fn_pass_step _ _ _ _ _ _`) focus_step_no_dload >> simp[] >>
     `k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6` by decide_tac >>
     pop_assum strip_assume_tac >> simp[o1_fn_passes_def]) >>
  drule focus_raw_reachable_members >> strip_tac >>
  irule inst_dload_in_section_other >>
  qpat_x_assum `!k. 2 <= k /\ k <= 7 ==> _` (qspec_then `7` mp_tac) >>
  simp[EVERY_MEM] >> metis_tac[]
QED

(* Reflect the selected scalar read after the paired history has been supplied. *)
Theorem focus_concretize_cut_read[local]:
  o1_ctx_shape C /\ o1_ctx_shape Ct /\ o1_ptr_safe_upto D lo n C V /\
  (?R lp positions.
    ptr_stage_placements Ct positions /\
    !ht at. ptr_chrono_history V Ct ht at ==> gas_cut n V at.po_state ==>
      (?h a done tokens registry births PT TG saved entries H calls ws.
        ptr_paired_prefix R lp positions lo V C Ct
          h a ht at done tokens registry births PT TG saved entries H calls ws /\
        EVERY (\i. ~in_revert_forward (EL i h).po_fn (EL i h).po_state) done /\
        a.po_inst.inst_opcode <> NOP /\
        at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst) \/
      (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
        revert_forward_pair bb i j /\
        i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j)) /\
  raw_reachable V Ct ft j t /\ gas_cut n V t /\
  j.inst_opcode = CODECOPY /\ j.inst_operands = [dst; Var x; sz] /\
  code_end_var ft x /\ eval_operand (Var x) t = SOME w ==>
  ?f i s. raw_reachable V C f i s /\ gas_cut n V s /\
    i.inst_opcode = CODECOPY /\ i.inst_operands = [dst; Var x; sz] /\
    code_end_var f x /\ eval_operand (Var x) s = SOME w /\
    s.vs_labels = t.vs_labels
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_discipline_upto lo n C V` by fs[o1_ptr_safe_upto_def] >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  drule ptr_reachable_has_chrono_history >> strip_tac >>
  qpat_x_assum `!ht at. ptr_chrono_history _ _ ht at ==> _` drule >>
  (impl_tac >- simp[ptr_observe_def]) >> strip_tac
  >- suspend "paired" >>
  suspend "corridor"
QED

Resume focus_concretize_cut_read[paired]:
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `gas_cut n V (ptr_observe stk PG G tn ft j t).po_state` by simp[ptr_observe_def] >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `MEM a.po_fn C.ctx_functions` by metis_tac[ptr_frame_context_membership] >>
  `MEM a.po_inst (fn_insts a.po_fn)` by metis_tac[ptr_frame_operand_instructions] >>
  `fn_shape_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `a.po_inst.inst_opcode <> ALLOCA` by
    (strip_tac >> gvs[concretize_inst_with_positions_def, AllCaseEqs(),
                     mk_nop_inst_def, mk_assign_inst_def, ptr_observe_def]) >>
  `j = a.po_inst` by fs[ptr_observe_def, concretize_positions_unchanged] >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn ft
     a.po_state t /\ a.po_state.vs_labels = t.vs_labels` by
    (fs[ptr_paired_sample_def, ptr_observe_def] >> metis_tac[ptr_history_content_labels]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule_all ptr_source_ownership_erases_upto >> strip_tac >>
  drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (fs[ptr_static_support_def, SUBSET_DEF, FLOOKUP_DEF] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `opaque_use_ok a.po_fn /\ fn_ptr_ok P a.po_fn` by fs[fn_shape_ok_def, EVERY_MEM] >>
  `eval_operand (Var x) a.po_state = eval_operand (Var x) t` by
    (irule code_end_concretize_read_value >> metis_tac[]) >>
  `code_end_var (concretize_function_with_positions (lp a.po_fn) a.po_fn) x` by
    (fs[ptr_paired_code_def, ptr_observe_def] >> metis_tac[code_end_var_same_blocks]) >>
  `code_end_var a.po_fn x` by metis_tac[concretize_code_end_backward] >>
  qexistsl [`a.po_fn`, `a.po_inst`, `a.po_state`] >> simp[] >>
  metis_tac[ld_frame_reachable_raw]
QED

Resume focus_concretize_cut_read[corridor]:
  fs[ptr_observe_def] >>
  drule raw_reachable_active >>
  rewrite_tac[active_inst_def] >>
  disch_then (qx_choose_then `active_bb` strip_assume_tac) >>
  `MEM ft Ct.ctx_functions` by metis_tac[ptr_frame_context_membership] >>
  `ALL_DISTINCT (fn_labels ft)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `lookup_block t.vs_current_bb ft.fn_blocks = SOME active_bb` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `active_bb = bb` by metis_tac[optionTheory.SOME_11] >>
  `get_instruction bb t.vs_inst_idx = SOME j` by fs[get_instruction_def] >>
  drule_all ld_revert_pair_suffix_opcode >> simp[]
QED

Finalise focus_concretize_cut_read

(* Scratch statement for elaboration and independent review.
   Use the actual stopped six tables and their C8 chronology. Split a
   compatible raw at Mcut, with the unread suffix and [0w] as tail.
   The bounded lowered-memory conclusion is separate from the original
   conditional static-memory clause. *)
Theorem focus_source_cut_provider:
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
       label_flow_ok unit.cu_context /\
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
    vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
    codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0 with
        as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
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
      EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  0 < N /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  (stage 7).ctx_entry = SOME nm /\ (stage 8).ctx_entry = SOME nm /\
  lookup_function nm (stage 7).ctx_functions = SOME root_sf /\
  lookup_function nm (stage 8).ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl7 /\ fn_entry_label root_tf = SOME lbl7 /\
  joint_initial vs0 (stage 8) q80 /\ joint_initial vs0 (stage 9) q90 /\
  joint_trace vs0 (stage 8) q80 evs8 qs8 (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8) /\
  joint_trace vs0 (stage 9) q90 evs9 qs9 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  cfg_norm_joint_cursors (stage 8) (stage 9) (schedules,current,saved) (JointConfig stk8 PG8 G8 tn8 fn8
    inst8 s8 oms8 om8 hs8 hist8) (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog asm_fuel (entry_asm_state vs0 es0) = AsmOK ast /\
  (fin = K SOME ==> normal_frame_plan rpolicy out.po_unit cpl prog (vs0 with
    <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp; vs_return_pc_token := 0w;
    vs_inst_idx := 0|>) es0 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) asm_fuel (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy out.po_unit cpl prog vs0 es0
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss) /\
  dft_focus_packet_rel N (stage 7) (stage 8) root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8
      om8 hs8 hist8) raw_slots sites unused /\
  j = LENGTH evs8 /\ LENGTH evs8 <= LENGTH evs9 /\ LENGTH (TAKE j (dftGasFromListTraceDefs$trace_blocks []
    0 N (stage 8) root_tf root_entry)) = j /\
  j < LENGTH (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) /\ obs =
    dftGasFromListTraceDefs$trace_gas (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8)
    root_tf root_entry)) /\
  EL j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) =
    ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) ==>
  (?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest.
      FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (p,d) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      get_instruction bt s8.vs_inst_idx = SOME inst8 /\
      ((inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
        inst8.inst_opcode = INVOKE \/ is_terminator inst8.inst_opcode) ==>
      ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
        src_inst = EL (LENGTH z)
          (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        ((IS_SOME body_entry /\ LENGTH ps <= s8.vs_inst_idx /\
          s8.vs_inst_idx - LENGTH ps < LENGTH rho /\
          q = EL (s8.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
          EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
          (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
          EL q xs = inst8 /\
          z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
         (p = p /\ d = d /\ s8 = s8 /\ body_entry = NONE /\
          s8.vs_inst_idx < LENGTH ps /\ q = 0 /\
          z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s8.vs_inst_idx ps))) /\
        MAP (\(ai,ds,ei,qi,zi). ai) cuts =
          REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then
              ai = p /\ ei = d /\ qi = q /\ zi = z
            else
              ?cid h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) =
                  SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                  MEM r done_at_call)) /\
            EL i levels =
              (sfi,
               MAP (\f.
                 (FST (THE (FLOOKUP blocks (ai,f))),f,
                  DROP (phi_prefix_length
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                 [(bbi,ei,zi)],
               if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
        Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
        raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
          ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
        LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
        (!F gs tail.
          N <= F /\
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          (?extra. Ecut = FST (rooted_eval F (stage 7) levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u =>
              FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after.
                dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                  before ++ [((p,d,(EL (LENGTH z)
                    (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions)).inst_id),sf,
                    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions),u)] ++ after /\
                dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail') =
                  (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==>
                u with vs_gas_readings := s8.vs_gas_readings = s8) /\
              (p = p /\ d = d /\ IS_SOME body_entry /\
               inv_memory_observation inst8.inst_opcode /\ EL q xs = inst8 ==>
                (!op. MEM op inst8.inst_operands ==>
                  eval_operand op u = eval_operand op s8) /\
                u.vs_initial_fmp = s8.vs_initial_fmp)
          | stopped =>
              run_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gas_events_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) =
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)))) /\
        (!F gs tail n u.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
          LENGTH Mcut < n /\
          mem_inv (\ctx src_fn src_inst src_state.
            gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
              static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
            (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
          rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
            (Ecut,OK u) ==>
          static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
          (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
          (inv_memory_observation src_inst.inst_opcode ==>
            (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op s8) /\
            u.vs_initial_fmp = s8.vs_initial_fmp)) /\
  (!raw F u.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>

    N <= F /\ LENGTH Mcut < (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) /\
    rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP
      (LENGTH Mcut) raw ++ [0w])) = (Ecut,OK u) ==>
    raw_reachable (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw
      ++ [0w])) (stage 7) sf src_inst u /\ gas_cut (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++
      [0w]))) (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw ++
      [0w])) u /\
    lowered_mem_fact cpl.cp_max_static_eom (stage 7) sf src_inst u /\
    u.vs_gas_readings = (DROP (LENGTH Mcut) raw ++ [0w]) /\
    (fin = asm_opt_finalizer ==>
      inst_dload_in_section src_inst u /\
      code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) (stage 7)) /\
    (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
    (inv_memory_observation inst8.inst_opcode ==>
      (!op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8) /\
      u.vs_initial_fmp = s8.vs_initial_fmp)))) /\
  (!h. h < j ==>
    ?a e tf inst visit_state stk PG G tn oms om hs hist.
      EL h (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry)) =
        ((a,e,inst.inst_id),tf,inst,visit_state) /\
      EL h (q80::qs8) = JointConfig stk PG G tn tf inst visit_state oms om hs hist /\
      ?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
        body_entry count front closed brest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
        get_instruction bt visit_state.vs_inst_idx = SOME inst /\
        ((inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
          inst.inst_opcode = INVOKE) /\ ~in_revert_forward tf visit_state ==>
          ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
            src_inst = EL (LENGTH z)
              (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
            ((IS_SOME body_entry /\ LENGTH ps <= visit_state.vs_inst_idx /\
              visit_state.vs_inst_idx - LENGTH ps < LENGTH rho /\
              q = EL (visit_state.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
              (a <> p \/ e <> d \/ visit_state <> s8 \/
                (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
                 (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)))) /\
              (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
                 inst.inst_opcode = INVOKE ==> EL q xs = inst) /\
              z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
             (a = p /\ e = d /\ visit_state = s8 /\ body_entry = NONE /\
              visit_state.vs_inst_idx < LENGTH ps /\ q = 0 /\
              z = DROP (phi_prefix_length bb.bb_instructions) (TAKE visit_state.vs_inst_idx ps))) /\
            MAP (\(ai,ds,ei,qi,zi). ai) cuts =
              REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
            LENGTH cuts = LENGTH levels /\
            (!i ai ds ei qi zi.
              i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
              ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
                ini hi bei counti fronti closedi resti later.
                FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
                FLOOKUP blocks (ai,ei) =
                  SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
                orderi = ds ++ ei::later /\
                (if SUC i = LENGTH cuts then
                  ai = a /\ ei = e /\ qi = q /\ zi = z
                else
                  ?cid h b0 done_at_call child_entry ret.
                    EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                    FLOOKUP calls (ai,ei,cid) =
                      SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                    qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                    zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                    EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                    (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                      MEM r done_at_call)) /\
                EL i levels =
                  (sfi,
                   MAP (\f.
                     (FST (THE (FLOOKUP blocks (ai,f))),f,
                      DROP (phi_prefix_length
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                     [(bbi,ei,zi)],
                   if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
            Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
            Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
            Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
            raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
              ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
            LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
            (!F gs tail.
              N <= F /\
              LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
              (?extra. Ecut = FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
              (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
                OK u =>
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
                  u.vs_gas_readings = tail /\
                  (?before after.
                    dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                      (root_entry with vs_gas_readings := gs ++ tail) =
                      before ++ [((a,e,(EL (LENGTH z)
                        (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions)).inst_id),sf,
                        EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions),u)] ++ after /\
                    dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
                  (!tail'. rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail') =
                      (Ecut,OK (u with vs_gas_readings := tail'))) /\
                  (body_entry = NONE ==>
                    u with vs_gas_readings := visit_state.vs_gas_readings = visit_state) /\
                  (a = p /\ e = d /\ IS_SOME body_entry /\
                   inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
                    (!op. MEM op inst.inst_operands ==>
                      eval_operand op u = eval_operand op visit_state) /\
                    u.vs_initial_fmp = visit_state.vs_initial_fmp)
              | stopped =>
                  run_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
                  gas_events_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) =
                      FST (rooted_eval F (stage 7) levels
                        (root_entry with vs_gas_readings := gs ++ tail)))) /\
            (!F gs tail n u.
              N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
              LENGTH Mcut < n /\
              mem_inv (\ctx src_fn src_inst src_state.
                gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
                  static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
                (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
              rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
                (Ecut,OK u) ==>
              static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
              ~in_revert_forward sf u /\
              (inv_memory_observation src_inst.inst_opcode ==>
                (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op visit_state) /\
                u.vs_initial_fmp = visit_state.vs_initial_fmp)) /\
  (!raw F u.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>

    N <= F /\ LENGTH Mcut < (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) /\
    rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP
      (LENGTH Mcut) raw ++ [0w])) = (Ecut,OK u) ==>
    raw_reachable (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw
      ++ [0w])) (stage 7) sf src_inst u /\ gas_cut (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++
      [0w]))) (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw ++
      [0w])) u /\
    lowered_mem_fact cpl.cp_max_static_eom (stage 7) sf src_inst u /\
    u.vs_gas_readings = (DROP (LENGTH Mcut) raw ++ [0w]) /\
    (fin = asm_opt_finalizer ==>
      inst_dload_in_section src_inst u /\
      code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) (stage 7)) /\
    (~in_revert_forward tf visit_state ==> ~in_revert_forward sf u) /\
    (inv_memory_observation inst.inst_opcode ==>
      (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op visit_state) /\
      u.vs_initial_fmp = visit_state.vs_initial_fmp)))) /\
  (!raw.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
    ?f7 f extra.
      MAP project (gas_events_blocks f unit.cu_context entryfn (vs0 with <|vs_gas_readings := raw ++ [0w];
        vs_fmp := fmp; vs_initial_fmp := fmp; vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) =
        markf (raw ++ [0w]) ++ extra /\
      (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) <= LENGTH (gas_events_blocks f7 (stage
        7) root_sf (root_entry with vs_gas_readings := raw ++ [0w])) /\
      TAKE (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) (gas_events_blocks f7 (stage 7)
        root_sf (root_entry with vs_gas_readings := raw ++ [0w])) =
        TAKE (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) (gas_events_blocks f
          unit.cu_context entryfn (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp;
          vs_initial_fmp := fmp; vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)))
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> strip_tac >>
  sg `mem_inv (\ctx fn inst u.
         gas_cut (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail)))
           (root_entry with vs_gas_readings := gs ++ tail) u ==>
         lowered_mem_fact cpl.cp_max_static_eom ctx fn inst u)
       (stage 7) (root_entry with vs_gas_readings := gs ++ tail)`
  >- (irule (DISCH_ALL (CONJUNCT1 (UNDISCH
          (CONV_RULE (DEPTH_CONV BETA_CONV) (PURE_REWRITE_RULE [LET_THM] focus_source_stages_cut))))) >> cheat) >>
  cheat
QED

Theorem focus_history_source_slice[local]:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ks
    q z cuts levels Mcut F gs tail events u.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  q < LENGTH xs /\ z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cuts = LENGTH levels /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then
        ai = a /\ ei = e /\ qi = q /\ zi = z
       else
        ?cid call_h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
      EL i levels =
        (sfi, MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
          [(bbi,ei,zi)], if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
  N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
    (events,OK u) ==>
  ALL_DISTINCT (MAP FST obs) /\
  ALL_DISTINCT (FLAT (TAKE q ks)) /\
  LIST_REL (\key slot. slot = ALOOKUP obs key) (FLAT (TAKE q ks)) (FLAT (TAKE q ms)) /\
  ?Mbefore gpre vals.
    Mcut = Mbefore ++ FLAT (TAKE q ms) /\ gs = gpre ++ vals /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mbefore gpre /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q ms)) vals /\
    FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
      (be with vs_gas_readings := vals ++ tail) = OK u /\
    trace_gas (trace_block a e (F-e) C7 sf
        (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
        (be with vs_gas_readings := vals ++ tail)) = ZIP (FLAT (TAKE q ks),vals)
Proof
  rpt gen_tac >> strip_tac >>
  `!q. LIST_REL (\key slot. slot = ALOOKUP obs key)
        (FLAT (TAKE q ks)) (FLAT (TAKE q ms))` by
    (drule_all dft_packet_retained_prefix_lookup >> simp[]) >>
  `ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT (FLAT ks)` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     conj_tac >-
       (qpat_assum `(j,obs) = _` mp_tac >>
        qpat_assum `ALL_DISTINCT (MAP FST _)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
     qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
        FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\ FLOOKUP es_tab (a,e) = _ /\
        FLOOKUP ks_tab (a,e) = _ ==> _` (mp_tac o cj 6) >>
     `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
       (qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
        qpat_assum `FLOOKUP blocks (a,e) = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        Cases_on `FLOOKUP es_tab (a,e)` >> gvs[FLOOKUP_DEF]) >>
     disch_then (drule_all_then ACCEPT_TAC)) >>
  `ALL_DISTINCT (FLAT (TAKE q ks))` by
    (`ALL_DISTINCT (FLAT (TAKE q ks) ++ FLAT (DROP q ks))` by
       (pure_rewrite_tac[GSYM FLAT_APPEND, TAKE_DROP] >> first_assum ACCEPT_TAC) >>
     pop_assum (mp_tac o REWRITE_RULE [ALL_DISTINCT_APPEND]) >> simp[NoAsms]) >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
  `FDOM ms_tab = FDOM ms_tab` by REFL_TAC >>
  `!key old new. FLOOKUP ms_tab key = SOME old /\ FLOOKUP ms_tab key = SOME new ==>
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) old new` by
    (POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[LIST_REL_refl]) >>
  drule dft_packet_cut_row_trace >>
  disch_then (qspec_then `ms_tab` (drule_all_then strip_assume_tac)) >>
  rename1 `gs = gpre ++ FLAT vals` >>
  qpat_assum `FLOOKUP ms_tab (a,e) = SOME ms` (fn m =>
    qpat_assum `FLOOKUP ks_tab (a,e) = SOME ks` (fn k =>
      qpat_assum `FLOOKUP acts a = SOME _` (fn act =>
        RULE_ASSUM_TAC (REWRITE_RULE [m,k,act,optionTheory.THE_DEF,pairTheory.FST])))) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
     (FLAT (TAKE q ms)) (FLAT vals)` by
    (qpat_assum `LIST_REL _ Mcut gs` mp_tac >>
     qpat_assum `Mcut = Mbefore ++ _` (fn m =>
       qpat_assum `gs = gpre ++ FLAT vals`
         (fn g => rewrite_tac[m,g])) >>
     qpat_assum `LIST_REL _ Mbefore gpre` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     rpt strip_tac >> drule_all LIST_REL_APPEND_IMP >> simp[]) >>
  qexistsl [`Mbefore`,`gpre`,`FLAT vals`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
