Theory o1CreateSizeTransport
Ancestors
  o1ContractCfgNormJointCursors o1ContractCfgNormCursors
  o1ContractCfgNorm cfgNormSupplySim cfgNormDefs
  jointRequestCut frameRawProjection frameJointTrace frameJointTransition
  dftContractGas dftGasInvMemoryObservation dftGasInvCrossingProbe
  requestCutDftStaticRequest
  dftGasOracleDefs dftRunRel dftDefs gasOracleReplay o1PassContract
  requestCutStageFacts o1DftStageSsa unitTransformDefs venomPassSchedule
  o1CodeEndSueTransport o1ContractSue o1PassLift singleUseExpansionSupplySim
  o1CodeEndCfgRounds o1CodeEndCfgCollapse o1ContractSimplifyCfg
  simplifyCfgStaticInterface simplifyCfgShapeCore simplifyCfgDefs
  simplifyCfgProof simplifyCfgControl simplifyCfgSimTools
  requestCutLowerDloadCursor lowerDloadOwnership lowerDloadReachableFloor
  lowerDloadExternalInputs lowerDloadPtrRawReachable ptrDiscipline
  requestCutFmpCursor fmpStageCoverage fmpStageCoverBack fmpStageOpSimMemCalls
  fmpStageRel
  requestCutConcretizeCursor requestCutConcretizeOperands
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrSourceOwnership concretizePtrParamSupport
  concretizePtrParamShape concretizePtrOperationalOpcodes concretizePtrOpaqueRetpc
  concretizePtrValueTransport concretizePtrRequestHistory
  lowerDloadDefs unitMemInv finite_map pred_set
  o1ContractSimplifyCfgSrcFrame codegenRel stateFrame
  concretizePtrCoverageStaticMemReachability concretizePtrChronologicalDemand
  lowerDloadNormalData passSimulationDefs
  requestCutOracleClip o1StaticPipelineCompose o1PipelineCompose o1ContractMakeSsaSrc
  requestCutOracleFrames loweringBudgetFrameOracleTransport extCallOracle
  o1DretDesugarContract o1ComposeSupport o1ContractTheorems
  ctxLookupAgree fcgPruning venomPipelineRunner
  o1StaticPipelineCorrect o1PipelineCorrect
  o1LabelFlowStaticContracts o1FnScheduleDecompHelpers
  requestCutClippedSafety o1SafeUpto e2eRequestCutDefs
  ctxLookupAgreeHelpers
  contextCodegenRel opcodeClass venomExecSemantics venomExecProofs
  unitShapeDefs lowerDloadPtrStatic venomInst venomState venomWf venomWfProps
  irSupply list pair

(* Match the visited instructions before executing the final instruction. *)
Triviality cfg_norm_joint_chain_back:
  !es q9 qs r9 q8 current saved.
    joint_chain C9 q9 es qs r9 /\
    joint_config_reachable v C8 q8 /\
    cfg_norm_joint_cursors C8 C9 (schedules,current,saved) q8 q9 ==>
    ?r8 current' saved'.
      joint_config_reachable v C8 r8 /\
      cfg_norm_joint_cursors C8 C9 (schedules,current',saved') r8 r9
Proof
  Induct
  >- (rpt gen_tac >> Cases_on `qs` >> simp[joint_chain_def] >> metis_tac[]) >>
  rpt gen_tac >> namedCases_on `qs` ["","qnext rest"] >>
  simp[joint_chain_def] >> strip_tac >> Cases_on `q8` >> Cases_on `q9` >>
  drule_all_then (strip_assume_tac o cj 4) cfg_norm_joint_cursors_step >>
  `joint_config_reachable v C8 q8'` by metis_tac[joint_transition_reachable] >>
  first_x_assum (qspecl_then [`qnext`,`rest`,`r9`,`q8'`,`current'`,`saved'`] mp_tac) >>
  simp[]
QED

Triviality cfg_norm_reached_cursor:
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) view C8 C9 /\
  o1_ctx_shape C8 /\ EVERY wf_ssa C8.ctx_functions /\
  v.vs_vars = FEMPTY /\ ~v.vs_halted /\
  joint_initial v C8 start8 /\ joint_config_reachable v C9 q9 ==>
  ?q8 schedules current saved.
    joint_config_reachable v C8 q8 /\
    cfg_norm_joint_cursors C8 C9 (schedules,current,saved) q8 q9
Proof
  strip_tac >> drule_all cfg_norm_joint_cursors_initial >>
  disch_then (qx_choose_then `schedules` assume_tac) >>
  qpat_x_assum `joint_config_reachable v C9 q9`
    (strip_assume_tac o REWRITE_RULE [joint_reachable_iff_trace]) >>
  fs[joint_trace_def] >>
  qpat_x_assum `!vs0 q8 q9. _`
    (qspecl_then [`v`,`start8`,`q0`] mp_tac) >> simp[] >> strip_tac >>
  `joint_config_reachable v C8 start8` by metis_tac[joint_initial_reachable] >>
  drule_all cfg_norm_joint_chain_back >> metis_tac[]
QED

Triviality cfg_norm_cursors_retained_operands:
  !C rounds cells. cfg_norm_cursors C rounds cells ==>
    ~MEM (FST (FST (LAST cells))).inst_opcode [PHI; ASSIGN; JMP; JNZ] ==>
    FST (FST (HD cells)) = FST (FST (LAST cells)) /\
    (!op. MEM op (FST (FST (LAST cells))).inst_operands ==>
      eval_operand op (SND (FST (HD cells))) =
      eval_operand op (SND (FST (LAST cells))))
Proof
  ho_match_mp_tac cfg_norm_cursors_ind >> simp[LAST_CONS_cond] >>
  rpt conj_tac >> rpt (gen_tac ORELSE disch_then strip_assume_tac) >> gvs[]
  >- (rename1 `supply_state_agree fn a v` >>
      `EVERY label_positions_ok bb.bb_instructions` by
        (gvs[fn_insts_def, EVERY_MEM] >> metis_tac[MEM_fn_insts_blocks]) >>
      `(EL v.vs_inst_idx (supply_block_image pred target split repls bb).bb_instructions).inst_opcode =
       (EL v.vs_inst_idx bb.bb_instructions).inst_opcode` by
        metis_tac[supply_block_image_index] >>
      `EL v.vs_inst_idx (supply_block_image pred target split repls bb).bb_instructions =
       EL v.vs_inst_idx bb.bb_instructions` by
        (irule supply_block_image_index_unchanged >>
         simp[EVERY_EL] >> metis_tac[EVERY_EL]) >>
      `MEM (EL v.vs_inst_idx bb.bb_instructions) (fn_insts fn)` by
        metis_tac[fn_insts_def, MEM_fn_insts_blocks, MEM_EL] >>
      conj_tac >- metis_tac[] >>
      gen_tac >> strip_tac >>
      `eval_operand op a = eval_operand op v` by
        (irule supply_eval_operand_agree >> qexists_tac `fn` >>
         simp[] >> metis_tac[fn_ir_vars_operand]) >>
      metis_tac[]) >>
  `ir_supply_inst_ok s /\ ir_supply_covers_fn s fn` by
    gvs[supply_norm_inv_def] >>
  drule_all supply_split_index_shape >> simp[] >> metis_tac[]
QED

Triviality cfg_norm_joint_retained_operands:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  ~MEM inst9.inst_opcode [PHI; ASSIGN; JMP; JNZ] ==>
  inst8 = inst9 /\
  (!op. MEM op inst9.inst_operands ==> eval_operand op s8 = eval_operand op s9)
Proof
  strip_tac >> PairCases_on `current` >> gvs[cfg_norm_joint_cursors_def] >>
  drule cfg_norm_cursors_retained_operands >> simp[]
QED

Triviality cfg_norm_reached_retained_operands:
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) view C8 C9 /\
  o1_ctx_shape C8 /\ EVERY wf_ssa C8.ctx_functions /\
  EVERY wf_function C8.ctx_functions /\ v.vs_vars = FEMPTY /\ ~v.vs_halted /\
  joint_initial v C8 start8 /\ raw_reachable v C9 fn9 inst s9 /\
  ~MEM inst.inst_opcode [PHI; ASSIGN; JMP; JNZ] ==>
  ?fn8 s8. raw_reachable v C8 fn8 inst s8 /\
    (!op. MEM op inst.inst_operands ==> eval_operand op s8 = eval_operand op s9)
Proof
  strip_tac >> drule raw_reachable_joint_trace >> strip_tac >>
  drule joint_trace_reachable >> strip_tac >>
  drule_all cfg_norm_reached_cursor >>
  disch_then (qx_choose_then `q8` strip_assume_tac) >>
  Cases_on `q8` >> drule_all cfg_norm_joint_retained_operands >>
  strip_tac >> gvs[] >> metis_tac[joint_config_raw]
QED

(* The native replay may reorder the GAS filling, but keeps the evaluated
   operands at an external instruction that has been reached. *)
Triviality dft_reached_external_operands:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  C8.ctx_entry = C7.ctx_entry /\ o1_ctx_shape C7 /\
  ctx_labels_bound C7 v.vs_labels /\ o1_initial_state_ok v /\
  v.vs_fmp = v.vs_initial_fmp /\ code_layout_valid v /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)) C7.ctx_functions /\
  raw_reachable v C8 fn8 inst s8 /\ is_ext_call_op inst.inst_opcode ==>
  ?rds fn7 s7. raw_reachable (v with vs_gas_readings := rds) C7 fn7 inst s7 /\
    (!op. MEM op inst.inst_operands ==> eval_operand op s7 = eval_operand op s8)
Proof
  strip_tac >>
  mp_tac (Q.INST [`C` |-> `C7`, `C'` |-> `C8`, `s` |-> `v`]
    dft_ctx_gas_replay_witness) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `orc` (qx_choose_then `rds` strip_assume_tac)) >>
  qpat_x_assum `!fn inst t. raw_reachable v C8 fn inst t ==> _` drule >>
  disch_then (qx_choose_then `p` (qx_choose_then `d` assume_tac)) >>
  `?fn7 s7. ev_reachable orc v C7 p d fn7 inst s7 /\
     (!op. MEM op inst.inst_operands ==> eval_operand op s7 = eval_operand op s8)` by
    (Cases_on `v.vs_call_ctx.cc_static`
     >- (drule_all request_cut_dft_static_external_fields >> simp[] >> metis_tac[]) >>
     `o1_run_state_ok v` by simp[o1_run_state_ok_def] >>
     `inv_memory_observation inst.inst_opcode` by
       (Cases_on `inst.inst_opcode` >>
        gvs[is_ext_call_op_def, inv_memory_observation_def]) >>
     drule_all inv_reachable_memory_observation_oracle >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!p d fn inst t. ev_reachable orc v C7 p d fn inst t ==> _`
    (qspecl_then [`p`, `d`, `fn7`, `inst`, `s7`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`rds`, `fn7`, `s7 with vs_gas_readings := ws`] >> simp[]
QED

Triviality o1_shaped_joint_initial:
  o1_ctx_shape C ==> ?q. joint_initial v C q
Proof
  simp[o1_ctx_shape_def, ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def] >>
  strip_tac >>
  Cases_on `lookup_function entry_name C.ctx_functions`
  >- metis_tac[lookup_function_not_mem] >>
  rename1 `lookup_function entry_name C.ctx_functions = SOME fn` >>
  `o1_fn_shape C fn` by (fs[EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  Cases_on `fn.fn_blocks` >> gvs[o1_fn_shape_def, wf_function_def, fn_has_entry_def] >>
  rename1 `fn.fn_blocks = bb::bbs` >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> gvs[first_block_no_phi_def] >>
  qabbrev_tac `s = v with <|vs_prev_bb := NONE; vs_current_bb := bb.bb_label;
                            vs_inst_idx := 0|>` >>
  `enters_block fn s s` by
    (simp[enters_block_def, Abbr `s`] >> qexists_tac `bb` >>
     simp[lookup_block_def, FIND_thm, eval_phis_def, phi_prefix_length_def]) >>
  `active_inst fn (HD bb.bb_instructions) s` by
    (simp[active_inst_def, Abbr `s`] >> qexists_tac `bb` >> simp[]) >>
  `fn_entry_label fn = SOME bb.bb_label` by simp[fn_entry_label_def, entry_block_def] >>
  simp[Once joint_initial_cases] >> metis_tac[]
QED

Triviality o1_post_dft_reached_external_operands:
  (!i. i < 9 ==> ctx_pass_stage rp (EL i o1_fn_passes) (o1_walk_view rp i)
    (stage i) (stage (SUC i))) /\
  (!i. i <= 9 ==> o1_ctx_shape (stage i) /\
    EVERY (o1_fn_row i) (stage i).ctx_functions) /\
  o1_initial_state_ok v /\ v.vs_fmp = v.vs_initial_fmp /\ code_layout_valid v /\
  raw_reachable v (stage 9) fn9 inst s9 /\ is_ext_call_op inst.inst_opcode ==>
  ?rds fn7 s7. raw_reachable (v with vs_gas_readings := rds) (stage 7) fn7 inst s7 /\
    (!op. MEM op inst.inst_operands ==> eval_operand op s7 = eval_operand op s9)
Proof
  strip_tac >> drule_all request_cut_stage_facts >> strip_tac >>
  `o1_ctx_shape (stage 7)` by simp[] >>
  `EVERY wf_ssa (stage 8).ctx_functions` by
    (irule dft_stage_wf_ssa >> metis_tac[DECIDE ``7 <= 9``]) >>
  `?q8. joint_initial v (stage 8) q8` by
    metis_tac[o1_shaped_joint_initial, DECIDE ``8 <= 9``] >>
  `v.vs_vars = FEMPTY /\ ~v.vs_halted` by fs[o1_initial_state_ok_def] >>
  `~MEM inst.inst_opcode [PHI; ASSIGN; JMP; JNZ]` by
    (Cases_on `inst.inst_opcode` >> gvs[is_ext_call_op_def]) >>
  `?fn8 s8. raw_reachable v (stage 8) fn8 inst s8 /\
    (!op. MEM op inst.inst_operands ==> eval_operand op s8 = eval_operand op s9)` by
    (irule cfg_norm_reached_retained_operands >>
     metis_tac[DECIDE ``8 <= 9``]) >>
  drule_all dft_reached_external_operands >> simp[] >>
  metis_tac[]
QED

Triviality sue_frame_reached_operands:
  sue_frame_align C C' f g entry j t /\ j.inst_opcode <> ASSIGN ==>
  ?i s. frame_reach C f entry i s /\ i.inst_opcode = j.inst_opcode /\
    s.vs_outcomes = t.vs_outcomes /\
    LIST_REL (\op op'. eval_operand op s = eval_operand op' t)
      i.inst_operands j.inst_operands
Proof
  rewrite_tac[sue_frame_align_def] >> strip_tac >>
  `MEM bb f.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `!x. MEM (Var x) (EL i bb.bb_instructions).inst_operands ==>
     MEM x (fn_ir_vars f)` by metis_tac[sue_original_operand_covered, MEM_EL] >>
  drule_all sue_segments_supply_index_ready >> strip_tac >>
  drule_all sue_segment_operand_eval >> strip_tac >> gvs[] >>
  `u.vs_outcomes = t.vs_outcomes` by
    fs[sue_state_rel_def, execution_frame_def, venom_state_component_equality] >>
  qexistsl [`EL u.vs_inst_idx bb.bb_instructions`, `u`] >> simp[] >>
  irule LIST_REL_mono >>
  goal_assum (drule_at Any) >> simp[]
QED

Triviality sue_reached_operands:
  ctx_pass_stage rp (CFP_Simple VP_SingleUseExpansion) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY (o1_fn_row 6) C.ctx_functions /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  raw_reachable vs C' f j t /\ j.inst_opcode <> ASSIGN ==>
  ?g i s. raw_reachable vs C g i s /\ i.inst_opcode = j.inst_opcode /\
    s.vs_outcomes = t.vs_outcomes /\
    LIST_REL (\op op'. eval_operand op s = eval_operand op' t)
      i.inst_operands j.inst_operands
Proof
  strip_tac >>
  `ctx_bisim C C'` by metis_tac[sue_stage_bisim] >>
  drule_all sue_code_end_stage_pairs >>
  disch_then (qspec_then `vs.vs_labels` assume_tac) >>
  `frame_origin vs C C' f j t` by
    (irule frame_sim_raw_origins >> simp[] >>
     fs[ctx_pass_stage_def] >>
     irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `frame_origin _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[frame_origin_def] >>
  disch_then (qx_choosel_then [`g`, `entry`] strip_assume_tac) >>
  rename1 `lookup_function source_name C.ctx_functions = SOME g` >>
  drule list_rel_lookup_function >> simp[] >>
  disch_then (qspec_then `source_name` mp_tac) >> simp[optionTheory.OPTREL_def] >> strip_tac >>
  `sue_frame_align C C' g f entry j t` by
    (irule sue_frame_reach_align >> metis_tac[]) >>
  drule_all sue_frame_reached_operands >>
  disch_then (qx_choosel_then [`i`, `s`] strip_assume_tac) >>
  qexistsl [`g`, `i`, `s`] >> simp[] >>
  metis_tac[frame_reach_raw_reachable]
QED

Triviality simplify_cfg_reached_external_operands:
  ctx_pass_stage rp (CFP_Simple VP_SimplifyCFG) view C CT /\
  o1_ctx_shape C /\ EVERY simplify_cfg_fn_ok C.ctx_functions /\
  v.vs_vars = FEMPTY /\ ~v.vs_halted /\
  raw_reachable v CT g i t /\ is_ext_call_op i.inst_opcode ==>
  ?f s. raw_reachable v C f i s /\ s.vs_outcomes = t.vs_outcomes /\
    !op. eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule simplify_cfg_stage_functions >> strip_tac >>
  `ctx_bisim C CT` by metis_tac[simplify_cfg_stage_bisim] >>
  `LIST_REL (\f g. g.fn_name = f.fn_name /\ fn_entry_label g = fn_entry_label f /\
    frame_sim v.vs_labels C CT f g /\ g = simplify_cfg_fn f /\ scfg_static f)
    C.ctx_functions CT.ctx_functions` by
    (simp[LIST_REL_MAP2, LIST_REL_EL_EQN] >> rpt gen_tac >> strip_tac >> simp[EL_MAP] >>
     `MEM (EL n C.ctx_functions) C.ctx_functions` by metis_tac[MEM_EL] >>
     `o1_fn_shape C (EL n C.ctx_functions) /\ simplify_cfg_fn_ok (EL n C.ctx_functions)` by
       fs[o1_ctx_shape_def, EVERY_MEM] >>
     `fn_bisim (EL n C.ctx_functions) (simplify_cfg_fn (EL n C.ctx_functions))` by
       (irule simplify_cfg_fn_correct >> fs[o1_fn_shape_def]) >>
     fs[fn_bisim_def] >> conj_tac
     >- (irule simplify_cfg_frame_sim >> fs[o1_fn_shape_def]) >>
     fs[scfg_static_def, o1_fn_shape_def] >> metis_tac[fn_shape_ok_scfg_shape]) >>
  `frame_origin v C CT g i t` by
    (irule frame_sim_raw_origins >> fs[ctx_pass_stage_def] >>
     qpat_x_assum `LIST_REL (\fn fn'. ?observed s out. _) _ _` kall_tac >>
     qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     qpat_x_assum `CT.ctx_functions = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  qpat_x_assum `frame_origin _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[frame_origin_def] >>
  disch_then (qx_choosel_then [`f`, `s0`] strip_assume_tac) >>
  `g = simplify_cfg_fn f /\ scfg_static f` by
    (drule list_rel_lookup_function >> simp[] >>
     disch_then (qspec_then `nm` mp_tac) >> simp[optionTheory.OPTREL_def] >>
     strip_tac >> gvs[]) >>
  `frame_reach C g s0 i t` by metis_tac[frame_reach_ctx_bisim] >>
  `i.inst_opcode <> ASSIGN /\ i.inst_opcode <> PHI /\ ~is_terminator i.inst_opcode` by
    (Cases_on `i.inst_opcode` >> gvs[is_ext_call_op_def, is_terminator_def]) >>
  `?s. frame_reach C f s0 i s /\ scfg_payload s t` by
    (irule o1_code_end_iter_reach_back >>
     conj_tac >- metis_tac[scfg_collapse_frame_observation_joint] >>
     asm_rewrite_tac[] >> qexists_tac `LENGTH f.fn_blocks` >>
     qpat_x_assum `g = simplify_cfg_fn f` SUBST_ALL_TAC >>
     fs[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def]) >>
  `s.vs_outcomes = t.vs_outcomes` by
    (qpat_assum `scfg_payload s t`
       (mp_tac o Q.AP_TERM `\u. u.vs_outcomes` o REWRITE_RULE [scfg_payload_def, scfg_ctrl_def]) >>
     simp[]) >>
  qexistsl [`f`, `s`] >> simp[] >>
  metis_tac[frame_reach_raw_reachable, scfg_payload_operand]
QED

Triviality create_size_operand_scalar:
  ((i.inst_opcode = CREATE /\ i.inst_operands = [value;off;sz]) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [value;off;sz;salt])) ==>
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  MEM sz i.inst_operands /\
  (FILTER ($= sz) i.inst_operands = [sz] ==>
    !ops. mem_read_ops i = SOME ops \/ mem_write_ops i = SOME ops ==>
      ops.iao_ofst <> sz)
Proof
  strip_tac
  >- (mp_tac (Q.INST [`scalars` |-> `[value;sz]`, `v` |-> `value`] ld_external_layout_scalars) >>
      simp[MEM] >> disch_then (qspec_then `sz` mp_tac) >> simp[]) >>
  mp_tac (Q.INST [`scalars` |-> `[value;sz;salt]`, `v` |-> `value`] ld_external_layout_scalars) >>
  simp[MEM] >> disch_then (qspec_then `sz` mp_tac) >> simp[]
QED

Triviality lower_dload_reached_create_size:
  ctx_pass_stage rp (CFP_Simple VP_LowerDload) view C CT /\
  dead_wf D /\ o1_ctx_shape C /\ o1_initial_state_ok v /\
  v.vs_fmp = v.vs_initial_fmp /\ code_layout_valid v /\
  o1_src_inv D C v /\ callee_first names C.ctx_functions /\
  raw_reachable v CT fnT i t /\ t.vs_outcomes = [] /\
  ((i.inst_opcode = CREATE /\ i.inst_operands = [value;off;sz]) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [value;off;sz;salt])) ==>
  ?fn s. raw_reachable v C fn i s /\ s.vs_outcomes = t.vs_outcomes /\
    eval_operand sz s = eval_operand sz t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule create_size_operand_scalar >> strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  drule_all request_cut_lower_dload_cursor >> strip_tac >>
  `ptr_discipline v.vs_alloca_next C v` by
    metis_tac[ld_o1_src_inv_frontier_discipline_static] >>
  `?P. !g. MEM g C.ctx_functions ==> fn_ptr_ok P g` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all ld_normal_external_operands >> strip_tac >>
  `eval_operand sz s = eval_operand sz t` by metis_tac[] >>
  `EVERY wf_function C.ctx_functions` by fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  metis_tac[ld_annotated_erasure, frameRawProjectionTheory.frame_reachable_raw]
QED

Triviality fmp_reached_create_size:
  fmp_stage_ctx rp D C CT v vt fmp eom /\ o1_ctx_shape CT /\
  raw_reachable vt CT fnT i t /\
  ((i.inst_opcode = CREATE /\ i.inst_operands = [value;off;sz]) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [value;off;sz;salt])) /\
  eval_operand sz t = SOME nbytes ==>
  ?fn s. raw_reachable v C fn i s /\ s.vs_outcomes = t.vs_outcomes /\
    eval_operand sz s = SOME nbytes
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule create_size_operand_scalar >> strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  rename1 `frame_reachable vt CT stk PG G tn fnT i t` >>
  `ALL_DISTINCT (fn_labels fnT)` by
    (drule scfg_frame_reachable_functions >>
     fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `active_inst fnT i t` by metis_tac[scfg_frame_reachable_active] >>
  qpat_assum `fmp_stage_ctx rp D C CT v vt fmp eom`
    (mp_tac o MATCH_MP fmp_stage_coverage) >>
  disch_then (qspecl_then [`stk`,`PG`,`G`,`tn`,`fnT`,`i`,`t`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  drule_all request_cut_fmp_cursor >>
  disch_then (qx_choosel_then [`stkS`,`PGS`,`GS`,`tnS`,`fn`,`s`,`sm`,`lo`,`ts`,`restored`]
    strip_assume_tac) >>
  `s.vs_labels = t.vs_labels` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `i.inst_opcode <> PHI` by fs[MEM] >>
  `?w. eval_operand sz s = SOME w` by
    (Cases_on `sz` >> simp[eval_operand_def]
     >- (drule_all fmp_stage_src_defined >>
         simp[optionTheory.IS_SOME_EXISTS]) >>
     qexists_tac `nbytes` >>
     qpat_assum `eval_operand (Label _) t = SOME nbytes`
       (ACCEPT_TAC o REWRITE_RULE [eval_operand_def])) >>
  drule_all fmp_mem_external_scalar >> strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    fs[fmp_stage_ctx_def, o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  qexistsl [`fn`, `s`] >> simp[] >>
  conj_tac
  >- metis_tac[frameRawProjectionTheory.frame_reachable_raw] >>
  metis_tac[optionTheory.SOME_11]
QED

Triviality concretize_reached_create_size:
  ctx_pass_stage rp (CFP_Simple VP_ConcretizeMemLoc) (o1_walk_view rp 2) C CT /\
  o1_ctx_shape C /\ o1_ctx_shape CT /\ o1_initial_state_ok v /\
  v.vs_fmp = v.vs_initial_fmp /\ code_layout_valid v /\
  o1_inv D 2 C v /\ max_live_eom CT = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n v.vs_initial_fmp) /\
  raw_reachable v CT fnT i t /\
  ((i.inst_opcode = CREATE /\ i.inst_operands = [value;off;sz]) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [value;off;sz;salt])) ==>
  ?fn s. raw_reachable v C fn i s /\ s.vs_outcomes = t.vs_outcomes /\
    eval_operand sz s = eval_operand sz t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule create_size_operand_scalar >> strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  rename1 `frame_reachable v CT stk PG G un fnT i t` >>
  `EVERY all_reachable C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
   ctx_inst_ids_distinct C` by
    fs[o1_inv_def, o1_ctx_shape_def, make_ssa_input_ok_def, EVERY_MEM] >>
  qpat_x_assum `o1_inv D 2 C v` (strip_assume_tac o SIMP_RULE (srw_ss()) [o1_inv_def,o1_src_inv_def]) >>
  `ctx_has_dalloca C ==> !n. max_live_eom CT = SOME n ==> n <= w2n v.vs_initial_fmp` by
    metis_tac[optionTheory.SOME_11] >>
  rename1 `fixed_region_reserved lo C` >>
  mp_tac (Q.INST [`C` |-> `C`, `CT` |-> `CT`, `rpolicy` |-> `rp`, `clip0` |-> `v`,
    `i` |-> `i`, `gn` |-> `fnT`, `t` |-> `t`, `stk` |-> `stk`, `PG` |-> `PG`,
    `G` |-> `G`, `un` |-> `un`, `lo` |-> `lo`, `eom` |-> `eom`]
    request_cut_concretize_cursor) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`R`,`lp`,`positions`,`h`,`a`,`ht`,`done`,
    `tokens`,`registry`,`births`,`PT`,`TG`,`saved`,`entries`,`H`,`calls`,`ws`]
      strip_assume_tac) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    simp[o1_ctx_shape_instructions_wf] >>
  drule_all ptr_source_ownership_prov_erases >> strip_tac >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (fs[ptr_static_support_def, SUBSET_DEF, FLOOKUP_DEF] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `MEM i (fn_insts a.po_fn)` by
    metis_tac[ptr_frame_operand_instructions] >>
  `o1_fn_shape C a.po_fn` by (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `opaque_use_ok a.po_fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  `ptr_use_ok P (fn_pv P a.po_fn) i` by (fs[fn_ptr_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `taint_ok a.po_fn a.po_taint i a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) i.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> fs[MEM]) >>
  `a.po_state.vs_labels = t.vs_labels` by metis_tac[ptr_history_content_labels] >>
  mp_tac (Q.INST [`tn` |-> `a.po_taint`, `fn` |-> `a.po_fn`, `gn` |-> `fnT`,
    `s` |-> `a.po_state`, `t` |-> `t`, `dyn` |-> `dyn_floor C v`,
    `G` |-> `a.po_prov`, `pv` |-> `fn_pv P a.po_fn`, `i` |-> `i`]
    request_cut_concretize_operands) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `eval_operand sz a.po_state = eval_operand sz t` by metis_tac[] >>
  `EVERY wf_function C.ctx_functions` by fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  metis_tac[frameRawProjectionTheory.frame_reachable_raw]
QED

Triviality create_size_list_rel:
  i.inst_opcode = j.inst_opcode /\
  LIST_REL (\op op'. eval_operand op s = eval_operand op' t)
    i.inst_operands j.inst_operands /\
  ((j.inst_opcode = CREATE /\ j.inst_operands = [value;off;sz]) \/
   (j.inst_opcode = CREATE2 /\ j.inst_operands = [value;off;sz;salt])) /\
  eval_operand sz t = SOME nbytes ==>
  ?v p z sl.
    ((i.inst_opcode = CREATE /\ i.inst_operands = [v;p;z]) \/
     (i.inst_opcode = CREATE2 /\ i.inst_operands = [v;p;z;sl])) /\
    eval_operand z s = SOME nbytes
Proof
  strip_tac >> gvs[LIST_REL_CONS2] >> metis_tac[]
QED

Triviality make_ssa_reached_create_size:
  ctx_pass_stage rp (CFP_Simple VP_MakeSSA) view C CT /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  v.vs_vars = FEMPTY /\ ~v.vs_halted /\
  raw_reachable v CT g j t /\
  ((j.inst_opcode = CREATE /\ j.inst_operands = [value;off;sz]) \/
   (j.inst_opcode = CREATE2 /\ j.inst_operands = [value;off;sz;salt])) /\
  eval_operand sz t = SOME nbytes ==>
  ?f i s a p z sl. raw_reachable v C f i s /\ s.vs_outcomes = t.vs_outcomes /\
    ((i.inst_opcode = CREATE /\ i.inst_operands = [a;p;z]) \/
     (i.inst_opcode = CREATE2 /\ i.inst_operands = [a;p;z;sl])) /\
    eval_operand z s = SOME nbytes
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `j.inst_opcode <> ASSIGN /\ j.inst_opcode <> NOP` by
    (qpat_assum `(j.inst_opcode = CREATE /\ _) \/ _` strip_assume_tac >> simp[]) >>
  drule_all make_ssa_src_stage_observation >>
  disch_then (qx_choosel_then [`f`,`i`,`s`] strip_assume_tac) >>
  `s.vs_outcomes = t.vs_outcomes` by
    fs[execution_frame_def, venom_state_component_equality] >>
  `LIST_REL (\op op'. eval_operand op s = eval_operand op' t)
      i.inst_operands j.inst_operands` by
    (irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all create_size_list_rel >> metis_tac[]
QED

(* The prefix to the visit is unchanged by discarding the unread suffix
   of the outcome list. Reattach the suffix after transporting the visit. *)
Triviality o1_pre_dft_reached_create_size:
  (!j. j < LENGTH o1_fn_passes ==>
    ctx_pass_stage rp (EL j o1_fn_passes) (o1_walk_view rp j) (stage j) (stage (SUC j))) /\
  (!j. j <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage j)) /\
  (!j. j <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row j) (stage j).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok v7 /\ v7.vs_fmp = v7.vs_initial_fmp /\
  code_layout_valid v7 /\ fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) v7 /\
  vi = (v7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  short = TAKE (LENGTH t.vs_requests - LENGTH v7.vs_requests) v7.vs_outcomes /\
  o1_inv D 0 (stage 0) (vi with vs_outcomes := short) /\
  raw_reachable v7 (stage 7) fn j t /\
  ((j.inst_opcode = CREATE /\ j.inst_operands = [value;off;sz]) \/
   (j.inst_opcode = CREATE2 /\ j.inst_operands = [value;off;sz;salt])) /\
  eval_operand sz t = SOME nbytes ==>
  ?f i s a p z sl. raw_reachable vi (stage 0) f i s /\
    ((i.inst_opcode = CREATE /\ i.inst_operands = [a;p;z]) \/
     (i.inst_opcode = CREATE2 /\ i.inst_operands = [a;p;z;sl])) /\
    eval_operand z s = SOME nbytes
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `clip7 = v7 with vs_outcomes := short` >>
  qabbrev_tac `clip = vi with vs_outcomes := short` >>
  `!suffix. (clip with vs_outcomes := clip.vs_outcomes ++ suffix) =
    (vi with vs_outcomes := short ++ suffix)` by simp[Abbr `clip`] >>
  `clip = (clip7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>)` by
    simp[Abbr `clip`, Abbr `clip7`] >>
  `code_layout_valid clip7` by
    (qpat_assum `code_layout_valid v7` (mp_tac o REWRITE_RULE [code_layout_valid_def]) >>
     simp[Abbr `clip7`, code_layout_valid_def]) >>
  `code_layout_valid clip` by
    (qpat_assum `code_layout_valid clip7` (mp_tac o REWRITE_RULE [code_layout_valid_def]) >>
     simp[code_layout_valid_def]) >>
  `o1_initial_state_ok clip7 /\ clip7.vs_fmp = clip7.vs_initial_fmp /\
   fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) clip7` by
    fs[Abbr `clip7`, o1_initial_state_ok_def, fmp_variant_room_def] >>
  `o1_initial_state_ok clip /\ clip.vs_fmp = clip.vs_initial_fmp /\
   clip.vs_vars = FEMPTY /\ ~clip.vs_halted /\
   clip7.vs_vars = FEMPTY /\ ~clip7.vs_halted` by
    fs[o1_initial_state_ok_def] >>
  mp_tac (Q.INST [`rpolicy` |-> `rp`, `stage` |-> `stage`, `D` |-> `D`,
    `vs_out` |-> `clip7`, `rds` |-> `clip7.vs_gas_readings`, `fmp` |-> `fmp`]
    o1_walk_pre_dft_stage_facts_static_abort_fixed) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  PURE_REWRITE_TAC[LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  `(clip7 with vs_gas_readings := clip7.vs_gas_readings) = clip7` by
    simp[venom_state_component_equality] >>
  qpat_assum `(clip7 with vs_gas_readings := _) = clip7`
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
       [`3`,`4`,`6`]) >>
  `EVERY make_ssa_input_ok (stage 0).ctx_functions /\
   EVERY make_ssa_input_ok (stage 4).ctx_functions /\
   EVERY simplify_cfg_fn_ok (stage 5).ctx_functions /\
   EVERY wf_ssa (stage 6).ctx_functions` by
    (fs[o1_inv_def, o1_ssa_inv_def, o1_walk_src_inv_def] >>
     fs[o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[simplify_cfg_fn_ok_ssa, o1_fn_shape_def]) >>
  `!rq rqs. record_request rq rqs = rqs ++ [rq]` by simp[record_request_def] >>
  `EVERY wf_function (stage 7).ctx_functions` by metis_tac[o1_ctx_shape_wf_functions] >>
  `?s7. raw_reachable clip7 (stage 7) fn j s7 /\
        s7.vs_outcomes = [] /\ eval_operand sz s7 = SOME nbytes` by
    (mp_tac (Q.INST [`k` |-> `LENGTH t.vs_requests`, `vs` |-> `v7`,
       `C` |-> `stage 7`, `fn` |-> `fn`, `i` |-> `j`, `s` |-> `t`]
       raw_reachable_outcome_clip) >>
     (impl_tac >- simp[]) >>
     simp[Abbr `clip7`] >> disch_tac >>
     qexists_tac `t with vs_outcomes := []` >>
     simp[operand_outcomes_update]) >>
  `j.inst_opcode <> ASSIGN` by
    (qpat_assum `(j.inst_opcode = CREATE /\ _) \/ _` strip_assume_tac >> simp[]) >>
  drule_all (Q.INST [`C` |-> `stage 6`, `C'` |-> `stage 7`]
    sue_reached_operands) >>
  disch_then (qx_choosel_then [`f6`,`i6`,`s6`] strip_assume_tac) >>
  drule_all create_size_list_rel >>
  disch_then (qx_choosel_then [`a6`,`p6`,`z6`,`sl6`]
    (map_every assume_tac o CONJUNCTS)) >>
  `is_ext_call_op i6.inst_opcode` by
    (qpat_assum `(i6.inst_opcode = CREATE /\ _) \/ _` strip_assume_tac >>
     simp[is_ext_call_op_def]) >>
  drule_all (Q.INST [`C` |-> `stage 5`, `CT` |-> `stage 6`]
    simplify_cfg_reached_external_operands) >>
  disch_then (qx_choosel_then [`f5`,`s5`] strip_assume_tac) >>
  `eval_operand z6 s5 = SOME nbytes` by simp[] >>
  drule_all (Q.INST [`C` |-> `stage 4`, `CT` |-> `stage 5`]
    make_ssa_reached_create_size) >>
  disch_then (qx_choosel_then [`f4`,`i4`,`s4`,`a4`,`p4`,`z4`,`sl4`]
    (map_every assume_tac o CONJUNCTS)) >>
  `?eom. max_live_eom (stage 3) = SOME eom` by fs[o1_inv_def,o1_static_inv_def] >>
  qpat_assum `!j. 3 + j <= LENGTH o1_fn_passes ==> _`
    (fn th => map_every
      (fn n => assume_tac (SIMP_RULE (srw_ss()) [o1_fn_passes_def] (Q.SPEC n th)))
      [`1`, `6`]) >>
  `fmp_variant_room (SOME fmp) (stage 4) clip7 /\ eom <= w2n clip.vs_initial_fmp` by
    (fs[fmp_variant_room_def, o1_fn_passes_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `fmp_stage_ctx rp D (stage 3) (stage 4) clip clip7 fmp eom` by
    simp[fmp_stage_ctx_def, o1_pre_def] >>
  drule_all fmp_reached_create_size >>
  disch_then (qx_choosel_then [`f3`,`s3`] strip_assume_tac) >>
  `ctx_has_dalloca (stage 2) ==> eom <= w2n clip.vs_initial_fmp` by simp[] >>
  drule_all (Q.INST [`C` |-> `stage 2`, `CT` |-> `stage 3`]
    concretize_reached_create_size) >>
  disch_then (qx_choosel_then [`f2`,`s2`] strip_assume_tac) >>
  qpat_assum `o1_inv D 1 (stage 1) clip`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [o1_inv_def]) >>
  `s2.vs_outcomes = []` by fs[] >>
  drule_all (Q.INST [`C` |-> `stage 1`, `CT` |-> `stage 2`]
    lower_dload_reached_create_size) >>
  disch_then (qx_choosel_then [`f1`,`s1`] strip_assume_tac) >>
  `eval_operand z4 s1 = SOME nbytes` by fs[] >>
  drule_all (Q.INST [`C` |-> `stage 0`, `CT` |-> `stage 1`]
    make_ssa_reached_create_size) >>
  disch_then (qx_choosel_then [`f0`,`i0`,`s0`,`a0`,`p0`,`z0`,`sl0`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `raw_reachable clip (stage 0) f0 i0 s0`
    (strip_assume_tac o MATCH_MP (SPEC_ALL ptr_raw_reachable_frame)) >>
  qabbrev_tac `tail = DROP (LENGTH t.vs_requests - LENGTH v7.vs_requests) vi.vs_outcomes` >>
  `vi.vs_outcomes = v7.vs_outcomes` by simp[] >>
  `short ++ tail = vi.vs_outcomes` by simp[Abbr `tail`, TAKE_DROP] >>
  `clip with vs_outcomes := clip.vs_outcomes ++ tail = vi` by
    (qpat_assum `!suffix. (clip with vs_outcomes := _) = (vi with vs_outcomes := _)`
       (qspec_then `tail` mp_tac) >>
     simp[venom_state_component_equality]) >>
  drule (Q.INST [`tail` |-> `tail`] (SPEC_ALL frame_reachable_outcome_suffix)) >>
  simp[] >> strip_tac >>
  qexistsl [`f0`,`i0`,`s0 with vs_outcomes := s0.vs_outcomes ++ tail`,`a0`,`p0`,`z0`,`sl0`] >>
  simp[operand_outcomes_update] >>
  metis_tac[frameRawProjectionTheory.frame_reachable_raw, o1_ctx_shape_wf_functions]
QED

Triviality o1_pre_walk_reached_external_operands:
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit sup0 =
    SOME (pre,sup') /\ o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok sup0 /\
  EVERY fn_defs_reach_uses unit.cu_context.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) unit.cu_context.ctx_functions /\
  pre.cu_context.ctx_entry = SOME entry /\
  C0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  raw_reachable vs C0 g i t /\ is_ext_call_op i.inst_opcode ==>
  ?f s. raw_reachable vs unit.cu_context f i s /\
    !op. eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule o1_pre_walk_runs >> strip_tac >>
  `o1_step_contract rp (CFP_Simple VP_SimplifyCFG)` by
    simp[o1_contract_simplify_cfg_pre_walk] >>
  drule_all mapped_pass_stage >> strip_tac >>
  `o1_step_contract rp (CFP_Simple VP_DretDesugar)` by
    simp[o1_contract_dret_desugar_pre_walk] >>
  drule unit_labels_wf_namespace >> strip_tac >>
  `ctx_pass_stage rp (CFP_Simple VP_DretDesugar) any_view mid.cu_context pre.cu_context` by
    metis_tac[mapped_pass_stage] >>
  `pre.cu_context = mid.cu_context` by metis_tac[dret_desugar_stage_identity] >>
  `ctx_wf pre.cu_context /\ wf_invoke_targets pre.cu_context` by
    metis_tac[o1_ctx_shape_wf] >>
  `ctx_agree (fcg_is_reachable (fcg_analyze pre.cu_context)) pre.cu_context C0` by
    (qpat_assum `C0 = _` SUBST1_TAC >> irule prune_unit_ctx_agree >> simp[]) >>
  `C0.ctx_entry = pre.cu_context.ctx_entry` by
    simp[prune_unit_fcg_unreachable_fields] >>
  `fcg_is_reachable (fcg_analyze pre.cu_context) entry` by
    metis_tac[fcg_analyze_entry_reachable] >>
  `raw_reachable vs pre.cu_context g i t` by
    (mp_tac (Q.SPECL [`fcg_is_reachable (fcg_analyze pre.cu_context)`,
       `C0`, `pre.cu_context`, `vs`] raw_reachable_ctx_agree) >>
     (impl_tac >- (simp[] >> metis_tac[ctx_agree_sym])) >>
     disch_then (mp_tac o Q.SPECL [`g`, `i`, `t`]) >>
     simp[]) >>
  `raw_reachable vs mid.cu_context g i t` by metis_tac[] >>
  `EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_no_phi >>
     simp[EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  drule_all (Q.INST [`C` |-> `unit.cu_context`, `CT` |-> `mid.cu_context`]
    simplify_cfg_reached_external_operands) >> metis_tac[]
QED

Triviality create_size_pre_walk_clip:
  o1_ctx_shape C /\ o1_pre_walk_inv D C v /\
  mem_inv (\ctx fn i s. inst_dload_in_section i s /\
    s.vs_code = v.vs_code /\ s.vs_data_section = v.vs_data_section) C v /\
  v.vs_outcomes = short ++ tail ==>
  o1_pre_walk_inv D C (v with vs_outcomes := short)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?entry fn lbl. C.ctx_entry = SOME entry /\
     lookup_function entry C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl` by
    (drule o1_shaped_joint_initial >> simp[Once joint_initial_cases] >> metis_tac[]) >>
  `EVERY wf_function C.ctx_functions` by metis_tac[o1_ctx_shape_wf_functions] >>
  `!rq rqs. record_request rq rqs = rqs ++ [rq]` by simp[record_request_def] >>
  fs[o1_pre_walk_inv_def] >>
  qpat_assum `o1_src_inv D C v` (strip_assume_tac o REWRITE_RULE [o1_src_inv_def]) >>
  `!n. o1_safe_upto D lo n C v` by metis_tac[o1_src_inv_ptr_safe_upto] >>
  `raw_safe_rq_upto D lo (LENGTH short + LENGTH v.vs_requests) C v` by
    (simp[raw_safe_rq_upto_def] >> rpt conj_tac
     >- (fs[ptr_discipline_rq_upto_def, ptr_discipline_def] >> metis_tac[])
     >- (fs[taint_within_rq_upto_def, taint_within_def, final_taint_def] >>
         metis_tac[]) >>
     fs[mem_inv_raw_reachable] >> metis_tac[]) >>
  mp_tac (Q.INST [`vs` |-> `v`, `C` |-> `C`, `D` |-> `D`, `lo` |-> `lo`,
    `entry` |-> `entry`, `f` |-> `fn`, `lbl` |-> `lbl`,
    `k` |-> `LENGTH short + LENGTH v.vs_requests`, `n` |-> `0`,
    `short` |-> `short`, `tail` |-> `tail`, `Ds` |-> `D`, `reserve` |-> `lo`]
    request_cut_clipped_pre_walk) >>
  (impl_tac >- simp[]) >> simp[o1_pre_walk_inv_def]
QED

(* Give the source front end the filling selected by DFT. The two raw
   invariants are provided for that entry, before looking for a visit. *)
Theorem o1_pipeline_reached_create_size:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  dead_wf D /\ o1_initial_state_ok v /\ v.vs_fmp = v.vs_initial_fmp /\
  code_layout_valid v /\ fmp_variant_room (SOME fmp) out.po_unit.cu_context v /\
  (!vi. raw_variant fmp vi v ==>
    o1_pre_walk_inv D unit.cu_context vi /\
    mem_inv (\ctx fn i s. inst_dload_in_section i s /\
      s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section) unit.cu_context vi) /\
  raw_reachable v out.po_unit.cu_context fn j t /\
  ((j.inst_opcode = CREATE /\ j.inst_operands = [value;off;sz]) \/
   (j.inst_opcode = CREATE2 /\ j.inst_operands = [value;off;sz;salt])) /\
  eval_operand sz t = SOME nbytes ==>
  ?vi f i s a p z sl. raw_variant fmp vi v /\
    raw_reachable vi unit.cu_context f i s /\
    ((i.inst_opcode = CREATE /\ i.inst_operands = [a;p;z]) \/
     (i.inst_opcode = CREATE2 /\ i.inst_operands = [a;p;z;sl])) /\
    eval_operand z s = SOME nbytes
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `o1PipelineCorrect$o1_pipeline rp unit = SOME out`
    (assume_tac o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
  drule o1_driver_runs >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`pre`,`supply`,`entry`,`out_supply`] strip_assume_tac))) >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by simp[init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  `ALL_DISTINCT (unit_label_namespace pre)` by metis_tac[unit_labels_wf_namespace] >>
  mp_tac (Q.INST [`unit` |-> `pre`, `fcg` |-> `fcg_analyze pre.cu_context`]
    o1_ctx_shape_prune) >> simp[] >> strip_tac >>
  mp_tac (Q.INST [`unit` |-> `pre`, `fcg` |-> `fcg_analyze pre.cu_context`,
    `entry` |-> `entry`] o1_walk_callee_first) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC))) >>
  strip_tac >>
  rule_assum_tac (REWRITE_RULE [run_callee_first_def]) >>
  drule_at (Pos (el 3)) (Q.INST [`R` |-> `o1_fn_row`] o1_schedule_stages) >>
  (impl_tac >- fs[o1_fn_passes_steps, o1_step_contracts_from_rows, o1_prune_every]) >>
  strip_tac >>
  `!k. k < LENGTH o1_fn_passes ==>
    ctx_pass_stage rp (EL k o1_fn_passes) (o1_walk_view rp k) (stage k) (stage (SUC k))` by
    (rpt strip_tac >> first_x_assum drule >> simp[o1_walk_view_def]) >>
  `(!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
   (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions)` by
    (conj_tac >> rpt strip_tac >>
     qpat_assum `!k. k <= LENGTH _ ==> o1_ctx_shape _ /\ _` (qspec_then `k` mp_tac) >>
     simp[]) >>
  `!k. k <= 9 ==> o1_ctx_shape (stage k) /\ EVERY (o1_fn_row k) (stage k).ctx_functions` by
    simp[o1_fn_passes_def] >>
  `!k. k < 9 ==> ctx_pass_stage rp (EL k o1_fn_passes) (o1_walk_view rp k)
      (stage k) (stage (SUC k))` by simp[o1_fn_passes_def] >>
  `stage 9 = out.po_unit.cu_context` by
    (qpat_assum `stage (LENGTH o1_fn_passes) = _`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [o1_fn_passes_def])) >>
  `raw_reachable v (stage 9) fn j t` by simp[] >>
  `is_ext_call_op j.inst_opcode /\ MEM sz j.inst_operands` by
    (qpat_assum `(j.inst_opcode = CREATE /\ _) \/ _` strip_assume_tac >>
     simp[is_ext_call_op_def]) >>
  drule_all o1_post_dft_reached_external_operands >>
  disch_then (qx_choosel_then [`rds`,`f7`,`s7`] strip_assume_tac) >>
  qabbrev_tac `v7 = v with vs_gas_readings := rds` >>
  qabbrev_tac `vi = v7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  qabbrev_tac `k = LENGTH s7.vs_requests - LENGTH v7.vs_requests` >>
  qabbrev_tac `short = TAKE k v7.vs_outcomes` >>
  qabbrev_tac `clip7 = v7 with vs_outcomes := short` >>
  `raw_variant fmp vi v` by
    simp[raw_variant_def, gas_variant_def, Abbr `vi`, Abbr `v7`,
      venom_state_component_equality] >>
  `eval_operand sz s7 = SOME nbytes` by simp[] >>
  qpat_assum `!vi. raw_variant fmp vi v ==> _` (qspec_then `vi` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `EVERY fn_defs_reach_uses unit.cu_context.ctx_functions /\
   EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) unit.cu_context.ctx_functions` by
    (qpat_assum `o1_pre_walk_inv D unit.cu_context vi`
      (mp_tac o REWRITE_RULE [o1_pre_walk_inv_def, EVERY_MEM]) >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  `vi.vs_outcomes = short ++ DROP k vi.vs_outcomes` by
    simp[Abbr `vi`, Abbr `short`, TAKE_DROP] >>
  drule_all create_size_pre_walk_clip >> strip_tac >>
  `code_layout_valid v7` by
    (qpat_assum `code_layout_valid v` (mp_tac o REWRITE_RULE [code_layout_valid_def]) >>
     simp[Abbr `v7`, code_layout_valid_def]) >>
  `o1_initial_state_ok v7 /\ v7.vs_fmp = v7.vs_initial_fmp /\
   fmp_variant_room (SOME fmp) out.po_unit.cu_context v7` by
    fs[Abbr `v7`, o1_initial_state_ok_def, fmp_variant_room_def] >>
  `code_layout_valid clip7` by
    (qpat_assum `code_layout_valid v7` (mp_tac o REWRITE_RULE [code_layout_valid_def]) >>
     simp[Abbr `clip7`, code_layout_valid_def]) >>
  `o1_initial_state_ok clip7 /\ clip7.vs_fmp = clip7.vs_initial_fmp /\
   fmp_variant_room (SOME fmp) out.po_unit.cu_context clip7` by
    fs[Abbr `clip7`, o1_initial_state_ok_def, fmp_variant_room_def] >>
  `clip7 with vs_gas_readings := clip7.vs_gas_readings = clip7` by
    simp[venom_state_component_equality] >>
  `clip7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|> = vi with vs_outcomes := short` by
    simp[Abbr `vi`, Abbr `clip7`] >>
  mp_tac (Q.INST [`rpolicy` |-> `rp`, `stage` |-> `stage`, `D` |-> `D`,
    `unit` |-> `unit`, `out` |-> `out`, `pre` |-> `pre`, `t` |-> `supply`,
    `entry` |-> `entry`, `vs_out` |-> `clip7`, `rds` |-> `clip7.vs_gas_readings`,
    `fmp` |-> `fmp`] o1_pipeline_pre_dft_source_facts_static_abort_fixed) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  PURE_REWRITE_TAC[LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  qpat_assum `(clip7 with vs_gas_readings := _) = clip7`
    (fn th => PURE_REWRITE_TAC[th]) >>
  qpat_assum `(clip7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>) = _`
    (fn th => PURE_REWRITE_TAC[th]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `short = TAKE (LENGTH s7.vs_requests - LENGTH v7.vs_requests) v7.vs_outcomes` by
    simp[Abbr `short`, Abbr `k`] >>
  mp_tac (Q.INST [`rp` |-> `rp`, `stage` |-> `stage`, `D` |-> `D`,
    `v7` |-> `v7`, `vi` |-> `vi`, `fmp` |-> `fmp`, `short` |-> `short`,
    `fn` |-> `f7`, `t` |-> `s7`, `j` |-> `j`, `value` |-> `value`,
    `off` |-> `off`, `sz` |-> `sz`, `salt` |-> `salt`, `nbytes` |-> `nbytes`]
    o1_pre_dft_reached_create_size) >>
  (impl_tac >- (rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE simp[Abbr `vi`, Abbr `v7`]))) >>
  disch_then (qx_choosel_then [`f0`,`i0`,`s0`,`a0`,`p0`,`z0`,`sl0`]
    (map_every assume_tac o CONJUNCTS)) >>
  `is_ext_call_op i0.inst_opcode` by
    (qpat_assum `(i0.inst_opcode = CREATE /\ _) \/ _` strip_assume_tac >>
     simp[is_ext_call_op_def]) >>
  `vi.vs_vars = FEMPTY /\ ~vi.vs_halted` by fs[Abbr `vi`, o1_initial_state_ok_def] >>
  drule_all (Q.INST [`C0` |-> `stage 0`, `vs` |-> `vi`]
    o1_pre_walk_reached_external_operands) >>
  disch_then (qx_choosel_then [`f`,`s`] strip_assume_tac) >>
  qexistsl [`vi`,`f`,`i0`,`s`,`a0`,`p0`,`z0`,`sl0`] >> simp[]
QED
