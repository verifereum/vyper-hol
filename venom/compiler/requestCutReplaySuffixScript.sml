Theory requestCutReplaySuffix
Ancestors
  dftWaveStaticMemoryInv dftContractGas
  o1DftStageSsa o1CodeEndDftTransport o1CodeEndCfgNormTransport o1ContractCfgNorm
  o1PassContract unitMemInv unitTransformDefs dftGasOracleDefs
  stateFrame staticAbortDefs o1ScheduleDecompHelpers venomState venomWf venomInst list
  fnFrameSymbolicPrefix contextPlanLayoutProps ctxLookupAgree o1PassLift
  asmSem codegenSymRel finite_map option words arithmetic
  o1ContractCfgNormJointCursors o1ContractCfgNormCursors cfgNormSupplySim
  frameJointTransition jointRequestCut

Theorem request_cut_dft_cfg_invariants:
  ctx_pass_stage rp (CFP_Simple VP_DFT) dft_view C7 C8 /\ o1_pre 7 C7 C8 /\
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) cfg_view C8 C9 /\
  o1_ctx_shape C7 /\ EVERY wf_ssa C7.ctx_functions /\ o1_ctx_shape C8 /\
  ctx_labels_bound C7 vs0.vs_labels /\ o1_initial_state_ok vs0 /\
  vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0 /\
  (!fn inst t. raw_reachable vs0 C8 fn inst t /\ LENGTH t.vs_requests <= k /\
    ~in_static_abort_prefix fn t ==>
    ?p d. ev_reachable orc vs0 C8 p d fn inst (t with vs_gas_readings := vs0.vs_gas_readings)) /\
  (!p d fn inst s. ev_reachable orc vs0 C7 p d fn inst s /\ LENGTH s.vs_requests <= k ==>
    in_static_abort_prefix fn s \/ lowered_mem_fact eom C7 fn inst s) /\
  (guarded ==>
    (!p d fn inst s. ev_reachable orc vs0 C7 p d fn inst s /\ LENGTH s.vs_requests <= k ==>
       ?ws. raw_reachable source C7 fn inst (s with vs_gas_readings := ws)) /\
    code_end_offset_ok (\ctx fn inst s. raw_reachable source ctx fn inst s /\
      LENGTH s.vs_requests <= k) C7) ==>
  mem_inv (\ctx fn inst t. LENGTH t.vs_requests <= k /\ ~in_static_abort_prefix fn t ==>
    lowered_mem_ok eom (w2n t.vs_initial_fmp) ctx fn inst t) C9 vs0 /\
  (guarded ==> code_end_offset_ok (\ctx fn inst t. raw_reachable vs0 ctx fn inst t /\
    LENGTH t.vs_requests <= k /\ ~in_static_abort_prefix fn t) C9)
Proof
  strip_tac >> drule_all dft_stage_fn_rel >> strip_tac >>
  `EVERY wf_ssa C8.ctx_functions` by (irule dft_stage_wf_ssa >> metis_tac[]) >>
  `vs0.vs_vars = FEMPTY /\ ~vs0.vs_halted` by fs[o1_initial_state_ok_def] >>
  `?name fn lbl. C8.ctx_entry = SOME name /\
    lookup_function name C8.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl` by
    (qpat_x_assum `o1_ctx_shape C8` mp_tac >>
     simp[o1_ctx_shape_def, ctx_wf_def, ctx_has_entry_def, ctx_distinct_fn_names_def,
          ctx_fn_names_def, MEM_MAP, EVERY_MEM] >>
     strip_tac >> rename1 `C7.ctx_entry = SOME name` >>
     rename1 `MEM fn C8.ctx_functions` >>
     qexistsl_tac [`name`, `fn`, `(HD fn.fn_blocks).bb_label`] >>
     `fn.fn_blocks <> []` by metis_tac[o1_fn_shape_def, wf_function_def, fn_has_entry_def] >>
     simp[lookup_function_member_iff, fn_entry_label_def, entry_block_def, NULL_EQ] >>
     metis_tac[]) >>
  conj_tac
  >- (mp_tac (Q.INST [`C` |-> `C7`, `C'` |-> `C8`, `s` |-> `vs0`,
       `P` |-> `\rqs. LENGTH rqs <= k`] dft_ev_lowered_inv_wave_static_abort_under_requests) >>
      simp[] >> impl_tac >- metis_tac[] >> strip_tac >>
      `mem_inv (\ctx fn inst t. (in_static_abort_prefix fn t \/ ~(LENGTH t.vs_requests <= k)) \/
        lowered_mem_fact eom ctx fn inst t) C8 vs0` by
        (simp[mem_inv_raw_reachable] >>
         qx_genl_tac [`f'`, `i`, `u`] >> strip_tac >>
         Cases_on `LENGTH u.vs_requests <= k` >> simp[] >>
         Cases_on `in_static_abort_prefix f' u` >> simp[] >>
         qpat_x_assum `!fn inst t. raw_reachable vs0 C8 fn inst t /\ LENGTH t.vs_requests <= k /\
    ~in_static_abort_prefix fn t ==> _`
           drule_all >> strip_tac >>
         qpat_x_assum `!p d fn inst t. ev_reachable orc vs0 C8 p d fn inst t /\ LENGTH t.vs_requests <= k ==> _`
           (qspecl_then [`p`, `d`, `f'`, `i`, `u with vs_gas_readings := vs0.vs_gas_readings`] mp_tac) >>
         fs[in_static_abort_prefix_def] >> metis_tac[]) >>
      mp_tac (Q.INST [`C` |-> `C8`, `C'` |-> `C9`, `vs` |-> `vs0`,
        `rpolicy` |-> `rp`, `view` |-> `cfg_view`,
        `P` |-> `\rqs. LENGTH rqs <= k`] cfg_norm_stage_mem_inv_lowered_abort_under_requests) >>
      simp[] >> strip_tac >>
      irule mem_inv_mono >>
      qexists_tac `\ctx fn inst t. (in_static_abort_prefix fn t \/ ~(LENGTH t.vs_requests <= k)) \/
        lowered_mem_fact eom ctx fn inst t` >>
      simp[lowered_mem_fact_def] >> metis_tac[]) >>
  strip_tac >>
  mp_tac (Q.INST [`C` |-> `C7`, `C'` |-> `C8`, `vs` |-> `vs0`,
    `P` |-> `\rqs. LENGTH rqs <= k`] dft_code_end_offset_ok_under_requests) >>
  simp[] >> impl_tac >- metis_tac[] >> strip_tac >>
  mp_tac (Q.INST [`C` |-> `C8`, `C'` |-> `C9`, `vs` |-> `vs0`,
        `rpolicy` |-> `rp`, `view` |-> `cfg_view`,
    `P` |-> `\s. LENGTH s.vs_requests <= k`, `guarded` |-> `T`] cfg_norm_code_end_offset_ok_under) >>
  simp[]
QED

(* The pointwise guard needed to continue the actual assembly frontier.
   Static abort and revert forwarding have their own terminal routes. *)
Theorem cfg_norm_cursor_execution_frame[local]:
  !C rounds cells. cfg_norm_cursors C rounds cells ==>
    execution_frame (SND (FST (HD cells))) =
    execution_frame (SND (FST (LAST cells)))
Proof
  ho_match_mp_tac cfg_norm_cursors_ind >>
  simp[LAST_CONS_cond, supply_state_agree_def] >> metis_tac[]
QED

Theorem cfg_norm_joint_cursor_execution_frame:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) ==>
  execution_frame s8 = execution_frame s9
Proof
  strip_tac >> PairCases_on `current` >>
  gvs[cfg_norm_joint_cursors_def] >>
  drule cfg_norm_cursor_execution_frame >> simp[]
QED

Theorem cfg_norm_joint_recording_step:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  joint_transition C9
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9)
    (SOME (OriginOrdinary fuel post)) q9' /\
  LENGTH s9.vs_requests < LENGTH post.vs_requests ==>
  inst8.inst_opcode <> INVOKE /\ s8.vs_requests = s9.vs_requests /\
  s8.vs_outcomes = s9.vs_outcomes /\
  ?u. step_inst fuel C8 inst8 s8 = OK u /\
    u.vs_requests = post.vs_requests /\ u.vs_outcomes = post.vs_outcomes
Proof
  strip_tac >> drule cfg_norm_joint_cursor_execution_frame >> strip_tac >>
  Cases_on `current` >>
  rename1 `cfg_norm_joint_cursors _ _ (schedules,(rounds,cells),saved) _ _` >>
  gvs[cfg_norm_joint_cursors_def, joint_transition_ordinary] >>
  `~MEM inst9.inst_opcode [ASSIGN; JMP; JNZ]` by
    (drule_all step_inst_request_outcomes >> Cases_on `inst9.inst_opcode` >> simp[]) >>
  `?supply. LAST rounds = (supply,fn9,NONE)` by
    (qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then drule >> simp[] >> metis_tac[]) >>
  drule_all cfg_norm_cursors_next_classified >> strip_tac >> gvs[] >>
  `execution_frame (u with vs_inst_idx := SUC s8.vs_inst_idx) =
    execution_frame (post with vs_inst_idx := SUC s9.vs_inst_idx)` by
    (qpat_assum `cfg_norm_cursors C8 rounds cursors'`
       (mp_tac o MATCH_MP cfg_norm_cursor_execution_frame) >> simp[]) >>
  pop_assum (mp_tac o Q.AP_TERM `\s. (s.vs_requests,s.vs_outcomes)`) >>
  simp[execution_frame_def]
QED
