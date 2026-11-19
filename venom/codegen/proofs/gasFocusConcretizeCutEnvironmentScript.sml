Theory gasFocusConcretizeCutEnvironment
Ancestors concretizePtrUnaryEnvironmentReadProducer[qualified]
  marker[qualified,ignore_grammar]
  gasFocusConcretizeEndpointCut gasFocusConcretizeTaggedSupport
  concretizePtrEnvironmentReadProducer concretizePtrRequestHistory
  concretizePtrOperationalOpcodes concretizePtrParamSupport
  concretizePtrOrdinaryNext concretizePtrValueTransport concretizePtrOpaqueRetpc
  concretizePtrReturnTransport
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrPrefixLedger
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrLedgerProbe concretizePtrSourceOwnership codegenRel
  concretizeStepStructure concretizeStageShape concretizePtrChronologicalHistory
  o1ContractSimplifyCfgSrcFrame[qualified] o1SafeUpto o1PassContract o1ScheduleDecomp
  pointerConfinedDefs opcodeClass ptrDiscipline memLocDefs
  frameViewFacts contextCodegenRel unitLabelMapIdentity
  unitShapeDefs venomWf cfgWf venomExecSemantics venomInst venomState
  list rich_list finite_map pred_set

Theorem focus_unary_environment_operands[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ ptr_static_support P fn TG /\
  MEM inst.inst_opcode [BLOCKHASH; BLOBHASH; BALANCE; EXTCODESIZE;
    EXTCODEHASH; CALLDATALOAD; DLOAD] ==>
  EVERY (\op. ptr_nonopaque_operand fn op /\ op_prov TG op = NONE /\
              op_taint tn op = {}) inst.inst_operands
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >> fs[MEM]) >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `fn_ptr_ok P fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts fn) ==> _`
       (qspec_then `inst` mp_tac) >> fs[MEM] >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  simp[EVERY_MEM] >> gen_tac >> strip_tac >>
  `ptr_nonopaque_operand fn op` by fs[EVERY_MEM] >> simp[] >> conj_tac
  >- (Cases_on `op` >> simp[op_prov_def] >>
      rename1 `FLOOKUP TG v = NONE` >> Cases_on `FLOOKUP TG v` >>
      fs[ptr_static_support_def] >> metis_tac[]) >>
  qpat_x_assum `taint_ok _ _ _ _` mp_tac >> fs[MEM] >>
  simp[taint_ok_def] >> metis_tac[]
QED

Theorem focus_environment_update[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  MEM inst.inst_opcode [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
    COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; CALLDATASIZE;
    RETURNDATASIZE; BLOBBASEFEE; CODESIZE; SELFBALANCE; BLOCKHASH; BLOBHASH;
    BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD; DLOAD] /\
  inst.inst_outputs = [out] /\ ~retpc_var f out ==>
  ptr_mixed_vars births positions
    (step_prov PT TG inst (update_var out v s))
    (step_taint inst s (update_var out v s) tn) f g
    (update_var out v s) (update_var out v t)
Proof
  strip_tac >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  fs[MEM] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ptr_value_transport_refl] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def]
QED

Theorem ptr_focus_environment_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ callee_first names C.ctx_functions /\
  ptr_discipline_upto lo n C vs /\ gas_cut n vs at.po_state /\
  MEM a.po_inst.inst_opcode [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
    COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; CALLDATASIZE;
    RETURNDATASIZE; BLOBBASEFEE; CODESIZE; SELFBALANCE; BLOCKHASH; BLOBHASH;
    BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD; DLOAD] /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?z TG'. TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `MEM a.po_fn C.ctx_functions` by (drule ptr_frame_context_membership >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (drule o1ContractSimplifyCfgSrcFrameTheory.scfg_frame_reachable_active >> simp[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `o1_fn_shape C a.po_fn` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `inst_wf a.po_inst` by
    (qpat_assum `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >> metis_tac[]) >>
  `?out. a.po_inst.inst_outputs = [out]` by
    (fs[MEM] >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >>
     conj_tac >- fs[EVERY_MEM] >> qexists `a.po_inst` >> fs[MEM]) >>
  `at.po_inst = a.po_inst` by (fs[MEM] >> gvs[concretize_positions_unchanged]) >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
   a.po_inst.inst_opcode <> NOP` by (fs[MEM] >> simp[is_terminator_def]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gnvs[Excl "MEM"] >>
  IF (qpat_assum `step_inst _ _ _ _ = OK _` kall_tac) all_tac
    (qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
     simp[step_inst_non_invoke, Excl "MEM"] >> strip_tac >>
     drule step_inst_base_intret_opcodes >> fs[MEM]) >>
  `?v. step_inst 0 C a.po_inst a.po_state = OK (update_var out v a.po_state) /\
       s' = update_var out v at.po_state` by suspend "execute" >>
  suspend "attach"
QED

Resume ptr_focus_environment_step[execute]:
  qpat_assum `ptr_paired_sample _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ptr_paired_sample_def]) >>
  Cases_on `MEM a.po_inst.inst_opcode [BLOCKHASH; BLOBHASH; BALANCE;
    EXTCODESIZE; EXTCODEHASH; CALLDATALOAD; DLOAD]`
  >- (`?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
        (drule o1LowerDloadPtrDisciplineTheory.ptr_discipline_upto_fn_ptr_ok >>
         strip_tac >> metis_tac[]) >>
      drule ptr_paired_prefix_transcript >> strip_tac >>
      drule ptr_structural_transcript_erasure >> strip_tac >>
      drule ptr_structural_trace_ownership >> strip_tac >>
      `?P. fn_ptr_ok P a.po_fn /\ ptr_static_support P a.po_fn TG` by
        (drule_all ptr_focus_source_tagged_support >> fs[EVERY_MEM] >> metis_tac[]) >>
      `opaque_use_ok a.po_fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
      drule_all focus_unary_environment_operands >> strip_tac >>
      `a.po_state.vs_labels = at.po_state.vs_labels` by
        (drule ptr_history_content_labels >> simp[]) >>
      `eval_operands a.po_inst.inst_operands a.po_state =
       eval_operands a.po_inst.inst_operands at.po_state` by
        (drule_all ptr_mixed_scalar_operands_equal >> simp[]) >>
      drule_all concretizePtrUnaryEnvironmentReadProducerTheory.ptr_unary_environment_execution >> simp[]) >>
  `MEM a.po_inst.inst_opcode [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
    COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; CALLDATASIZE;
    RETURNDATASIZE; BLOBBASEFEE; CODESIZE; SELFBALANCE]` by fs[MEM] >>
  drule_all concretizePtrEnvironmentReadProducerTheory.ptr_environment_read_execution >> simp[]
QED

Resume ptr_focus_environment_step[attach]:
  markerLib.RESUME_TAC >>
  `EVERY bb_well_formed a.po_fn.fn_blocks /\ ALL_DISTINCT (fn_labels a.po_fn)` by
    (qpat_assum `o1_fn_shape C a.po_fn`
       (mp_tac o REWRITE_RULE [o1_fn_shape_def, wf_function_def, EVERY_MEM]) >>
     simp[EVERY_MEM]) >>
  `?i. active_inst a.po_fn i
     ((update_var out v a.po_state) with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[update_var_def]) >>
  qabbrev_tac `z = ptr_ledger_next a i (update_var out v a.po_state)` >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`,`rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    suspend "sample" >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def] >>
  qexists `z` >> simp[] >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def, ptr_tagged_step_def] >>
  fs[MEM] >> simp[step_prov_def, out_prov_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
  (reverse conj_tac >- fs[update_var_def] >>
   qexistsl [`0`, `update_var out v a.po_state`] >> fs[update_var_def])
QED

Resume ptr_focus_environment_step[sample]:
  markerLib.RESUME_TAC >>
  simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  reverse conj_tac
  >- (fs[ptr_paired_sample_def] >>
      irule ptr_history_content_masks >> goal_assum (drule_at Any) >>
      fs[MEM] >> simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def]) >>
  `ptr_mixed_vars births positions
     (step_prov PT TG a.po_inst (update_var out v a.po_state))
     (step_taint a.po_inst a.po_state (update_var out v a.po_state) a.po_taint)
     a.po_fn at.po_fn (update_var out v a.po_state) (update_var out v at.po_state)` by
    (fs[ptr_paired_sample_def] >> irule focus_environment_update >> simp[]) >>
  gvs[step_prov_def, out_prov_def] >>
  irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >>
  simp[update_var_def]
QED

Finalise ptr_focus_environment_step
