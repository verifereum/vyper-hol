(*
 * Paired-prefix extension for the N10 opcode family (CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY).
 *)
Theory concretizePtrBufferCopyFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrBufferCopyContent
  concretizePtrPairedPrefixProbe
  concretizePtrOpaqueRetpc ptrDiscipline memLocDefs list pointerConfinedDefs
  concretizePtrRequestHistory venomExecSemantics venomState venomInst words codegenRel
  concretizePtrWriteFootprint concretizePtrPrefixLedger concretizePtrBytes
  concretizePtrChronologicalHistory pred_set arithmetic
  concretizePtrWriteOwnership concretizePtrOwnershipErasure
  concretizePtrComparisonTransport concretizePtrPairedFields
  concretizePtrSourceOwnership concretizePtrValueTransport
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrEventEmbedding
  concretizePtrDeletedGapHistory concretizePtrExecutedCoverage
  unitShapeDefs venomWf cfgWf o1PassContract
  concretizeStepStructure concretizeStepShape concretizePtrDeletedGaps
  concretizePtrOrdinaryNext concretizePtrTaggedSupport
  concretizePtrLedgerProbe concretizePtrReturnTransport
  concretizePtrOperationalOpcodes finite_map concretizePtrAllocationSize
  contextCodegenRel unitLabelMapIdentity opcodeClass venomExecProps memSafeRun
  concretizePtrActivationChronology concretizePtrPlacementBounds

Theorem ptr_buffer_copy_operand_discipline[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) /\
  MEM inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  inst.inst_operands = [dop;sop;nop] ==>
  EVERY (ptr_nonopaque_operand fn) [dop;sop;nop] /\
  EVERY (\op. op_prov TG op = NONE /\ op_taint tn op = {}) [sop;nop]
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) [dop;sop;nop]` by
    (`EVERY (ptr_nonopaque_operand fn) inst.inst_operands` suffices_by simp[] >>
     irule ptr_nonopaque_instruction_operands >> simp[] >> fs[MEM]) >>
  simp[] >>
  `!v. (sop = Var v \/ nop = Var v) ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `fn_ptr_ok P fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts fn) ==> _`
       (qspec_then `inst` mp_tac) >> fs[MEM] >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `!v'. _` (qspec_then `v` mp_tac) >>
     simp[] >> strip_tac >> gvs[] >>
     Cases_on `dop = Var v` >> gvs[] >>
     Cases_on `sop = Var v` >> gvs[] >>
     Cases_on `nop = Var v` >> gvs[]) >>
  `op_taint tn sop = {} /\ op_taint tn nop = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> fs[MEM] >>
     simp[taint_ok_def] >> metis_tac[]) >>
  simp[] >> conj_tac >> Cases_on `sop` >> Cases_on `nop` >>
  simp[op_prov_def] >> rpt conj_tac >>
  qmatch_goalsub_rename_tac `FLOOKUP TG v` >>
  Cases_on `FLOOKUP TG v` >> gvs[] >> metis_tac[]
QED

Theorem ptr_buffer_copy_execution[local]:
  ptr_history_content tn s t /\
  MEM inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  inst.inst_operands = [dop;sop;nop] /\
  IS_SOME (eval_operand dop s) = IS_SOME (eval_operand dop t) /\
  eval_operand sop s = eval_operand sop t /\
  eval_operand nop s = eval_operand nop t /\
  step_inst fuel Ct inst t = OK t' ==>
  ?d dt r n s'.
    eval_operand dop s = SOME d /\ eval_operand dop t = SOME dt /\
    eval_operand sop s = SOME r /\ eval_operand sop t = SOME r /\
    eval_operand nop s = SOME n /\ eval_operand nop t = SOME n /\
    step_inst 0 C inst s = OK s' /\
    (inst.inst_opcode = RETURNDATACOPY ==>
      w2n r + w2n n <= LENGTH s.vs_returndata) /\
    (!i. i < w2n n ==>
      read_byte (w2n d+i) s'.vs_memory =
      read_byte (w2n dt+i) t'.vs_memory)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_code = t.vs_code /\
   s.vs_data_section = t.vs_data_section /\ s.vs_returndata = t.vs_returndata` by
    metis_tac[ptr_history_content_call_ctx, ptr_history_content_code,
      ptr_history_content_data_section, ptr_history_content_returndata] >>
  `inst.inst_opcode <> INVOKE` by (fs[MEM]) >>
  `step_inst_base inst t = OK t'` by
    metis_tac[step_inst_non_invoke] >>
  `?d dt r n. eval_operand dop s = SOME d /\ eval_operand dop t = SOME dt /\
    eval_operand sop s = SOME r /\ eval_operand sop t = SOME r /\
    eval_operand nop s = SOME n /\ eval_operand nop t = SOME n` by
    (qpat_x_assum `step_inst_base inst t = OK t'` mp_tac >>
     fs[MEM] >> PURE_REWRITE_TAC[step_inst_base_def] >>
     ASM_REWRITE_TAC[] >> PURE_REWRITE_TAC[opcode_case_def] >>
     simp[AllCaseEqs()] >>
     Cases_on `eval_operand dop s` >> gvs[] >> metis_tac[]) >>
  `inst.inst_opcode = RETURNDATACOPY ==>
    w2n r + w2n n <= LENGTH s.vs_returndata` by
    (strip_tac >> drule_all ptr_returndatacopy_success_bound >> simp[]) >>
  `?s' tt. step_inst_base inst s = OK s' /\
    step_inst_base inst t = OK tt /\
    (!i. i < w2n n ==> read_byte (w2n d+i) s'.vs_memory =
      read_byte (w2n dt+i) tt.vs_memory)` by
    (`s.vs_call_ctx.cc_calldata = t.vs_call_ctx.cc_calldata` by simp[] >>
     fs[MEM]
     >- (drule_all ptr_calldatacopy_content >> strip_tac >> gvs[] >>
         goal_assum (drule_at Any) >> simp[arithmeticTheory.ADD_COMM])
     >- (drule_all ptr_codecopy_content >> strip_tac >> gvs[] >>
         goal_assum (drule_at Any) >> simp[arithmeticTheory.ADD_COMM])
     >- (drule_all ptr_dloadbytes_content >> strip_tac >> gvs[] >>
         goal_assum (drule_at Any) >> simp[arithmeticTheory.ADD_COMM]) >>
     `w2n r + w2n n <= LENGTH s.vs_returndata` by gvs[] >>
     drule_all ptr_returndatacopy_content >> strip_tac >> gvs[] >>
     goal_assum (drule_at Any) >> simp[arithmeticTheory.ADD_COMM]) >>
  gvs[] >> qexists_tac `s'` >> simp[] >>
  fs[MEM] >> simp[step_inst_non_invoke]
QED

Theorem ptr_buffer_copy_post_memory[local]:
  MEM inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  step_inst fuel C inst s = OK s' ==>
  s' = s with vs_memory := s'.vs_memory
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by fs[MEM] >>
  `step_inst_base inst s = OK s'` by metis_tac[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  fs[MEM] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> PURE_REWRITE_TAC[opcode_case_def] >>
     simp[AllCaseEqs()] >>
  strip_tac >> gvs[write_memory_with_expansion_def]
QED

Theorem ptr_buffer_copy_history_content[local]:
  ptr_history_content tn s t /\
  MEM inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  step_inst fuel C inst s = OK s' /\ step_inst fuelt Ct inst t = OK t' ==>
  ptr_history_content (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `s' = s with vs_memory := s'.vs_memory` by
    (irule ptr_buffer_copy_post_memory >> rpt (goal_assum (drule_at Any))) >>
  `t' = t with vs_memory := t'.vs_memory` by
    (irule ptr_buffer_copy_post_memory >> rpt (goal_assum (drule_at Any))) >>
  once_asm_rewrite_tac[] >> simp[] >>
  irule ptr_history_content_masks >> goal_assum (drule_at Any) >>
  fs[MEM] >> simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def]
QED

Theorem ptr_buffer_copy_write_pair[local]:
  ptr_chrono_step C a z /\ ptr_chrono_step Ct at zt /\
  MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  at.po_inst = a.po_inst /\ a.po_inst.inst_operands = [dop;sop;nop] /\
  eval_operand dop a.po_state = SOME d /\ eval_operand dop at.po_state = SOME dt /\
  eval_operand sop a.po_state = SOME r /\ eval_operand sop at.po_state = SOME r /\
  eval_operand nop a.po_state = SOME n /\ eval_operand nop at.po_state = SOME n /\
  (!i. i < w2n n ==> read_byte (w2n d+i) z.po_state.vs_memory =
    read_byte (w2n dt+i) zt.po_state.vs_memory) ==>
  ptr_ledger_write_pair C Ct (\x. w2n dt + (x - w2n d)) a z at zt
Proof
  strip_tac >>
  `!x. x IN range_bytes (step_writes a.po_inst a.po_state z.po_state) <=>
    w2n d <= x /\ x < w2n d + w2n n` by
    (gen_tac >> irule ptr_copy_footprint_interval >> simp[] >> fs[MEM] >>
     metis_tac[]) >>
  `!x. x IN range_bytes (step_writes at.po_inst at.po_state zt.po_state) <=>
    w2n dt <= x /\ x < w2n dt + w2n n` by
    (gen_tac >> irule ptr_copy_footprint_interval >> simp[] >> fs[MEM] >>
     metis_tac[]) >>
  simp[ptr_ledger_write_pair_def] >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    (fs[MEM] >> simp[is_terminator_def]) >>
  simp[ptr_bytes_agree_def] >> rpt strip_tac >>
  `x - w2n d < w2n n` by decide_tac >>
  qpat_x_assum `!i. i < w2n n ==> _`
    (qspec_then `x - w2n d` mp_tac) >> simp[]
QED

Theorem ptr_buffer_copy_range_owner[local]:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  mem_write_ops a.po_inst = SOME ops /\
  MEM (w2n d,len) (source_memory_write_ranges a.po_inst a.po_state) /\
  ptr_value_transport births positions (op_prov TG ops.iao_ofst) {} d dt /\
  (!aid pos sz. FLOOKUP positions (Allocation aid) = SOME (pos,sz) ==>
    pos + sz < dimword(:256)) ==>
  ptr_paired_write_owner lo positions (\x. w2n dt + (x-w2n d))
    {x | w2n d <= x /\ x < w2n d + len}
    (tokens,registry,births,PT,TG,saved,entries)
Proof
  strip_tac >>
  simp[ptr_paired_write_owner_def] >> gen_tac >> strip_tac >>
  `len <> 0` by decide_tac >>
  `ptr_ledger_erases births TG a.po_prov` by
    (irule ptr_source_ownership_prov_erases >> metis_tac[]) >>
  drule_all ptr_source_write_owner_cases >> strip_tac
  >- (`op_prov TG ops.iao_ofst = NONE` by
        (drule ptr_owner_op_projection >>
         disch_then (qspec_then `ops.iao_ofst` strip_assume_tac) >>
         Cases_on `op_prov TG ops.iao_ofst` >>
         gvs[ptr_owner_project_def] >>
         fs[finite_mapTheory.FLOOKUP_DEF]) >>
      gvs[ptr_value_transport_scalar_empty] >> disj1_tac >> decide_tac) >>
  fs[] >>
  `MEM token tokens` by (irule ptr_source_ownership_live_prov >> metis_tac[]) >>
  `FLOOKUP births (token,aid) = SOME (b,sz)` by
    (fs[ptr_ledger_erases_def] >>
     qpat_x_assum `!v. FLOOKUP a.po_prov v = _`
       (qspec_then `v` mp_tac) >> simp[]) >>
  qpat_x_assum `ops' = ops` SUBST_ALL_TAC >>
  qpat_x_assum `ptr_value_transport _ _ _ _ _ _` mp_tac >>
  asm_simp_tac (srw_ss()) [op_prov_def, ptr_value_transport_def] >> strip_tac >>
  `pos + sz < dimword(:256)` by metis_tac[] >>
  `w2n dt = pos + (w2n d - b)` by
    (irule ptr_closed_relocation_value >> simp[] >>
     qexists_tac `sz` >> simp[] >> decide_tac) >>
  disj2_tac >> qexistsl_tac [`token`,`aid`,`b`,`sz`,`pos`,`x-b`] >>
  simp[] >> decide_tac
QED

Theorem ptr_buffer_copy_write_event[local]:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  ptr_chrono_step C a z /\ ptr_chrono_step Ct at zt /\
  MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  at.po_inst = a.po_inst /\ a.po_inst.inst_operands = [dop;sop;nop] /\
  eval_operand dop a.po_state = SOME d /\ eval_operand dop at.po_state = SOME dt /\
  eval_operand sop a.po_state = SOME r /\ eval_operand sop at.po_state = SOME r /\
  eval_operand nop a.po_state = SOME n /\ eval_operand nop at.po_state = SOME n /\
  (!i. i < w2n n ==> read_byte (w2n d+i) z.po_state.vs_memory =
    read_byte (w2n dt+i) zt.po_state.vs_memory) /\
  ptr_value_transport births positions (op_prov TG dop) {} d dt /\
  (!aid pos sz. FLOOKUP positions (Allocation aid) = SOME (pos,sz) ==>
    pos + sz < dimword(:256)) /\
  LENGTH H = LENGTH h /\ 0 < LENGTH h /\ LAST h = a /\ LAST ht = at /\
  LENGTH ht = SUC (LENGTH done) ==>
  ?extra.
    (extra = [] \/ extra = [(LENGTH h - 1,LENGTH done,\x. w2n dt + (x-w2n d))]) /\
    EVERY (ptr_paired_write lo positions C Ct (h ++ [z]) (ht ++ [zt])
      (done ++ [LENGTH h - 1])
      (H ++ [(tokens,registry,births,PT,TG,saved,entries)])) extra /\
    (range_bytes (step_writes a.po_inst a.po_state z.po_state) <> {} ==>
      ?rho. MEM (LENGTH h - 1,LENGTH done,rho) extra)
Proof
  strip_tac >>
  `range_bytes (step_writes a.po_inst a.po_state z.po_state) =
    {x | w2n d <= x /\ x < w2n d + w2n n}` by
    (simp[EXTENSION] >> gen_tac >> irule ptr_copy_footprint_interval >>
     simp[] >> fs[MEM] >> metis_tac[]) >>
  `ptr_ledger_write_pair C Ct (\x. w2n dt + (x-w2n d)) a z at zt` by
    (irule ptr_buffer_copy_write_pair >> metis_tac[]) >>
  `ptr_paired_write_owner lo positions (\x. w2n dt + (x-w2n d))
    (range_bytes (step_writes a.po_inst a.po_state z.po_state))
    (tokens,registry,births,PT,TG,saved,entries)` by
    (asm_rewrite_tac[] >> irule ptr_buffer_copy_range_owner >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `ptr_source_ownership _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexists_tac `<|iao_ofst := dop; iao_size := SOME nop;
       iao_max_size := SOME nop|>` >>
     simp[] >> fs[MEM] >>
     simp[mem_write_ops_def, source_memory_write_ranges_def,
       sized_source_write_range_def]) >>
  Cases_on `range_bytes (step_writes a.po_inst a.po_state z.po_state) = {}`
  >- (qexists_tac `[]` >> simp[]) >>
  qexists_tac `[(LENGTH h - 1,LENGTH done,\x. w2n dt + (x-w2n d))]` >>
  `SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
  `h <> [] /\ ht <> []` by (conj_tac >> strip_tac >> fs[]) >>
  `EL (LENGTH h - 1) h = a /\ EL (LENGTH done) ht = at` by
    (fs[LAST_EL, PRE_SUB1]) >>
  simp[ptr_paired_write_def, EL_APPEND_EQN] >> metis_tac[]
QED

Theorem ptr_buffer_copy_prefix_attach[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_structural_transcript R vs C C' (h ++ [b]) b (ht ++ [bt]) bt
    (done ++ [LENGTH h - 1]) tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) /\
  ptr_paired_sample positions b bt (tokens,registry,births,PT,TG',saved,entries) /\
  ptr_paired_code R lp positions b.po_fn bt.po_fn /\ ptr_paired_cursor lp b bt /\
  ptr_paired_params positions b bt (tokens,registry,births,PT,TG',saved,entries) /\
  b.po_stack = a.po_stack /\ bt.po_stack = at.po_stack /\
  (extra = [] \/ ?rho. extra = [(LENGTH h - 1,LENGTH done,rho)]) /\
  EVERY (ptr_paired_write lo positions C C' (h ++ [b]) (ht ++ [bt])
    (done ++ [LENGTH h - 1])
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)])) extra /\
  (range_bytes (step_writes a.po_inst a.po_state b.po_state) <> {} ==>
    ?rho. MEM (LENGTH h - 1,LENGTH done,rho) extra) ==>
  ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [b]) b (ht ++ [bt]) bt (done ++ [LENGTH h - 1])
    tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls (ws ++ extra)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `LAST h = a` by metis_tac[ptr_chrono_history_end] >>
  `EVERY (\n. SUC n < LENGTH h) done` by
    (qpat_assum `ptr_structural_transcript _ _ _ _ (h ++ _) _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP ptr_structural_transcript_erasure) >>
     drule ptr_structural_trace_embedding >>
     simp[ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN] >>
     fs[ptr_paired_prefix_def, ptr_paired_samples_def, ptr_sample_list_def] >> decide_tac) >>
  qhdtm_x_assum `ptr_paired_prefix` mp_tac >> rewrite_tac[ptr_paired_prefix_def] >> strip_tac >> simp[] >>
  conj_tac >- (irule ptr_paired_samples_pair >> simp[]) >>
  conj_tac >- (irule ptr_paired_alignment_pair >> simp[]) >>
  conj_tac >- (irule ptr_paired_callers_retained >> simp[] >>
    fs[ptr_paired_samples_def, ptr_sample_list_def] >> qexistsl_tac [`a`,`at`] >> simp[]) >>
  irule ptr_paired_writes_pair >> simp[] >>
  fs[ptr_paired_samples_def, ptr_sample_list_def] >> metis_tac[]
QED

Theorem ptr_paired_prefix_buffer_copy[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  ~in_revert_forward a.po_fn a.po_state /\
  ptr_chrono_step C' at zt ==>
  ?z TG' extra.
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls (ws ++ extra)
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn) /\ inst_wf a.po_inst` by
    (conj_asm1_tac
     >- (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
     fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
        wf_function_def, fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `?dop sop nop. a.po_inst.inst_operands = [dop;sop;nop]` by
    (fs[MEM] >> gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute]) >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> ASSIGN /\
   a.po_inst.inst_opcode <> PHI /\ a.po_inst.inst_opcode <> RETPC_PARAM /\
   ~is_terminator a.po_inst.inst_opcode` by (fs[MEM] >> simp[is_terminator_def]) >>
  `at.po_inst = a.po_inst` by (fs[MEM] >> gvs[concretize_positions_unchanged]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) [dop;sop;nop] /\
   EVERY (\op. op_prov TG op = NONE /\ op_taint a.po_taint op = {}) [sop;nop]` by
    (`?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
       (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
     `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
           EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
     `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions` by
       (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
     `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
       (rpt strip_tac >> irule ptr_source_tagged_var_support >>
        rpt (goal_assum (drule_at Any))) >>
     `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
       (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
     `fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
     drule_all ptr_buffer_copy_operand_discipline >> simp[]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"] >>
  IF (qpat_assum `step_inst _ _ _ _ = OK _` (K all_tac)) all_tac
    (qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
     simp[step_inst_non_invoke] >> strip_tac >>
     drule step_inst_base_intret_opcodes >> fs[MEM]) >>

  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn a.po_state at.po_state /\
   ptr_history_content a.po_taint a.po_state at.po_state` by
    fs[ptr_paired_sample_def] >>
  `a.po_state.vs_labels = at.po_state.vs_labels` by
    metis_tac[ptr_history_content_labels] >>
  `IS_SOME (eval_operand dop a.po_state) = IS_SOME (eval_operand dop at.po_state)` by
    metis_tac[ptr_mixed_vars_eval_presence] >>
  `eval_operand sop a.po_state = eval_operand sop at.po_state /\
   eval_operand nop a.po_state = eval_operand nop at.po_state` by
    (`!op. ptr_nonopaque_operand a.po_fn op /\ op_prov TG op = NONE /\
       op_taint a.po_taint op = {} ==>
       eval_operand op a.po_state = eval_operand op at.po_state` by
       (rpt strip_tac >>
        drule ptr_mixed_vars_eval >>
        disch_then (qspec_then `op` mp_tac) >> simp[] >>
        Cases_on `eval_operand op a.po_state` >>
        Cases_on `eval_operand op at.po_state` >>
        simp[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]) >>
     metis_tac[]) >>
  `MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY]` by simp[] >>
  drule_all ptr_buffer_copy_execution >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `s''.vs_current_bb = a.po_state.vs_current_bb /\
   s''.vs_prev_bb = a.po_state.vs_prev_bb /\
   s''.vs_allocas = a.po_state.vs_allocas /\
   s''.vs_params = a.po_state.vs_params /\
   s''.vs_vars = a.po_state.vs_vars /\ s''.vs_labels = a.po_state.vs_labels` by
    (qpat_assum `step_inst 0 C _ _ = OK _`
       (mp_then Any mp_tac ptr_buffer_copy_post_memory) >>
     simp[] >> disch_then SUBST1_TAC >> simp[]) >>
  `s'.vs_current_bb = at.po_state.vs_current_bb /\
   s'.vs_prev_bb = at.po_state.vs_prev_bb /\
   s'.vs_params = at.po_state.vs_params /\
   s'.vs_vars = at.po_state.vs_vars /\ s'.vs_labels = at.po_state.vs_labels` by
    (qpat_assum `step_inst fuel C' _ _ = OK _`
       (mp_then Any mp_tac ptr_buffer_copy_post_memory) >>
     simp[] >> disch_then SUBST1_TAC >> simp[]) >>
  `?i. active_inst a.po_fn i (s'' with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (`EVERY bb_well_formed a.po_fn.fn_blocks` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
     qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[]) >>
  qabbrev_tac `z = ptr_ledger_next a i s''` >>
  `ptr_chrono_step C a z` by
    (simp[Abbr `z`, ptr_ledger_next_def] >>
     once_rewrite_tac[ptr_chrono_step_cases] >>
     simp[ptr_observe_def, ptr_observation_component_equality] >>
     qexistsl_tac [`s''`,`0`] >> simp[]) >>
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`,`rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_paired_sample positions z zt
    (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
     reverse conj_tac
     >- (drule_all ptr_buffer_copy_history_content >> simp[]) >>
     `a.po_inst.inst_outputs = []` by
       (qpat_x_assum `inst_wf a.po_inst` mp_tac >> simp[inst_wf_def]) >>
     simp[step_prov_def, out_prov_def, step_taint_def, set_prov_def,
          set_var_taint_def, DRESTRICT_UNIV] >>
     irule ptr_mixed_vars_fields >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac
     >- (qpat_assum `step_inst 0 C _ _ = OK _`
           (mp_then Any mp_tac ptr_buffer_copy_post_memory) >>
         simp[] >> disch_then SUBST1_TAC >> simp[]) >>
     qpat_assum `step_inst fuel C' _ _ = OK _`
       (mp_then Any mp_tac ptr_buffer_copy_post_memory) >>
     simp[] >> disch_then SUBST1_TAC >> simp[]) >>
  `ptr_paired_params positions z zt
    (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def]) >>
  `a.po_inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf a.po_inst` mp_tac >> simp[inst_wf_def]) >>
  `step_prov PT TG a.po_inst z.po_state = TG` by
    simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def,
         step_prov_def, out_prov_def, set_prov_def, DRESTRICT_UNIV] >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved` by
    (`ptr_tagged_step (HD tokens) PT TG a.po_inst s'' = TG` by
       simp[ptr_tagged_step_def, step_prov_def, out_prov_def,
            set_prov_def, DRESTRICT_UNIV] >>
     `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by simp[] >>
     qpat_assum `step_inst 0 C _ _ = OK _`
       (mp_then (Pos (el 4)) mp_tac (cj 1 ptr_tagged_chrono_step_rules)) >>
     simp[] >> strip_tac >>
     `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
       a.po_fn a.po_inst a.po_state = a` by
       simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
     fs[Abbr `z`, ptr_ledger_next_def] >> metis_tac[]) >>
  `ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
    (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)])` by
    (drule ptr_ownership_overlay_fixed >> strip_tac >>
     drule (cj 3 ptr_structural_transcript_rules) >>
     disch_then drule >> disch_then drule >>
     simp[ptr_activation_tokens_def, ptr_activation_registry_def,
          Abbr `z`, ptr_ledger_next_def, ptr_observe_def]) >>
  `ptr_paired_cursor lp z zt` by
    (drule ptr_ordinary_next_cursor >> disch_then irule >>
     simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def]) >>
  `access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
   taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `op_taint a.po_taint dop = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> simp[taint_ok_def] >> metis_tac[]) >>
  `ptr_value_transport births positions (op_prov TG dop) {} d dt` by
    (qpat_assum `ptr_mixed_vars _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac ptr_mixed_vars_eval) >>
     disch_then (qspec_then `dop` mp_tac) >>
     simp[ptr_lookup_transport_def]) >>
  `!aid pos sz. FLOOKUP positions (Allocation aid) = SOME (pos,sz) ==>
    pos + sz < dimword(:256)` by
    (drule ptr_paired_prefix_placements >> strip_tac >>
     rpt strip_tac >> irule ptr_stage_placements_strict_bound >>
     rpt (goal_assum (drule_at Any))) >>
  `LENGTH H = LENGTH h /\ 0 < LENGTH h /\ LAST h = a /\ LAST ht = at /\
   LENGTH ht = SUC (LENGTH done)` by
    (drule ptr_structural_trace_source >>
     drule ptr_structural_trace_target >>
     metis_tac[ptr_chrono_history_end, ptr_paired_prefix_def,
       ptr_paired_samples_def, ptr_sample_list_def]) >>
  `!j. j < w2n n ==> read_byte (w2n d+j) z.po_state.vs_memory =
    read_byte (w2n dt+j) zt.po_state.vs_memory` by
    fs[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  drule_all ptr_buffer_copy_write_event >>
  disch_then (qspec_then `entries` strip_assume_tac) >>
  qexistsl_tac [`z`,`TG`,`extra`] >>
  irule ptr_buffer_copy_prefix_attach >>
  qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ h a ht at _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >>
  fs[] >> simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >> metis_tac[]
QED

Theorem ptr_paired_buffer_copy_prefix_normalize:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ~in_revert_forward a.po_fn a.po_state /\
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_paired_prefix_buffer_copy >> strip_tac >>
  `fn_inst_wf z.po_fn` by
    (qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ (_ ++ [_]) _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac ptr_paired_prefix_transcript) >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_reachable >> strip_tac >>
     fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> strip_tac >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ (_ ++ [_]) _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac ptr_paired_prefix_normalize) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`[z] ++ delta`, `ptr_gap_scan bb (LENGTH delta) z`,
    `tokens`, `registry`, `births`, `PT`, `TG'`, `saved`, `entries`,
    `[(tokens,registry,births,PT,TG',saved,entries)] ++ snapshots`, `calls`, `ws ++ extra`] >>
  simp[APPEND_ASSOC, ptr_gap_scan_fields]
QED

