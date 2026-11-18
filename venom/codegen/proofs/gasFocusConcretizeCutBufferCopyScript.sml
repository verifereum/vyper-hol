Theory gasFocusConcretizeCutBufferCopy
Ancestors
  gasFocusConcretizeTaggedSupport concretizePtrParamSupport
  concretizePtrBufferCopyContent concretizePtrOrdinaryNext
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrPrefixWriteAttach
  concretizePtrStructuralTranscript concretizePtrStructuralTrace concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizePtrOperationalOpcodes
  concretizePtrLedgerProbe concretizePtrSourceOwnership concretizePtrPrefixLedger
  concretizePtrRequestHistory concretizePtrOpaqueRetpc concretizePtrValueTransport
  concretizePtrWriteFootprint concretizePtrOwnershipErasure concretizePtrPlacementBounds
  concretizePtrBytes concretizePtrEventEmbedding concretizePtrActivationChronology
  concretizePtrComparisonTransport
  concretizeStepStructure o1PassContract unitShapeDefs contextCodegenRel codegenRel
  ptrDiscipline ptrDisciplineEmptyTaint pointerConfinedDefs unitLabelMapIdentity
  o1ContractSimplifyCfgSrcFrame memLocDefs
  venomExecSemantics venomExecProps venomState venomWf venomInst opcodeClass
  list finite_map words pred_set arithmetic

Theorem focus_buffer_copy_execution[local]:
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
    (!i. i < w2n n ==>
      read_byte (w2n d+i) s'.vs_memory =
      read_byte (w2n dt+i) t'.vs_memory)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_code = t.vs_code /\
   s.vs_data_section = t.vs_data_section /\ s.vs_returndata = t.vs_returndata` by
    metis_tac[ptr_history_content_call_ctx, ptr_history_content_code,
      ptr_history_content_data_section, ptr_history_content_returndata] >>
  `inst.inst_opcode <> INVOKE` by fs[MEM] >>
  `step_inst_base inst t = OK t'` by metis_tac[step_inst_non_invoke] >>
  `?d dt r n. eval_operand dop s = SOME d /\ eval_operand dop t = SOME dt /\
    eval_operand sop s = SOME r /\ eval_operand sop t = SOME r /\
    eval_operand nop s = SOME n /\ eval_operand nop t = SOME n` by
    (qpat_x_assum `step_inst_base inst t = OK t'` mp_tac >>
     fs[MEM] >> pure_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[] >> pure_rewrite_tac[opcode_case_def] >>
     simp[AllCaseEqs()] >> Cases_on `eval_operand dop s` >> gvs[] >> metis_tac[]) >>
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
         goal_assum (drule_at Any) >> simp[ADD_COMM])
     >- (drule_all ptr_codecopy_content >> strip_tac >> gvs[] >>
         goal_assum (drule_at Any) >> simp[ADD_COMM])
     >- (drule_all ptr_dloadbytes_content >> strip_tac >> gvs[] >>
         goal_assum (drule_at Any) >> simp[ADD_COMM]) >>
     `w2n r + w2n n <= LENGTH s.vs_returndata` by gvs[] >>
     drule_all ptr_returndatacopy_content >> strip_tac >> gvs[] >>
     goal_assum (drule_at Any) >> simp[ADD_COMM]) >>
  gvs[] >> qexists `s'` >> simp[step_inst_non_invoke]
QED

Theorem focus_buffer_copy_post_memory[local]:
  MEM inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  step_inst fuel C inst s = OK s' ==>
  s' = s with vs_memory := s'.vs_memory
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by fs[MEM] >>
  `step_inst_base inst s = OK s'` by metis_tac[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  fs[MEM] >> pure_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[write_memory_with_expansion_def]
QED

Theorem focus_buffer_copy_history_content[local]:
  ptr_history_content tn s t /\
  MEM inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  s' = s with vs_memory := s'.vs_memory /\
  t' = t with vs_memory := t'.vs_memory ==>
  ptr_history_content (step_taint inst s s' tn) s' t'
Proof
  strip_tac >> once_asm_rewrite_tac[] >> simp[] >>
  irule ptr_history_content_masks >> goal_assum (drule_at Any) >>
  fs[MEM] >> simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def]
QED

Theorem focus_buffer_copy_access_range[local]:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = dop /\
  MEM (off,len) (source_memory_write_ranges inst s) /\ len <> 0 /\
  (lo < off + len \/ op_prov G dop <> NONE) ==>
  ?v b sz. dop = Var v /\ FLOOKUP G v = SOME (b,sz) /\
    b <= off /\ off + len <= b + sz
Proof
  strip_tac >>
  `?ops'. mem_write_ops inst = SOME ops' /\ op_prov G ops'.iao_ofst <> NONE \/
           lo < off + len` by metis_tac[] >>
  `?ops' v b sz. mem_write_ops inst = SOME ops' /\ ops'.iao_ofst = Var v /\
     FLOOKUP G v = SOME (b,sz) /\ b <= off /\ off + len <= b + sz` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     simp[access_ok_def] >> strip_tac >>
     qpat_x_assum `!i n. MEM (i,n) (source_memory_write_ranges _ _) ==> _`
       (qspecl_then [`off`,`len`] mp_tac) >> simp[]) >> gvs[] >> metis_tac[]
QED

Theorem focus_buffer_copy_range_owner[local]:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_ledger_erases (dyn_floor C vs) births TG a.po_prov /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  mem_write_ops a.po_inst = SOME ops /\ ops.iao_ofst = dop /\
  MEM (w2n d,len) (source_memory_write_ranges a.po_inst a.po_state) /\
  ptr_value_transport births positions (op_prov TG dop) {} d dt /\
  (!aid pos sz. FLOOKUP positions (Allocation aid) = SOME (pos,sz) ==>
    pos + sz < dimword(:256)) ==>
  ptr_paired_write_owner (dyn_floor C vs) lo positions (\x. w2n dt + (x-w2n d))
    {x | w2n d <= x /\ x < w2n d + len}
    (tokens,registry,births,PT,TG,saved,entries)
Proof
  strip_tac >> simp[ptr_paired_write_owner_def] >> gen_tac >> strip_tac >>
  `len <> 0` by decide_tac >>
  drule ptr_owner_op_projection >> disch_then (qspec_then `dop` strip_assume_tac) >>
  Cases_on `op_prov TG dop` >-
   (`dt = d` by fs[ptr_value_transport_scalar_empty] >>
    Cases_on `w2n d + len <= lo` >- (disj1_tac >> gvs[] >> decide_tac) >>
    `lo < w2n d + len` by decide_tac >>
    `?v b sz. dop = Var v /\ FLOOKUP a.po_prov v = SOME (b,sz) /\
       b <= w2n d /\ w2n d + len <= b + sz` by
      (irule focus_buffer_copy_access_range >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
    `dyn_floor C vs <= b` by gvs[ptr_owner_erases_def, op_prov_def] >>
    disj2_tac >> disj2_tac >> gvs[] >> decide_tac) >>
  rename1 `op_prov TG dop = SOME owner` >> PairCases_on `owner` >>
  qpat_x_assum `ptr_value_transport _ _ _ _ _ _` mp_tac >>
  simp[ptr_value_transport_def] >> strip_tac >>
  rename1 `FLOOKUP births (owner0,owner1) = SOME (b0,sz0)` >>
  `op_prov a.po_prov dop = SOME (b0,sz0)` by fs[ptr_owner_erases_def] >>
  `?v b sz. dop = Var v /\ FLOOKUP a.po_prov v = SOME (b,sz) /\
     b <= w2n d /\ w2n d + len <= b + sz` by
    (irule focus_buffer_copy_access_range >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  gvs[op_prov_def, ptr_value_transport_def] >>
  `MEM owner0 tokens` by (irule ptr_source_ownership_live_prov >> metis_tac[]) >>
  rename1 `FLOOKUP births (owner0,owner1) = SOME (src_base,src_size)` >>
  `pos + src_size < dimword(:256)` by metis_tac[] >>
  `w2n (d - n2w src_base + n2w pos) = pos + (w2n d - src_base)` by
    (irule ptr_closed_relocation_value >> simp[] >> qexists `src_size` >> simp[] >> decide_tac) >>
  disj2_tac >> disj1_tac >>
  qexistsl [`owner0`,`owner1`,`src_base`,`src_size`,`pos`,`x-src_base`] >>
  simp[] >> decide_tac
QED

Theorem focus_buffer_copy_write_pair[local]:
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
    (gen_tac >> irule ptr_copy_footprint_interval >> simp[] >> fs[MEM] >> metis_tac[]) >>
  `!x. x IN range_bytes (step_writes at.po_inst at.po_state zt.po_state) <=>
    w2n dt <= x /\ x < w2n dt + w2n n` by
    (gen_tac >> irule ptr_copy_footprint_interval >> simp[] >> fs[MEM] >> metis_tac[]) >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    (fs[MEM] >> simp[is_terminator_def]) >>
  simp[ptr_ledger_write_pair_def, ptr_bytes_agree_def] >> rpt strip_tac >>
  `x - w2n d < w2n n` by decide_tac >>
  qpat_x_assum `!i. i < w2n n ==> _` (qspec_then `x - w2n d` mp_tac) >> simp[]
QED

Theorem focus_buffer_copy_write_event[local]:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  dyn_floor C a.po_state = dyn_floor C vs /\
  ptr_ledger_erases (dyn_floor C vs) births TG a.po_prov /\
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
  Cases_on `range_bytes (step_writes a.po_inst a.po_state z.po_state) = {}`
  >- (qexists `[]` >> simp[]) >>
  `range_bytes (step_writes a.po_inst a.po_state z.po_state) =
    {x | w2n d <= x /\ x < w2n d + w2n n}` by
    (simp[EXTENSION] >> gen_tac >> irule ptr_copy_footprint_interval >>
     simp[] >> fs[MEM] >> metis_tac[]) >>
  `ptr_ledger_write_pair C Ct (\x. w2n dt + (x-w2n d)) a z at zt` by
    (irule focus_buffer_copy_write_pair >>
     qpat_assum `a.po_inst.inst_operands = [dop;sop;nop]` (irule_at Any) >>
     simp[] >> metis_tac[ADD_COMM]) >>
  `ptr_paired_write_owner (dyn_floor C a.po_state) lo positions (\x. w2n dt + (x-w2n d))
    (range_bytes (step_writes a.po_inst a.po_state z.po_state))
    (tokens,registry,births,PT,TG,saved,entries)` by
    (asm_rewrite_tac[] >> irule focus_buffer_copy_range_owner >>
     qpat_assum `ptr_source_ownership _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexists `<|iao_ofst := dop; iao_size := SOME nop; iao_max_size := SOME nop|>` >>
     simp[] >> fs[MEM] >> simp[mem_write_ops_def, source_memory_write_ranges_def,
       sized_source_write_range_def] >> metis_tac[]) >>
  qexists `[(LENGTH h - 1,LENGTH done,\x. w2n dt + (x-w2n d))]` >>
  `SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
  `h <> [] /\ ht <> []` by (conj_tac >> strip_tac >> fs[]) >>
  `EL (LENGTH h - 1) h = a /\ EL (LENGTH done) ht = at` by fs[LAST_EL, PRE_SUB1] >>
  simp[ptr_paired_write_def, EL_APPEND_EQN] >> metis_tac[]
QED

Theorem focus_buffer_copy_operand_discipline[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ ptr_static_support P fn TG /\
  MEM inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  inst.inst_operands = [dop;sop;nop] ==>
  EVERY (ptr_nonopaque_operand fn) [dop;sop;nop] /\
  op_prov TG sop = NONE /\ op_prov TG nop = NONE /\
  op_taint tn dop = {} /\ op_taint tn sop = {} /\ op_taint tn nop = {}
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >> fs[MEM]) >>
  `!v. (sop = Var v \/ nop = Var v) ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `fn_ptr_ok P fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!i. MEM i (fn_insts fn) ==> _` (qspec_then `inst` mp_tac) >>
     fs[MEM] >> simp[ptr_use_ok_def, is_pointer_preserving_op_def,
                    mem_write_ops_def, mem_read_ops_def] >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `!v'. _` (qspec_then `v` mp_tac) >>
     simp[] >> strip_tac >> gvs[] >>
     Cases_on `dop = Var v` >> gvs[] >> Cases_on `sop = Var v` >> gvs[] >>
     Cases_on `nop = Var v` >> gvs[]) >>
  `op_taint tn dop = {} /\ op_taint tn sop = {} /\ op_taint tn nop = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> fs[MEM] >> simp[taint_ok_def] >> metis_tac[]) >>
  simp[] >> Cases_on `sop` >> Cases_on `nop` >>
  gvs[op_prov_def, ptr_static_support_def] >> rpt conj_tac >>
  qmatch_goalsub_rename_tac `FLOOKUP TG v` >> Cases_on `FLOOKUP TG v` >> gvs[] >> metis_tac[]
QED

Theorem ptr_focus_buffer_copy_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\ callee_first names C.ctx_functions /\
  frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state /\
  ptr_ledger_erases (dyn_floor C vs) births TG a.po_prov /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  ptr_chrono_step C' at zt ==>
  ?z extra. ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG saved entries
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) calls (ws ++ extra)
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `dyn_floor C a.po_state = dyn_floor C vs` by
    (drule frame_reachable_initial_fmp >> simp[dyn_floor_def]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule_all ptr_focus_source_tagged_support >> strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  `inst_wf a.po_inst /\ fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn /\
   EVERY bb_well_formed a.po_fn.fn_blocks /\ ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_shape_ok_def, EVERY_MEM] >>
     metis_tac[]) >>
  `?dop sop nop. a.po_inst.inst_operands = [dop;sop;nop] /\ a.po_inst.inst_outputs = []` by
    (fs[MEM] >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  drule_all focus_buffer_copy_operand_discipline >> strip_tac >>
  `at.po_inst = a.po_inst /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ ~is_terminator a.po_inst.inst_opcode` by
    (fs[MEM] >> simp[concretize_positions_unchanged, is_terminator_def]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  suspend "edge"
QED

Resume ptr_focus_buffer_copy_step[edge]:
  `!fuel ret s. step_inst fuel C' a.po_inst at.po_state <> IntRet ret s` by
    (simp[step_inst_non_invoke] >> rpt strip_tac >>
     drule step_inst_base_intret_opcodes >> fs[MEM]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"] >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn a.po_state at.po_state /\
   ptr_history_content a.po_taint a.po_state at.po_state` by fs[ptr_paired_sample_def] >>
  `a.po_state.vs_labels = at.po_state.vs_labels` by metis_tac[ptr_history_content_labels] >>
  `IS_SOME (eval_operand dop a.po_state) = IS_SOME (eval_operand dop at.po_state)` by
    (drule_all ptr_mixed_vars_eval_presence >> disch_then (qspec_then `dop` mp_tac) >> simp[]) >>
  `eval_operand sop a.po_state = eval_operand sop at.po_state /\
   eval_operand nop a.po_state = eval_operand nop at.po_state` by
    (`!op. ptr_nonopaque_operand a.po_fn op /\ op_prov TG op = NONE /\
       op_taint a.po_taint op = {} ==>
       eval_operand op a.po_state = eval_operand op at.po_state` by
       (rpt strip_tac >> drule_all ptr_mixed_vars_eval >> simp[] >>
        Cases_on `eval_operand op a.po_state` >> Cases_on `eval_operand op at.po_state` >>
        simp[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]) >>
     fs[] >> metis_tac[]) >>
  `MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY]` by simp[] >>
  drule_all focus_buffer_copy_execution >> disch_then (qspec_then `C` strip_assume_tac) >>
  suspend "source"
QED

Resume ptr_focus_buffer_copy_step[source]:
  markerLib.RESUME_TAC >>
  `s''.vs_current_bb = a.po_state.vs_current_bb /\ s''.vs_prev_bb = a.po_state.vs_prev_bb /\
   s''.vs_allocas = a.po_state.vs_allocas /\ s''.vs_params = a.po_state.vs_params` by
    (qpat_assum `step_inst 0 C _ _ = OK _`
       (mp_then Any mp_tac focus_buffer_copy_post_memory) >>
     simp[] >> disch_then SUBST1_TAC >> simp[]) >>
  `s'.vs_current_bb = at.po_state.vs_current_bb /\ s'.vs_prev_bb = at.po_state.vs_prev_bb /\
   s'.vs_params = at.po_state.vs_params` by
    (qpat_assum `step_inst fuel C' _ _ = OK _`
       (mp_then Any mp_tac focus_buffer_copy_post_memory) >>
     simp[] >> disch_then SUBST1_TAC >> simp[]) >>
  `?i. active_inst a.po_fn i (s'' with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (irule ptr_ordinary_next_active >> metis_tac[]) >>
  qabbrev_tac `z = ptr_ledger_next a i s''` >>
  `ptr_chrono_step C a z` by
    (simp[Abbr `z`, ptr_ledger_next_def] >> once_rewrite_tac[ptr_chrono_step_cases] >>
     simp[ptr_observe_def, ptr_observation_component_equality] >> qexistsl [`s''`,`0`] >> simp[]) >>
  suspend "attach"
QED

Resume ptr_focus_buffer_copy_step[attach]:
  markerLib.RESUME_TAC >>
  `s'' = a.po_state with vs_memory := s''.vs_memory /\
   s' = at.po_state with vs_memory := s'.vs_memory` by
    (conj_tac >> irule focus_buffer_copy_post_memory >> simp[] >> metis_tac[]) >>
  `ptr_paired_sample positions z zt (tokens,registry,births,PT,TG,saved,entries)` by
    (simp[IgnAsm `s'' = _`, IgnAsm `s' = _`, ptr_paired_sample_def,
          Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
     reverse conj_tac
     >- (drule_all focus_buffer_copy_history_content >> disch_then ACCEPT_TAC) >>
     simp[IgnAsm `s'' = _`, IgnAsm `s' = _`, step_taint_def, set_var_taint_def, DRESTRICT_UNIV] >>
     irule ptr_mixed_vars_fields >> goal_assum (drule_at Any) >>
     qpat_x_assum `s'' = _` (once_rewrite_tac o single) >>
     qpat_x_assum `s' = _` (once_rewrite_tac o single) >> simp[]) >>
  `ptr_paired_params positions z zt (tokens,registry,births,PT,TG,saved,entries)` by
    fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  qpat_x_assum `s'' = a.po_state with vs_memory := _` kall_tac >>
  qpat_x_assum `s' = at.po_state with vs_memory := _` kall_tac >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved` by
    (`ptr_tagged_step (HD tokens) PT TG a.po_inst s'' = TG` by
       simp[ptr_tagged_step_def, step_prov_def, out_prov_def, set_prov_def, DRESTRICT_UNIV] >>
     qpat_assum `step_inst 0 C _ _ = OK _`
       (mp_then (Pos (el 4)) mp_tac ptr_tagged_chrono_step_next) >>
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
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`,`rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_paired_cursor lp z zt` by
    (drule ptr_ordinary_next_cursor >> disch_then irule >>
     simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def]) >>
  `ptr_value_transport births positions (op_prov TG dop) {} d dt` by
    (drule ptr_mixed_vars_eval >> disch_then (qspec_then `dop` mp_tac) >>
     simp[ptr_lookup_transport_def]) >>
  `!aid pos sz. FLOOKUP positions (Allocation aid) = SOME (pos,sz) ==>
    pos + sz < dimword(:256)` by
    (drule ptr_paired_prefix_placements >> strip_tac >>
     rpt strip_tac >> irule ptr_stage_placements_strict_bound >>
     rpt (goal_assum (drule_at Any))) >>
  `LENGTH H = LENGTH h /\ 0 < LENGTH h /\ LAST h = a /\ LAST ht = at /\
   LENGTH ht = SUC (LENGTH done)` by
    (drule ptr_structural_trace_source >> drule ptr_structural_trace_target >>
     metis_tac[ptr_chrono_history_end, ptr_paired_prefix_def,
       ptr_paired_samples_def, ptr_sample_list_def]) >>
  `!j. j < w2n n ==> read_byte (w2n d+j) z.po_state.vs_memory =
    read_byte (w2n dt+j) zt.po_state.vs_memory` by
    fs[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  drule_all focus_buffer_copy_write_event >>
  disch_then (qspec_then `entries` strip_assume_tac) >>
  qexistsl [`z`,`extra`] >>
  irule ptr_paired_prefix_write_attach >>
  qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ h a ht at _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >> metis_tac[]
QED

Finalise ptr_focus_buffer_copy_step
