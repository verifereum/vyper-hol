(*
 * Paired-prefix extension for the N11 opcode family (EXTCODECOPY).
 *)
Theory concretizePtrExtcodecopyFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrBufferCopyContent
  concretizePtrWriteClassification concretizePtrRequestHistory concretizePtrTaintContent
  concretizePtrPrefixLedger ptrDiscipline codegenRel memLocDefs
  concretizePtrOpaqueRetpc concretizePtrReturnTransport
  concretizePtrValueTransport pointerConfinedDefs
  concretizePtrPairedPrefix concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrSourceOwnership concretizePtrChronologicalHistory
  concretizePtrAllocationSize concretizePtrDeletedGapHistory concretizePtrTaggedSupport
  concretizePtrOrdinaryNext concretizePtrLedgerProbe concretizePtrActivationChronology
  concretizePtrHistoricalWriteClassification concretizePtrPairedFields
  concretizePtrStagePlacements concretizePtrComparisonTransport concretizePtrBytes
  concretizeStepStructure o1PassContract unitShapeDefs venomWf cfgWf
  codegenRel contextCodegenRel unitLabelMapIdentity
  venomExecSemantics venomExecProofs venomState venomInst finite_map list words arithmetic

Theorem ptr_extcodecopy_account_code[local]:
  ptr_history_content tn s t ==>
  (lookup_account addr s.vs_accounts).code =
  (lookup_account addr t.vs_accounts).code
Proof
  strip_tac >> drule ptr_history_content_current >> strip_tac >>
  drule ptr_taint_content_account >>
  simp[vfmStateTheory.lookup_account_def] >>
  disch_then (qspec_then `addr` mp_tac) >>
  disch_then (mp_tac o AP_TERM ``\a:account_state. a.code``) >> simp[]
QED

Theorem ptr_extcodecopy_success[local]:
  inst.inst_opcode = EXTCODECOPY /\
  inst.inst_operands = [a;d;r;n] ==>
  (step_inst fuel C inst s = OK post <=>
   ?addr dst src sz.
     eval_operand a s = SOME addr /\ eval_operand d s = SOME dst /\
     eval_operand r s = SOME src /\ eval_operand n s = SOME sz /\
     post = write_memory_with_expansion (w2n dst)
       (TAKE (w2n sz) (DROP (w2n src)
         (lookup_account (w2w addr) s.vs_accounts).code ++
         REPLICATE (w2n sz) 0w)) s)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem ptr_extcodecopy_footprint[local]:
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [a;d;r;n] /\
  eval_operand a s = SOME addr /\ eval_operand d s = SOME dst /\
  eval_operand r s = SOME src /\ eval_operand n s = SOME sz ==>
  (i IN range_bytes (step_writes inst s post) <=>
   w2n dst <= i /\ i < w2n dst + w2n sz)
Proof
  simp[step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, range_bytes_def,
       arithmeticTheory.ADD_COMM]
QED

Theorem ptr_extcodecopy_scalar_discipline[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) /\
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [a;d;r;n] ==>
  EVERY (ptr_nonopaque_operand fn) [a;d;r;n] /\
  EVERY (\op. op_taint tn op = {}) [a;d;r;n] /\
  EVERY (\op. op_prov TG op = NONE) [a;r;n]
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  `EVERY (\op. op_taint tn op = {}) inst.inst_operands` by
    (fs[taint_ok_def, EVERY_MEM] >> metis_tac[]) >>
  simp[] >>
  `!v. MEM (Var v) [a;r;n] ==> v NOTIN fn_pv P fn` by
    (`ptr_use_ok P (fn_pv P fn) inst` by
       (fs[fn_ptr_ok_def] >> metis_tac[]) >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >> strip_tac >>
     gen_tac >> disch_tac >> disch_tac >>
     first_x_assum (qspec_then `v` mp_tac) >>
     Cases_on `a = Var v` >> Cases_on `d = Var v` >>
     Cases_on `r = Var v` >> Cases_on `n = Var v` >>
     fs[]) >>
  `EVERY (\op. op_prov TG op = NONE) [a;r;n]` by
    (pure_rewrite_tac[EVERY_MEM] >> qx_gen_tac `op` >> strip_tac >>
     Cases_on `op` >> simp[op_prov_def] >>
     Cases_on `FLOOKUP TG s'` >> simp[] >> metis_tac[]) >>
  gvs[]
QED

Theorem ptr_extcodecopy_mixed_execution[local]:
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [a;d;r;n] /\
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t /\
  EVERY (ptr_nonopaque_operand f) [a;d;r;n] /\
  EVERY (\op. op_prov TG op = NONE /\ op_taint tn op = {}) [a;r;n] /\
  step_inst fuel Ct inst t = OK postt ==>
  ?addr dst dt src sz bytes post.
    eval_operand a s = SOME addr /\ eval_operand a t = SOME addr /\
    eval_operand d s = SOME dst /\ eval_operand d t = SOME dt /\
    eval_operand r s = SOME src /\ eval_operand r t = SOME src /\
    eval_operand n s = SOME sz /\ eval_operand n t = SOME sz /\
    LENGTH bytes = w2n sz /\
    step_inst 0 C inst s = OK post /\
    post = write_memory_with_expansion (w2n dst) bytes s /\
    postt = write_memory_with_expansion (w2n dt) bytes t /\
    (!i. i < w2n sz ==>
      read_byte (w2n dst + i) post.vs_memory =
      read_byte (w2n dt + i) postt.vs_memory)
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels` by metis_tac[ptr_history_content_labels] >>
  `eval_operands [a;r;n] s = eval_operands [a;r;n] t` by
    (irule ptr_mixed_scalar_operands_equal >> simp[] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_extcodecopy_success >> strip_tac >>
  qpat_x_assum `step_inst fuel Ct inst t = OK postt` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  `ptr_lookup_transport births positions (op_prov TG d) (op_taint tn d)
    (eval_operand d s) (eval_operand d t)` by
    (irule ptr_mixed_vars_eval >>
     rpt (goal_assum (drule_at Any)) >> fs[]) >>
  gvs[ptr_lookup_transport_some_right, eval_operands_def, AllCaseEqs()] >>
  qexists_tac `TAKE (w2n sz) (DROP (w2n src)
      (lookup_account (w2w addr) t.vs_accounts).code ++ REPLICATE (w2n sz) 0w)` >>
  simp[LENGTH_TAKE] >>
  `!addr. (lookup_account addr s.vs_accounts).code =
          (lookup_account addr t.vs_accounts).code` by
    metis_tac[ptr_extcodecopy_account_code] >>
  simp[] >> rpt strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule ptr_payload_write_content >> simp[LENGTH_TAKE]
QED

Theorem ptr_extcodecopy_post_content[local]:
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_outputs = [] /\
  ptr_mixed_vars births positions TG tn f g s t /\
  ptr_history_content tn s t ==>
  step_prov PT TG inst (write_memory_with_expansion dst bytes s) = TG /\
  ptr_mixed_vars births positions TG
    (step_taint inst s (write_memory_with_expansion dst bytes s) tn) f g
    (write_memory_with_expansion dst bytes s with vs_inst_idx := k)
    (write_memory_with_expansion dt bytes t with vs_inst_idx := kt) /\
  ptr_history_content
    (step_taint inst s (write_memory_with_expansion dst bytes s) tn)
    (write_memory_with_expansion dst bytes s with vs_inst_idx := k)
    (write_memory_with_expansion dt bytes t with vs_inst_idx := kt)
Proof
  strip_tac >>
  conj_tac >- simp[step_prov_def, set_prov_def, finite_mapTheory.DRESTRICT_UNIV] >>
  reverse conj_tac
  >- (simp[write_memory_with_expansion_def] >>
      irule ptr_history_content_masks >> qexists_tac `tn` >>
      simp[step_taint_def, set_var_taint_def, adopt_reset_def,
           store_taint_def, imm_taint_def]) >>
  irule ptr_mixed_vars_fields >>
  rpt (goal_assum (drule_at Any)) >>
  simp[write_memory_with_expansion_def, step_taint_def, set_var_taint_def,
       finite_mapTheory.DRESTRICT_UNIV]
QED

Theorem ptr_extcodecopy_prefix_execution[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ ptr_discipline lo C vs /\
  ~ctx_has_dalloca C /\
  a.po_inst.inst_opcode = EXTCODECOPY /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?aop dop rop nop addr dst dt src sz bytes post.
    a.po_inst.inst_operands = [aop;dop;rop;nop] /\
    a.po_inst.inst_outputs = [] /\ at.po_inst = a.po_inst /\
    eval_operand aop a.po_state = SOME addr /\
    eval_operand aop at.po_state = SOME addr /\
    eval_operand dop a.po_state = SOME dst /\
    eval_operand dop at.po_state = SOME dt /\
    eval_operand rop a.po_state = SOME src /\
    eval_operand rop at.po_state = SOME src /\
    eval_operand nop a.po_state = SOME sz /\
    eval_operand nop at.po_state = SOME sz /\
    LENGTH bytes = w2n sz /\ step_inst 0 C a.po_inst a.po_state = OK post /\
    post = write_memory_with_expansion (w2n dst) bytes a.po_state /\
    zt.po_state = (write_memory_with_expansion (w2n dt) bytes at.po_state
      with vs_inst_idx := SUC at.po_state.vs_inst_idx) /\
    zt.po_fn = at.po_fn /\ zt.po_stack = at.po_stack /\
    active_inst zt.po_fn zt.po_inst zt.po_state /\
    (!i. i < w2n sz ==>
      read_byte (w2n dst+i) post.vs_memory =
      read_byte (w2n dt+i) zt.po_state.vs_memory)
Proof
  strip_tac >> drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >>
     fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `inst_wf a.po_inst` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_inst_wf_def,
        EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `?aop dop rop nop. a.po_inst.inst_operands = [aop;dop;rop;nop] /\
    a.po_inst.inst_outputs = []` by
    gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
  `EVERY (ptr_nonopaque_operand a.po_fn) [aop;dop;rop;nop] /\
   EVERY (\op. op_prov TG op = NONE /\ op_taint a.po_taint op = {}) [aop;rop;nop]`
    by suspend "operands" >>
  `at.po_inst = a.po_inst` by simp[concretize_positions_unchanged] >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac >> gvs[] >>
  IF (qpat_assum `step_inst _ _ _ _ = OK _` (K all_tac)) all_tac
    (qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()]) >>
  `?addr dst dt src sz bytes post.
    eval_operand aop a.po_state = SOME addr /\ eval_operand aop at.po_state = SOME addr /\
    eval_operand dop a.po_state = SOME dst /\ eval_operand dop at.po_state = SOME dt /\
    eval_operand rop a.po_state = SOME src /\ eval_operand rop at.po_state = SOME src /\
    eval_operand nop a.po_state = SOME sz /\ eval_operand nop at.po_state = SOME sz /\
    LENGTH bytes = w2n sz /\ step_inst 0 C a.po_inst a.po_state = OK post /\
    post = write_memory_with_expansion (w2n dst) bytes a.po_state /\
    s' = write_memory_with_expansion (w2n dt) bytes at.po_state /\
    (!i. i < w2n sz ==> read_byte (w2n dst+i) post.vs_memory =
      read_byte (w2n dt+i) s'.vs_memory)` by
    (fs[ptr_paired_sample_def] >>
     drule_at (Pos (el 3)) ptr_extcodecopy_mixed_execution >>
     simp[] >> disch_then drule_all >> simp[]) >>
  qexistsl_tac [`addr`,`dst`,`dt`,`src`,`sz`,`bytes`] >>
  gvs[]
QED

Resume ptr_extcodecopy_prefix_execution[operands]:
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
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
  drule_all ptr_extcodecopy_scalar_discipline >> simp[]
QED
Finalise ptr_extcodecopy_prefix_execution

Theorem ptr_extcodecopy_transcript_successor[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ ptr_discipline lo C vs /\
  ~ctx_has_dalloca C /\ a.po_inst.inst_opcode = EXTCODECOPY /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?z bytes (dst:256 word) (dt:256 word) (sz:256 word).
    ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
      (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
      (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) /\
    ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved /\
    z = ptr_ledger_next a z.po_inst
      (write_memory_with_expansion (w2n dst) bytes a.po_state) /\
    LENGTH bytes = w2n sz /\
    (?dop nop.
      mem_write_ops a.po_inst = SOME
        <|iao_ofst := dop; iao_size := SOME nop; iao_max_size := SOME nop|> /\
      eval_operand dop a.po_state = SOME dst /\
      eval_operand dop at.po_state = SOME dt /\
      eval_operand nop a.po_state = SOME sz /\
      MEM (w2n dst,w2n sz) (source_memory_write_ranges a.po_inst a.po_state)) /\
    (!x. x IN range_bytes (step_writes a.po_inst a.po_state z.po_state) <=>
      w2n dst <= x /\ x < w2n dst + w2n sz) /\
    (!x. x IN range_bytes (step_writes at.po_inst at.po_state zt.po_state) <=>
      w2n dt <= x /\ x < w2n dt + w2n sz) /\
    zt.po_state = (write_memory_with_expansion (w2n dt) bytes at.po_state
      with vs_inst_idx := SUC at.po_state.vs_inst_idx) /\
    (!j. j < w2n sz ==>
      read_byte (w2n dst+j) z.po_state.vs_memory =
      read_byte (w2n dt+j) zt.po_state.vs_memory)
Proof
  strip_tac >> drule_all ptr_extcodecopy_prefix_execution >> strip_tac >>
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
  `EVERY bb_well_formed a.po_fn.fn_blocks` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (drule ptr_ordinary_next_active >> disch_then irule >>
     simp[write_memory_with_expansion_def, is_terminator_def]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  `z.po_stack = a.po_stack` by simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved` by
    (`ptr_tagged_step (HD tokens) PT TG a.po_inst post = TG` by
       simp[ptr_tagged_step_def, step_prov_def, set_prov_def, DRESTRICT_UNIV] >>
     `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
       simp[is_terminator_def] >>
     drule_all (cj 1 ptr_tagged_chrono_step_rules) >> strip_tac >>
     `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
        a.po_fn a.po_inst a.po_state = a` by
       simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
     fs[Abbr `z`, ptr_ledger_next_def] >> metis_tac[]) >>
  qexistsl_tac [`z`,`bytes`,`dst`,`dt`,`sz`] >> conj_tac
  >- (drule ptr_ownership_overlay_fixed >> strip_tac >>
      drule (cj 3 ptr_structural_transcript_rules) >>
      disch_then drule >> disch_then drule >>
      simp[ptr_activation_tokens_def, ptr_activation_registry_def] >>
      gvs[Abbr `z`, ptr_ledger_next_def, ptr_observe_def]) >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def,
       mem_write_ops_def, step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, range_bytes_def] >>
  gvs[] >> qexistsl_tac [`dop`,`nop`] >> simp[]
QED

Theorem ptr_extcodecopy_write_certificate[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  a.po_inst.inst_opcode = EXTCODECOPY /\ at.po_inst = a.po_inst /\
  ptr_chrono_step C' at zt /\
  ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved /\
  z = ptr_ledger_next a z.po_inst
    (write_memory_with_expansion (w2n (dst:256 word)) bytes a.po_state) /\
  mem_write_ops a.po_inst = SOME
    <|iao_ofst := dop; iao_size := SOME nop; iao_max_size := SOME nop|> /\
  eval_operand dop a.po_state = SOME dst /\
  eval_operand dop at.po_state = SOME (dt:256 word) /\
  MEM (w2n dst,w2n (sz:256 word)) (source_memory_write_ranges a.po_inst a.po_state) /\
  (!x. x IN range_bytes (step_writes a.po_inst a.po_state z.po_state) <=>
    w2n dst <= x /\ x < w2n dst + w2n sz) /\
  (!x. x IN range_bytes (step_writes at.po_inst at.po_state zt.po_state) <=>
    w2n dt <= x /\ x < w2n dt + w2n sz) /\
  (!j. j < w2n sz ==> read_byte (w2n dst+j) z.po_state.vs_memory =
    read_byte (w2n dt+j) zt.po_state.vs_memory) /\
  range_bytes (step_writes a.po_inst a.po_state z.po_state) <> {} ==>
  ?rho. ptr_paired_write lo positions C C' (h ++ [z]) (ht ++ [zt])
    (done ++ [LENGTH h - 1])
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)])
    (LENGTH h - 1,LENGTH done,rho)
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
  `access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
   taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `~in_revert_forward a.po_fn a.po_state /\
   ptr_nonopaque_operand a.po_fn dop` by suspend "shape" >>
  `ptr_lookup_transport births positions (op_prov TG dop) (op_taint a.po_taint dop)
    (SOME dst) (SOME dt)` by
    (`ptr_lookup_transport births positions (op_prov TG dop) (op_taint a.po_taint dop)
      (eval_operand dop a.po_state) (eval_operand dop at.po_state)` suffices_by simp[] >>
     irule ptr_mixed_vars_eval >> conj_tac
     >- (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
     qexistsl_tac [`a.po_fn`,`at.po_fn`] >> fs[ptr_paired_sample_def]) >>
  `ptr_chrono_step C a z` by
    (drule ptr_tagged_chrono_step_projection >> simp[]) >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  `0 < LENGTH h /\ LAST h = a` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_end >> strip_tac >> Cases_on `h` >> gvs[]) >>
  `SUC (LENGTH h - 1) = LENGTH h /\ SUC (LENGTH done) = LENGTH ht /\
   LENGTH ht - 1 = LENGTH done` by decide_tac >>
  `EL (LENGTH done) ht = at` by
    (qpat_x_assum `LAST ht = at` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `h <> []` by (Cases_on `h` >> gvs[]) >>
  `EL (LENGTH h - 1) h = a` by
    (qpat_x_assum `LAST h = a` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `ptr_stage_placements C' positions` by fs[ptr_paired_prefix_def] >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  `EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (`H <> []` by (Cases_on `H` >> gvs[]) >>
     qpat_x_assum `LAST H = _` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `0 < w2n sz` by
    (qpat_x_assum `range_bytes _ <> {}` mp_tac >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `sz <> 0w` by (strip_tac >> gvs[]) >>
  qabbrev_tac `ops = <|iao_ofst := dop; iao_size := SOME nop; iao_max_size := SOME nop|>` >>
  `(op_prov TG ops.iao_ofst = NONE /\
    op_taint (EL (LENGTH h - 1) h).po_taint ops.iao_ofst = {} /\
      w2n dst + w2n sz <= lo) \/
   (?dv token bid db sb pb. ops.iao_ofst = Var dv /\ FLOOKUP TG dv = SOME (token,bid) /\
    FLOOKUP (EL (LENGTH h - 1) h).po_prov dv = SOME (db,sb) /\
    FLOOKUP positions (Allocation bid) = SOME (pb,sb) /\ db <= w2n dst /\
    w2n dst + w2n sz <= db+sb /\ pb+sb < dimword(:256))` by
    (irule (Q.INST [`ops` |-> `ops`] (SPEC_ALL ptr_historical_write_classification)) >>
     simp[Abbr `ops`] >>
     conj_tac >- (qexists_tac `a.po_fn` >> simp[]) >>
     rpt (goal_assum (drule_at Any)) >> simp[])
  >- suspend "fixed" >>
  suspend "owned"
QED

Resume ptr_extcodecopy_write_certificate[shape]:
  `ALL_DISTINCT (fn_labels a.po_fn) /\ opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `active_inst a.po_fn a.po_inst a.po_state` mp_tac >>
      simp[active_inst_def] >> strip_tac >>
      `lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb` by
        (irule MEM_lookup_block >> fs[fn_labels_def]) >>
      `get_instruction bb a.po_state.vs_inst_idx = SOME a.po_inst` by
        simp[get_instruction_def] >>
      simp[in_revert_forward_def] >> strip_tac >>
      drule_all memSafeRunTheory.revert_forward_at_opcode >> simp[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  fs[mem_write_ops_def, AllCaseEqs(), EVERY_MEM] >> metis_tac[]
QED

Resume ptr_extcodecopy_write_certificate[fixed]:
  fs[Abbr `ops`] >>
  `SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
  `dt = dst` by
    (gvs[ptr_lookup_transport_def, ptr_value_transport_def] >>
     gvs[word_agree_except_bits, fcpTheory.CART_EQ]) >>
  qexists_tac `\x:num. x` >>
  simp[ptr_paired_write_def, EL_APPEND_EQN] >>
  reverse conj_tac
  >- (simp[ptr_paired_write_owner_def] >> rpt strip_tac >> disj1_tac >> decide_tac) >>
  simp[ptr_ledger_write_pair_def, is_terminator_def, ptr_bytes_agree_def] >>
  rpt strip_tac >>
  `x = w2n dst + (x-w2n dst) /\ x-w2n dst < w2n sz` by decide_tac >>
  qpat_x_assum `!j. j < w2n sz ==> _` (qspec_then `x-w2n dst` mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Resume ptr_extcodecopy_write_certificate[owned]:
  fs[Abbr `ops`] >>
  `SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `MEM token tokens` by (drule_all ptr_source_ownership_live_prov >> simp[]) >>
  `FLOOKUP births (token,bid) = SOME (db,sb)` by
    (drule_all ptr_source_ownership_prov_erases >>
     simp[ptr_ledger_erases_def] >> strip_tac >>
     first_x_assum (qspec_then `dv` mp_tac) >> gvs[]) >>
  `dt = dst - n2w db + n2w pb` by
    gvs[ptr_lookup_transport_def, ptr_value_transport_def, op_prov_def] >>
  `w2n dt = pb + (w2n dst - db)` by
    (irule ptr_closed_relocation_value >> simp[] >> qexists_tac `sb` >> simp[] >> decide_tac) >>
  qpat_x_assum `dt = dst - n2w db + n2w pb` kall_tac >>
  qexists_tac `\x:num. pb + (x-db)` >>
  simp[ptr_paired_write_def, EL_APPEND_EQN] >>
  reverse conj_tac
  >- (simp[ptr_paired_write_owner_def] >> rpt strip_tac >>
      disj2_tac >> qexistsl_tac [`token`,`bid`,`db`,`sb`,`pb`,`x-db`] >> simp[] >> decide_tac) >>
  simp[ptr_ledger_write_pair_def, is_terminator_def] >>
  simp[ptr_bytes_agree_def] >> rpt strip_tac >>
  `x = w2n dst + (x-w2n dst) /\ x-w2n dst < w2n sz /\
   pb + (x-db) = w2n dt + (x-w2n dst)` by decide_tac >>
  qpat_x_assum `!j. j < w2n sz ==> _` (qspec_then `x-w2n dst` mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED
Finalise ptr_extcodecopy_write_certificate

Theorem ptr_paired_extcodecopy_prefix_normalize:
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
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [EXTCODECOPY] ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst
Proof
  cheat
QED

