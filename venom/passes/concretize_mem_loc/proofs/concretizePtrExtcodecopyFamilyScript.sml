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
  concretizeStepStructure o1PassContract unitShapeDefs venomWf cfgWf
  codegenRel contextCodegenRel unitLabelMapIdentity
  venomExecSemantics venomState venomInst finite_map list words

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

