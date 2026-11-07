(*
 * Paired-prefix extension for the N15 opcode family (CALL; STATICCALL).
 *)
Theory concretizePtrCallFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrMloadRecovery
  concretizePtrRequestCompletionProbe copyFwdEquiv venomInstProofs1
  concretizePtrLedgerProbe concretizePtrPrefixLedger
  concretizePtrBufferCopyContent venomCallOracleDefs venomExecSemantics
  concretizePtrRequestHistory concretizePtrTaggedSupport
  concretizePtrSourceOwnership concretizePtrAllocationSize concretizeStepStructure
  o1PassContract unitShapeDefs venomWf unitLabelMapIdentity venomInst
  venomExecProofs memSafeRun opcodeClass
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory ptrDiscipline
  list venomState contextCodegenRel codegenRel allocaRemapDefs
  pointerConfinedDefs memLocDefs concretizePtrOpaqueRetpc
  concretizePtrReturnTransport concretizePtrValueTransport finite_map pred_set

Theorem ptr_call_scalar_not_pointer[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  ((inst.inst_opcode = CALL /\ pre = [gas; addr; value]) \/
   (inst.inst_opcode = STATICCALL /\ pre = [gas; addr])) /\
  inst.inst_operands = pre ++ [aop; azop; rop; rzop] /\
  MEM (Var v) (pre ++ [azop; rzop]) ==>
  v NOTIN fn_pv P fn
Proof
  strip_tac >> strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  qpat_x_assum `fn_ptr_ok _ _` kall_tac >>
  fs[ptr_use_ok_def] >>
  qpat_x_assum `!v. _ ==> _` (qspec_then `v` mp_tac) >>
  simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def,
       Excl "FILTER"] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  fs[MEM] >> gvs[] >>
  rpt strip_tac >> gvs[]
QED

Theorem ptr_call_operand_transport:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  ((inst.inst_opcode = CALL /\ pre = [gas; addr; value]) \/
   (inst.inst_opcode = STATICCALL /\ pre = [gas; addr])) /\
  inst.inst_operands = pre ++ [aop; azop; rop; rzop] /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) /\
  ptr_mixed_vars births positions TG tn fn ft s t /\ s.vs_labels = t.vs_labels ==>
  (!op. MEM op inst.inst_operands ==>
    op_taint tn op = {} /\
    ptr_lookup_transport births positions (op_prov TG op) {}
      (eval_operand op s) (eval_operand op t)) /\
  eval_operands (pre ++ [azop; rzop]) s = eval_operands (pre ++ [azop; rzop]) t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >> fs[]) >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def, MEM] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> simp[] >>
      drule ptr_mixed_vars_eval >> simp[EVERY_MEM] >>
      disch_then (qspec_then `op` mp_tac) >> fs[EVERY_MEM]) >>
  `EVERY (\op. ptr_nonopaque_operand fn op /\ op_prov TG op = NONE /\
      op_taint tn op = {}) (pre ++ [azop; rzop])` by
    (pure_rewrite_tac[EVERY_MEM] >> qx_gen_tac `op` >> strip_tac >>
     `MEM op inst.inst_operands` by (gvs[] >> fs[MEM]) >>
     `ptr_nonopaque_operand fn op /\ op_taint tn op = {}` by fs[EVERY_MEM] >>
     simp[] >> Cases_on `op` >> simp[op_prov_def] >>
     Cases_on `FLOOKUP TG s'` >> simp[] >>
     metis_tac[ptr_call_scalar_not_pointer]) >>
  drule_all ptr_mixed_scalar_operands_equal >> simp[]
QED

Theorem ptr_paired_call_input_bytes:
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
  MEM a.po_inst.inst_opcode [CALL; STATICCALL] /\
  ~in_revert_forward a.po_fn a.po_state /\
  mem_read_ops a.po_inst = SOME ops /\ inst_read_op a.po_inst = SOME ops.iao_ofst /\
  MEM ops.iao_ofst a.po_inst.inst_operands /\
  eval_operand ops.iao_ofst a.po_state = SOME x /\
  eval_operand ops.iao_ofst at.po_state = SOME y /\
  MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
  read_memory (w2n x) n a.po_state = read_memory (w2n y) n at.po_state
Proof
  strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_ownership >> strip_tac >>
     drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `!j. j < n ==> w2n x + j NOTIN a.po_taint.t_mem` by
    (rpt strip_tac >>
     `w2n x <= w2n x + j /\ w2n x + j < w2n x + n` by decide_tac >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     fs[MEM] >> simp[taint_ok_def, about_to_revert_def] >>
     disj2_tac >> qexistsl_tac [`w2n x`, `n`, `w2n x + j`] >> simp[]) >>
  `!j. j < n ==> read_byte (w2n x + j) a.po_state.vs_memory =
     read_byte (w2n y + j) at.po_state.vs_memory` by
    (`a.po_inst.inst_opcode <> ASSIGN` by fs[MEM] >>
     drule ptr_paired_read_range_masked_bytes >>
     simp[] >> gvs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  irule LIST_EQ >> simp[read_memory_def, LENGTH_TAKE_EQ] >>
  rpt strip_tac >>
  simp[take_drop_replicate_el, GSYM read_byte_def, mem_byte_at_def]
QED

Theorem ptr_call_history_execution:
  ptr_history_content tn s t /\
  ((inst.inst_opcode = CALL /\ st = s.vs_call_ctx.cc_static) \/
   (inst.inst_opcode = STATICCALL /\ st)) /\
  inst.inst_outputs = [out] /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n at) (w2n az) t /\
  exec_ext_call inst t (gt:256 word) addr value at az (rt:256 word) (rz:256 word) st = OK target ==>
  ?w u v.
    target = update_var out w v /\
    exec_ext_call inst s (gas:256 word) addr value ao az (ro:256 word) rz st = OK (update_var out w u) /\
    u.vs_returndata = v.vs_returndata /\
    ptr_history_content (step_taint inst s (update_var out w u) tn)
      (update_var out w u) target /\
    (!i. i < MIN (w2n rz) (LENGTH u.vs_returndata) ==>
      read_byte (w2n ro+i) u.vs_memory = read_byte (w2n rt+i) v.vs_memory)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `consume_call_outcome (venom_call_request s addr value ao az st)
    (w2n ro) (w2n rz) s` >>
  Cases_on `consume_call_outcome (venom_call_request t addr value at az st)
    (w2n rt) (w2n rz) t` >>
  drule_all ptr_history_call_completion >> strip_tac >>
  `target = update_var out q r'` by
    (gvs[exec_ext_call_def, Excl "consume_call_outcome_eq"]) >>
  qexistsl_tac [`q`,`r`,`r'`] >>
  simp[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  conj_tac
  >- (irule ptr_history_content_masks >>
      goal_assum (drule_at Any) >>
      fs[step_taint_def, store_taint_def, adopt_reset_def,
         imm_taint_def, ptr_call_adopted_def, update_var_def,
         Excl "consume_call_outcome_eq"] >>
      simp[SF CONJ_ss]) >>
  qpat_x_assum `consume_call_outcome _ _ _ s = _` mp_tac >>
  qpat_x_assum `consume_call_outcome _ _ _ t = _` mp_tac >>
  simp[consume_call_outcome_eq] >> rpt strip_tac >> gvs[] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule ptr_payload_write_content >> simp[LENGTH_TAKE_EQ]
QED

Theorem ptr_paired_call_step:
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
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [CALL; STATICCALL] ==>
  ?post TG' ops (x:256 word) (y:256 word) (n:256 word) k.
    step_inst 0 C a.po_inst a.po_state = OK post /\
    at.po_inst = a.po_inst /\
    active_inst a.po_fn a.po_inst a.po_state /\
    frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
      a.po_fn a.po_inst a.po_state /\
    ~in_revert_forward a.po_fn a.po_state /\
    post.vs_allocas = a.po_state.vs_allocas /\
    post.vs_current_bb = a.po_state.vs_current_bb /\
    post.vs_prev_bb = a.po_state.vs_prev_bb /\
    zt.po_stack = at.po_stack /\ zt.po_fn = at.po_fn /\
    zt.po_state.vs_current_bb = at.po_state.vs_current_bb /\
    zt.po_state.vs_prev_bb = at.po_state.vs_prev_bb /\
    zt.po_state.vs_inst_idx = SUC at.po_state.vs_inst_idx /\
    active_inst zt.po_fn zt.po_inst zt.po_state /\
    ptr_history_content (step_taint a.po_inst a.po_state post a.po_taint) post zt.po_state /\
    post.vs_returndata = zt.po_state.vs_returndata /\
    mem_write_ops a.po_inst = SOME ops /\
    MEM ops.iao_ofst a.po_inst.inst_operands /\
    eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst at.po_state = SOME y /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) /\
    MEM (w2n x,w2n n) (source_memory_write_ranges a.po_inst a.po_state) /\
    k = MIN (w2n n) (LENGTH post.vs_returndata) /\
    (!q. q IN range_bytes (step_writes a.po_inst a.po_state post) <=>
      w2n x <= q /\ q < w2n x + k) /\
    (!q. q IN range_bytes (step_writes at.po_inst at.po_state zt.po_state) <=>
      w2n y <= q /\ q < w2n y + k) /\
    (!j. j < k ==> read_byte (w2n x+j) post.vs_memory =
      read_byte (w2n y+j) zt.po_state.vs_memory) /\
    (!i. ptr_tagged_step (HD tokens) PT TG a.po_inst (ptr_ledger_next a i post).po_state = TG' /\
      ptr_paired_sample positions (ptr_ledger_next a i post) zt
        (tokens,registry,births,PT,TG',saved,entries) /\
      ptr_paired_params positions (ptr_ledger_next a i post) zt
        (tokens,registry,births,PT,TG',saved,entries))
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
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `inst_wf a.po_inst /\ opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        fn_inst_wf_def, fn_shape_ok_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `at.po_inst = a.po_inst` by
    (fs[MEM] >> simp[concretize_positions_unchanged]) >>
  qpat_x_assum `at.po_inst = concretize_inst_with_positions _ _` kall_tac >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
  `EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_inst_wf_def,
        EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> drule_all ptr_source_tagged_var_support >> simp[]) >>
  `~in_revert_forward a.po_fn a.po_state` by
    (`ALL_DISTINCT (fn_labels a.po_fn)` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
     qpat_x_assum `active_inst a.po_fn a.po_inst a.po_state` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     `lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb` by
       (irule MEM_lookup_block >> fs[fn_labels_def]) >>
     `get_instruction bb a.po_state.vs_inst_idx = SOME a.po_inst` by
       simp[get_instruction_def] >>
     simp[in_revert_forward_def] >> strip_tac >>
     drule_all memSafeRunTheory.revert_forward_at_opcode >> fs[MEM]) >>
  `ptr_history_content a.po_taint a.po_state at.po_state /\
   ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  `a.po_inst.inst_opcode <> INVOKE /\ ~is_terminator a.po_inst.inst_opcode` by
    (fs[MEM] >> simp[is_terminator_def]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"] >>
  IF (qpat_assum `step_inst _ _ _ _ = OK _` (K all_tac)) all_tac
    (qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
     simp[step_inst_non_invoke] >> strip_tac >>
     drule step_inst_base_intret_opcodes >> fs[MEM]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >> pure_rewrite_tac[step_inst_base_def] >>
  qpat_assum `a.po_inst.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `?pre vop.
    ((a.po_inst.inst_opcode = CALL /\ pre = [gas_op;addr_op;vop]) \/
     (a.po_inst.inst_opcode = STATICCALL /\ pre = [gas_op;addr_op])) /\
    a.po_inst.inst_operands = pre ++ [ao_op;as_op;ro_op;rs_op]` by
    (Cases_on `a.po_inst.inst_opcode = CALL`
     >- (gvs[] >> qexistsl_tac [`[gas_op;addr_op;val_op]`,`val_op`] >> simp[]) >>
     gvs[] >> qexistsl_tac [`[gas_op;addr_op]`,`Lit 0w`] >> simp[]) >>
  `(!op. MEM op a.po_inst.inst_operands ==>
      op_taint a.po_taint op = {} /\
      ptr_lookup_transport births positions (op_prov TG op) {}
        (eval_operand op a.po_state) (eval_operand op at.po_state)) /\
    eval_operands (pre ++ [as_op;rs_op]) a.po_state =
    eval_operands (pre ++ [as_op;rs_op]) at.po_state` by
    (irule ptr_call_operand_transport >> simp[] >> metis_tac[]) >>
  `?sa sr. eval_operand ao_op a.po_state = SOME sa /\
      eval_operand ro_op a.po_state = SOME sr /\
      ptr_lookup_transport births positions (op_prov TG ao_op) {} (SOME sa) (SOME ao) /\
      ptr_lookup_transport births positions (op_prov TG ro_op) {} (SOME sr) (SOME ro)` by
    (`ptr_lookup_transport births positions (op_prov TG ao_op) {}
        (eval_operand ao_op a.po_state) (SOME ao) /\
      ptr_lookup_transport births positions (op_prov TG ro_op) {}
        (eval_operand ro_op a.po_state) (SOME ro)` by
       (`MEM ao_op a.po_inst.inst_operands /\ MEM ro_op a.po_inst.inst_operands` by
          simp[] >> metis_tac[]) >>
     fs[ptr_lookup_transport_some_right] >> metis_tac[ptr_lookup_transport_some]) >>
  qpat_x_assum `eval_operands _ a.po_state = _` mp_tac >>
  gvs[eval_operands_def, AllCaseEqs()] >> strip_tac >>
  `read_memory (w2n sa) (w2n as_) a.po_state =
    read_memory (w2n ao) (w2n as_) at.po_state` by
    (drule ptr_paired_call_input_bytes >>
     disch_then irule >>
     simp[mem_read_ops_def, concretizeMemLocDefsTheory.inst_read_op_def,
          source_memory_read_ranges_def, memory_range_of_operands_def,
          eval_operands_def, AllCaseEqs()] >> metis_tac[]) >>
  `?out. a.po_inst.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf _` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `a.po_state.vs_call_ctx = at.po_state.vs_call_ctx` by
    metis_tac[ptr_history_content_call_ctx] >>
  drule_at (Pos last) ptr_call_history_execution >>
  disch_then drule >> simp[] >>
  disch_then (drule_at (Pos last)) >> simp[] >>
  disch_then (qspecl_then [`sr`,`gas`] strip_assume_tac) >>
  `ptr_history_content (step_taint a.po_inst a.po_state (update_var out w u) a.po_taint)
    (update_var out w u) zt.po_state` by
    (simp[] >>
     qpat_x_assum `ptr_history_content (step_taint _ _ _ _) _ _` mp_tac >>
     simp[ptr_history_content_def,
          concretizePtrTaintContentTheory.ptr_taint_content_def,
          concretizePtrTaintContentTheory.ptr_taint_control_def,
          ptr_core_shared_def, concretizePtrSharedFieldsTheory.ptr_shared_fields_def,
          contract_storage_def, contract_transient_def] >> strip_tac >> gvs[]) >>
  qexistsl_tac [`update_var out w u`, `step_prov PT TG a.po_inst (update_var out w u)`,
    `<|iao_ofst := ro_op; iao_size := NONE; iao_max_size := SOME rs_op|>`,
    `sr`, `ro`, `rs`] >>
  simp[] >> (
  `u.vs_allocas = a.po_state.vs_allocas /\
   u.vs_current_bb = a.po_state.vs_current_bb /\
   u.vs_prev_bb = a.po_state.vs_prev_bb /\
   u.vs_params = a.po_state.vs_params /\
   (!x. x <> out ==> lookup_var x u = lookup_var x a.po_state) /\
   u.vs_return_pc_token = a.po_state.vs_return_pc_token` by
    (qpat_x_assum `exec_ext_call _ a.po_state _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[exec_ext_call_def, update_var_def, venom_state_component_equality] >>
     strip_tac >> gvs[lookup_var_def] >> metis_tac[FLOOKUP_UPDATE]) >>
  `v.vs_current_bb = at.po_state.vs_current_bb /\
   v.vs_prev_bb = at.po_state.vs_prev_bb /\
   v.vs_params = at.po_state.vs_params /\
   (!x. x <> out ==> lookup_var x v = lookup_var x at.po_state) /\
   v.vs_return_pc_token = at.po_state.vs_return_pc_token` by
    (qpat_x_assum `exec_ext_call _ at.po_state _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[exec_ext_call_def, update_var_def, venom_state_component_equality] >>
     strip_tac >> gvs[lookup_var_def] >> metis_tac[FLOOKUP_UPDATE]) >>
  gvs[Excl "MEM"] >>
  simp[mem_write_ops_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, memory_range_of_operands_def,
       eval_operands_def, step_writes_def, range_bytes_def] >>
  gen_tac >> conj_tac
  >- simp[ptr_tagged_step_def, ptr_ledger_next_def, ptr_observe_def,
          step_prov_def, out_prov_def] >>
  reverse conj_tac
  >- (qpat_x_assum `ptr_paired_params _ _ _ _` mp_tac >>
      simp[concretizePtrPairedFieldsTheory.ptr_paired_params_def, ptr_ledger_next_def, ptr_observe_def,
           update_var_def]) >>
  simp[ptr_paired_sample_def, ptr_ledger_next_def, ptr_observe_def] >>
  `ssa_form a.po_fn` by metis_tac[EVERY_MEM] >>
  `~retpc_var a.po_fn out` by
    (irule frameViewFactsTheory.noncopy_output_not_retpc >>
     simp[] >> qexists_tac `a.po_inst` >> simp[]) >>
  qpat_x_assum `ptr_mixed_vars births positions TG _ _ _ _ _` mp_tac >>
  simp[ptr_mixed_vars_pointwise] >> strip_tac >>
  `~retpc_var at.po_fn out` by metis_tac[] >>
  gen_tac >>
  Cases_on `x = out`
  >- simp[FLOOKUP_DRESTRICT, word_agree_except_def, step_prov_def, out_prov_def, set_prov_def, step_taint_def,
          out_taint_def, set_var_taint_def, op_taint_def,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE,
          ptr_lookup_transport_def, ptr_value_transport_def] >>
  simp[step_prov_def, out_prov_def, set_prov_def, step_taint_def,
       out_taint_def, set_var_taint_def, op_taint_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `!x. if retpc_var _ x then _ else _`
    (qspec_then `x` mp_tac) >>
  gvs[lookup_var_def, op_taint_def, FLOOKUP_DRESTRICT])
QED

Theorem ptr_paired_prefix_write_attach:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_structural_transcript R vs C C' (h ++ [b]) b (ht ++ [bt]) bt
    (done ++ [LENGTH h - 1]) tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) /\
  ptr_paired_sample positions b bt (tokens,registry,births,PT,TG',saved,entries) /\
  ptr_paired_code R lp positions b.po_fn bt.po_fn /\
  ptr_paired_cursor lp b bt /\
  ptr_paired_params positions b bt (tokens,registry,births,PT,TG',saved,entries) /\
  b.po_stack = a.po_stack /\ bt.po_stack = at.po_stack /\
  (extra = [] \/ ?rho. extra = [(LENGTH h - 1,LENGTH done,rho)]) /\
  EVERY (ptr_paired_write lo positions C C' (h ++ [b]) (ht ++ [bt])
    (done ++ [LENGTH h - 1])
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)])) extra /\
  (~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
   range_bytes (step_writes a.po_inst a.po_state b.po_state) <> {} ==>
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
     simp[concretizePtrEventEmbeddingTheory.ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN] >> fs[ptr_paired_prefix_def, ptr_paired_samples_def, ptr_sample_list_def] >> decide_tac) >>
  gns[ptr_paired_prefix_def] >>
  conj_tac >- (irule ptr_paired_samples_pair >> simp[]) >>
  conj_tac >- (irule ptr_paired_alignment_pair >> simp[]) >>
  conj_tac >- (irule concretizePtrPairedFieldsTheory.ptr_paired_callers_retained >> simp[] >>
               fs[ptr_paired_samples_def, ptr_sample_list_def] >> qexistsl_tac [`a`,`at`] >> simp[]) >>
  irule concretizePtrPairedFieldsTheory.ptr_paired_writes_pair >> simp[] >>
  fs[ptr_paired_samples_def, ptr_sample_list_def]
QED

Theorem ptr_paired_call_prefix_step:
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
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [CALL; STATICCALL] ==>
  ?z TG' ws'. TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws'
Proof
  strip_tac >>
  drule_all ptr_paired_call_step >> strip_tac >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    (gvs[is_terminator_def]) >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `EVERY bb_well_formed a.po_fn.fn_blocks /\
   ALL_DISTINCT (fn_labels a.po_fn)` by
    (qpat_x_assum `EVERY (\f. fn_inst_wf f /\ _) _` mp_tac >>
     simp[EVERY_MEM] >> disch_then (qspec_then `a.po_fn` mp_tac) >> simp[]) >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (irule concretizePtrOrdinaryNextTheory.ptr_ordinary_next_active >> simp[] >>
     qexists_tac `a.po_inst` >> simp[]) >>
  qmatch_assum_abbrev_tac `active_inst a.po_fn i nextstate` >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  `z.po_fn = a.po_fn /\ z.po_stack = a.po_stack /\
   z.po_state.vs_allocas = a.po_state.vs_allocas` by
    simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, Abbr `nextstate`] >>
  `active_inst z.po_fn z.po_inst z.po_state` by
    simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, Abbr `nextstate`] >>
  `ptr_tagged_step (HD tokens) PT TG a.po_inst z.po_state = TG' /\
   ptr_paired_sample positions z zt (tokens,registry,births,PT,TG',saved,entries) /\
   ptr_paired_params positions z zt (tokens,registry,births,PT,TG',saved,entries)` by
    metis_tac[] >>
  `ptr_tagged_step (HD tokens) PT TG a.po_inst post = TG'` by
    gvs[Abbr `z`, ptr_ledger_next_def, ptr_observe_def,
        ptr_tagged_step_def, step_prov_def, out_prov_def, lookup_var_def] >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG' saved` by
    (`active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
       fs[Abbr `nextstate`] >>
     drule_all (cj 1 ptr_tagged_chrono_step_rules) >> strip_tac >>
     `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
       a.po_fn a.po_inst a.po_state = a` by
       simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
     fs[Abbr `z`, ptr_ledger_next_def, Abbr `nextstate`] >> metis_tac[]) >>
  `ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
     (done ++ [LENGTH h - 1]) tokens registry births PT TG' saved entries
     (H ++ [(tokens,registry,births,PT,TG',saved,entries)])` by
    (drule ptr_ownership_overlay_fixed >> strip_tac >>
     drule (cj 3 ptr_structural_transcript_rules) >>
     disch_then drule >> disch_then drule >>
     simp[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
          concretizePtrActivationChronologyTheory.ptr_activation_registry_def]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (qpat_x_assum `ptr_paired_code _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[concretizePtrPairedFieldsTheory.ptr_paired_code_def] >> strip_tac >>
     gns[fn_labels_def] >>
     metis_tac[concretizeStepStructureTheory.concretize_positions_labels, fn_labels_def]) >>
  `!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP (lp a.po_fn) (Allocation ai.inst_id) = SOME p` by
    (qpat_x_assum `EVERY (\f. fn_inst_wf f /\ _) _` mp_tac >>
     simp[EVERY_MEM] >> disch_then (qspec_then `a.po_fn` mp_tac) >>
     simp[] >> strip_tac >> rpt strip_tac >>
     first_x_assum drule >> simp[] >>
     Cases_on `FLOOKUP (lp a.po_fn) (Allocation ai.inst_id)` >> simp[]) >>
  `ptr_paired_cursor lp z zt` by
    (drule concretizePtrOrdinaryNextTheory.ptr_ordinary_next_cursor >> disch_then irule >>
     simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, Abbr `nextstate`]) >>
  `z.po_state.vs_memory = post.vs_memory /\
   step_writes a.po_inst a.po_state z.po_state = step_writes a.po_inst a.po_state post` by
    simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, Abbr `nextstate`, step_writes_def] >>
  `TG' = step_prov PT TG a.po_inst z.po_state` by
    gvs[ptr_tagged_step_def, step_prov_def, out_prov_def] >>
  Cases_on `k = 0`
  >- (`range_bytes (step_writes a.po_inst a.po_state z.po_state) = {}` by
        (simp[EXTENSION] >> metis_tac[DECIDE ``~(m <= q /\ q < m)``]) >>
      qexistsl_tac [`z`,`TG'`,`ws`] >> simp[] >>
      drule concretizePtrPairedNextAttachTheory.ptr_paired_prefix_nonwrite_attach >> disch_then irule >> gns[]) >>
  `w2n n <> 0` by (strip_tac >> fs[]) >>
  drule_at (Pat `ptr_lookup_transport _ _ _ _ _ _`)
    concretizePtrMloadEndpointTheory.ptr_paired_current_range_classification >>
  disch_then (drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`rpolicy`,`names`,`w2n n`,`eom`] mp_tac) >>
  simp[] >> disch_tac >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `k <= w2n n` by simp[] >>
  `?rho. (!j. j < k ==> rho (w2n x + j) = w2n y + j) /\
    concretizePtrPairedFields$ptr_paired_write_owner lo positions rho
      (range_bytes (step_writes a.po_inst a.po_state post))
      (tokens,registry,births,PT,TG',saved,entries)` by
    (qexists_tac `\q. w2n y + (q - w2n x)` >> conj_tac
     >- simp[] >>
     qpat_x_assum `_ \/ ?v token aid b sz pa. _` strip_assume_tac
     >- (simp[concretizePtrPairedFieldsTheory.ptr_paired_write_owner_def] >>
         rpt strip_tac >> disj1_tac >>
         Cases_on `w2n n < LENGTH post.vs_returndata` >>
         gns[arithmeticTheory.MIN_DEF] >> decide_tac) >>
     `MEM token tokens` by (drule_all ptr_source_ownership_live_prov >> simp[]) >>
     simp[concretizePtrPairedFieldsTheory.ptr_paired_write_owner_def] >>
     rpt strip_tac >> disj2_tac >>
     qexistsl_tac [`token`,`aid`,`b`,`sz`,`pa`,`q - b`] >>
     Cases_on `w2n n < LENGTH post.vs_returndata` >>
     gns[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  rename1 `concretizePtrPairedFields$ptr_paired_write_owner lo positions reloc _ _` >>
  `ptr_ledger_write_pair C C' reloc a z at zt` by
    (simp[ptr_ledger_write_pair_def] >>
     conj_tac >- metis_tac[ptr_tagged_chrono_step_projection] >>
     conj_tac
     >- (rpt strip_tac >> rename1 `w2n x <= q` >>
         `q = w2n x + (q - w2n x) /\ q - w2n x < k` by
           (Cases_on `w2n n < LENGTH post.vs_returndata` >>
            gns[arithmeticTheory.MIN_DEF] >> decide_tac) >>
         `reloc q = w2n y + (q - w2n x)` by metis_tac[] >>
         simp[] >> gns[] >> decide_tac) >>
     simp[concretizePtrBytesTheory.ptr_bytes_agree_def] >>
     rpt strip_tac >> rename1 `read_byte q _ = _` >>
     `q = w2n x + (q - w2n x) /\ q - w2n x < k` by
       (Cases_on `w2n n < LENGTH post.vs_returndata` >>
        gns[arithmeticTheory.MIN_DEF] >> decide_tac) >> metis_tac[]) >>
  `LENGTH H = LENGTH h /\ 0 < LENGTH h /\ LENGTH ht = SUC (LENGTH done)` by
    fs[ptr_paired_prefix_def, ptr_paired_samples_def, ptr_sample_list_def] >>
  `EL (LENGTH h - 1) h = a /\ EL (LENGTH done) ht = at` by
    (drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_structural_trace_target >> strip_tac >>
     `h <> [] /\ LAST h = a` by metis_tac[ptr_chrono_history_end] >>
     `ht <> [] /\ LAST ht = at` by metis_tac[ptr_chrono_history_end] >>
     conj_tac
     >- (qpat_x_assum `LAST h = a` mp_tac >> simp[LAST_EL, arithmeticTheory.PRE_SUB1]) >>
     qpat_x_assum `LAST ht = at` mp_tac >> simp[LAST_EL]) >>
  `range_bytes (step_writes a.po_inst a.po_state z.po_state) <> {}` by
    (`w2n x IN range_bytes (step_writes a.po_inst a.po_state post)` by
       (qpat_assum `!q. q IN range_bytes (step_writes a.po_inst a.po_state post) <=> _`
          (qspec_then `w2n x` (fn th => pure_rewrite_tac[th])) >>
        decide_tac) >>
     metis_tac[NOT_IN_EMPTY]) >>
  `ptr_paired_write lo positions C C' (h ++ [z]) (ht ++ [zt])
    (done ++ [LENGTH h - 1])
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)])
    (LENGTH h - 1,LENGTH done,reloc)` by
    (`SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
     simp[concretizePtrPairedFieldsTheory.ptr_paired_write_def, EL_APPEND_EQN] >>
     gns[]) >>
  qexistsl_tac [`z`,`ws ++ [(LENGTH h - 1,LENGTH done,reloc)]`] >> simp[] >>
  irule ptr_paired_prefix_write_attach >> gns[] >>
  qexistsl_tac [`TG`,`a`,`at`] >> simp[]
QED

Theorem ptr_paired_call_prefix_normalize:
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
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [CALL; STATICCALL] ==>
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

