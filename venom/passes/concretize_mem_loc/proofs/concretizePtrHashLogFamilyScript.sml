(*
 * Paired-prefix extension for the N14 opcode family (SHA3; LOG).
 *)
Theory concretizePtrHashLogFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrMloadRecovery
  regularMemorySim memSafeRun ptrDiscipline contextCodegenRel
  venomInst venomWf venomExecProofs unitLabelMapIdentity list
  pointerConfinedDefs memLocDefs finite_map pred_set
  concretizePtrReturnTransport concretizePtrOpaqueRetpc
  concretizePtrCurrentRangeTransport concretizePtrObservationInterface
  venomState concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizePtrAllocationSize
  concretizePtrSourceOwnership concretizePtrParamSupport
  o1PassContract unitShapeDefs venomExecSemantics concretizeStepStructure
  concretizePtrRequestHistory concretizePtrValueTransport

Theorem ptr_hash_log_nonrevert[local]:
  active_inst fn inst s /\ ALL_DISTINCT (fn_labels fn) /\
  MEM inst.inst_opcode [SHA3; LOG] ==>
  ~in_revert_forward fn s /\ ~about_to_revert fn inst s
Proof
  strip_tac >> reverse conj_tac
  >- (fs[MEM] >> simp[about_to_revert_def]) >>
  qpat_x_assum `active_inst fn inst s` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    simp[get_instruction_def] >>
  simp[in_revert_forward_def] >> strip_tac >>
  drule_all revert_forward_at_opcode >> fs[MEM]
QED

Theorem ptr_hash_log_read_untainted[local]:
  taint_ok fn tn inst s /\ MEM inst.inst_opcode [SHA3; LOG] /\
  MEM (off,n) (source_memory_read_ranges inst s) ==>
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) /\
  (!j. j < n ==> off+j NOTIN tn.t_mem)
Proof
  strip_tac >>
  `~about_to_revert fn inst s` by (fs[MEM] >> simp[about_to_revert_def]) >>
  conj_tac
  >- (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  fs[MEM] >> gvs[taint_ok_def] >>
  qpat_x_assum `!off' len i. _`
    (qspecl_then [`off`,`n`,`off+j`] mp_tac) >> simp[]
QED

Theorem ptr_log_read_descriptor[local]:
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc::rest /\
  REVERSE rest = addr::szop::topics ==>
  mem_write_ops inst = NONE /\
  mem_read_ops inst = SOME <|iao_ofst := addr; iao_size := SOME szop;
                            iao_max_size := SOME szop|>
Proof
  strip_tac >> simp[mem_write_ops_def, mem_read_ops_def] >>
  Cases_on `topics` >> simp[]
QED

Theorem ptr_log_scalar_vars[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc::rest /\
  REVERSE rest = addr::szop::topics ==>
  !v. MEM (Var v) (szop::topics) ==> v NOTIN fn_pv P fn
Proof
  strip_tac >>
  drule_all ptr_log_read_descriptor >> strip_tac >>
  gen_tac >> strip_tac >> spose_not_then assume_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `MEM (Var v) inst.inst_operands` by
    (simp[] >> metis_tac[MEM_REVERSE, MEM]) >>
  `FILTER ($= (Var v)) inst.inst_operands = [Var v] /\ addr = Var v` by
    (qpat_x_assum `ptr_use_ok P _ inst` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def] >>
     disch_then (qspec_then `v` mp_tac) >>
     `MEM (Var v) rest` by (qpat_x_assum `MEM (Var v) inst.inst_operands` mp_tac >> simp[]) >> simp[]) >>
  `REVERSE inst.inst_operands = Var v::szop::topics ++ [Lit tc]` by
    simp[REVERSE_APPEND] >>
  `FILTER ($= (Var v)) (REVERSE inst.inst_operands) = [Var v]` by
    simp[FILTER_REVERSE] >>
  qpat_x_assum `FILTER _ (REVERSE inst.inst_operands) = _` mp_tac >>
  simp[FILTER_APPEND_DISTRIB] >>
  Cases_on `szop = Var v` >> simp[] >>
  fs[MEM, FILTER_EQ_NIL, EXISTS_MEM]
QED

Theorem ptr_log_scalar_evaluations[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\ opaque_use_ok fn /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc::rest /\
  REVERSE rest = addr::szop::topics /\ taint_ok fn tn inst src /\
  ptr_ledger_erases births TG G /\ FDOM G SUBSET fn_pv P fn /\
  ptr_mixed_vars births positions TG tn fn ft src tgt /\
  src.vs_labels = tgt.vs_labels ==>
  EVERY (\op. eval_operand op src = eval_operand op tgt) (szop::topics) /\
  eval_operands topics src = eval_operands topics tgt
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  `!op. MEM op (szop::topics) ==> MEM op inst.inst_operands` by
    (simp[] >> metis_tac[MEM_REVERSE, MEM]) >>
  `EVERY (\op. ptr_nonopaque_operand fn op /\ op_prov G op = NONE /\
      op_taint tn op = {}) (szop::topics)` by
    (rewrite_tac[EVERY_MEM] >> qx_gen_tac `op` >> strip_tac >> BETA_TAC >>
     conj_tac
     >- (fs[EVERY_MEM] >> metis_tac[]) >> conj_tac
     >- (`!v. op = Var v ==> v NOTIN fn_pv P fn` by
           (fs[MEM] >> metis_tac[ptr_log_scalar_vars, MEM]) >>
         Cases_on `op` >> gvs[op_prov_def] >>
         metis_tac[flookup_thm, SUBSET_DEF]) >>
     gvs[taint_ok_def] >> metis_tac[]) >>
  `EVERY (\op. eval_operand op src = eval_operand op tgt) (szop::topics)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     irule ptr_mixed_scalar_eval >> metis_tac[]) >>
  simp[] >>
  qpat_x_assum `EVERY (\op. eval_operand op src = _) _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  Induct_on `topics` >> simp[eval_operands_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ptr_hash_log_read_transport[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  opaque_use_ok fn /\ MEM inst.inst_opcode [SHA3; LOG] /\
  taint_ok fn tn inst src /\
  ptr_ledger_erases births TG G /\ FDOM G SUBSET fn_pv P fn /\
  ptr_mixed_vars births positions TG tn fn ft src tgt /\
  src.vs_labels = tgt.vs_labels /\
  MEM (off,n) (source_memory_read_ranges inst tgt) ==>
  ?ops x y. mem_read_ops inst = SOME ops /\
    inst_read_op inst = SOME ops.iao_ofst /\
    MEM ops.iao_ofst inst.inst_operands /\
    eval_operand ops.iao_ofst src = SOME x /\
    eval_operand ops.iao_ofst tgt = SOME y /\ off = w2n y /\
    MEM (w2n x,n) (source_memory_read_ranges inst src) /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
      (SOME x) (SOME y)
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> fs[MEM]) >>
  `!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt)` by
    (drule_all ptr_mixed_vars_eval_presence >> simp[]) >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  `?addr szop. mem_read_ops inst = SOME
      <|iao_ofst := addr; iao_size := SOME szop; iao_max_size := SOME szop|> /\
    MEM addr inst.inst_operands /\ MEM szop inst.inst_operands /\
    (?x y. eval_operand addr src = SOME x /\ eval_operand addr tgt = SOME y /\
      off = w2n y /\ MEM (w2n x,n) (source_memory_read_ranges inst src))` by
      suspend "ranges" >>
  qexistsl_tac [`<|iao_ofst := addr; iao_size := SOME szop;
                  iao_max_size := SOME szop|>`,`x`,`y`] >>
  simp[concretizeMemLocDefsTheory.inst_read_op_def] >>
  `ptr_nonopaque_operand fn addr /\ op_taint tn addr = {}` by
    metis_tac[EVERY_MEM] >>
  drule_all ptr_mixed_vars_eval >> simp[]
QED

Resume ptr_hash_log_read_transport[ranges]:
  Cases_on `inst.inst_opcode = SHA3`
  >- (`?addr szop. inst.inst_operands = [addr;szop]` by
        gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      `mem_read_ops inst = SOME
        <|iao_ofst := addr; iao_size := SOME szop; iao_max_size := SOME szop|>` by
        simp[mem_read_ops_def] >>
      `!v. szop = Var v ==> v NOTIN fn_pv P fn` by
        (qpat_assum `mem_read_ops inst = SOME _`
           (mp_then Any mp_tac ptr_read_max_size_not_pointer) >> simp[]) >>
      `op_prov G szop = NONE` by
        (Cases_on `szop` >> gvs[op_prov_def] >>
         metis_tac[flookup_thm, SUBSET_DEF]) >>
      `eval_operand szop src = eval_operand szop tgt` by
        (irule ptr_mixed_scalar_eval >> fs[EVERY_MEM] >> metis_tac[MEM]) >>
      qexistsl_tac [`addr`,`szop`] >> simp[] >>
      Cases_on `eval_operand addr tgt` >>
      Cases_on `eval_operand szop tgt` >>
      gvs[source_memory_read_ranges_def, memory_range_of_operands_def] >>
      Cases_on `eval_operand addr src` >> gvs[] >>
      qpat_x_assum `!op. IS_SOME (eval_operand op src) = _`
        (qspec_then `addr` mp_tac) >> simp[]) >>
  `inst.inst_opcode = LOG` by fs[MEM] >>
  `?tc rest. inst.inst_operands = Lit tc::rest /\ LENGTH rest = w2n tc+2` by
    gvs[inst_wf_def] >>
  `?addr szop topics. REVERSE rest = addr::szop::topics` by
    (Cases_on `REVERSE rest` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  drule_all ptr_log_scalar_evaluations >> strip_tac >>
  drule_all ptr_log_read_descriptor >> strip_tac >>
  `MEM addr inst.inst_operands /\ MEM szop inst.inst_operands` by
    (simp[] >> metis_tac[MEM_REVERSE, MEM]) >>
  qexistsl_tac [`addr`,`szop`] >> simp[] >>
  qpat_x_assum `MEM addr inst.inst_operands` kall_tac >>
  qpat_x_assum `MEM szop inst.inst_operands` kall_tac >>
  Cases_on `eval_operands topics tgt` >>
  Cases_on `eval_operand addr tgt` >>
  Cases_on `eval_operand szop tgt` >>
  gvs[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  Cases_on `eval_operand addr src` >> gvs[] >>
  qpat_x_assum `!op. IS_SOME (eval_operand op src) = _`
    (qspec_then `addr` mp_tac) >> simp[]
QED

Finalise ptr_hash_log_read_transport

Theorem ptr_paired_hash_log_payload[local]:
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
  active_inst a.po_fn a.po_inst a.po_state /\
  ALL_DISTINCT (fn_labels a.po_fn) /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  MEM a.po_inst.inst_opcode [SHA3; LOG] /\
  mem_read_ops a.po_inst = SOME ops /\
  inst_read_op a.po_inst = SOME ops.iao_ofst /\
  MEM ops.iao_ofst a.po_inst.inst_operands /\
  eval_operand ops.iao_ofst a.po_state = SOME x /\
  eval_operand ops.iao_ofst at.po_state = SOME y /\
  MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
    (SOME x) (SOME y) ==>
  TAKE n (DROP (w2n x) a.po_state.vs_memory ++ REPLICATE n 0w) =
  TAKE n (DROP (w2n y) at.po_state.vs_memory ++ REPLICATE n 0w)
Proof
  strip_tac >>
  `~in_revert_forward a.po_fn a.po_state` by
    (drule_all ptr_hash_log_nonrevert >> simp[]) >>
  `!j. j < n ==> w2n x+j NOTIN a.po_taint.t_mem` by
    (drule_all ptr_hash_log_read_untainted >> simp[]) >>
  `a.po_inst.inst_opcode <> ASSIGN` by fs[MEM] >>
  drule ptr_paired_read_range_masked_bytes >>
  simp[] >> strip_tac >>
  simp[venom_returndata_read_byte] >> irule GENLIST_CONG >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ptr_paired_hash_log_endpoint[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  ptr_discipline lo C vs /\ ~ctx_has_dalloca C /\
  MEM a.po_inst.inst_opcode [SHA3; LOG] ==>
  active_inst a.po_fn a.po_inst a.po_state /\
  MEM a.po_inst (fn_insts a.po_fn) /\ inst_wf a.po_inst /\
  fn_shape_ok a.po_fn /\ ALL_DISTINCT (fn_labels a.po_fn) /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
    a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels /\
  ptr_ledger_erases births TG a.po_prov /\
  ?P. fn_ptr_ok P a.po_fn /\ FDOM a.po_prov SUBSET fn_pv P a.po_fn
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
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  `inst_wf a.po_inst /\ fn_shape_ok a.po_fn /\
   ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def,
        fn_insts_MEM, wf_function_def] >> metis_tac[]) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `~in_revert_forward a.po_fn a.po_state` by
    (drule_all ptr_hash_log_nonrevert >> simp[]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  drule_all ptr_source_ownership_prov_erases >> strip_tac >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >>
     metis_tac[concretizePtrRequestHistoryTheory.ptr_history_content_labels]) >>
  simp[] >>
  qpat_assum `ptr_discipline _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[EVERY_MEM] >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  qexists_tac `P` >> conj_tac >- fs[EVERY_MEM] >>
  fs[ptr_static_support_def, pred_setTheory.SUBSET_DEF, FLOOKUP_DEF] >>
  metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem ptr_paired_hash_log_read_inputs[local]:
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
  MEM a.po_inst.inst_opcode [SHA3; LOG] /\
  MEM (off,n) (source_memory_read_ranges a.po_inst at.po_state) ==>
  ?ops x y. mem_read_ops a.po_inst = SOME ops /\
    inst_read_op a.po_inst = SOME ops.iao_ofst /\
    MEM ops.iao_ofst a.po_inst.inst_operands /\
    eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst at.po_state = SOME y /\ off = w2n y /\
    MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
      (SOME x) (SOME y) /\
    TAKE n (DROP (w2n x) a.po_state.vs_memory ++ REPLICATE n 0w) =
    TAKE n (DROP (w2n y) at.po_state.vs_memory ++ REPLICATE n 0w)
Proof
  strip_tac >>
  drule_all ptr_paired_hash_log_endpoint >> strip_tac >>
  `opaque_use_ok a.po_fn` by fs[fn_shape_ok_def] >>
  drule_all ptr_hash_log_read_transport >> strip_tac >>
  qexistsl_tac [`ops`,`x`,`y`] >> simp[] >>
  irule ptr_paired_hash_log_payload >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ptr_sha3_execution[local]:
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [addr;szop] /\
  inst.inst_outputs = [out] /\
  eval_operand addr s = SOME x /\ eval_operand addr t = SOME y /\
  eval_operand szop s = SOME n /\ eval_operand szop t = SOME n /\
  TAKE (w2n n) (DROP (w2n x) s.vs_memory ++ REPLICATE (w2n n) 0w) =
  TAKE (w2n n) (DROP (w2n y) t.vs_memory ++ REPLICATE (w2n n) 0w) ==>
  ?v. step_inst 0 C inst s = OK (update_var out v s) /\
      step_inst fuel Ct inst t = OK (update_var out v t)
Proof
  strip_tac >>
  simp[step_inst_non_invoke] >>
  pure_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >> simp[Once opcode_case_def] >> metis_tac[]
QED

Theorem ptr_log_execution[local]:
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc::rest /\
  REVERSE rest = addr::szop::topicops /\ LENGTH rest = w2n tc+2 /\
  s.vs_call_ctx = t.vs_call_ctx /\
  eval_operand addr s = SOME x /\ eval_operand addr t = SOME y /\
  eval_operand szop s = SOME n /\ eval_operand szop t = SOME n /\
  eval_operands topicops s = SOME vals /\ eval_operands topicops t = SOME vals /\
  TAKE (w2n n) (DROP (w2n x) s.vs_memory ++ REPLICATE (w2n n) 0w) =
  TAKE (w2n n) (DROP (w2n y) t.vs_memory ++ REPLICATE (w2n n) 0w) /\
  step_inst fuel Ct inst t = OK t' ==>
  ?ev. step_inst 0 C inst s = OK (s with vs_logs := s.vs_logs ++ [ev]) /\
       t' = t with vs_logs := t.vs_logs ++ [ev]
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands t)` by
    (simp[eval_operands_IS_SOME_EVERY, eval_operand_def] >>
     `EVERY (\op. IS_SOME (eval_operand op t)) topicops` by
       metis_tac[eval_operands_IS_SOME_EVERY, optionTheory.IS_SOME_DEF] >>
     rewrite_tac[EVERY_MEM] >> qx_gen_tac `op` >> strip_tac >> BETA_TAC >>
     `MEM op (addr::szop::topicops)` by metis_tac[MEM_REVERSE] >>
     fs[MEM, EVERY_MEM] >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  simp[step_inst_non_invoke, step_inst_base_def] >> metis_tac[]
QED

Theorem ptr_sha3_successor_relations[local]:
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t /\
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [addr;szop] /\
  inst.inst_outputs = [out] /\ ~retpc_var f out ==>
  ptr_mixed_vars births positions
    (step_prov PT TG inst (update_var out v s))
    (step_taint inst s (update_var out v s) tn)
    f g (update_var out v s) (update_var out v t) /\
  ptr_history_content (step_taint inst s (update_var out v s) tn)
    (update_var out v s) (update_var out v t)
Proof
  strip_tac >> conj_tac
  >- (drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
      simp[step_prov_def, out_prov_def, set_prov_def,
           step_taint_def, set_var_taint_def, out_taint_def,
           FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ptr_value_transport_def] >>
      Cases_on `eval_operand addr s` >> simp[] >>
      rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def] >>
      gvs[FLOOKUP_UPDATE, word_agree_except_def]) >>
  simp[] >> irule ptr_history_content_masks >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
  qexists_tac `tn` >> simp[]
QED

Theorem ptr_paired_hash_log_prefix_normalize:
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
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [SHA3; LOG] ==>
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

