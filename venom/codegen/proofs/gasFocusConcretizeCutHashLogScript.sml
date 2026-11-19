Theory gasFocusConcretizeCutHashLog
Ancestors concretizePtrHashLogFamily[qualified]
  gasFocusConcretizeTaggedSupport concretizePtrCurrentRangeTransport
  concretizePtrOrdinaryNext concretizePtrOpaqueRetpc concretizePtrRequestHistory
  concretizePtrTaintContent concretizePtrSharedFields concretizePtrValueTransport
  concretizePtrStructuralTrace concretizePtrStructuralTranscript concretizePtrPairedPrefix
  concretizeStepStructure concretizeMemLocDefs memoryReadRel memLocDefs
  pointerConfinedDefs ptrDiscipline venomInstProofs venomExecProofs venomWf
  venomExecSemantics unitShapeDefs list finite_map concretizePtrParamSupport
  frameRelocationGuardedValues venomState venomInst opcodeClass contextCodegenRel
  o1PassContract unitLabelMapIdentity frameViewFacts concretizePtrPairedFields codegenRel
  concretizePtrChronologicalHistory concretizePtrLedgerProbe concretizePtrSourceOwnership

Theorem focus_hash_log_untainted[local]:
  taint_ok fn tn inst s /\ MEM inst.inst_opcode [SHA3; LOG] ==>
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) /\
  (!off n j. MEM (off,n) (source_memory_read_ranges inst s) /\ j < n ==>
              off+j NOTIN tn.t_mem)
Proof
  strip_tac >>
  `~about_to_revert fn inst s` by (fs[MEM] >> simp[about_to_revert_def]) >>
  conj_tac >- (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  rpt strip_tac >> fs[MEM] >> gvs[taint_ok_def] >>
  qpat_x_assum `!off' len i. _`
    (qspecl_then [`off`,`n`,`off+j`] mp_tac) >> simp[]
QED

Theorem focus_hash_log_scalar_eval[local]:
  ptr_static_support P fn (TG : string |-> num # num) /\ ptr_mixed_vars births positions TG tn fn ft src tgt /\
  src.vs_labels = tgt.vs_labels /\ ptr_nonopaque_operand fn op /\ op_taint tn op = {} /\
  (!v. op = Var v ==> v NOTIN fn_pv P fn) ==>
  eval_operand op src = eval_operand op tgt
Proof
  strip_tac >>
  `op_prov TG op = NONE` by
    (Cases_on `op` >> gvs[op_prov_def, ptr_static_support_def] >>
     Cases_on `FLOOKUP TG s` >> gvs[] >> metis_tac[]) >>
  drule_all ptr_mixed_vars_eval >> simp[] >>
  Cases_on `eval_operand op src` >> Cases_on `eval_operand op tgt` >>
  simp[ptr_lookup_transport_def, ptr_value_transport_def, word_agree_except_empty] >>
  metis_tac[word_agree_except_empty]
QED

Theorem focus_hash_log_eval_operands[local]:
  !ops. EVERY (\op. eval_operand op src = eval_operand op tgt) ops ==>
        eval_operands ops src = eval_operands ops tgt
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >> gvs[]
QED

(* Only the selected read slice is observed. The caller obtains its bytes
   from the bounded chronological recovery for this instruction. *)
Theorem focus_hash_log_payload[local]:
  MEM inst.inst_opcode [SHA3; LOG] /\ taint_ok fn tn inst s /\
  ptr_mixed_vars births positions TG tn fn ft s t /\ s.vs_labels = t.vs_labels /\
  ptr_nonopaque_operand fn addr /\ op_taint tn addr = {} /\
  mem_read_ops inst = SOME ops /\ inst_read_op inst = SOME ops.iao_ofst /\
  ops.iao_ofst = addr /\ MEM addr inst.inst_operands /\
  eval_operand addr s = SOME x /\ eval_operand addr t = SOME y /\
  MEM (w2n x,n) (source_memory_read_ranges inst s) /\
  (!ops x y n.
     mem_read_ops inst = SOME ops /\ inst_read_op inst = SOME ops.iao_ofst /\
     MEM ops.iao_ofst inst.inst_operands /\
     eval_operand ops.iao_ofst s = SOME x /\ eval_operand ops.iao_ofst t = SOME y /\
     MEM (w2n x,n) (source_memory_read_ranges inst s) /\
     ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
     !j. j < n /\ w2n x + j NOTIN tn.t_mem ==>
       read_byte (w2n x+j) s.vs_memory = read_byte (w2n y+j) t.vs_memory) ==>
  TAKE n (DROP (w2n x) s.vs_memory ++ REPLICATE n 0w) =
  TAKE n (DROP (w2n y) t.vs_memory ++ REPLICATE n 0w)
Proof
  strip_tac >>
  drule_all ptr_mixed_vars_eval >> simp[] >> strip_tac >>
  drule_all focus_hash_log_untainted >> strip_tac >>
  simp[venom_returndata_read_byte] >> irule GENLIST_CONG >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem focus_sha3_successor[local]:
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t /\
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [addr;szop] /\
  inst.inst_outputs = [out] /\ ~retpc_var f out /\
  eval_operand addr s = SOME x /\ eval_operand addr t = SOME y /\
  eval_operand szop s = SOME n /\ eval_operand szop t = SOME n /\
  TAKE (w2n n) (DROP (w2n x) s.vs_memory ++ REPLICATE (w2n n) 0w) =
  TAKE (w2n n) (DROP (w2n y) t.vs_memory ++ REPLICATE (w2n n) 0w) /\
  step_inst fuel Ct inst t = OK postt ==>
  ?post. step_inst 0 C inst s = OK post /\
    ptr_mixed_vars births positions (step_prov PT TG inst post)
      (step_taint inst s post tn) f g post postt /\
    ptr_history_content (step_taint inst s post tn) post postt /\
    post.vs_allocas = s.vs_allocas /\ post.vs_params = s.vs_params /\
    postt.vs_params = t.vs_params
Proof
  strip_tac >>
  `?v. step_inst 0 C inst s = OK (update_var out v s) /\
       step_inst fuel Ct inst t = OK (update_var out v t)` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[step_inst_non_invoke] >> pure_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[] >> simp[Once opcode_case_def, AllCaseEqs()] >> metis_tac[]) >>
  `postt = update_var out v t` by fs[] >>
  qexists `update_var out v s` >> gvs[] >>
  rpt conj_tac
  >- (drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
      simp[step_prov_def, out_prov_def, set_prov_def, step_taint_def,
           set_var_taint_def, out_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
           ptr_value_transport_def] >>
      rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def] >>
      gvs[FLOOKUP_UPDATE, word_agree_except_def])
  >- (simp[] >> irule ptr_history_content_masks >>
      simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
      qexists `tn` >> simp[]) >>
  simp[update_var_def]
QED

Theorem focus_hash_log_execution:
  inst_wf inst /\ MEM inst.inst_opcode [SHA3; LOG] /\
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\ opaque_use_ok fn /\
  ptr_static_support P fn TG /\ taint_ok fn tn inst s /\
  ptr_mixed_vars births positions TG tn fn ft s t /\
  ptr_history_content tn s t /\
  (!out. MEM out inst.inst_outputs ==> ~retpc_var fn out) /\
  step_inst fuel Ct inst t = OK postt /\
  (!ops x y n.
     mem_read_ops inst = SOME ops /\ inst_read_op inst = SOME ops.iao_ofst /\
     MEM ops.iao_ofst inst.inst_operands /\
     eval_operand ops.iao_ofst s = SOME x /\ eval_operand ops.iao_ofst t = SOME y /\
     MEM (w2n x,n) (source_memory_read_ranges inst s) /\
     ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
     !j. j < n /\ w2n x + j NOTIN tn.t_mem ==>
       read_byte (w2n x+j) s.vs_memory = read_byte (w2n y+j) t.vs_memory) ==>
  ?post. step_inst 0 C inst s = OK post /\
    ptr_mixed_vars births positions (step_prov PT TG inst post)
      (step_taint inst s post tn) fn ft post postt /\
    ptr_history_content (step_taint inst s post tn) post postt /\
    post.vs_allocas = s.vs_allocas /\ post.vs_params = s.vs_params /\
    postt.vs_params = t.vs_params
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels` by metis_tac[ptr_history_content_labels] >>
  `!op. MEM op inst.inst_operands ==>
    ptr_nonopaque_operand fn op /\ op_taint tn op = {}` by
    (drule_all focus_hash_log_untainted >> strip_tac >>
     `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
       (irule ptr_nonopaque_instruction_operands >> fs[MEM]) >>
     gvs[EVERY_MEM]) >>
  `!op. IS_SOME (eval_operand op s) = IS_SOME (eval_operand op t)` by
    (drule_all ptr_mixed_vars_eval_presence >> simp[]) >>
  Cases_on `inst.inst_opcode = SHA3`
  >- suspend "sha3" >>
  suspend "log"
QED

Resume focus_hash_log_execution[sha3]:
  `?addr szop out. inst.inst_operands = [addr;szop] /\ inst.inst_outputs = [out]` by
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  qabbrev_tac `ops = <|iao_ofst := addr; iao_size := SOME szop;
                       iao_max_size := SOME szop|>` >>
  `mem_read_ops inst = SOME ops /\ inst_read_op inst = SOME addr /\
   ops.iao_ofst = addr /\ ops.iao_max_size = SOME szop` by
    simp[Abbr `ops`, mem_read_ops_def, inst_read_op_def] >>
  `!v. szop = Var v ==> v NOTIN fn_pv P fn` by
    (qpat_assum `mem_read_ops inst = SOME _`
       (mp_then Any mp_tac ptr_read_max_size_not_pointer) >> simp[]) >>
  `eval_operand szop s = eval_operand szop t` by
    (irule focus_hash_log_scalar_eval >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `?y n. eval_operand addr t = SOME y /\ eval_operand szop t = SOME n` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[step_inst_non_invoke] >> pure_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[] >> simp[Once opcode_case_def, AllCaseEqs()] >> metis_tac[]) >>
  `?x. eval_operand addr s = SOME x` by
    (qpat_assum `!op. IS_SOME (eval_operand op s) = _` (qspec_then `addr` mp_tac) >>
     Cases_on `eval_operand addr s` >> simp[]) >>
  `MEM (w2n x,w2n n) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  `TAKE (w2n n) (DROP (w2n x) s.vs_memory ++ REPLICATE (w2n n) 0w) =
   TAKE (w2n n) (DROP (w2n y) t.vs_memory ++ REPLICATE (w2n n) 0w)` by
    (irule focus_hash_log_payload >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  irule focus_sha3_successor >> rpt (goal_assum (drule_at Any)) >> simp[] >>
  metis_tac[]
QED

Resume focus_hash_log_execution[log]:
  `inst.inst_opcode = LOG` by fs[MEM] >>
  `?tc rest. inst.inst_operands = Lit tc::rest /\ LENGTH rest = w2n tc+2 /\
             inst.inst_outputs = []` by gvs[inst_wf_def] >>
  `?addr szop topics. REVERSE rest = addr::szop::topics` by
    (Cases_on `REVERSE rest` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  qabbrev_tac `ops = <|iao_ofst := addr; iao_size := SOME szop;
                       iao_max_size := SOME szop|>` >>
  `mem_read_ops inst = SOME ops /\ inst_read_op inst = SOME addr /\
   ops.iao_ofst = addr` by
    (simp[Abbr `ops`, mem_read_ops_def, inst_read_op_def] >> Cases_on `topics` >> simp[]) >>
  `MEM addr inst.inst_operands /\
   (!op. MEM op (szop::topics) ==> MEM op inst.inst_operands)` by
    (simp[] >> metis_tac[MEM_REVERSE, MEM]) >>
  `!v. MEM (Var v) (szop::topics) ==> v NOTIN fn_pv P fn` by
    metis_tac[concretizePtrHashLogFamilyTheory.ptr_log_scalar_vars] >>
  `EVERY (\op. eval_operand op s = eval_operand op t) (szop::topics)` by
    (rewrite_tac[EVERY_MEM] >> gen_tac >> strip_tac >> BETA_TAC >>
     irule focus_hash_log_scalar_eval >> rpt (goal_assum (drule_at Any)) >> metis_tac[]) >>
  `eval_operand szop s = eval_operand szop t /\
   eval_operands topics s = eval_operands topics t` by
    (gvs[] >> irule focus_hash_log_eval_operands >> simp[]) >>
  `?y n vals. eval_operand addr t = SOME y /\ eval_operand szop t = SOME n /\
              eval_operands topics t = SOME vals` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[step_inst_non_invoke] >> pure_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[] >> simp[Once opcode_case_def, AllCaseEqs()] >> metis_tac[]) >>
  `?x. eval_operand addr s = SOME x` by
    (qpat_assum `!op. IS_SOME (eval_operand op s) = _` (qspec_then `addr` mp_tac) >>
     Cases_on `eval_operand addr s` >> simp[]) >>
  `MEM (w2n x,w2n n) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  `TAKE (w2n n) (DROP (w2n x) s.vs_memory ++ REPLICATE (w2n n) 0w) =
   TAKE (w2n n) (DROP (w2n y) t.vs_memory ++ REPLICATE (w2n n) 0w)` by
    (irule focus_hash_log_payload >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[ptr_history_content_call_ctx] >>
  `?ev. step_inst 0 C inst s = OK (s with vs_logs := s.vs_logs ++ [ev]) /\
       postt = t with vs_logs := t.vs_logs ++ [ev]` by
    (irule concretizePtrHashLogFamilyTheory.ptr_log_execution >> rpt (goal_assum (drule_at Any)) >>
     simp[] >> metis_tac[]) >>
  qexists `s with vs_logs := s.vs_logs ++ [ev]` >>
  drule_all concretizePtrHashLogFamilyTheory.ptr_log_successor_relations >> gvs[]
QED

Finalise focus_hash_log_execution[local]

Theorem ptr_focus_hash_log_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state /\
  o1_ctx_shape C /\ EVERY ssa_form C.ctx_functions /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  (!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
        ?p. FLOOKUP (lp a.po_fn) (Allocation ai.inst_id) = SOME p) /\
  MEM a.po_inst.inst_opcode [SHA3; LOG] /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  ptr_chrono_step C' at zt /\
  (!ops x y n.
     mem_read_ops a.po_inst = SOME ops /\ inst_read_op a.po_inst = SOME ops.iao_ofst /\
     MEM ops.iao_ofst a.po_inst.inst_operands /\
     eval_operand ops.iao_ofst a.po_state = SOME x /\
     eval_operand ops.iao_ofst at.po_state = SOME y /\
     MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\
     ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
     !j. j < n /\ w2n x + j NOTIN a.po_taint.t_mem ==>
       read_byte (w2n x+j) a.po_state.vs_memory = read_byte (w2n y+j) at.po_state.vs_memory) ==>
  ?z TG'. ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
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
  `!out. MEM out a.po_inst.inst_outputs ==> ~retpc_var a.po_fn out` by
    (gen_tac >> disch_tac >> irule noncopy_output_not_retpc >>
     conj_tac >- fs[EVERY_MEM] >> qexists `a.po_inst` >> fs[MEM]) >>
  `at.po_inst = a.po_inst /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ ~is_terminator a.po_inst.inst_opcode` by
    (fs[MEM] >> simp[concretize_positions_unchanged, is_terminator_def]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  suspend "edge"
QED

Resume ptr_focus_hash_log_step[edge]:
  `!fuel ret s. step_inst fuel C' a.po_inst at.po_state <> IntRet ret s` by
    (simp[step_inst_non_invoke] >> rpt strip_tac >>
     drule step_inst_base_intret_opcodes >> fs[MEM]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"] >>
  `?post. step_inst 0 C a.po_inst a.po_state = OK post /\
    ptr_mixed_vars births positions (step_prov PT TG a.po_inst post)
      (step_taint a.po_inst a.po_state post a.po_taint) a.po_fn at.po_fn post s' /\
    ptr_history_content (step_taint a.po_inst a.po_state post a.po_taint) post s' /\
    post.vs_allocas = a.po_state.vs_allocas /\ post.vs_params = a.po_state.vs_params /\
    s'.vs_params = at.po_state.vs_params` by
    (irule focus_hash_log_execution >>
     fs[ptr_paired_sample_def] >> rpt (goal_assum (drule_at Any)) >> simp[] >>
     metis_tac[]) >>
  suspend "attach"
QED

Resume ptr_focus_hash_log_step[attach]:
  markerLib.RESUME_TAC >>
  `post.vs_current_bb = a.po_state.vs_current_bb /\ post.vs_prev_bb = a.po_state.vs_prev_bb /\
   s'.vs_current_bb = at.po_state.vs_current_bb /\ s'.vs_inst_idx = at.po_state.vs_inst_idx /\
   s'.vs_prev_bb = at.po_state.vs_prev_bb` by metis_tac[step_preserves_control_flow] >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (irule ptr_ordinary_next_active >> metis_tac[]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  qexistsl_tac [`z`, `step_prov PT TG a.po_inst z.po_state`] >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    suspend "sample" >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, ptr_tagged_step_def] >>
  simp[step_prov_def, out_prov_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
  qexistsl_tac [`0`, `post`] >> simp[]
QED

Resume ptr_focus_hash_log_step[sample]:
  markerLib.RESUME_TAC >>
  simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  gvs[step_prov_def, out_prov_def] >>
  irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >> simp[]
QED

Finalise ptr_focus_hash_log_step
