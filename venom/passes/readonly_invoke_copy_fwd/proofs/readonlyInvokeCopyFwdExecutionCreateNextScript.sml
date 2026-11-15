Theory readonlyInvokeCopyFwdExecutionCreateNext
Ancestors
  readonlyInvokeCopyFwdExecutionCreate readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionReadClassification
  readonlyInvokeCopyFwdExecutionMemoryScalars readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdStepsExternalOracle readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdMapCoverage
  o1LowerDloadOccurrence internalReturnCopyFwdSim allocaFrontierBound
  lowerDloadPtrCreateInterfaces pointerConfinedDefs ptrDiscipline memLocDefs
  frameViewFacts frameRel taintAgree venomCallOracleDefs extCallOracle
  venomExecSemantics venomState venomInst codegenRel contextCodegenRel
  finite_map list pred_set words

Theorem ricf_opaque_create_request[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t ==>
  venom_create_request s value off sz salt =
    venom_create_request t value off' sz salt
Proof
  strip_tac >> fs[ricf_opaque_frame_agree_def, read_memory_def] >>
  drule ricf_create_request_agree >>
  simp[ricf_opaque_view_def, venom_create_request_def, read_memory_def] >>
  metis_tac[]
QED

Theorem ricf_execution_create_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_mapped_support a B E PG G sites /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `?vop addr sizeop salt_ops value off size_word salt.
    eval_operand vop s = SOME value /\ eval_operand addr s = SOME off /\
    eval_operand sizeop s = SOME size_word /\
    inst.inst_operands = [vop;addr;sizeop] ++ salt_ops /\
    ((inst.inst_opcode = CREATE /\ salt_ops = [] /\ salt = NONE) \/
     (inst.inst_opcode = CREATE2 /\ ?sop sw. salt_ops = [sop] /\
       eval_operand sop s = SOME sw /\ salt = SOME sw)) /\
    ~s.vs_call_ctx.cc_static /\ exec_create inst s value off size_word salt = OK u` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     gvs[MEM] >> simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[AllCaseEqs()] >> rpt strip_tac >>
     gvs[eval_operands_def] >> metis_tac[]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `tn.t_stor = {} /\ tn.t_trans = {} /\
   (!op. MEM op inst.inst_operands ==> op_taint tn op = {})` by
    (gvs[MEM, taint_ok_def] >> metis_tac[]) >>
  `!op x. MEM op (vop::sizeop::salt_ops) /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`rt` |-> `tn`] ricf_execution_nonaddress_operand) >>
     (impl_tac >- (simp[Excl "FILTER"] >>
       gvs[Excl "FILTER", MEM, is_pointer_preserving_op_def,
         mem_read_ops_def, mem_write_ops_def] >>
       rpt strip_tac >> gvs[Excl "FILTER"] >>
       qpat_x_assum `FILTER _ _ = [_]` mp_tac >> simp[FILTER] >>
       rpt (IF_CASES_TAC >> simp[]))) >> simp[]) >>
  `eval_operand vop t = SOME value /\ eval_operand sizeop t = SOME size_word /\
   (inst.inst_opcode = CREATE2 ==>
     ?sop sw. salt_ops = [sop] /\ eval_operand sop t = SOME sw /\ salt = SOME sw)` by
    (gvs[MEM] >> metis_tac[]) >>
  qpat_x_assum `!op x. _` (K ALL_TAC) >>
  `!name. addr = Var name ==> ~retpc_var fn name` by
    (rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> simp[] >> metis_tac[MEM, active_inst_mem_fn_insts]) >>
  `?off'. eval_operand addr t = SOME off' /\
    read_memory (w2n off) (w2n size_word) s =
      read_memory (w2n off') (w2n size_word) t` by
    (mp_tac (Q.INST [`x` |-> `off:256 word`,
       `len` |-> `w2n (size_word:256 word)`,
       `ops` |-> `<|iao_ofst := addr; iao_size := SOME sizeop;
         iao_max_size := SOME sizeop|>`] ricf_execution_observer_read) >>
     (impl_tac >- (gvs[MEM] >> simp[mem_read_ops_def,
       source_memory_read_ranges_def, memory_range_of_operands_def])) >> simp[]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  `t.vs_call_ctx = s.vs_call_ctx` by
    (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >>
     drule taint_agree_call_ctx >> simp[ricf_opaque_view_def]) >>
  `step_inst fuel Ct inst t = exec_create inst t value off' size_word salt` by
    (fs[MEM] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
      eval_operands_def]) >>
  `?out w r. inst.inst_outputs = [out] /\
    w2n size_word <= 2 * max_code_size /\
    consume_create_outcome (venom_create_request s value off size_word salt) s = (w,r) /\
    u = update_var out w r` by metis_tac[dload_exec_create_success_iff] >>
  `venom_create_request s value off size_word salt =
    venom_create_request t value off' size_word salt` by
    (mp_tac (Q.INST [`X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`,
       `PG` |-> `ricf_complete_params PG s.vs_params`,
       `sz` |-> `size_word:256 word`] ricf_opaque_create_request) >>
     (impl_tac >- simp[]) >> simp[]) >>
  `!z v. consume_create_outcome
      (venom_create_request s value off size_word salt) t = (z,v) ==>
    step_inst fuel Ct inst t = OK (update_var out z v)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `step_inst fuel Ct inst t = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[exec_create_def, LET_THM] >>
     qpat_assum `venom_create_request s value off size_word salt = _`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     qpat_assum `consume_create_outcome _ t = (z,v)`
       (fn th => pure_rewrite_tac[th]) >>
     simp[Excl "consume_create_outcome_eq"]) >>
  `r.vs_allocas = s.vs_allocas /\ r.vs_fmp = s.vs_fmp` by
    (qpat_x_assum `consume_create_outcome _ s = (w,r)` mp_tac >>
     simp[consume_create_outcome_eq] >> rpt strip_tac >> gvs[]) >>
  `step_prov PG G inst (update_var out w r) = set_prov G [out] NONE /\
   step_taint inst s (update_var out w r) tn =
     tn with t_var := set_var_taint tn.t_var [out] {} /\
   occurrence_sites_step a B inst (update_var out w r) = B` by
    (fs[MEM, Excl "consume_create_outcome_eq"] >>
     simp[step_prov_def, out_prov_def, step_taint_def, out_taint_def,
      mem_taint_def, store_taint_def, imm_taint_def, new_site_bytes_def,
      step_writes_def, written_taint_def, occurrence_sites_step_def,
      source_memory_write_ranges_def, range_bytes_def, adopt_reset_def,
      taint_component_equality, update_var_def, FLOOKUP_DEF,
      Excl "consume_create_outcome_eq"] >>
     simp[EXTENSION] >> metis_tac[]) >>
  mp_tac (Q.INST [`rq` |-> `venom_create_request s value off size_word salt`]
    ricf_execution_consume_create_next) >>
  (impl_tac >- (gvs[Excl "consume_create_outcome_eq"] >> metis_tac[])) >>
  simp[Excl "consume_create_outcome_eq"]
QED
