Theory readonlyInvokeCopyFwdExecutionObserverOperands
Ancestors
  readonlyInvokeCopyFwdExecutionObservers readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionReadClassification
  readonlyInvokeCopyFwdExecutionMemoryScalars
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdMapCoverage
  readonlyInvokeCopyFwdOpaque o1LowerDloadOccurrence internalReturnCopyFwdSim
  pointerConfinedDefs ptrDiscipline memLocDefs frameViewFacts
  allocaFrontierBound frameRelocationGuardedValues
  o1LowerDloadGhost o1LowerDloadRelocationKernel
  o1LowerDloadPtrDiscipline readonlyInvokeCopyFwdValues readonlyInvokeCopyFwdRel
  venomExecSemantics venomExecProps venomState venomInst codegenRel contextCodegenRel
  taintAgree
  venomWf finite_map list rich_list pred_set words

Theorem ricf_execution_sha3_operands_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_mapped_support a B E PG G sites /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = SHA3 /\ step_inst fuel C inst s = OK u /\
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
  `?addr sizeop out p size_word.
    inst.inst_operands = [addr;sizeop] /\ inst.inst_outputs = [out] /\
    eval_operand addr s = SOME p /\ eval_operand sizeop s = SOME size_word /\
    u = update_var out (word_of_bytes T (0w:bytes32)
      (Keccak_256_w64 (read_memory (w2n p) (w2n size_word) s))) s` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, GSYM read_memory_def] >>
     gvs[AllCaseEqs()] >> metis_tac[]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn addr = {} /\ op_taint tn sizeop = {}` by
    metis_tac[taint_ok_observation_operand, MEM] >>
  `eval_operand sizeop t = SOME size_word` by
    (mp_tac (Q.INST [`op` |-> `sizeop`, `x` |-> `size_word:256 word`,
       `rt` |-> `tn`] ricf_execution_nonaddress_operand) >>
     (impl_tac >- (simp[is_pointer_preserving_op_def, mem_read_ops_def,
       mem_write_ops_def] >> Cases_on `sizeop = addr` >> simp[FILTER])) >> simp[]) >>
  `!name. addr = Var name ==> ~retpc_var fn name` by
    (rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> simp[] >> metis_tac[active_inst_mem_fn_insts]) >>
  `?q. eval_operand addr t = SOME q /\
    read_memory (w2n p) (w2n size_word) s =
      read_memory (w2n q) (w2n size_word) t` by
    (mp_tac (Q.INST [`x` |-> `p:256 word`, `len` |-> `w2n (size_word:256 word)`,
       `ops` |-> `<|iao_ofst := addr; iao_size := SOME sizeop;
         iao_max_size := SOME sizeop|>`] ricf_execution_observer_read) >>
     (impl_tac >- simp[mem_read_ops_def, source_memory_read_ranges_def,
       memory_range_of_operands_def]) >> simp[]) >>
  gvs[] >>
  qexists_tac `update_var out (word_of_bytes T (0w:bytes32)
    (Keccak_256_w64 (read_memory (w2n p) (w2n size_word) s))) t` >>
  mp_tac (Q.INST [`addr` |-> `addr`, `lenop` |-> `sizeop`,
    `len` |-> `size_word:256 word`, `rt` |-> `tn`,
    `hash` |-> `word_of_bytes T (0w:bytes32)
      (Keccak_256_w64 (read_memory (w2n (p:256 word)) (w2n (size_word:256 word)) s))`]
    ricf_execution_sha3_next) >>
  (impl_tac >- simp[]) >>
  simp[occurrence_sites_step_def]
QED

Theorem ricf_execution_log_scalar[local]:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit tc :: REVERSE (addr::sizeop::tops) /\
  MEM op (sizeop::tops) /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[frame_reachable_prov_support] >>
  `fn_ptr_ok P fn /\ taint_ok fn tn inst s /\ MEM inst (fn_insts fn)` by
    metis_tac[EVERY_MEM, ptr_discipline_def, active_inst_mem_fn_insts] >>
  `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
  `op_prov G op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >>
     rename1 `FLOOKUP G vv` >> Cases_on `FLOOKUP G vv` >> simp[] >>
     `vv IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
     metis_tac[ptr_use_ok_log_scalar]) >>
  `op_taint tn op = {}` by
    (mp_tac taint_ok_observation_operand >>
     (impl_tac >- (simp[MEM_REVERSE] >> metis_tac[MEM])) >> simp[]) >>
  `!name. op = Var name ==> ~retpc_var fn name` by
    (rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> simp[MEM_REVERSE] >> metis_tac[MEM]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  drule_all ricf_opaque_frame_operand >> strip_tac >>
  gvs[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
    ricf_value_agree_def, ld_value_agree_def, word_agree_except_empty]
QED

Theorem ricf_execution_log_operands_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_mapped_support a B E PG G sites /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit tc :: REVERSE (addr::sizeop::tops) /\
  step_inst fuel C inst s = OK u /\
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
  `?p size_word topics. LENGTH tops = w2n tc /\
    eval_operand addr s = SOME p /\ eval_operand sizeop s = SOME size_word /\
    eval_operands tops s = SOME topics /\
    u = s with vs_logs := s.vs_logs ++
      [<|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
         data := read_memory (w2n p) (w2n size_word) s|>]` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, REVERSE_APPEND,
       GSYM read_memory_def] >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  `IS_SOME (eval_operands inst.inst_operands s)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_REVERSE, eval_operand_def] >>
     metis_tac[eval_operands_IS_SOME_EVERY, optionTheory.IS_SOME_EXISTS]) >>
  `~s.vs_call_ctx.cc_static` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
     Cases_on `s.vs_call_ctx.cc_static` >> simp[]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ taint_ok fn tn inst s` by
    metis_tac[ptr_discipline_def, frame_reachable_prov_support] >>
  `fn_inst_wf fn` by metis_tac[EVERY_MEM] >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by gvs[inst_wf_def] >>
  `step_taint inst s u tn = tn` by metis_tac[step_taint_log_logs] >>
  `eval_operand sizeop t = SOME size_word` by
    (mp_tac (Q.INST [`op` |-> `sizeop`, `x` |-> `size_word:256 word`]
       ricf_execution_log_scalar) >> (impl_tac >- simp[]) >> simp[]) >>
  `eval_operands tops t = SOME topics` by
    (mp_tac (Q.SPECL [`tops`,`t`,`s`] eval_operands_agree) >>
     (impl_tac >- (rpt strip_tac >>
     `?x. eval_operand op s = SOME x` by
       (fs[GSYM optionTheory.IS_SOME_EXISTS, eval_operands_IS_SOME_EVERY, EVERY_MEM] >>
        metis_tac[]) >>
     mp_tac ricf_execution_log_scalar >>
     (impl_tac >- simp[]) >> simp[])) >> simp[]) >>
  `op_taint tn addr = {}` by
    (mp_tac (Q.INST [`op` |-> `addr`] taint_ok_observation_operand) >>
     (impl_tac >- simp[MEM_REVERSE]) >> simp[]) >>
  `!name. addr = Var name ==> ~retpc_var fn name` by
    (rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> simp[MEM_REVERSE] >>
     metis_tac[active_inst_mem_fn_insts]) >>
  `?q. eval_operand addr t = SOME q /\
    read_memory (w2n p) (w2n size_word) s =
      read_memory (w2n q) (w2n size_word) t` by
    (mp_tac (Q.INST [`x` |-> `p:256 word`, `len` |-> `w2n (size_word:256 word)`,
       `ops` |-> `<|iao_ofst := addr; iao_size := SOME sizeop;
         iao_max_size := SOME sizeop|>`] ricf_execution_observer_read) >>
     (impl_tac >- (Cases_on `tops` >>
       simp[mem_read_ops_def, source_memory_read_ranges_def,
         memory_range_of_operands_def, REVERSE_APPEND] >>
       IF_CASES_TAC >> fs[] >> decide_tac)) >> simp[]) >>
  gvs[] >>
  qabbrev_tac `ev = <|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
    data := read_memory (w2n p) (w2n size_word) s|>` >>
  qexists_tac `t with vs_logs := t.vs_logs ++ [ev]` >>
  mp_tac (Q.INST [`lenop` |-> `sizeop`, `len` |-> `size_word:256 word`,
    `ev` |-> `ev`] ricf_execution_log_next) >>
  (impl_tac >- simp[Abbr `ev`]) >>
  fs[Abbr `ev`, step_prov_def, out_prov_def, set_prov_def,
    DRESTRICT_UNIV, occurrence_sites_step_def]
QED
