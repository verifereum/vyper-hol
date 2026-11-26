(* The real SHA suffix cannot add taint below the entry allocation floor. *)
Theory bodyShaSuffixLowTaintMods
Ancestors
  bodyPtrIfExpAllocSeparation stmtReasonMemory ptrSafetyTransport taintAgree
  lowerDloadPtrScalar fragGasSeqPtr fragExec instIdxIndep ptrDiscipline
  exprSimHash builtinHashing context emitHelper compileEnv exprLoweringProps
  bufferAllocationExecution
  venomExecSemantics venomInst venomState list rich_list finite_map pred_set words

Theorem sha_mem_step_low[local]:
  step_inst_base inst s = OK t /\ lo <= s.vs_alloca_next /\
  inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> SETFMP /\
  inst.inst_opcode <> DRET /\ i < lo /\ i NOTIN written_taint tn inst s /\
  i IN (step_taint inst s t tn).t_mem ==> i IN tn.t_mem
Proof
  strip_tac >>
  `i < s.vs_alloca_next` by decide_tac >>
  drule_all_then assume_tac step_inst_base_new_site_bytes_frontier >>
  gvs[step_taint_def, mem_taint_def]
QED

Theorem sha_step_floor[local]:
  step_inst_base inst s = OK t /\ inst.inst_opcode <> INVOKE /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  allocas_from lo (t with vs_inst_idx := k) /\ lo <= (t with vs_inst_idx := k).vs_alloca_next
Proof
  strip_tac >>
  `step_inst 0 ctx inst s = OK t` by simp[step_inst_non_invoke] >>
  drule_all_then strip_assume_tac step_inst_allocas_from >>
  conj_tac
  >- (qpat_x_assum `allocas_from lo t` mp_tac >> simp[allocas_from_def]) >>
  simp[]
QED

Theorem sha_no_store_seq_low[local]:
  !code s G tn. EVERY (\inst. MEM inst.inst_opcode
       [ALLOCA; MLOAD; ADD; GAS; STATICCALL; ASSERT]) code /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    inst_seq_ptr D lo ctx func PG G tn code s Gf tf ==>
    !i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK t` >>
  `h.inst_opcode <> INVOKE /\ h.inst_opcode <> DALLOCA /\
   h.inst_opcode <> SETFMP /\ h.inst_opcode <> DRET /\
   ~MEM h.inst_opcode [MSTORE; ISTORE; MCOPY]` by (fs[] >> metis_tac[]) >>
  drule_all_then (qspec_then `SUC s.vs_inst_idx` strip_assume_tac) sha_step_floor >>
  rpt strip_tac >>
  `i IN (step_taint h s t tn).t_mem` by metis_tac[] >>
  irule sha_mem_step_low >>
  qexistsl_tac [`h`,`lo`,`s`,`t`] >> simp[written_taint_opcode_exclusion]
QED

Theorem sha_fixed_taint_layout[local]:
  compile_sha256_bytesm x n sm = (op,sb) ==>
  ?tail. emitted_insts sm sb =
    mk_inst sm.cs_next_id ALLOCA [Lit 32w] [STRING #"%" (toString sm.cs_next_var)] ::
    mk_inst (sm.cs_next_id+1) MSTORE [Var (STRING #"%" (toString sm.cs_next_var));x] [] :: tail /\
  EVERY (\inst. MEM inst.inst_opcode [ALLOCA; MLOAD; ADD; GAS; STATICCALL; ASSERT]) tail
Proof
  simp[compile_sha256_bytesm_def, compile_alloc_buffer_def, emit_op_def,
       emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[mk_inst_def]
QED

Theorem sha_bytes_taint_layout[local]:
  compile_sha256_bytes x sm = (op,sb) ==>
  EVERY (\inst. MEM inst.inst_opcode [ALLOCA; MLOAD; ADD; GAS; STATICCALL; ASSERT])
    (emitted_insts sm sb)
Proof
  simp[compile_sha256_bytes_def, compile_alloc_buffer_def, emit_op_def,
       emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[mk_inst_def]
QED

Theorem sha_staging_address_floor[local]:
  stmt_state_rel H ctx func ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit 32w] [p]) (fn_insts func) /\
  step_inst_base (mk_inst id ALLOCA [Lit 32w] [p]) s = OK t /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?a. eval_operand (Var p) (t with vs_inst_idx := k) = SOME a /\ lo <= w2n a
Proof
  strip_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all_then assume_tac (Q.INST [`n` |-> `32`] ifexp_alloca_base_bound) >>
  drule_all_then assume_tac (Q.INST [`n` |-> `32`] ifexp_alloca_step_base) >>
  qexists_tac `n2w (buffer_allocation_base s id)` >>
  `buffer_allocation_base s id < dimword (:256)` by decide_tac >>
  conj_tac
  >- (qpat_x_assum `lookup_var p t = _` mp_tac >> simp[lookup_var_def, eval_operand_def]) >>
  simp[w2n_n2w] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[buffer_allocation_base_def] >>
  qmatch_asmsub_rename_tac `FLOOKUP s.vs_allocas id = SOME site` >>
  PairCases_on `site` >>
  fs[buffer_allocation_base_def, allocas_from_def] >> metis_tac[]
QED

Theorem sha_fixed_seq_low[local]:
  stmt_state_rel H ctx func ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit 32w] [p]) (fn_insts func) /\
  EVERY (\inst. MEM inst.inst_opcode [ALLOCA; MLOAD; ADD; GAS; STATICCALL; ASSERT]) tail /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  inst_seq_ptr D lo ctx func PG G tn
    (mk_inst id ALLOCA [Lit 32w] [p] :: mk_inst j MSTORE [Var p;x] [] :: tail)
    s Gf tf ==>
  !i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem
Proof
  strip_tac >>
  qabbrev_tac `alloc = mk_inst id ALLOCA [Lit 32w] [p]` >>
  qabbrev_tac `store = mk_inst j MSTORE [Var p;x] []` >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ (_::_) _ _ _` mp_tac >>
  simp[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base alloc s` >> simp[] >>
  rpt strip_tac >> gvs[] >> rename1 `step_inst_base alloc s = OK u` >>
  qabbrev_tac `a = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `tn1 = step_taint alloc s u tn` >>
  `alloc.inst_opcode = ALLOCA` by simp[Abbr `alloc`, mk_inst_def] >>
  `i IN tn1.t_mem` suffices_by
    (strip_tac >> `i IN (step_taint alloc s u tn).t_mem` by fs[Abbr `tn1`] >>
     irule sha_mem_step_low >> qexistsl_tac [`alloc`,`lo`,`s`,`u`] >>
     simp[written_taint_opcode_exclusion]) >>
  `allocas_from lo a /\ lo <= a.vs_alloca_next` by
    (`alloc.inst_opcode <> INVOKE` by simp[] >>
     drule_all_then (qspec_then `SUC s.vs_inst_idx` assume_tac) sha_step_floor >>
     fs[Abbr `a`]) >>
  `?w. eval_operand (Var p) a = SOME w /\ lo <= w2n w` by
    (fs[Abbr `alloc`] >>
     drule_all_then (qspec_then `SUC s.vs_inst_idx`
       (qx_choose_then `addr` strip_assume_tac)) sha_staging_address_floor >>
     qexists_tac `addr` >> fs[Abbr `a`]) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ (store::_) _ _ _` mp_tac >>
  simp[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base store a` >> simp[] >>
  rpt strip_tac >> gvs[] >> rename1 `step_inst_base store a = OK v` >>
  `store.inst_opcode = MSTORE` by simp[Abbr `store`, mk_inst_def] >>
  `store.inst_opcode <> INVOKE` by simp[] >>
  drule_all_then (qspec_then `SUC a.vs_inst_idx` strip_assume_tac) sha_step_floor >>
  `i IN (step_taint store a v tn1).t_mem` by
    (irule sha_no_store_seq_low >>
     qpat_assum `inst_seq_ptr _ _ _ _ _ _ _ tail _ _ _` (irule_at Any) >>
     simp[]) >>
  irule sha_mem_step_low >> qexistsl_tac [`store`,`lo`,`a`,`v`] >> simp[] >>
  simp[Abbr `store`, mk_inst_def, written_taint_def] >>
  rpt strip_tac >> decide_tac
QED

Theorem sha_suffix_low_taint_mods:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sm sb) s = OK z /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) s Gf tf /\
  (compile_sha256_bytes x sm = (op,sb) \/
   (?n H ce cx es. compile_sha256_bytesm x n sm = (op,sb) /\
      stmt_state_rel H ctx func ce cx es s /\ fn_has_code sm sb func)) ==>
  !i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem
Proof
  strip_tac
  >- (drule_then assume_tac sha_bytes_taint_layout >>
      metis_tac[sha_no_store_seq_low]) >>
  drule_then strip_assume_tac sha_fixed_taint_layout >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w] [STRING #"%" (toString sm.cs_next_var)])
       (fn_insts func)` by
    (irule hash_emitted_inst_mem >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[sha_fixed_seq_low]
QED
