(* Actual decoder allocations, including allocations emitted in CFG blocks. *)
Theory actualDecoderSites
Ancestors
  allocaSiteResource actualAllocCredit abiAllocationHistory abiDecoderCode abiDecoderContract
  abiDecoderIndexInit emitHelperProps exprLoweringProps emitHelper context rich_list
  abiEncoder compileEnv vyperCompiler venomInst venomState finite_map list
  pred_set arithmetic words

Theorem actual_decoder_sites_finite:
  FINITE {i.inst_id | MEM i code /\ i.inst_opcode = ALLOCA /\
    abi_decoder_code_member i last /\ ~abi_decoder_code_member i first}
Proof
  irule SUBSET_FINITE_I >> qexists `set (MAP (\i. i.inst_id) code)` >>
  simp[listTheory.MEM_MAP, SUBSET_DEF] >> metis_tac[]
QED

Theorem actual_decoder_site_size:
  abi_decoder_code first last /\ MEM inst (fn_insts fn) /\
  abi_decoder_code_member inst last /\ ~abi_decoder_code_member inst first /\
  inst.inst_opcode = ALLOCA ==>
  first.cs_next_id <= inst.inst_id /\ inst.inst_id < last.cs_next_id /\
  alloca_size inst = 32 /\ MEM inst (fn_insts fn)
Proof
  strip_tac >> drule_all abi_decoder_code_alloca >> strip_tac >>
  simp[alloca_size_def, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem actual_decoder_site_fresh_credit:
  abi_decoder_code first last /\ abi_decoder_code_member inst last /\
  ~abi_decoder_code_member inst first /\ inst.inst_opcode = ALLOCA /\
  MEM inst (fn_insts fn) /\ inst.inst_id NOTIN FDOM s.vs_allocas /\
  alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) ==>
  s.vs_alloca_next + 32 < dimword (:256)
Proof
  strip_tac >> drule_all actual_decoder_site_size >> strip_tac >>
  drule_all actual_word_alloca_no_wrap >> simp[]
QED

Theorem actual_site_absent_from_history:
  abi_alloca_history code s /\
  (!inst. MEM inst code ==> inst.inst_id <> id) ==>
  FLOOKUP s.vs_allocas id = NONE
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id` >> simp[] >>
  PairCases_on `x` >> gvs[abi_alloca_history_def] >>
  metis_tac[]
QED

Theorem calldata_decoder_site_size:
  compile_abi_decode_to_buf dst src CALLDATALOAD base_op (Lit 0w) info first = ((),last) /\
  abi_decoder_code_member inst last /\ ~abi_decoder_code_member inst first /\
  inst.inst_opcode = ALLOCA ==>
  first.cs_next_id <= inst.inst_id /\ inst.inst_id < last.cs_next_id /\
  alloca_size inst = 32
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_to_buf_code >> strip_tac >>
  drule_all abi_decoder_code_alloca >> strip_tac >>
  simp[alloca_size_def, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem actual_decoder_site_absent_after_prefix:
  run_inst_seq prefix s = OK t /\ s.vs_allocas = FEMPTY /\
  (!inst. MEM inst prefix ==> inst.inst_id < first.cs_next_id) /\
  first.cs_next_id <= id ==>
  FLOOKUP t.vs_allocas id = NONE
Proof
  strip_tac >>
  `abi_alloca_history prefix s` by (irule abi_alloca_history_empty >> simp[]) >>
  `abi_alloca_history prefix t` by
    (irule abi_alloca_history_sequence >> qexistsl [`prefix`, `s`] >> simp[]) >>
  irule actual_site_absent_from_history >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem actual_decoder_child_sites_subset:
  abi_decoder_code parent child /\ abi_decoder_code child child_end /\
  abi_decoder_code child_end parent_end ==>
  {i.inst_id | MEM i code /\ i.inst_opcode = ALLOCA /\
    child.cs_next_id <= i.inst_id /\ i.inst_id < child_end.cs_next_id} SUBSET
  {i.inst_id | MEM i code /\ i.inst_opcode = ALLOCA /\
    parent.cs_next_id <= i.inst_id /\ i.inst_id < parent_end.cs_next_id}
Proof
  simp[SUBSET_DEF] >> rpt strip_tac >>
  drule_all abi_decoder_code_child_interval >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem actual_decoder_sequential_sites_disjoint:
  abi_decoder_code first middle /\ abi_decoder_code middle last ==>
  DISJOINT
    {i.inst_id | MEM i code /\ i.inst_opcode = ALLOCA /\
      first.cs_next_id <= i.inst_id /\ i.inst_id < middle.cs_next_id}
    {i.inst_id | MEM i code /\ i.inst_opcode = ALLOCA /\
      middle.cs_next_id <= i.inst_id /\ i.inst_id < last.cs_next_id}
Proof
  simp[DISJOINT_DEF, EXTENSION] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >> gvs[] >> decide_tac
QED

Theorem actual_index_init_allocation_site:
  abi_decode_index_init first = (ip,last) ==>
  ?inst. MEM inst (emitted_insts first last) /\
    inst.inst_id = first.cs_next_id /\ inst.inst_opcode = ALLOCA /\
    alloca_size inst = 32
Proof
  simp[abi_decode_index_init_def, compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND] >>
  qexists `mk_inst first.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString first.cs_next_var)]` >>
  simp[mk_inst_def, alloca_size_def,
       dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem actual_index_init_function_site:
  abi_decode_index_init first = (ip,last) /\
  (!i. MEM i (emitted_insts first last) ==> MEM i (fn_insts fn)) ==>
  ?inst. MEM inst (fn_insts fn) /\ inst.inst_id = first.cs_next_id /\
    inst.inst_opcode = ALLOCA /\ alloca_size inst = 32
Proof
  strip_tac >> drule actual_index_init_allocation_site >>
  strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

(* Actual-site credit is supplied by the expression state relation, also
   when this scratch instruction has executed on an earlier loop entry. *)
Theorem actual_decoder_caller_site_execute:
  stmt_state_rel ctx fn ce cx es s /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit 32w] /\ inst.inst_outputs = [out] ==>
  ?t b. exec_alloca inst s (32w:bytes32) = OK t /\
    alloca_room ctx fn t /\ alloca_inv t /\
    lookup_var out t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\ b + 32 <= t.vs_alloca_next /\
    (!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> irule alloca_site32_execute >>
  gvs[stmt_state_rel_def] >> rpt strip_tac >>
  first_x_assum drule_all >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem actual_index_init_allocation_instruction:
  abi_decode_index_init first = (ip,last) ==>
  MEM (mk_inst first.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString first.cs_next_var)]) (emitted_insts first last)
Proof
  simp[abi_decode_index_init_def, compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND]
QED

Theorem actual_index_init_caller_allocation:
  abi_decode_index_init first = (ip,last) /\
  (!i. MEM i (emitted_insts first last) ==> MEM i (fn_insts fn)) /\
  stmt_state_rel ctx fn ce cx es s ==>
  ?t b.
    exec_alloca (mk_inst first.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString first.cs_next_var)]) s (32w:bytes32) = OK t /\
    alloca_room ctx fn t /\ alloca_inv t /\
    FLOOKUP t.vs_allocas first.cs_next_id = SOME (b,32) /\
    b + 32 <= t.vs_alloca_next /\ t.vs_memory = s.vs_memory
Proof
  strip_tac >> drule actual_index_init_allocation_instruction >> strip_tac >>
  `MEM (mk_inst first.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString first.cs_next_var)]) (fn_insts fn)` by metis_tac[] >>
  drule actual_decoder_caller_site_execute >>
  disch_then drule >> simp[mk_inst_def] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Resources charged to actual function instructions, independent of ABI validity. *)
Definition decode_site_resources_def:
  decode_site_resources ctx fn s <=>
    alloca_room ctx fn s /\ alloca_inv s /\ fmp_room ctx fn s /\
    (!i n b sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit n] /\
      FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n n)
End

Theorem stmt_state_rel_decode_site_resources:
  stmt_state_rel ctx fn ce cx es s ==> decode_site_resources ctx fn s
Proof
  rw[stmt_state_rel_def, decode_site_resources_def] >> metis_tac[]
QED

Theorem decode_site_resources_exec_alloca:
  decode_site_resources ctx fn s /\ fn_inst_ids_distinct fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit n] /\ inst.inst_outputs = [out] /\
  exec_alloca inst s n = OK t ==>
  decode_site_resources ctx fn t
Proof
  strip_tac >> fs[decode_site_resources_def] >>
  `!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n` by
    metis_tac[] >>
  `alloca_room ctx fn t /\ alloca_inv t` by
    (drule_all alloca_site_execute >> strip_tac >> gvs[]) >>
  `fmp_room ctx fn t` by metis_tac[fmp_room_exec_alloca] >>
  simp[decode_site_resources_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (gvs[venomExecSemanticsTheory.exec_alloca_def, update_var_def,
          FLOOKUP_UPDATE] >>
      Cases_on `inst.inst_id = i.inst_id`
      >- (`inst = i` by metis_tac[localPtrsPropsTheory.fn_inst_ids_distinct_inj] >>
          gvs[]) >>
      gvs[] >> metis_tac[]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
  qpat_x_assum `!b sz. SOME entry = SOME (b,sz) ==> _` kall_tac >>
  PairCases_on `entry` >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     simp[venomExecSemanticsTheory.exec_alloca_def] >>
     strip_tac >> gvs[update_var_def]) >>
  metis_tac[]
QED

Theorem decode_site_allocation:
  decode_site_resources ctx fn s /\ fn_inst_ids_distinct fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit n] /\ inst.inst_outputs = [out] ==>
  ?t b. exec_alloca inst s n = OK t /\ decode_site_resources ctx fn t /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,w2n n) /\
    lookup_var out t = SOME (n2w b) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    b + w2n n <= t.vs_alloca_next /\
    (!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
    t = s with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
                vs_alloca_next := t.vs_alloca_next|>
Proof
  strip_tac >>
  `alloca_room ctx fn s /\ alloca_inv s /\
   (!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n)` by
    (fs[decode_site_resources_def] >> metis_tac[]) >>
  drule_all alloca_site_execute >> strip_tac >>
  `decode_site_resources ctx fn t` by
    (irule decode_site_resources_exec_alloca >> metis_tac[]) >>
  qexistsl_tac [`t`, `b`] >> simp[] >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (simp[venomExecSemanticsTheory.exec_alloca_def, update_var_def] >>
      strip_tac >> gvs[]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
  qpat_x_assum `!b sz. SOME entry = SOME (b,sz) ==> _` kall_tac >>
  PairCases_on `entry` >>
  simp[venomExecSemanticsTheory.exec_alloca_def, update_var_def] >>
  strip_tac >> gvs[]
QED
