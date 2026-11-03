(* Actual decoder allocations, including allocations emitted in CFG blocks. *)
Theory actualDecoderSites
Ancestors
  actualAllocCredit abiAllocationHistory abiDecoderCode abiDecoderContract
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
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info first = ((),last) /\
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
