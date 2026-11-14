Theory calldataExactDynInitSequence
Ancestors
  calldataDynOwned calldataDynInit calldataBytesLive fragExecMem safeSequence
  abiDecoderGuards abiDecoderArrayLoopInit abiDecoderIndexInit
  arithmetic list words finite_map venomExecSemantics venomState venomMemDefs
  abiDecoderFrame abiDecoderContract abiDecoderDynarrayPrefix abiDecoderArrayHeader
  compileEnv emitHelper emitHelperProps abiEncoder actualAllocExec allocaFrontierBound
  allocaBudgetProps valueEncodingProps valueEncodingDefs rich_list
  abiDecoderDynarrayBound exprLoweringProps abiDecoderReentry venomInst abiDecoderFrameCompose
  calldataWordLeaf calldataBytesLeaf
Libs
  wordsLib

Definition calldata_exact_init_fields_def:
  calldata_exact_init_fields live slot ip cnt p d maxn srcword initial t <=>
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD srcword initial /\
    eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD srcword initial) /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
    (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= p \/ p+32 <= a) ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n initial.vs_memory) /\
    (!id. id <> slot ==> FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    FLOOKUP t.vs_allocas slot = SOME (p,32) /\
    (if FLOOKUP initial.vs_allocas slot = NONE then
       t.vs_alloca_next = initial.vs_alloca_next+32
     else t.vs_alloca_next = initial.vs_alloca_next) /\
    (!op. abi_decoder_operand_live live op ==>
      eval_operand op t = eval_operand op initial)
End

Theorem calldata_exact_array_loop_init_sequence:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\ unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+sz <= p \/ p+32 <= d) /\
  w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn ==>
  (!pre i post u. emitted_insts st loop_st = pre ++ i::post /\
     run_inst_seq pre initial = OK u ==> inst_mem_below_frontier i u) /\
  ?t. run_inst_seq (emitted_insts st loop_st) initial = OK t /\
    calldata_exact_init_fields st.cs_next_var header_st.cs_next_id
      ip cnt p d maxn srcword initial t
Proof
  PURE_REWRITE_TAC [calldata_exact_init_fields_def] >>
  MATCH_ACCEPT_TAC calldata_array_loop_init_accepted_sequence
QED

Theorem calldata_exact_array_loop_init_accepted:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\ unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+sz <= p \/ p+32 <= d) /\
  w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn ==>
  frag_exec_mem ctx st loop_st (\s. s=initial)
    (calldata_exact_init_fields st.cs_next_var header_st.cs_next_id
      ip cnt p d maxn srcword initial) (K F)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_exact_array_loop_init_sequence >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `inst_extends st loop_st` by metis_tac[inst_extends_trans] >>
  `emitted_insts st loop_st = emitted_insts st guard_st ++
      emitted_insts guard_st header_st ++ emitted_insts header_st loop_st` by
    metis_tac[emitted_insts_append, inst_extends_def, APPEND_ASSOC] >>
  `isPREFIX st.cs_current_insts loop_st.cs_current_insts` by
    (qpat_x_assum `inst_extends st loop_st` mp_tac >>
     simp_tac bool_ss [inst_extends_def] >> strip_tac >>
     simp_tac bool_ss [IS_PREFIX_APPEND] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
     (emitted_insts st loop_st)` by
    (imp_res_tac calldata_dynarray_prefix_opcodes >>
     imp_res_tac calldata_array_header_opcodes >>
     imp_res_tac abi_decode_index_init_opcodes >>
     asm_rewrite_tac[EVERY_APPEND]) >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> asm_rewrite_tac[] >>
  simp_tac bool_ss [] >> conj_tac >- metis_tac[] >>
  disj1_tac >> qexists_tac `t` >>
  gvs[calldata_exact_init_fields_def, instIdxIndepTheory.eval_op_inst_idx,
      mload_def] >> metis_tac[]
QED
