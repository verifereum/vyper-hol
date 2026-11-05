(* Successful array initialization with actual-site allocation resources. *)
Theory calldataValidOwnedInit
Ancestors
  calldataInitSequence calldataDynOwned calldataDynInit actualAllocExec allocaFrontierBound
  abiDecoderArrayLoopInit abiDecoderDynarrayBound abiDecoderReservation
  abiDecoderFrameCompose
  allocaBudgetProps abiDecoderDynarrayPrefix abiDecoderArrayHeader
  abiDecoderGuards abiDecoderIndexInit abiDecoderFrame abiDecoderContract
  abiDecoderExecution emitHelperProps exprLoweringProps compileEnv emitHelper
  venomState venomInst venomExecSemantics valueEncodingProps finite_map words
  arithmetic list rich_list

Theorem calldata_array_loop_init_valid_sequence:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\ fresh_vars_wrt st initial /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
    p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+sz <= p \/ p+32 <= d) /\ alloca_inv initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn ==>
  ?t. run_inst_seq (emitted_insts st loop_st) initial = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD srcword initial) /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD srcword initial /\
    FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (p,32)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst` by
    metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_fresh] >>
  drule_all calldata_array_loop_init_repeat_sequence >> strip_tac >>
  qexists_tac `t` >> simp[]
QED
