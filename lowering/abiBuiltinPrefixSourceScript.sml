(* Full source-success decoding of static aggregates and dynamic arrays with
   static elements. The source may contain trailing noncanonical bytes. *)
Theory abiBuiltinPrefixSource
Ancestors
  abiValidPrefixSource abiBuiltinPrefixDecode abiBuiltinPrefixInput abiBuiltinSource
  abiBuiltinDecodeEffect abiDecoderCoherence abiDecoderContract abiDecoderLoop abiDecoderReentry
  abiEncoder builtinAbi fragExec compileEnv valueEncoding vyperABI contractABI venomState words
  list

Theorem lower_abi_decode_valid_prefix_source:
  lower_abi_decode data (type_to_abi_dec_info sf ce ty) min_size max_size
    (type_memory_bytes ce ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf ty tv /\ evaluate_abi_decode env ty bs = INL v /\
  (~is_dynamic (vyper_to_abi_type env ty) \/
    ?elem. vyper_to_abi_type env ty = Array NONE elem /\ ~is_dynamic elem) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) src_base initial.vs_memory /\
  eval_operand data initial = SOME (n2w src_base) /\ abi_decoder_operand_live start.cs_next_var data /\
  abi_builtin_decode_resources start first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) src_base d b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce ty)
      b cap initial actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_prefix_pre_valid_source >> strip_tac >>
  drule_all lower_abi_decode_prefix >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
