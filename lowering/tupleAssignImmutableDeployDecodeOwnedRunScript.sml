(* Raw TupleT decoding retains its output owner at the execution witness.
   Resources are exactly those of the existing source-valid runtime boundary;
   this theorem does not assert a gas path or synthesize those resources. *)
Theory tupleAssignImmutableDeployDecodeOwnedRun
Ancestors
  tupleAssignImmutableDeployDecodeBoundary abiBuiltinValidSource abiBuiltinValidInput
  abiBuiltinSetupReach abiBuiltinAllocation abiBuiltinDecodeCorrect abiBuiltinDecodeEffect
  abiDecoderValidRecursive abiDecoderEffect abiDecoderContract abiDecoderLoop
  abiValidBytesUnwrap abiBuiltinSource builtinAbi fragExec compileEnv valueEncoding vyperContext
  vyperValue venomState words list arithmetic finite_map

Theorem tuple_immutable_decode_owned_run:
  abi_decoder_coherent ce (get_tenv cx) sf (TupleT tys) tv /\
  evaluate_type_builtin cx (AbiDecode F) (TupleT tys) arg_tys
    [vyperValue$BytesV bs] = INL v /\
  lower_abi_decode data (type_to_abi_dec_info sf ce (TupleT tys)) min_size max_size
    (type_memory_bytes ce (TupleT tys)) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) src_base initial.vs_memory /\
  eval_operand data initial = SOME (n2w src_base) /\ abi_decoder_operand_live start.cs_next_var data /\
  abi_builtin_decode_resources start first last min_size max_size (type_memory_bytes ce (TupleT tys))
    (LENGTH bs) src_base d b cap initial /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce (TupleT tys))
      b cap initial actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    FLOOKUP actual.vs_allocas (abi_builtin_decode_output_site start min_size max_size) =
      SOME (d,type_memory_bytes ce (TupleT tys)) /\
    start.cs_next_id <= abi_builtin_decode_output_site start min_size max_size /\
    abi_builtin_decode_output_site start min_size max_size < final.cs_next_id
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `evaluate_abi_decode (get_tenv cx) (TupleT tys) bs = INL v` by
    metis_tac[abi_source_decode_wrapping_iff] >>
  drule_all abi_builtin_valid_pre_from_source >> strip_tac >>
  drule lower_abi_decode_setup_trace >> strip_tac >>
  drule_all abi_builtin_decode_code >> strip_tac >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  drule_all abi_builtin_valid_source >> strip_tac >>
  qpat_assum `abi_builtin_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_valid_pre_def]) >>
  qpat_assum `abi_builtin_decode_resources _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_decode_resources_def]) >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ src_base < dimword (:256) /\
   type_memory_bytes ce (TupleT tys) < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `p` |-> `n2w src_base:bytes32`,
    `outsz` |-> `type_memory_bytes ce (TupleT tys)`, `cnt` |-> `LENGTH (bs:word8 list)`]
    abi_builtin_decode_setup_reach) >>
  (impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w]) >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `eval_operand (FST (SND ops)) prepared = SOME (n2w (src_base + 32)) /\
   eval_operand (SND (SND ops)) prepared = SOME (n2w (LENGTH bs))`
    by asm_simp_tac (srw_ss()) [word_add_n2w] >>
  drule_all abi_builtin_valid_pre_ready >> strip_tac >>
  drule_at (Pat `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_decoder_valid_decode >>
  disch_then (qspecl_then [`limit_st`, `last`, `func`, `first`, `final`, `ctx`] mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  rename1 `val_in_memory tv v d actual.vs_memory` >>
  `eval_operand (FST ops) actual = SOME (n2w d)` by fs[abi_decoder_effect_def] >>
  `FLOOKUP actual.vs_allocas (abi_builtin_decode_output_site start min_size max_size) =
    SOME (d,type_memory_bytes ce (TupleT tys))` by
    (irule tuple_immutable_decode_retains_output >> metis_tac[]) >>
  mp_tac (Q.INST [`st` |-> `start`,
    `site` |-> `abi_builtin_decode_output_site start min_size max_size`,
    `outsz` |-> `type_memory_bytes ce (TupleT tys)`] abi_builtin_decode_effect_compose) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  conj_tac
  >- (irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  decide_tac
QED
