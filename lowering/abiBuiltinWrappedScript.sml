Theory abiBuiltinWrapped
Ancestors
  abiValidWrapped abiValidSingletonPrefix abiBuiltinPrefixSource abiBuiltinSource
  abiBuiltinDecodeSetup abiBuiltinSetupReach abiBuiltinAllocation abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiDecoderReentry abiDecoderAllocation
  abiDecoderArrayInitExec compileEnv valueEncoding vyperABI contractABI venomState words list
  arithmetic abiValidSingletonPrefixDecode abiBuiltinDecodeCorrect abiBuiltinSetupReach
  abiBuiltinDecodeEffect abiDecoderDynamic abiDecoderEffect abiDecoderLoop abiCanonicalHeadSize
  abiEncoder builtinAbi fragExec valueEncodingProps venomExecSemantics

(* ===== Array Ready ===== *)

(* The actual builtin allocation and length guards establish the singleton
   array input at the full input length, without canonicalizing its head. *)

Theorem abi_builtin_wrapped_array_ready:
  abi_builtin_decode_setup data min_size max_size (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
    st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  evaluate_abi_decode env (TupleT [ArrayT ty (Dynamic maxn)]) bs = INL (ArrayV (TupleV [v])) /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) p initial.vs_memory /\
  abi_builtin_decode_resources st first last min_size max_size
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) (LENGTH bs) p d b cap initial /\
  abi_builtin_allocation_frame st.cs_next_var (abi_builtin_decode_output_site st min_size max_size)
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) initial prepared /\
  eval_operand (FST ops) prepared = SOME (n2w d) /\
  eval_operand (FST (SND ops)) prepared = SOME (n2w (p + 32)) /\
  eval_operand (SND (SND ops)) prepared = SOME (n2w (p + 32 + LENGTH bs)) ==>
  first <= ready.cs_next_id /\ abi_decoder_budget first last b cap prepared /\
  abi_valid_singleton_prefix_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) bs
    (dec (Array NONE (vyper_to_abi_type env ty)) (DROP (abi_head_word bs) bs)) v
    ready (FST (SND ops)) (FST ops) MLOAD (SND (SND ops)) (p + 32) d b cap prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `first <= ready.cs_next_id` by fs[abi_builtin_decode_resources_def] >>
  `abi_decoder_budget first last b cap prepared` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
       `site` |-> `abi_builtin_decode_output_site st min_size max_size`,
       `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`,
       `s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`]
       abi_builtin_allocation_frame_budget) >> fs[abi_builtin_decode_resources_def]) >>
  `abi_decoder_ranges MLOAD (SND (SND ops)) (FST (SND ops)) (FST ops)
     (p + 32) (LENGTH bs) d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap prepared` by
    (drule_all (SIMP_RULE (srw_ss()) []
      (Q.INST [`prefix_len` |-> `LENGTH (bs:word8 list)`,
        `cnt` |-> `LENGTH (bs:word8 list)`] abi_builtin_prefix_ranges)) >> simp[]) >>
  `mem_bytes_at (p + 32) (LENGTH bs) (abi_decode_source MLOAD prepared) = bs` by
    fs[val_in_memory_def, abi_builtin_allocation_frame_def, abi_decode_source_def] >>
  drule_all abi_valid_wrapped_array_prefix_pre >> simp[]
QED

(* ===== Array Decode ===== *)

(* Full builtin execution for source-valid wrapped arrays of static elements. *)

Theorem lower_abi_decode_valid_wrapped_array:
  lower_abi_decode data (type_to_abi_dec_info sf ce (TupleT [ArrayT ty (Dynamic maxn)]))
    min_size max_size (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  evaluate_abi_decode env (TupleT [ArrayT ty (Dynamic maxn)]) bs = INL (ArrayV (TupleV [v])) /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) src_base initial.vs_memory /\
  eval_operand data initial = SOME (n2w src_base) /\ abi_decoder_operand_live start.cs_next_var data /\
  abi_builtin_decode_resources start first last min_size max_size
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) (LENGTH bs) src_base d b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_decode_setup_trace >> strip_tac >>
  drule_all abi_builtin_decode_code >> strip_tac >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  `mload src_base initial = n2w (LENGTH bs)` by fs[val_in_memory_def, mem_word_at_eq_mload] >>
  qpat_assum `abi_builtin_decode_resources _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_decode_resources_def]) >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ src_base < dimword (:256) /\
   type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `p` |-> `n2w src_base:bytes32`,
    `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`,
    `cnt` |-> `LENGTH (bs:word8 list)`] abi_builtin_decode_setup_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `eval_operand (FST (SND ops)) prepared = SOME (n2w (src_base + 32)) /\
   eval_operand (SND (SND ops)) prepared = SOME (n2w (src_base + 32 + LENGTH bs))` by
    asm_simp_tac (srw_ss()) [word_add_n2w] >>
  drule_all abi_builtin_wrapped_array_ready >> strip_tac >>
  `is_dynamic (vyper_to_abi_type env (ArrayT ty (Dynamic maxn)))` by simp[vyper_to_abi_type_def] >>
  drule_all abi_decoder_singleton_info >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  SUBGOAL_THEN ``ready.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0`` assume_tac
  >- asm_simp_tac bool_ss [] >>
  drule_all abi_valid_singleton_prefix_decode >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `val_in_memory (ArrayTV tv (Dynamic maxn)) v d actual.vs_memory` >>
  `eval_operand (FST ops) actual = SOME (n2w d)` by fs[abi_decoder_effect_def] >>
  drule_all abi_builtin_decode_effect_compose >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED
