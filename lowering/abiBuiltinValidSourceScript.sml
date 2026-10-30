Theory abiBuiltinValidSource
Ancestors
  abiBuiltinValidInput abiBuiltinPrefixSource abiBuiltinSource abiBuiltinDecodeSetup
  abiBuiltinSetupReach abiBuiltinAllocation abiDecoderValidContract abiDecoderCoherence
  abiDecoderTypedContract abiDecoderReentry abiDecoderContract abiDecoderAllocation
  abiDecoderArrayInitExec compileEnv valueEncoding vyperABI contractABI venomState words list
  arithmetic abiBuiltinDecodeCorrect abiBuiltinDecodeEffect abiDecoderValidRecursive
  abiDecoderEffect abiDecoderLoop abiEncoder builtinAbi fragExec venomExecSemantics
  abiDecoderReadableTypes

(* Actual builtin setup establishes the full source-valid recursive input. *)
Theorem abi_builtin_valid_pre_ready:
  abi_builtin_decode_setup data min_size max_size (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_builtin_valid_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap initial /\
  abi_builtin_allocation_frame st.cs_next_var (abi_builtin_decode_output_site st min_size max_size)
    (type_memory_bytes ce ty) initial prepared /\
  eval_operand (FST ops) prepared = SOME (n2w d) /\
  eval_operand (FST (SND ops)) prepared = SOME (n2w (p + 32)) /\
  eval_operand (SND (SND ops)) prepared = SOME (n2w (p + 32 + LENGTH bs)) ==>
  first <= ready.cs_next_id /\ abi_decoder_budget first last b cap prepared /\
  abi_decoder_valid_pre ce env sf ty tv bs v ready (FST (SND ops)) (FST ops)
    MLOAD (SND (SND ops)) (p + 32) d b cap prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  drule_all abi_builtin_valid_source >> strip_tac >>
  qpat_assum `abi_builtin_valid_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_valid_pre_def]) >>
  qpat_assum `abi_builtin_decode_resources _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_decode_resources_def]) >>
  `first <= ready.cs_next_id` by asm_simp_tac bool_ss [] >>
  `abi_decoder_budget first last b cap prepared` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
       `site` |-> `abi_builtin_decode_output_site st min_size max_size`,
       `outsz` |-> `type_memory_bytes ce ty`, `s` |-> `initial:venom_state`,
       `t` |-> `prepared:venom_state`] abi_builtin_allocation_frame_budget) >>
     asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`prefix_len` |-> `LENGTH (bs:word8 list)`, `cnt` |-> `LENGTH (bs:word8 list)`,
    `outsz` |-> `type_memory_bytes ce ty`, `src` |-> `FST (SND (ops:operand # operand # operand))`,
    `dst` |-> `FST (ops:operand # operand # operand)`,
    `hi` |-> `SND (SND (ops:operand # operand # operand))`] abi_builtin_prefix_ranges) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> strip_tac >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  asm_simp_tac (srw_ss()) [abi_decoder_valid_pre_def, abi_decode_source_def]
QED

(* Execute actual builtin setup and the general source-valid recursive decoder. *)
Theorem lower_abi_decode_valid:
  lower_abi_decode data (type_to_abi_dec_info sf ce ty) min_size max_size
    (type_memory_bytes ce ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_builtin_valid_pre ce env sf ty tv bs v start first last data min_size max_size
    src_base d b cap initial /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce ty)
      b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_decode_setup_trace >> strip_tac >>
  drule_all abi_builtin_decode_code >> strip_tac >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  drule_all abi_builtin_valid_source >> strip_tac >>
  qpat_assum `abi_builtin_valid_pre ce env sf ty tv bs v start first last data min_size max_size src_base d b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_valid_pre_def]) >>
  qpat_assum `abi_builtin_decode_resources _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_decode_resources_def]) >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ src_base < dimword (:256) /\
   type_memory_bytes ce ty < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `p` |-> `n2w src_base:bytes32`,
    `outsz` |-> `type_memory_bytes ce ty`, `cnt` |-> `LENGTH (bs:word8 list)`]
    abi_builtin_decode_setup_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `eval_operand (FST (SND ops)) prepared = SOME (n2w (src_base + 32)) /\
   eval_operand (SND (SND ops)) prepared = SOME (n2w (src_base + 32 + LENGTH bs))`
    by asm_simp_tac (srw_ss()) [word_add_n2w] >>
  drule_all abi_builtin_valid_pre_ready >> strip_tac >>
  mp_tac (Q.INST [`start` |-> `ready`, `end_st` |-> `final`, `opc` |-> `MLOAD`,
    `dst` |-> `FST (ops:operand # operand # operand)`,
    `src` |-> `FST (SND (ops:operand # operand # operand))`,
    `hi` |-> `SND (SND (ops:operand # operand # operand))`,
    `sb` |-> `src_base + 32`, `initial` |-> `prepared:venom_state`] abi_decoder_valid_decode) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `val_in_memory tv v d actual.vs_memory` >>
  `eval_operand (FST ops) actual = SOME (n2w d)` by fs[abi_decoder_effect_def] >>
  mp_tac (Q.INST [`st` |-> `start`,
    `site` |-> `abi_builtin_decode_output_site start min_size max_size`,
    `outsz` |-> `type_memory_bytes ce ty`] abi_builtin_decode_effect_compose) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

(* Complete source-success builtin decoding from coherent metadata. *)
Theorem lower_abi_decode_valid_source:
  lower_abi_decode data (type_to_abi_dec_info sf ce ty) min_size max_size
    (type_memory_bytes ce ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf ty tv /\ evaluate_abi_decode env ty bs = INL v /\
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
  drule_all abi_builtin_valid_pre_from_source >> strip_tac >>
  drule_all lower_abi_decode_valid >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
