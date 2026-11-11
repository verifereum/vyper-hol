Theory abiScratchDecodeSource
Ancestors
  abiScratchDecodeInput abiScratchDecoderContract abiScratchFootprint abiDecoderFootprint
  abiBuiltinAllocation abiBuiltinDecodeSetup abiBuiltinSetupReach abiDecoderCoherence
  abiDecoderTypedContract abiDecoderReentry abiDecoderContract abiDecoderAllocation
  abiDecoderArrayInitExec abiDecodeRanges compileEnv valueEncoding vyperABI contractABI
  venomState words list arithmetic abiScratchEncoderContract abiBuiltinSource
  abiBuiltinDecodeCorrect abiScratchDecodeEffect abiScratchDecoderRecursive abiDecoderEffect
  abiDecoderLoop abiEncoder builtinAbi fragExec venomExecSemantics abiDecoderReadableTypes

(* Setup boundary lemmas are proved in abiScratchDecodeInput. *)

(* Execute actual builtin setup and the general source-valid recursive decoder. *)
Theorem lower_abi_decode_scratch:
  lower_abi_decode data (type_to_abi_dec_info sf ce ty) min_size max_size
    (type_memory_bytes ce ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decode_pre ce env sf ty tv bs v start first last data min_size max_size
    src_base d b cap initial /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_scratch_decode_effect first last start final limit_st
      (abi_builtin_decode_output_site start min_size max_size) d (type_memory_bytes ce ty)
      b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_decode_setup_trace >> strip_tac >>
  drule_all abi_builtin_decode_code >> strip_tac >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  drule_all abi_scratch_decode_source >> strip_tac >>
  qpat_assum `abi_scratch_decode_pre ce env sf ty tv bs v start first last data min_size max_size src_base d b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decode_pre_def]) >>
  qpat_assum `abi_scratch_decode_resources _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_scratch_decode_resources_def, LET_THM]) >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ src_base < dimword (:256) /\
   type_memory_bytes ce ty < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `p` |-> `n2w src_base:bytes32`,
    `outsz` |-> `type_memory_bytes ce ty`, `cnt` |-> `LENGTH (bs:word8 list)`]
    abi_builtin_decode_setup_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `eval_operand (FST (SND ops)) prepared = SOME (n2w (src_base + 32)) /\
   eval_operand (SND (SND ops)) prepared = SOME (n2w (LENGTH bs))`
    by asm_simp_tac (srw_ss()) [word_add_n2w] >>
  drule_all abi_scratch_decode_pre_ready >> strip_tac >>
  drule_at (Pat `abi_scratch_decoder_input`) abi_scratch_decoder_decode_with_frame >>
  disch_then (qspecl_then [`limit_st`, `func`, `final`, `ctx`] mp_tac) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `val_in_memory tv v d actual.vs_memory` >>
  `eval_operand (FST ops) actual = SOME (n2w d)` by fs[abi_scratch_effect_def] >>
  mp_tac (Q.INST [`st` |-> `start`,
    `site` |-> `abi_builtin_decode_output_site start min_size max_size`,
    `outsz` |-> `type_memory_bytes ce ty`] abi_scratch_decode_effect_compose_frame) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

(* Complete source-success builtin decoding from coherent metadata. *)
Theorem lower_abi_decode_scratch_source:
  lower_abi_decode data (type_to_abi_dec_info sf ce ty) min_size max_size
    (type_memory_bytes ce ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf ty tv /\ evaluate_abi_decode env ty bs = INL v /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) src_base initial.vs_memory /\
  eval_operand data initial = SOME (n2w src_base) /\ abi_decoder_operand_live start.cs_next_var data /\
  abi_scratch_decode_resources start first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) src_base d b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_scratch_decode_effect first last start final limit_st
      (abi_builtin_decode_output_site start min_size max_size) d (type_memory_bytes ce ty)
      b cap initial actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decode_pre_from_source >> strip_tac >>
  drule_all lower_abi_decode_scratch >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
