Theory abiBuiltinPrefixSource
Ancestors
  abiBuiltinPrefixInput abiBuiltinSource abiBuiltinDecodeSetup abiBuiltinSetupReach
  abiBuiltinAllocation abiDecoderCoherence abiDecoderTypedContract abiDecoderReentry
  abiDecoderReservation abiDecoderAllocation abiDecoderArrayInitExec abiDecoderFrame
  abiDecoderContract compileEnv valueEncoding vyperABI contractABI venomState finite_map words
  list arithmetic abiBuiltinDecodeCorrect abiBuiltinDecodeEffect abiDecoderCoherentCorrect
  abiDecoderEffect abiDecoderLoop abiEncoder builtinAbi fragExec venomExecSemantics
  abiValidPrefixSource

(* The real builtin header uses the full input length; its recursive body may
   consume a shorter canonical prefix. *)
Theorem abi_footprint_disjoint_prefix:
  !(p:num) (whole:num) (part:num) (ranges:(num # num) list).
  abi_footprint_disjoint p whole ranges /\ part <= whole ==>
  abi_footprint_disjoint p part ranges
Proof
  rw[abi_footprint_disjoint_def] >> first_x_assum drule >> decide_tac
QED

Theorem abi_builtin_prefix_ranges:
  abi_builtin_decode_resources st first last min_size max_size outsz cnt p d b cap initial /\
  prefix_len <= cnt /\
  eval_operand src prepared = SOME (n2w (p + 32)) /\
  eval_operand dst prepared = SOME (n2w d) /\
  eval_operand hi prepared = SOME (n2w (p + 32 + cnt)) ==>
  abi_decoder_ranges MLOAD hi src dst (p + 32) prefix_len d outsz b cap prepared
Proof
  simp_tac bool_ss [abi_builtin_decode_resources_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `p + 32 + prefix_len < dimword (:256)` by decide_tac >>
  `abi_footprint_disjoint (p + 32) prefix_len [(d,outsz);(b,cap)]` by
    (irule abi_footprint_disjoint_prefix >> qexists_tac `cnt` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_decoder_ranges_def, abi_decode_source_opcode_def] >>
  disj2_tac >> qexists_tac `p + 32 + cnt` >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_builtin_prefix_pre_ready:
  abi_builtin_decode_setup data min_size max_size (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_builtin_prefix_pre ce env sf ty tv bs av v st first last data min_size max_size p d b cap initial /\
  abi_builtin_allocation_frame st.cs_next_var (abi_builtin_decode_output_site st min_size max_size)
    (type_memory_bytes ce ty) initial prepared /\
  eval_operand (FST ops) prepared = SOME (n2w d) /\
  eval_operand (FST (SND ops)) prepared = SOME (n2w (p + 32)) /\
  eval_operand (SND (SND ops)) prepared = SOME (n2w (p + 32 + LENGTH bs)) ==>
  first <= ready.cs_next_id /\ abi_decoder_budget first last b cap prepared /\
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v ready last
    (FST (SND ops)) (FST ops) MLOAD (SND (SND ops)) (p + 32) d b cap
    (abi_decoder_prune_vars ready.cs_next_var prepared)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  drule_all abi_builtin_prefix_source >> strip_tac >>
  qpat_assum `abi_builtin_prefix_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_pre_def]) >>
  `first <= ready.cs_next_id` by fs[abi_builtin_decode_resources_def] >>
  `abi_decoder_budget first last b cap prepared` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
       `site` |-> `abi_builtin_decode_output_site st min_size max_size`,
       `outsz` |-> `type_memory_bytes ce ty`, `s` |-> `initial:venom_state`,
       `t` |-> `prepared:venom_state`] abi_builtin_allocation_frame_budget) >>
     fs[abi_builtin_decode_resources_def]) >>
  drule abi_decoder_budget_reservation >> strip_tac >>
  `abi_decoder_reservation ready.cs_next_id last b cap prepared` by
    (mp_tac (Q.INST [`next` |-> `ready.cs_next_id`, `s` |-> `prepared:venom_state`,
      `t` |-> `prepared:venom_state`] abi_decoder_reservation_advance) >> asm_simp_tac bool_ss []) >>
  drule_all abi_builtin_prefix_ranges >> strip_tac >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  asm_simp_tac bool_ss [abi_decoder_recursive_pre_def] >>
  mp_tac (Q.INST [`st` |-> `ready`, `s` |-> `prepared:venom_state`,
    `di` |-> `type_to_abi_dec_info ce.ce_struct_fields ce ty`,
    `src` |-> `FST (SND (ops:operand # operand # operand))`,
    `dst` |-> `FST (ops:operand # operand # operand)`, `opc` |-> `MLOAD`,
    `hi` |-> `SND (SND (ops:operand # operand # operand))`, `sb` |-> `p + 32`]
    abi_decoder_pre_prune) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_def] >> asm_simp_tac bool_ss []
QED

(* Full recursive builtin execution consumes a canonical prefix while its actual
   length checks and upper pointer use the complete, possibly longer input. *)
Theorem lower_abi_decode_prefix:
  lower_abi_decode data (type_to_abi_dec_info sf ce ty) min_size max_size
    (type_memory_bytes ce ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_builtin_prefix_pre ce env sf ty tv bs av v start first last data min_size max_size
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
  drule_all abi_builtin_prefix_source >> strip_tac >>
  qpat_assum `abi_builtin_prefix_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_pre_def]) >>
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
  drule_all abi_builtin_prefix_pre_ready >> strip_tac >>
  mp_tac (Q.INST [`start` |-> `ready`, `end_st` |-> `final`, `opc` |-> `MLOAD`,
    `dst` |-> `FST (ops:operand # operand # operand)`,
    `src` |-> `FST (SND (ops:operand # operand # operand))`,
    `hi` |-> `SND (SND (ops:operand # operand # operand))`,
    `sb` |-> `src_base + 32`, `initial` |-> `prepared:venom_state`] abi_decoder_decode) >>
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

(* Full source-success decoding of static aggregates and dynamic arrays with
   static elements. The source may contain trailing noncanonical bytes. *)
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
