(* The real builtin header uses the full input length; its recursive body may
   consume a shorter canonical prefix. *)
Theory abiBuiltinPrefixReady
Ancestors
  abiBuiltinPrefixInput abiBuiltinSource abiBuiltinDecodeSetup abiBuiltinSetupExecute
  abiBuiltinAllocation abiDecoderCoherence abiDecoderTypedContract abiDecoderReentry
  abiDecoderReservation abiDecoderAllocation abiDecoderArrayInitExec abiDecoderFrame
  abiDecoderContract compileEnv valueEncoding vyperABI contractABI venomState finite_map words
  list arithmetic

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
