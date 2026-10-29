(* Incoming canonical bytes and resources for the complete decode builtin.
   All preconditions describe values, memory, compiler metadata or allocator
   metadata; none assumes successful execution of an emitted fragment. *)
Theory abiBuiltinCanonicalPre
Ancestors
  abiBuiltinAllocation abiBuiltinDecodeSetup abiBuiltinSetupExecute abiDecoderCoherence
  abiDecoderTypedContract abiDecoderReentry abiDecoderReservation abiDecoderAllocation
  abiDecoderArrayInitExec abiDecoderFrame abiDecoderContract compileEnv valueEncoding vyperABI
  contractABI venomState finite_map words list arithmetic

Definition abi_builtin_canonical_pre_def:
  abi_builtin_canonical_pre ce env sf ty tv av v st first last data min_size max_size p d b cap s <=>
    abi_decoder_coherent ce env sf ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
    eval_operand data s = SOME (n2w p) /\
    mload p s = n2w (LENGTH (enc (vyper_to_abi_type env ty) av)) /\
    mem_bytes_at (p + 32) (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
      enc (vyper_to_abi_type env ty) av /\
    min_size <= LENGTH (enc (vyper_to_abi_type env ty) av) /\
    LENGTH (enc (vyper_to_abi_type env ty) av) <= max_size /\ max_size < dimword (:256) /\
    abi_decoder_operand_live st.cs_next_var data /\
    p + 32 + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
    d + type_memory_bytes ce ty < dimword (:256) /\
    (d + type_memory_bytes ce ty <= b \/ b + cap <= d) /\
    abi_footprint_disjoint (p + 32) (LENGTH (enc (vyper_to_abi_type env ty) av))
      [(d,type_memory_bytes ce ty);(b,cap)] /\
    ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
        d = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
        SOME (d,type_memory_bytes ce ty)) /\
    first <= abi_builtin_decode_output_site st min_size max_size + 2 /\
    abi_decoder_budget first last b cap
      (abi_builtin_allocate_state (abi_builtin_decode_output_site st min_size max_size)
        (type_memory_bytes ce ty) s)
End

Theorem abi_builtin_canonical_pre_ready:
  abi_builtin_decode_setup data min_size max_size (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_builtin_canonical_pre ce env sf ty tv av v st first last data min_size max_size p d b cap initial /\
  abi_builtin_allocation_frame st.cs_next_var (abi_builtin_decode_output_site st min_size max_size)
    (type_memory_bytes ce ty) initial prepared /\
  eval_operand (FST ops) prepared = SOME (n2w d) /\
  eval_operand (FST (SND ops)) prepared = SOME (n2w (p + 32)) /\
  eval_operand (SND (SND ops)) prepared =
    SOME (n2w (p + 32 + LENGTH (enc (vyper_to_abi_type env ty) av))) ==>
  first <= ready.cs_next_id /\ abi_decoder_budget first last b cap prepared /\
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v ready last
    (FST (SND ops)) (FST ops) MLOAD (SND (SND ops)) (p + 32) d b cap
    (abi_decoder_prune_vars ready.cs_next_var prepared)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  qpat_assum `abi_builtin_canonical_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_canonical_pre_def]) >>
  `first <= ready.cs_next_id` by fs[] >>
  `abi_decoder_budget first last b cap prepared` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
      `site` |-> `abi_builtin_decode_output_site st min_size max_size`,
      `outsz` |-> `type_memory_bytes ce ty`, `s` |-> `initial:venom_state`,
      `t` |-> `prepared:venom_state`] abi_builtin_allocation_frame_budget) >>
     asm_simp_tac bool_ss []) >>
  drule abi_decoder_budget_reservation >> strip_tac >>
  `abi_decoder_reservation ready.cs_next_id last b cap prepared` by
    (mp_tac (Q.INST [`next` |-> `ready.cs_next_id`, `s` |-> `prepared:venom_state`,
      `t` |-> `prepared:venom_state`] abi_decoder_reservation_advance) >> asm_simp_tac bool_ss []) >>
  `abi_decoder_ranges MLOAD (SND (SND ops)) (FST (SND ops)) (FST ops) (p + 32)
    (LENGTH (enc (vyper_to_abi_type env ty) av)) d (type_memory_bytes ce ty) b cap prepared` by
    (asm_simp_tac bool_ss [abi_decoder_ranges_def, abi_decode_source_opcode_def] >>
     disj2_tac >> qexists_tac `p + 32 + LENGTH (enc (vyper_to_abi_type env ty) av)` >>
     asm_simp_tac (srw_ss()) []) >>
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
