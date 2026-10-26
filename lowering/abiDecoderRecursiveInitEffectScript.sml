(* An actual array initializer owns its slot and preserves surrounding scratch. *)
Theory abiDecoderRecursiveInitEffect
Ancestors
  abiDecoderArrayInit abiDecoderArrayInitExec abiDecoderEffect abiDecoderProtectedScratch
  abiDecoderAllocation abiDecoderTypedContract abiDecoderContract abiDecoderFrame compileEnv
  venomState words arithmetic

Theorem abi_decoder_recursive_init_effect:
  abi_decoder_array_init_post setup next limit_st site first last b cap d n initial prepared /\
  first <= lo /\ lo <= site /\ site < hi /\ hi <= last /\
  32 <= outsz /\ (d + outsz <= b \/ b + cap <= d) ==>
  abi_decoder_effect first last lo hi next limit_st d outsz b cap initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_array_init_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_array_init_post_def]) >>
  rename1 `FLOOKUP prepared.vs_allocas site = SOME (slot,32)` >>
  `abi_decode_footprint_frame [(d,outsz);(b,cap)] initial prepared` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`,
       `b` |-> `b:num`, `cap` |-> `cap:num`] abi_decoder_array_init_frame_widen) >>
     asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(d,outsz);(slot,32)] initial prepared` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`,
       `b` |-> `slot:num`, `cap` |-> `32:num`] abi_decoder_array_init_frame_widen) >>
     asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`,
    `child_first` |-> `lo:num`, `child_last` |-> `hi:num`] abi_decoder_child_scratch_preservation) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  asm_simp_tac bool_ss [abi_decoder_effect_def, abi_decoder_scratch_frame_def] >>
  conj_tac
  >- (rpt strip_tac >> `id <> site` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >> `id IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >> metis_tac[]
QED

Theorem abi_decoder_effect_lower_vars:
  abi_decoder_effect first last lo hi child_next limit_st d sz b cap s t /\ next <= child_next ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t
Proof
  strip_tac >> mp_tac (Q.INST [`child_lo` |-> `lo:num`, `child_hi` |-> `hi:num`,
    `child_d` |-> `d:num`, `child_sz` |-> `sz:num`] abi_decoder_effect_widen) >>
  asm_simp_tac (srw_ss()) []
QED
