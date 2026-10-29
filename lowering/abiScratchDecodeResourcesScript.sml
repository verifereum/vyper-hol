(* Ordinary allocation history establishes physical builtin decoder resources. *)
Theory abiScratchDecodeResources
Ancestors
  abiScratchDecodeInput abiScratchBuiltinCaller abiCallerAllocation abiBuiltinAllocation
  abiBuiltinDecodeSetup abiScratchFootprint abiDecoderAllocation abiDecoderFootprint
  abiDecoderFrame abiDecoderContract compileEnv venomMemDefs venomState finite_map pred_set
  words list arithmetic

Theorem abi_scratch_decode_allocation_windows:
  alloca_inv s /\ abi_decoder_budget first last b cap s /\
  FLOOKUP s.vs_allocas source_id = SOME (source_base,source_cap) /\
  FLOOKUP s.vs_allocas output_id = SOME (d,outsz) /\ source_id <> output_id /\
  ~(source_id IN abi_decoder_ids first last) /\ ~(output_id IN abi_decoder_ids first last) /\
  source_base <= p /\ p + 32 + cnt <= source_base + source_cap ==>
  p + 32 + cnt < dimword (:256) /\ d + outsz < dimword (:256) /\
  abi_footprint_disjoint d outsz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
  abi_footprint_disjoint (p + 32) cnt
    ((d,outsz)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `s.vs_alloca_next <= b + cap /\ b + cap < dimword (:256)` by
    (fs[abi_decoder_budget_def] >> decide_tac) >>
  `p + 32 + cnt <= s.vs_alloca_next` by
    (mp_tac (Q.INST [`live` |-> `source_id:num`, `loff` |-> `source_base:num`,
      `len` |-> `source_cap:num`, `p` |-> `p + 32`, `n` |-> `cnt:num`]
      abi_caller_allocation_end) >> asm_simp_tac bool_ss []) >>
  `d + outsz <= s.vs_alloca_next` by
    (mp_tac (Q.INST [`live` |-> `output_id:num`, `loff` |-> `d:num`,
      `len` |-> `outsz:num`, `p` |-> `d:num`, `n` |-> `outsz:num`]
      abi_caller_allocation_end) >> asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_footprint_disjoint d outsz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (mp_tac (Q.INST [`live` |-> `output_id:num`, `loff` |-> `d:num`,
      `len` |-> `outsz:num`, `p` |-> `d:num`, `n` |-> `outsz:num`,
      `ids` |-> `abi_decoder_ids first last`] abi_caller_allocation_scratch) >>
     asm_simp_tac (srw_ss()) [LESS_EQ_REFL]) >>
  `abi_footprint_disjoint (p + 32) cnt
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (mp_tac (Q.INST [`live` |-> `source_id:num`, `loff` |-> `source_base:num`,
      `len` |-> `source_cap:num`, `p` |-> `p + 32`, `n` |-> `cnt:num`,
      `ids` |-> `abi_decoder_ids first last`] abi_caller_allocation_scratch) >>
     asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  mp_tac (Q.INST [`live` |-> `source_id:num`, `site` |-> `output_id:num`,
    `loff` |-> `source_base:num`, `len` |-> `source_cap:num`,
    `q` |-> `d:num`, `sz` |-> `outsz:num`] abi_caller_allocation_separate) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  asm_simp_tac bool_ss [abi_scratch_disjoint_cons] >> decide_tac
QED

Theorem abi_scratch_decode_resources_caller:
  let site = abi_builtin_decode_output_site st min_size max_size in
  let allocated = abi_builtin_allocate_state site outsz initial in
  let cap = allocated.vs_alloca_next + 32 * CARD (abi_decoder_missing first last allocated) in
  alloca_inv initial /\ cap < dimword (:256) /\
  min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
  FLOOKUP initial.vs_allocas source_id = SOME (source_base,source_cap) /\ source_id <> site /\
  source_base <= p /\ p + 32 + cnt <= source_base + source_cap /\
  ((FLOOKUP initial.vs_allocas site = NONE /\ d = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas site = SOME (d,outsz)) /\
  site < first /\ first <= site + 2 /\ ~(source_id IN abi_decoder_ids first last) /\
  (!id off sz. id IN abi_decoder_ids first last /\
    FLOOKUP allocated.vs_allocas id = SOME (off,sz) ==> sz = 32) ==>
  abi_scratch_decode_resources st first last min_size max_size outsz cnt p d 0 cap initial
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`,
    `site` |-> `abi_builtin_decode_output_site st min_size max_size`,
    `sb` |-> `source_base:num`, `p` |-> `d:num`]
    abi_scratch_builtin_allocate_buffers) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `allocated = abi_builtin_allocate_state
    (abi_builtin_decode_output_site st min_size max_size) outsz initial` >>
  qabbrev_tac `cap = allocated.vs_alloca_next + 32 * CARD (abi_decoder_missing first last allocated)` >>
  `abi_decoder_budget first last 0 cap allocated` by
    (qunabbrev_tac `cap` >> irule abi_caller_allocation_budget_zero >>
     asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  `~(abi_builtin_decode_output_site st min_size max_size IN abi_decoder_ids first last)` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  mp_tac (Q.INST [`s` |-> `allocated:venom_state`,
    `output_id` |-> `abi_builtin_decode_output_site st min_size max_size`, `b` |-> `0:num`]
    abi_scratch_decode_allocation_windows) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  PURE_REWRITE_TAC [abi_scratch_decode_resources_def, LET_THM] >> BETA_TAC >>
  qpat_assum `Abbrev (allocated = _)` (fn th =>
    PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  asm_simp_tac bool_ss []
QED
