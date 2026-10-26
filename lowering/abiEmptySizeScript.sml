(* The actual Empty zero loop writes exactly the semantic allocation size. *)
Theory abiEmptySize
Ancestors
  abiEmptyAllocate abiDecoderCoherence valueEncoding compileEnv arithmetic

Theorem abi_empty_mod_add[local]:
  a MOD 32 = 0 /\ b MOD 32 = 0 ==> (a+b) MOD 32 = 0
Proof
  strip_tac >> ONCE_REWRITE_TAC [GSYM MOD_PLUS] >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_empty_mod_mul[local]:
  a MOD 32 = 0 \/ b MOD 32 = 0 ==> (a*b) MOD 32 = 0
Proof
  strip_tac >> ONCE_REWRITE_TAC [GSYM MOD_TIMES2] >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_empty_memory_alignment:
  (!tv. type_memory_size tv MOD 32 = 0) /\
  (!tvs. type_memory_size_list tvs MOD 32 = 0) /\
  (!fields. type_memory_size_fields fields MOD 32 = 0)
Proof
  ho_match_mp_tac type_memory_size_ind >>
  rw[] >> simp[type_memory_size_def, abi_empty_mod_add, abi_empty_mod_mul]
QED

Theorem abi_empty_round_aligned:
  outsz MOD 32 = 0 ==> abi_empty_initialized_bytes outsz F = outsz
Proof
  strip_tac >>
  `(outsz+31) DIV 32 = outsz DIV 32` by
    (mp_tac (Q.SPECL [`outsz`, `31:num`]
      (MATCH_MP ADD_DIV_RWT (DECIDE ``0 < 32:num``))) >> simp[]) >>
  asm_simp_tac (srw_ss()) [abi_empty_initialized_bytes_def] >>
  mp_tac (Q.SPEC `outsz` (MATCH_MP DIVISION (DECIDE ``0 < 32:num``))) >>
  asm_simp_tac (srw_ss()) [] >> decide_tac
QED

Theorem abi_empty_round_memory_size:
  abi_empty_initialized_bytes (type_memory_size tv) F = type_memory_size tv
Proof
  irule abi_empty_round_aligned >> simp[abi_empty_memory_alignment]
QED

Theorem abi_empty_round_coherent:
  abi_decoder_coherent ce env sf ty tv ==>
  abi_empty_initialized_bytes (type_memory_bytes ce ty) F = type_memory_bytes ce ty
Proof
  strip_tac >> drule abi_decoder_coherent_header >> strip_tac >>
  `type_memory_bytes ce ty = type_memory_size tv` by fs[abi_decoder_header_def] >>
  asm_rewrite_tac[abi_empty_round_memory_size]
QED
