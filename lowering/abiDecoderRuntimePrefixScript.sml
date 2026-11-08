(* Only completed array elements carry semantic witnesses.  The unread suffix
   is arbitrary: bs is the actual bounded payload, not a canonical encoding. *)
Theory abiDecoderRuntimePrefix
Ancestors
  abiBoundedLeafReflection abiDecoderArrayPrefix abiDecoderPrimitiveLoopInvariant
  abiDecoderNavigationTotal abiDecoderFrame valueEncoding vyperTyping
  vyperABI venomState words list rich_list arithmetic

Definition abi_decoder_reflected_prefix_def:
  abi_decoder_reflected_prefix env ty tv bs d j s <=>
    ?vs. LENGTH vs = j /\ all_have_type tv vs /\
      elems_in_memory vs (d + 32) tv s.vs_memory /\
    (!k. k < j ==>
      vyper_decode_valid_enc (vyper_to_abi_type env ty)
        (DROP (32 + k * 32) bs) /\
      abi_vyper_admissible env ty
        (dec (vyper_to_abi_type env ty) (DROP (32 + k * 32) bs)) /\
      abi_to_vyper env ty
        (dec (vyper_to_abi_type env ty) (DROP (32 + k * 32) bs)) = SOME (EL k vs))
End

Definition abi_decoder_runtime_prefix_def:
  abi_decoder_runtime_prefix env ty tv bs B n d cnt capacity slot
      first limit_st fp initial j s <=>
    j <= cnt /\ cnt <= capacity /\ cnt < dimword (:256) /\
    LENGTH bs = n /\ 32 <= n /\ 32 + j * 32 <= n /\
    word_of_bytes T (0w:bytes32) (TAKE 32 bs) = n2w cnt /\
    mem_word_at d s.vs_memory = n2w cnt /\ mload slot s = n2w j /\
    mem_bytes_at B n s.vs_memory = bs /\
    d + 32 + capacity * type_memory_size tv < dimword (:256) /\
    B + n < dimword (:256) /\ slot + 32 < dimword (:256) /\
    (d + 32 + capacity * type_memory_size tv <= B \/ B + n <= d) /\
    (d + 32 + capacity * type_memory_size tv <= slot \/ slot + 32 <= d) /\
    (B + n <= slot \/ slot + 32 <= B) /\
    abi_decoder_reflected_prefix env ty tv bs d j s /\
    abi_decoder_loop_rel first limit_st fp initial s
End

Theorem abi_decoder_reflected_prefix_empty:
  abi_decoder_reflected_prefix env ty tv bs d 0 s
Proof
  simp[abi_decoder_reflected_prefix_def, all_have_type_EVERY,
    val_in_memory_def]
QED

Theorem abi_decoder_runtime_prefix_init:
  cnt <= capacity /\ cnt < dimword (:256) /\ LENGTH bs = n /\ 32 <= n /\
  word_of_bytes T (0w:bytes32) (TAKE 32 bs) = n2w cnt /\
  mem_word_at d s.vs_memory = n2w cnt /\
  mload slot s = 0w /\ mem_bytes_at B n s.vs_memory = bs /\
  d + 32 + capacity * type_memory_size tv < dimword (:256) /\
  B + n < dimword (:256) /\ slot + 32 < dimword (:256) /\
  (d + 32 + capacity * type_memory_size tv <= B \/ B + n <= d) /\
  (d + 32 + capacity * type_memory_size tv <= slot \/ slot + 32 <= d) /\
  (B + n <= slot \/ slot + 32 <= B) /\ fresh_vars_wrt limit_st s ==>
  abi_decoder_runtime_prefix env ty tv bs B n d cnt capacity slot
    first limit_st fp s 0 s
Proof
  simp[abi_decoder_runtime_prefix_def, abi_decoder_reflected_prefix_empty,
    abi_decoder_loop_rel_refl]
QED

Theorem abi_decoder_reflected_prefix_append:
  abi_decoder_reflected_prefix env ty tv bs d j before /\
  value_has_type tv v /\
  val_in_memory tv v (d + 32 + j * type_memory_size tv) after.vs_memory /\
  abi_decode_frame (d + 32 + j * type_memory_size tv) (type_memory_size tv)
    before after /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP (32 + j * 32) bs) /\
  abi_vyper_admissible env ty
    (dec (vyper_to_abi_type env ty) (DROP (32 + j * 32) bs)) /\
  abi_to_vyper env ty
    (dec (vyper_to_abi_type env ty) (DROP (32 + j * 32) bs)) = SOME v ==>
  abi_decoder_reflected_prefix env ty tv bs d (SUC j) after
Proof
  simp_tac bool_ss [abi_decoder_reflected_prefix_def] >> strip_tac >>
  qexists `vs ++ [v]` >>
  fs[all_have_type_EVERY] >> conj_tac
  >- (irule abi_decode_frame_append_element >> simp[all_have_type_EVERY] >>
      qexists `before` >> simp[]) >>
  rpt strip_tac >> Cases_on `k = j` >> gvs[]
  >- simp[EL_APPEND_EQN] >>
  `k < LENGTH vs` by decide_tac >> simp[EL_APPEND_EQN] >> metis_tac[]
QED
