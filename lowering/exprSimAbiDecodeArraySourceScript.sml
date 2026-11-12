(* Source labels for the dynamic-array header and complete-head guards. *)
Theory exprSimAbiDecodeArraySource
Ancestors
  valueEncodingDefs
  abiValidAggregateHeads abiValidMembers abiDecodeRanges vyperABI contractABI
  abiDecoderBytestringSource abiDecoderSourceFacts abiCanonicalHeadSize
  vyperValue valueEncoding words list rich_list arithmetic

Theorem abi_decode_dynarray_source_guard_bounds:
  vyper_decode_valid_enc (Array NONE at) bs /\
  abi_to_vyper env (ArrayT ty (Dynamic maxn)) (dec (Array NONE at) bs) = SOME v ==>
  32 <= LENGTH bs /\ abi_head_word bs <= maxn /\
  32 + abi_head_word bs * abi_member_head_size at <= LENGTH bs
Proof
  strip_tac >> drule abi_valid_dynamic_array_view >> strip_tac >>
  gvs[abi_to_vyper_def, compatible_bound_def,
      Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  decide_tac
QED

Theorem abi_decode_dynarray_source_guard_reject:
  LENGTH bs < 32 \/ maxn < abi_head_word bs \/
  LENGTH bs < 32 + abi_head_word bs * abi_member_head_size at ==>
  ~(vyper_decode_valid_enc (Array NONE at) bs /\
    ?v. abi_to_vyper env (ArrayT ty (Dynamic maxn)) (dec (Array NONE at) bs) = SOME v)
Proof
  metis_tac[abi_decode_dynarray_source_guard_bounds, arithmeticTheory.NOT_LESS_EQUAL]
QED

Theorem abi_decode_dynarray_suffix_guard_bounds:
  bs = mem_bytes_at (b+p) (h-p) mem /\
  n = w2n (mem_word_at (b+p) mem) /\
  vyper_decode_valid_enc (Array NONE at) bs /\
  abi_to_vyper env (ArrayT ty (Dynamic maxn)) (dec (Array NONE at) bs) = SOME v ==>
  p+32 <= h /\ n <= maxn /\ p+32+n*abi_member_head_size at <= h
Proof
  strip_tac >> drule_all abi_decode_dynarray_source_guard_bounds >> strip_tac >>
  `LENGTH bs = h-p` by simp[mem_bytes_at_def] >>
  `p+32 <= h` by decide_tac >>
  `TAKE 32 bs = mem_bytes_at (b+p) 32 mem` by
    (gvs[] >>
     `TAKE 32 (DROP 0 (mem_bytes_at (b+p) (h-p) mem)) =
      mem_bytes_at ((b+p)+0) 32 mem` by
        (irule mem_bytes_at_window >> decide_tac) >> gvs[]) >>
  `n = abi_head_word bs` by
    simp[abi_head_word_def, mem_word_at_def, mem_bytes_at_def] >>
  gvs[] >> decide_tac
QED

Theorem abi_decode_dynarray_suffix_guard_reject:
  bs = mem_bytes_at (b+p) (h-p) mem /\
  n = w2n (mem_word_at (b+p) mem) /\
  (h < p+32 \/ maxn < n \/ h < p+32+n*abi_member_head_size at) ==>
  ~(vyper_decode_valid_enc (Array NONE at) bs /\
    ?v. abi_to_vyper env (ArrayT ty (Dynamic maxn)) (dec (Array NONE at) bs) = SOME v)
Proof
  metis_tac[abi_decode_dynarray_suffix_guard_bounds, arithmeticTheory.NOT_LESS_EQUAL]
QED
