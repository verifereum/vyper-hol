(* Typed primitive source values determine their canonical ABI word. Reuse
   the checked reverse-layout theorem on the canonical encoding itself. *)
Theory abiEncoderWordSource
Ancestors
  abiTupleProps abiStaticAggregateProps abiEncoderMemory abiBuiltinEncodeWord valueEncoding
  valueEncodingProps vyperABI vyperTyping contractABI compileEnv venomState venomExecSemantics
  words byte list rich_list arithmetic

Theorem abi_encoder_base_word_value:
  is_word_type (BaseT bt) /\ value_has_type (BaseTV bt) v ==>
  abi_tuple_word (BaseTV bt) v
Proof
  Cases_on `bt` >> FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
  Cases_on `v` >> simp[is_word_type_def, value_has_type_def, abi_tuple_word_def]
QED

Theorem abi_encoder_word_memory_value:
  abi_tuple_word tv v /\ val_in_memory tv v off mem ==>
  mem_word_at off mem = typed_val_to_w256 tv v
Proof
  rw[abi_tuple_word_def] >> fs[val_in_memory_def, typed_val_to_w256_def] >>
  Cases_on `tv` >> simp[typed_val_to_w256_def] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[typed_val_to_w256_def]
QED

Theorem abi_encoder_base_source_word:
  is_word_type (BaseT bt) /\ value_has_type (BaseTV bt) v /\
  vyper_to_abi_base bt v = SOME av /\ LENGTH (enc (vyper_base_to_abi_type bt) av) = 32 ==>
  word_to_bytes (typed_val_to_w256 (BaseTV bt) v) T = enc (vyper_base_to_abi_type bt) av
Proof
  strip_tac >> drule_all abi_encoder_base_word_value >> strip_tac >>
  `mem_bytes_at 0 32 (enc (vyper_base_to_abi_type bt) av) = enc (vyper_base_to_abi_type bt) av` by
    (qpat_assum `LENGTH (enc _ _) = 32` (fn len => pure_rewrite_tac [GSYM len]) >>
     simp_tac bool_ss [mem_bytes_at_def, DROP, TAKE_LENGTH_APPEND]) >>
  `val_in_memory (BaseTV bt) v 0 (enc (vyper_base_to_abi_type bt) av)` by
    (drule_all abi_static_primitive_layout >> simp[]) >>
  drule_all abi_encoder_word_memory_value >> strip_tac >>
  mp_tac (Q.INST [`off` |-> `0:num`, `mem` |-> `enc (vyper_base_to_abi_type bt) av`]
    abi_encoder_word_window) >> asm_simp_tac bool_ss [EQ_SYM_EQ]
QED

Theorem abi_encoder_flag_source_word:
  word_to_bytes (typed_val_to_w256 (FlagTV m) (FlagV k)) T = enc (Uint 256) (NumV k)
Proof
  simp[typed_val_to_w256_def, val_to_w256_def, enc_def, enc_number_def]
QED
