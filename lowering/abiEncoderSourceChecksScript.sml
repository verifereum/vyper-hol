(* Regression: omitted fixed-array defaults constrain the source memory.
   val_in_memory rejects this nonzero default slot; AbiCopy still copies the
   actual bytes when executed on that invalid source. *)
Theory abiEncoderSourceChecks
Ancestors
  venomMemProps
  abiEncoderLeaves valueEncoding vyperABI vyperValue vyperTyping contractABI
  venomState compileEnv abiEncoder words list rich_list byte

Definition abi_encoder_sparse_probe_memory_def:
  abi_encoder_sparse_probe_memory = word_to_bytes (1w:bytes32) T ++ REPLICATE 64 0w
End

Theorem abi_encoder_sparse_probe_window:
  LENGTH abi_encoder_sparse_probe_memory = 96 /\
  mem_bytes_at 0 32 abi_encoder_sparse_probe_memory <>
    enc (vyper_to_abi_type FEMPTY (ArrayT (BaseT (UintT 256)) (Fixed 1))) (ListV [NumV 0])
Proof
  simp[abi_encoder_sparse_probe_memory_def, mem_bytes_at_def,
       vyper_to_abi_type_def, enc_def, enc_number_def, REPLICATE,
       EVAL ``REPLICATE 1 (Uint 256)``, head_lengths_def, is_dynamic_def,
       static_length_def, REV_DEF, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >> strip_tac >>
  qpat_x_assum `word_to_bytes _ _ = _`
    (mp_tac o AP_TERM ``word_of_bytes T (0w:bytes32)``) >>
  simp[word_of_bytes_word_to_bytes, dividesTheory.divides_def]
QED


Theorem abi_encoder_sparse_source_rejected:
  let ty = ArrayT (BaseT (UintT 256)) (Fixed 1) in
  let tv = ArrayTV (BaseTV (UintT 256)) (Fixed 1) in
  let v = ArrayV (SArrayV []) in
  let av = ListV [NumV 0] in
  let mem = abi_encoder_sparse_probe_memory in
    evaluate_type FEMPTY ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi FEMPTY ty v = SOME av /\
    ~val_in_memory tv v 0 mem /\ LENGTH mem = 96 /\
    mem_bytes_at 0 32 mem <> enc (vyper_to_abi_type FEMPTY ty) av
Proof
  simp_tac bool_ss [LET_THM, abi_encoder_sparse_probe_window] >>
  simp[val_in_memory_def, default_value_def, type_memory_size_def,
       val_to_w256_def, mem_word_at_def, abi_encoder_sparse_probe_memory_def,
       TAKE_APPEND, TAKE_LENGTH_TOO_LONG, word_of_bytes_word_to_bytes,
       dividesTheory.divides_def] >>
  EVAL_TAC >> simp[]
QED

(* Execution on an invalid source is not an encoder-correctness counterexample:
   MCOPY copies its bytes without establishing the source relation. *)
Theorem abi_encoder_sparse_copy_probe:
  compile_abi_encode_to_buf (Lit 64w) (Lit 0w) (AbiCopy 32) st = (out,st') /\
  fresh_vars_wrt st s /\ s.vs_memory = abi_encoder_sparse_probe_memory ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at 64 32 t.vs_memory =
      mem_bytes_at 0 32 abi_encoder_sparse_probe_memory /\
    mem_bytes_at 64 32 t.vs_memory <>
      enc (vyper_to_abi_type FEMPTY (ArrayT (BaseT (UintT 256)) (Fixed 1))) (ListV [NumV 0])
Proof
  strip_tac >>
  mp_tac (Q.INST [`dst` |-> `Lit 64w`, `src` |-> `Lit 0w`,
    `db` |-> `64:num`, `sb` |-> `0:num`, `sz` |-> `32:num`] abi_encode_copy_sequence) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def, wordsTheory.dimword_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK actual` >>
  mp_tac abi_encoder_sparse_probe_window >> strip_tac >>
  qexists_tac `actual` >> gvs[]
QED
