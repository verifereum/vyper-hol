(* The encoder's source relation must constrain omitted fixed-array defaults.
   The existing val_in_memory predicate intentionally observes stored keys only. *)
Theory abiEncoderSourceChecks
Ancestors
  abiEncoderLeaves valueEncoding vyperABI vyperValue vyperTyping contractABI
  venomState compileEnv abiEncoder words list rich_list byte

Theorem abi_encoder_source_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

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

Theorem abi_encoder_sparse_source_counterexample:
  let ty = ArrayT (BaseT (UintT 256)) (Fixed 1) in
  let tv = ArrayTV (BaseTV (UintT 256)) (Fixed 1) in
  let v = ArrayV (SArrayV []) in
  let av = ListV [NumV 0] in
  let mem = abi_encoder_sparse_probe_memory in
    evaluate_type FEMPTY ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi FEMPTY ty v = SOME av /\
    val_in_memory tv v 0 mem /\ LENGTH mem = 96 /\
    mem_bytes_at 0 32 mem <> enc (vyper_to_abi_type FEMPTY ty) av
Proof
  simp_tac bool_ss [LET_THM, abi_encoder_sparse_probe_window] >>
  EVAL_TAC >> simp_tac bool_ss [wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC
QED

Theorem abi_encoder_sparse_copy_counterexample:
  compile_abi_encode_to_buf (Lit 64w) (Lit 0w) (AbiCopy 32) st = (out,st') /\
  fresh_vars_wrt st s /\ s.vs_memory = abi_encoder_sparse_probe_memory ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at 64 32 t.vs_memory <>
      enc (vyper_to_abi_type FEMPTY (ArrayT (BaseT (UintT 256)) (Fixed 1))) (ListV [NumV 0])
Proof
  strip_tac >>
  mp_tac (Q.INST [`dst` |-> `Lit 64w`, `src` |-> `Lit 0w`,
    `db` |-> `64:num`, `sb` |-> `0:num`, `sz` |-> `32:num`] abi_encode_copy_sequence) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def, wordsTheory.dimword_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK actual` >>
  mp_tac abi_encoder_sparse_source_counterexample >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qexists_tac `actual` >> gvs[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_SOURCE_CHECKS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder source check not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderSourceChecks");
