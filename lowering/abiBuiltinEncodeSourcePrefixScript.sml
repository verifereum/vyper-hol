(* Connect the dispatcher's byte-list method ID to the actual shifted word
   store and the source evaluator's prefix. *)
Theory abiBuiltinEncodeSourcePrefix
Ancestors
  abiBuiltinEncodeRun abiBuiltinEncodeMethodReach builtinAbi valueEncodingProofs
  vyperAST vyperTypeSystem cv_std byte words list rich_list arithmetic divides

Theorem abi_builtin_method_word_aligned:
  LENGTH bs = 4 ==>
  bytes_method_id_word bs << 224 = (word_of_bytes_be bs:bytes32)
Proof
  strip_tac >>
  `(word_of_bytes_be bs:bytes32) = n2w (num_of_bytes (be_bytes 32 [] bs))` by
    (irule (SIMP_RULE (srw_ss()) [divides_def]
      (INST_TYPE [alpha |-> ``:256``] word_of_bytes_be_eq_num_of_bytes)) >>
     qexists_tac `32` >> simp[]) >>
  `TAKE 32 (bs ++ REPLICATE 32 0w) = bs ++ REPLICATE 28 0w` by
    simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG, REPLICATE_GENLIST, TAKE_GENLIST] >>
  asm_simp_tac (srw_ss()) [bytes_method_id_word_def, be_bytes_thm, REVERSE_APPEND,
    REVERSE_REPLICATE, num_of_bytes_APPEND, word_lsl_n2w, MULT_COMM]
QED

Theorem abi_builtin_method_word_prefix:
  LENGTH bs = 4 ==>
  abi_builtin_encode_method_bytes (bytes_method_id_word bs) = bs
Proof
  strip_tac >> drule abi_builtin_method_word_aligned >> strip_tac >>
  mp_tac (Q.SPEC `bs` TAKE_word_to_bytes_be_word_of_bytes_be) >>
  asm_simp_tac (srw_ss()) [abi_builtin_encode_method_bytes_def, word_to_bytes_be_def]
QED

Theorem abi_builtin_encode_source_prefix:
  (case method_id of NONE => T | SOME bs => LENGTH bs = 4) ==>
  abi_builtin_encode_prefix (OPTION_MAP bytes_method_id_word method_id) =
    abi_encode_method_id_bytes method_id
Proof
  Cases_on `method_id` >> simp[abi_builtin_encode_prefix_def, abi_encode_method_id_bytes_def] >>
  strip_tac >> drule abi_builtin_method_word_prefix >> simp[]
QED

Theorem abi_builtin_encode_checked_prefix:
  well_typed_type_builtin_args (AbiEncode ensure method_id) target_ty arg_tys ==>
  abi_builtin_encode_prefix (OPTION_MAP bytes_method_id_word method_id) =
    abi_encode_method_id_bytes method_id
Proof
  simp_tac bool_ss [well_typed_type_builtin_args_def] >> strip_tac >>
  irule abi_builtin_encode_source_prefix >> asm_simp_tac bool_ss []
QED

Theorem abi_builtin_encode_store_case:
  (case OPTION_MAP bytes_method_id_word method_id of NONE => 0 | SOME _ => 32) =
  (case method_id of NONE => 0 | SOME _ => 32)
Proof
  Cases_on `method_id` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_SOURCE_PREFIX_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin encode source prefix not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeSourcePrefix");
