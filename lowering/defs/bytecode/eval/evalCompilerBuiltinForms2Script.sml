(* Independent checked-frontend bytecode witnesses for builtin forms (#566):
   concat (a07-05): the running offset kept in a 64-byte memory temporary.
   Part 2 of evalCompilerBuiltinForms.
   TOP-LEVEL: concat_bytes2_matches_python_oracle,
              concat_bytesn_matches_python_oracle,
              concat_one_bytes_arg_matches_python_oracle,
              concat_string3args_matches_python_oracle,
              concat_string3_matches_python_oracle,
              len_concat_matches_python_oracle,
              concat_storage_matches_python_oracle. *)
Theory evalCompilerBuiltinForms2
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../builtin-forms"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../builtin-forms/oracle"

Theorem concat_fixed_word_allocation:
  concat_alloc_size [BaseT (BytesT (Fixed 1)); BaseT (BytesT (Fixed 1))] = 65 /\
  concat_alloc_size [BaseT (BytesT (Dynamic 10)); BaseT (BytesT (Fixed 4))] = 74
Proof
  EVAL_TAC
QED

(* two Bytes arguments. *)
val concat_bytes2 = memoryStoreWitnessLib.evaluate fixture_root "concat_bytes2"
Theorem concat_bytes2_matches_python_oracle:
  ^(#term concat_bytes2) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "concat_bytes2")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation concat_bytes2))) >> EVAL_TAC
QED

(* bytes32, bytes4 and Bytes arguments. *)
val concat_bytesn = memoryStoreWitnessLib.evaluate fixture_root "concat_bytesn"
Theorem concat_bytesn_matches_python_oracle:
  ^(#term concat_bytesn) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "concat_bytesn")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation concat_bytesn))) >> EVAL_TAC
QED

(* a Bytes and a bytes4 argument. *)
val concat_one_bytes_arg = memoryStoreWitnessLib.evaluate fixture_root "concat_one_bytes_arg"
Theorem concat_one_bytes_arg_matches_python_oracle:
  ^(#term concat_one_bytes_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "concat_one_bytes_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation concat_one_bytes_arg))) >> EVAL_TAC
QED

(* three String arguments. *)
val concat_string3args = memoryStoreWitnessLib.evaluate fixture_root "concat_string3args"
Theorem concat_string3args_matches_python_oracle:
  ^(#term concat_string3args) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "concat_string3args")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation concat_string3args))) >> EVAL_TAC
QED

(* String arguments around a literal. *)
val concat_string3 = memoryStoreWitnessLib.evaluate fixture_root "concat_string3"
Theorem concat_string3_matches_python_oracle:
  ^(#term concat_string3) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "concat_string3")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation concat_string3))) >> EVAL_TAC
QED

(* len of a concat. *)
val len_concat = memoryStoreWitnessLib.evaluate fixture_root "len_concat"
Theorem len_concat_matches_python_oracle:
  ^(#term len_concat) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "len_concat")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation len_concat))) >> EVAL_TAC
QED

(* uint2str_local is out of parity: see ../pending-uint2str-buffer.md. *)

(* a storage Bytes argument. *)
val concat_storage = memoryStoreWitnessLib.evaluate fixture_root "concat_storage"
Theorem concat_storage_matches_python_oracle:
  ^(#term concat_storage) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "concat_storage")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation concat_storage))) >> EVAL_TAC
QED
