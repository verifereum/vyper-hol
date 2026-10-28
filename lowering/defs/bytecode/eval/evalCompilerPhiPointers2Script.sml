(* Independent checked-frontend bytecode witnesses for memory pointers merged
   by a PHI: uint2str and ternaries (IfExp) of non-word type (#561).
   Half 2 of evalCompilerPhiPointers: ifexp_string, ifexp_bytes,
   ifexp_sarray, ifexp_struct, ctl_ret_string_phi.
   TOP-LEVEL: ifexp_string_matches_python_oracle,
              ifexp_bytes_matches_python_oracle,
              ifexp_sarray_matches_python_oracle,
              ifexp_struct_matches_python_oracle,
              ctl_ret_string_phi_matches_python_oracle. *)
Theory evalCompilerPhiPointers2
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../phi-pointers"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../phi-pointers/oracle"

(* String ternary returned directly: the result is a PHI of two memory pointers (a14-01). *)
val ifexp_string = memoryStoreWitnessLib.evaluate fixture_root "ifexp_string"
Theorem ifexp_string_matches_python_oracle:
  ^(#term ifexp_string) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ifexp_string")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ifexp_string))) >> EVAL_TAC
QED

(* Bytes ternary with a literal branch (a14-01). *)
val ifexp_bytes = memoryStoreWitnessLib.evaluate fixture_root "ifexp_bytes"
Theorem ifexp_bytes_matches_python_oracle:
  ^(#term ifexp_bytes) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ifexp_bytes")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ifexp_bytes))) >> EVAL_TAC
QED

(* static-array ternary assigned to a local: a memory pointer value, copied through a temporary (a10-04). *)
val ifexp_sarray = memoryStoreWitnessLib.evaluate fixture_root "ifexp_sarray"
Theorem ifexp_sarray_matches_python_oracle:
  ^(#term ifexp_sarray) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ifexp_sarray")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ifexp_sarray))) >> EVAL_TAC
QED

(* struct ternary assigned to a local (a10-04). *)
val ifexp_struct = memoryStoreWitnessLib.evaluate fixture_root "ifexp_struct"
Theorem ifexp_struct_matches_python_oracle:
  ^(#term ifexp_struct) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ifexp_struct")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ifexp_struct))) >> EVAL_TAC
QED

(* control: String result chosen by if/else statements, no ternary. *)
val ctl_ret_string_phi = memoryStoreWitnessLib.evaluate fixture_root "ctl_ret_string_phi"
Theorem ctl_ret_string_phi_matches_python_oracle:
  ^(#term ctl_ret_string_phi) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ctl_ret_string_phi")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ctl_ret_string_phi))) >> EVAL_TAC
QED
