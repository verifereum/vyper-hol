(* Independent checked-frontend bytecode witnesses for builtin forms (#566):
   extract32 (a07-01, a07-03) and ceil (a07-11), with floor, len and a bytes32 slice (a07-07).
   Part 1 of evalCompilerBuiltinForms.
   TOP-LEVEL: extract32_default_matches_python_oracle,
              extract32_uint_matches_python_oracle,
              extract32_bytes4_matches_python_oracle,
              extract32_int128_matches_python_oracle,
              extract32_addr_matches_python_oracle,
              ceil_dec_matches_python_oracle,
              floor_dec_matches_python_oracle,
              len_bytes_arg_matches_python_oracle,
              slice_bytes32_matches_python_oracle. *)
Theory evalCompilerBuiltinForms1
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../builtin-forms"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../builtin-forms/oracle"

(* extract32(b, i) to bytes32: bounds check end < start or end > len, then load. *)
val extract32_default = memoryStoreWitnessLib.evaluate fixture_root "extract32_default"
Theorem extract32_default_matches_python_oracle:
  ^(#term extract32_default) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "extract32_default")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation extract32_default))) >> EVAL_TAC
QED

(* extract32 to uint256: no clamp. *)
val extract32_uint = memoryStoreWitnessLib.evaluate fixture_root "extract32_uint"
Theorem extract32_uint_matches_python_oracle:
  ^(#term extract32_uint) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "extract32_uint")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation extract32_uint))) >> EVAL_TAC
QED

(* extract32 to bytes4: clamp iszero(shl(32, val)). *)
val extract32_bytes4 = memoryStoreWitnessLib.evaluate fixture_root "extract32_bytes4"
Theorem extract32_bytes4_matches_python_oracle:
  ^(#term extract32_bytes4) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "extract32_bytes4")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation extract32_bytes4))) >> EVAL_TAC
QED

(* extract32 to int128: signed slt/sgt clamp. *)
val extract32_int128 = memoryStoreWitnessLib.evaluate fixture_root "extract32_int128"
Theorem extract32_int128_matches_python_oracle:
  ^(#term extract32_int128) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "extract32_int128")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation extract32_int128))) >> EVAL_TAC
QED

(* extract32 to address: clamp iszero(gt(val, 2**160 - 1)). *)
val extract32_addr = memoryStoreWitnessLib.evaluate fixture_root "extract32_addr"
Theorem extract32_addr_matches_python_oracle:
  ^(#term extract32_addr) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "extract32_addr")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation extract32_addr))) >> EVAL_TAC
QED

(* ceil(x): slt(x, 0) selects x or x + 10**10 - 1. *)
val ceil_dec = memoryStoreWitnessLib.evaluate fixture_root "ceil_dec"
Theorem ceil_dec_matches_python_oracle:
  ^(#term ceil_dec) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ceil_dec")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ceil_dec))) >> EVAL_TAC
QED

(* control: floor(x). *)
val floor_dec = memoryStoreWitnessLib.evaluate fixture_root "floor_dec"
Theorem floor_dec_matches_python_oracle:
  ^(#term floor_dec) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "floor_dec")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation floor_dec))) >> EVAL_TAC
QED

(* control: len of a Bytes argument. *)
val len_bytes_arg = memoryStoreWitnessLib.evaluate fixture_root "len_bytes_arg"
Theorem len_bytes_arg_matches_python_oracle:
  ^(#term len_bytes_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "len_bytes_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation len_bytes_arg))) >> EVAL_TAC
QED

(* slice of a bytes32: a 32-byte scratch and the literal length 32. *)
val slice_bytes32 = memoryStoreWitnessLib.evaluate fixture_root "slice_bytes32"
Theorem slice_bytes32_matches_python_oracle:
  ^(#term slice_bytes32) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "slice_bytes32")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation slice_bytes32))) >> EVAL_TAC
QED
