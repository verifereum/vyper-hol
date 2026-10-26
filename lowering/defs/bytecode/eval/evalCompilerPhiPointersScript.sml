(* Independent checked-frontend bytecode witnesses for memory pointers merged
   by a PHI: uint2str and ternaries (IfExp) of non-word type (#561).
   TOP-LEVEL: uint2str_arg_matches_python_oracle,
              ifexp_string_matches_python_oracle,
              ifexp_bytes_matches_python_oracle,
              ifexp_dynarray_matches_python_oracle,
              ifexp_sarray_matches_python_oracle,
              ifexp_struct_matches_python_oracle,
              ifexp_bytes20_matches_python_oracle,
              ifexp_flag_matches_python_oracle,
              ifexp_decimal_matches_python_oracle,
              ctl_sarray_assign_matches_python_oracle,
              ctl_ret_string_phi_matches_python_oracle. *)
Theory evalCompilerPhiPointers
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../phi-pointers/oracle/uint2str_arg.json",
   "../phi-pointers/oracle/uint2str_arg.hex",
   "../phi-pointers/oracle/ifexp_string.json",
   "../phi-pointers/oracle/ifexp_string.hex",
   "../phi-pointers/oracle/ifexp_bytes.json",
   "../phi-pointers/oracle/ifexp_bytes.hex",
   "../phi-pointers/oracle/ifexp_dynarray.json",
   "../phi-pointers/oracle/ifexp_dynarray.hex",
   "../phi-pointers/oracle/ifexp_sarray.json",
   "../phi-pointers/oracle/ifexp_sarray.hex",
   "../phi-pointers/oracle/ifexp_struct.json",
   "../phi-pointers/oracle/ifexp_struct.hex",
   "../phi-pointers/oracle/ifexp_bytes20.json",
   "../phi-pointers/oracle/ifexp_bytes20.hex",
   "../phi-pointers/oracle/ifexp_flag.json",
   "../phi-pointers/oracle/ifexp_flag.hex",
   "../phi-pointers/oracle/ifexp_decimal.json",
   "../phi-pointers/oracle/ifexp_decimal.hex",
   "../phi-pointers/oracle/ctl_sarray_assign.json",
   "../phi-pointers/oracle/ctl_sarray_assign.hex",
   "../phi-pointers/oracle/ctl_ret_string_phi.json",
   "../phi-pointers/oracle/ctl_ret_string_phi.hex"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../phi-pointers/oracle"

(* uint2str(x): the digit buffer reached only through the result PHI stays live (a14-01, a14-02, a07-06). *)
val uint2str_arg = memoryStoreWitnessLib.evaluate fixture_root "uint2str_arg"
Theorem uint2str_arg_matches_python_oracle:
  ^(#term uint2str_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "uint2str_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation uint2str_arg))) >> EVAL_TAC
QED

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

(* DynArray ternary (a14-01). *)
val ifexp_dynarray = memoryStoreWitnessLib.evaluate fixture_root "ifexp_dynarray"
Theorem ifexp_dynarray_matches_python_oracle:
  ^(#term ifexp_dynarray) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ifexp_dynarray")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ifexp_dynarray))) >> EVAL_TAC
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

(* control: bytes20 ternary stays a stack value. *)
val ifexp_bytes20 = memoryStoreWitnessLib.evaluate fixture_root "ifexp_bytes20"
Theorem ifexp_bytes20_matches_python_oracle:
  ^(#term ifexp_bytes20) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ifexp_bytes20")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ifexp_bytes20))) >> EVAL_TAC
QED

(* control: flag ternary stays a stack value. *)
val ifexp_flag = memoryStoreWitnessLib.evaluate fixture_root "ifexp_flag"
Theorem ifexp_flag_matches_python_oracle:
  ^(#term ifexp_flag) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ifexp_flag")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ifexp_flag))) >> EVAL_TAC
QED

(* control: decimal ternary stays a stack value. *)
val ifexp_decimal = memoryStoreWitnessLib.evaluate fixture_root "ifexp_decimal"
Theorem ifexp_decimal_matches_python_oracle:
  ^(#term ifexp_decimal) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ifexp_decimal")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ifexp_decimal))) >> EVAL_TAC
QED

(* control: static-array local assigned from a parameter, no ternary. *)
val ctl_sarray_assign = memoryStoreWitnessLib.evaluate fixture_root "ctl_sarray_assign"
Theorem ctl_sarray_assign_matches_python_oracle:
  ^(#term ctl_sarray_assign) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ctl_sarray_assign")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ctl_sarray_assign))) >> EVAL_TAC
QED

(* control: String result chosen by if/else statements, no ternary. *)
val ctl_ret_string_phi = memoryStoreWitnessLib.evaluate fixture_root "ctl_ret_string_phi"
Theorem ctl_ret_string_phi_matches_python_oracle:
  ^(#term ctl_ret_string_phi) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ctl_ret_string_phi")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ctl_ret_string_phi))) >> EVAL_TAC
QED
