(* Bytecode checks for interface calls and value sending: send_value matches
   the pinned Python oracle exactly; interface_calls decodes call results with
   the bounded decoder, so it is checked to be supported, to compile, and to
   differ from the pinned bytes. *)

Theory evalCompilerBytecodeAbiExternalCalls
Ancestors evalCompilerSubsetAbiExternalCalls compileVyper supportedProgram concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

(* Bounded return decoding deliberately differs from VYPER_PIN: it checks
   relative positions before forming pointers and copies bytestrings by their
   runtime length (vyperlang/vyper#5333). Keep the independent pinned oracle. *)
val interface_calls_compile_eval = EVAL
  ``compile_vyper (K SOME) (o1_policy all_capabilities)
      task090_interface_calls_program``
val _ = save_thm ("interface_calls_supported_status",
  EVAL ``supported_program task090_interface_calls_program``)
Theorem interface_calls_compiles:
  IS_SOME (compile_vyper (K SOME) (o1_policy all_capabilities)
    task090_interface_calls_program)
Proof
  CONV_TAC (RAND_CONV (K interface_calls_compile_eval)) >> EVAL_TAC
QED
Theorem interface_calls_differs_from_pinned_decoder:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    task090_interface_calls_program <>
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "interface_calls.hex")
Proof
  CONV_TAC (RAND_CONV (LAND_CONV (K interface_calls_compile_eval))) >>
  EVAL_TAC
QED

Theorem send_value_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    task090_send_value_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "send_value.hex")
Proof
  EVAL_TAC
QED
