(* Exact Python-oracle bytecode check for the external array ABI fixture. *)

Theory evalCompilerBytecodeAbiExternalArrays
Ancestors evalCompilerSubsetAbiExternal compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

val external_arrays_compile_eval = save_thm
  ("external_arrays_compile_eval",
   EVAL ``compile_vyper (K SOME) (o1_policy prague_capabilities)
      task090_external_arrays_program``)
val external_arrays_oracle_eq = EQT_ELIM (EVAL (mk_eq
  (rhs (concl external_arrays_compile_eval),
   ``SOME ^(evalCompilerBytecodeLib.read_hex_bytes "external_arrays.hex")``)))
val external_arrays_matches_python_oracle = save_thm
  ("external_arrays_matches_python_oracle",
   TRANS external_arrays_compile_eval external_arrays_oracle_eq)

val _ = export_theory()
