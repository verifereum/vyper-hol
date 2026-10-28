(* Exact Python-oracle bytecode checks for evaluator-small scalar width fixtures. *)

Theory evalCompilerBytecodeScalarWidths
Ancestors evalCompilerSubsetScalars compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerClosedFixtureEvalLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../python-o1-no-asm-opt/scalar_widths_int_high.hex",
   "../python-o1-no-asm-opt/scalar_widths_int_low.hex",
   "../python-o1-no-asm-opt/scalar_widths_uint_high.hex",
   "../python-o1-no-asm-opt/scalar_widths_uint_low.hex"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset
  (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_widths_uint_low" ``scalar_widths_uint_low_program``

Theorem scalar_widths_uint_low_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_widths_uint_low_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_widths_uint_low.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_widths_uint_high" ``scalar_widths_uint_high_program``

Theorem scalar_widths_uint_high_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_widths_uint_high_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_widths_uint_high.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_widths_int_low" ``scalar_widths_int_low_program``

Theorem scalar_widths_int_low_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_widths_int_low_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_widths_int_low.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_widths_int_high" ``scalar_widths_int_high_program``

Theorem scalar_widths_int_high_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_widths_int_high_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_widths_int_high.hex")
Proof
  EVAL_TAC
QED

val () = app (fn (name,theorem) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
in if null (Thm.hyp theorem) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then
    print ("SCALAR_WIDTHS_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
  else raise Fail "scalar width parity has kernel assumptions or admission tags"
end) [("scalar_widths_uint_low_matches_python_oracle",scalar_widths_uint_low_matches_python_oracle),
       ("scalar_widths_uint_high_matches_python_oracle",scalar_widths_uint_high_matches_python_oracle),
       ("scalar_widths_int_low_matches_python_oracle",scalar_widths_int_low_matches_python_oracle),
       ("scalar_widths_int_high_matches_python_oracle",scalar_widths_int_high_matches_python_oracle)]
