(* TOP-LEVEL: original compiler stages and computed result; no oracle bytes. *)
Theory evalCompilerBytecodeScalarMinmaxIntLowering
Ancestors
  evalCompilerSubsetScalars evalCompilerBytecodeStages venomSupplyEval
  venomMemLivenessEval compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerPackagingEvalLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20
val () = compilerPackagingEvalLib.configure ()
val () = evalCompilerBytecodeLib.configure_pass_stages ()
val scalar_minmax_int_stage_goals = strip_conj (rhs (concl
  (SPEC ``scalar_minmax_int_program`` parity_stages_def)))
val () = if length scalar_minmax_int_stage_goals = 31 then ()
  else raise Fail "expected all31 original compiler stages"

Theorem scalar_minmax_int_stage_00:
  ^(List.nth (scalar_minmax_int_stage_goals,0))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_01:
  ^(List.nth (scalar_minmax_int_stage_goals,1))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_02:
  ^(List.nth (scalar_minmax_int_stage_goals,2))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_03:
  ^(List.nth (scalar_minmax_int_stage_goals,3))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_04:
  ^(List.nth (scalar_minmax_int_stage_goals,4))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_05:
  ^(List.nth (scalar_minmax_int_stage_goals,5))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_06:
  ^(List.nth (scalar_minmax_int_stage_goals,6))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_07:
  ^(List.nth (scalar_minmax_int_stage_goals,7))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_08:
  ^(List.nth (scalar_minmax_int_stage_goals,8))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_09:
  ^(List.nth (scalar_minmax_int_stage_goals,9))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

val () = app (fn (name,theorem) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
in if null (Thm.hyp theorem) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then
    print ("SCALAR_MINMAX_INT_LOWERING_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
  else raise Fail "signed min/max early stages have kernel assumptions or admission tags"
end) [("scalar_minmax_int_stage_00",scalar_minmax_int_stage_00),
       ("scalar_minmax_int_stage_01",scalar_minmax_int_stage_01),
       ("scalar_minmax_int_stage_02",scalar_minmax_int_stage_02),
       ("scalar_minmax_int_stage_03",scalar_minmax_int_stage_03),
       ("scalar_minmax_int_stage_04",scalar_minmax_int_stage_04),
       ("scalar_minmax_int_stage_05",scalar_minmax_int_stage_05),
       ("scalar_minmax_int_stage_06",scalar_minmax_int_stage_06),
       ("scalar_minmax_int_stage_07",scalar_minmax_int_stage_07),
       ("scalar_minmax_int_stage_08",scalar_minmax_int_stage_08),
       ("scalar_minmax_int_stage_09",scalar_minmax_int_stage_09)]
val () = evalCompilerBytecodeLib.pending_stage_values :=
  List.filter (fn (named,equation) => Option.isSome named orelse
    optionSyntax.is_some (rhs (concl equation)))
    (!evalCompilerBytecodeLib.pending_stage_values)
val () = evalCompilerBytecodeLib.publish_stage_values ()
val () = evalCompilerBytecodeLib.compiler_certificates := []
