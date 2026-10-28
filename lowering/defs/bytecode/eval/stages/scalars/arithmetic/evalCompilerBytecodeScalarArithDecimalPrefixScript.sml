(* TOP-LEVEL: original compiler stages and computed result; no oracle bytes. *)
Theory evalCompilerBytecodeScalarArithDecimalPrefix
Ancestors
  venomDfsCases venomDftEval venomDftLoopCases venomWorklistEval venomStackOrderEval
  evalCompilerBytecodeScalarWordEval
  evalCompilerSubsetScalars evalCompilerBytecodeStages venomSupplyEval
  venomMemLivenessEval compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerPackagingEvalLib
  compilerDftEvalLib compilerDftWorklistEvalLib compilerDftBoundaryEvalLib
  compilerDftLoopBoundaryEvalLib compilerProofSliceEvalLib
  finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = computeLib.upd_compset
  (computeLib.add_thms [scalar_decimal_type_bounds_eval,
    w2n_scalar_decimal_lo_word_eval, w2n_scalar_decimal_hi_word_eval])
val () = Globals.max_print_depth := 20
val () = compilerPackagingEvalLib.configure ()
val () = evalCompilerBytecodeLib.configure_pass_stages ()
val scalar_arith_decimal_stage_goals = strip_conj (rhs (concl
  (SPEC ``scalar_arith_decimal_program`` parity_stages_def)))
val () = if length scalar_arith_decimal_stage_goals = 31 then ()
  else raise Fail "expected all31 original compiler stages"

Theorem scalar_arith_decimal_stage_00:
  ^(List.nth (scalar_arith_decimal_stage_goals,0))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_01:
  ^(List.nth (scalar_arith_decimal_stage_goals,1))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_02:
  ^(List.nth (scalar_arith_decimal_stage_goals,2))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_03:
  ^(List.nth (scalar_arith_decimal_stage_goals,3))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_04:
  ^(List.nth (scalar_arith_decimal_stage_goals,4))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_05:
  ^(List.nth (scalar_arith_decimal_stage_goals,5))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_06:
  ^(List.nth (scalar_arith_decimal_stage_goals,6))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_07:
  ^(List.nth (scalar_arith_decimal_stage_goals,7))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_08:
  ^(List.nth (scalar_arith_decimal_stage_goals,8))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_09:
  ^(List.nth (scalar_arith_decimal_stage_goals,9))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_10:
  ^(List.nth (scalar_arith_decimal_stage_goals,10))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

(* Prepare the exact DFT call through the existing checked worklist. *)
val () = evalCompilerBytecodeLib.ensure_certificate_head ``dft_fn`` 1
val () = compilerDftWorklistEvalLib.configure ()
fun warm_fixture_dft goal =
  if List.exists (aconv ``dft_fn (FST (parity_pass scalar_arith_decimal_program 6))``)
      (!compilerDftWorklistEvalLib.completed) then
    evalCompilerBytecodeLib.cache_checkpoint goal
  else compilerDftLoopBoundaryEvalLib.warm_call
    ``dft_fn (FST (parity_pass scalar_arith_decimal_program 6))`` goal
val dft_slice = compilerProofSliceEvalLib.run warm_fixture_dft

Theorem scalar_arith_decimal_stage_11:
  ^(List.nth (scalar_arith_decimal_stage_goals,11))
Proof
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> dft_slice >> 
  compilerDftWorklistEvalLib.require_complete
    ``dft_fn (FST (parity_pass scalar_arith_decimal_program 6))`` >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_12:
  ^(List.nth (scalar_arith_decimal_stage_goals,12))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_13:
  ^(List.nth (scalar_arith_decimal_stage_goals,13))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_14:
  ^(List.nth (scalar_arith_decimal_stage_goals,14))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_decimal_stage_15:
  ^(List.nth (scalar_arith_decimal_stage_goals,15))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

val () = app (fn (name,theorem) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
in if null (Thm.hyp theorem) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then
    print ("SCALAR_ARITH_DECIMAL_PREFIX_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
  else raise Fail "decimal prefix has kernel assumptions or admission tags"
end) [("scalar_arith_decimal_stage_00",scalar_arith_decimal_stage_00),
       ("scalar_arith_decimal_stage_01",scalar_arith_decimal_stage_01),
       ("scalar_arith_decimal_stage_02",scalar_arith_decimal_stage_02),
       ("scalar_arith_decimal_stage_03",scalar_arith_decimal_stage_03),
       ("scalar_arith_decimal_stage_04",scalar_arith_decimal_stage_04),
       ("scalar_arith_decimal_stage_05",scalar_arith_decimal_stage_05),
       ("scalar_arith_decimal_stage_06",scalar_arith_decimal_stage_06),
       ("scalar_arith_decimal_stage_07",scalar_arith_decimal_stage_07),
       ("scalar_arith_decimal_stage_08",scalar_arith_decimal_stage_08),
       ("scalar_arith_decimal_stage_09",scalar_arith_decimal_stage_09),
       ("scalar_arith_decimal_stage_10",scalar_arith_decimal_stage_10),
       ("scalar_arith_decimal_stage_11",scalar_arith_decimal_stage_11),
       ("scalar_arith_decimal_stage_12",scalar_arith_decimal_stage_12),
       ("scalar_arith_decimal_stage_13",scalar_arith_decimal_stage_13),
       ("scalar_arith_decimal_stage_14",scalar_arith_decimal_stage_14),
       ("scalar_arith_decimal_stage_15",scalar_arith_decimal_stage_15)]

val () = evalCompilerBytecodeLib.pending_stage_values :=
  List.filter (fn (named,equation) => Option.isSome named orelse
    optionSyntax.is_some (rhs (concl equation)))
    (!evalCompilerBytecodeLib.pending_stage_values)
val () = evalCompilerBytecodeLib.publish_stage_values ()
val () = evalCompilerBytecodeLib.compiler_certificates := []
