(* Original loops compiler stages and result; no oracle bytes. *)
Theory evalCompilerBytecodeLoopsStages
Ancestors
  evalCompilerBytecodeLoopsPlanning
  evalCompilerBytecodeLoopsLowering
  evalCompilerBytecodeLoopsMemory
  evalCompilerBytecodeLoopsSsa
  evalCompilerBytecodeLoopsPrefix
  evalCompilerBytecodeLoopsDft
  evalCompilerBytecodeLoopsPipeline
  evalCompilerBytecodeLoopsReadiness
  stackPlanRegularCases stackPlanCleanupCases stackPlanInstructionCases
  stackPlanBlockCases stackPlanTraversalCases stackPlanReorderEval planExecEval
  evalCompilerSubsetControlDeploy evalCompilerBytecodeStages compileVyper
  concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerPackagingEvalLib compilerExternalPlannerEvalLib
  compilerTraversalPlannerEvalLib compilerContextPlannerEvalLib compilerAssemblyEvalLib
  finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20
val () = compilerPackagingEvalLib.configure ()
val () = evalCompilerBytecodeLib.configure_pass_stages ()
val () = compilerTraversalPlannerEvalLib.configure ()
val () = compilerContextPlannerEvalLib.configure ()
val () = compilerAssemblyEvalLib.configure ()
val context_slice = compilerContextPlannerEvalLib.warm_slice
val assembly_slice = compilerAssemblyEvalLib.warm_slice
val loops_stage_goals = strip_conj (rhs (concl
  (SPEC ``loops_program`` parity_stages_def)))
val () = if length loops_stage_goals = 31 then ()
  else raise Fail "expected all31 original loops compiler stages"
val () = app evalCompilerBytecodeLib.restore_stage_values
  ["evalCompilerBytecodeLoopsLowering",
   "evalCompilerBytecodeLoopsMemory",
   "evalCompilerBytecodeLoopsSsa",
   "evalCompilerBytecodeLoopsPrefix",
   "evalCompilerBytecodeLoopsDft",
   "evalCompilerBytecodeLoopsPipeline",
   "evalCompilerBytecodeLoopsReadiness"]

val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeLoopsPlanning"

Theorem loops_stage_25[local]:
  ^(List.nth (loops_stage_goals,25))
Proof
  assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >>
  compilerAssemblyEvalLib.finish
QED

Theorem loops_stage_26[local]:
  ^(List.nth (loops_stage_goals,26))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem loops_stage_27[local]:
  ^(List.nth (loops_stage_goals,27))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem loops_stage_28[local]:
  ^(List.nth (loops_stage_goals,28))
Proof
  context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >>
  context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >>
  context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >>
  context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >>
  context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >>
  context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >>
  context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >>
  context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >> context_slice >>
  compilerContextPlannerEvalLib.finish
QED

Theorem loops_stage_29[local]:
  ^(List.nth (loops_stage_goals,29))
Proof
  assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >>
  assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >>
  compilerAssemblyEvalLib.finish
QED

Theorem loops_stage_30[local]:
  ^(List.nth (loops_stage_goals,30))
Proof
  assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >> assembly_slice >>
  compilerAssemblyEvalLib.finish
QED

Theorem loops_stages:
  parity_stages loops_program
Proof
  rewrite_tac[parity_stages_def] >>
  ACCEPT_TAC (LIST_CONJ
    [loops_stage_00,
     loops_stage_01,
     loops_stage_02,
     loops_stage_03,
     loops_stage_04,
     loops_stage_05,
     loops_stage_06,
     loops_stage_07,
     loops_stage_08,
     loops_stage_09,
     loops_stage_10,
     loops_stage_11,
     loops_stage_12,
     loops_stage_13,
     loops_stage_14,
     loops_stage_15,
     loops_stage_16,
     loops_stage_17,
     loops_stage_18,
     loops_stage_19,
     loops_stage_20,
     loops_stage_21,
     loops_stage_22,
     loops_stage_23,
     loops_stage_24,
     loops_stage_25,
     loops_stage_26,
     loops_stage_27,
     loops_stage_28,
     loops_stage_29,
     loops_stage_30])
QED

Theorem loops_compiles:
  IS_SOME (compile_vyper (K SOME) (o1_policy all_capabilities) loops_program)
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

val () = app (fn (name,theorem) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
in if null (Thm.hyp theorem) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then
    print ("FIXTURE_STAGE_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
  else raise Fail "compiler fixture has kernel assumptions or admission tags"
end) [("loops_stages",loops_stages),
       ("loops_compiles",loops_compiles)]
val () = evalCompilerBytecodeLib.pending_stage_values :=
  List.filter (fn (_,equation) => same_const
    (fst (strip_comb (lhs (concl equation))))
    (prim_mk_const {Thy="compileVyper",Name="compile_vyper"}))
    (!evalCompilerBytecodeLib.pending_stage_values)
val () = if null (!evalCompilerBytecodeLib.pending_stage_values) then
  raise Fail "completed compiler equation missing" else ()
val () = evalCompilerBytecodeLib.publish_stage_values ()
val () = evalCompilerBytecodeLib.compiler_certificates := []

val () = compilerInstructionPlannerEvalLib.normalization_certificates := []
val () = compilerInstructionPlannerEvalLib.argument_certificates := []
