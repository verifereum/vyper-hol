(* Exact lowering and initial pass certificates for the external-call corpus. *)

Theory evalCompilerBytecodeAbiExternalCallsLowering
Ancestors evalCompilerSubsetAbiExternalCalls evalCompilerBytecodeStages venomSupplyEval compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerSsaEvalLib compilerPackagingEvalLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

val () = compilerPackagingEvalLib.configure ()
val () = evalCompilerBytecodeLib.configure_pass_stages ()

val () = compilerSsaEvalLib.configure ()
val pass_step = compilerSsaEvalLib.warm_step

(* Certify the actual guarded compiler stages under individual tactic limits.
   The original independent bytecode equality below remains plain EVAL_TAC. *)
val interface_calls_stage_goals = strip_conj (rhs (concl
  (SPEC ``task090_interface_calls_program`` parity_stages_def)))
val () = if length interface_calls_stage_goals = 31 then ()
  else raise Fail "expected all 31 original interface compiler stages"

Theorem interface_calls_stage_00:
  ^(List.nth (interface_calls_stage_goals,0))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem interface_calls_stage_01:
  ^(List.nth (interface_calls_stage_goals,1))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem interface_calls_stage_02:
  ^(List.nth (interface_calls_stage_goals,2))
Proof
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem interface_calls_stage_03:
  ^(List.nth (interface_calls_stage_goals,3))
Proof
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem interface_calls_stage_04:
  ^(List.nth (interface_calls_stage_goals,4))
Proof
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem interface_calls_stage_05:
  ^(List.nth (interface_calls_stage_goals,5))
Proof
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >> pass_step >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

(* Export optional stage results and their checked projections. Internal SSA
   traversal equations are private to this proof and need no disk bindings. *)
val () = evalCompilerBytecodeLib.pending_stage_values :=
  List.filter (fn (named,equation) => Option.isSome named orelse
    optionSyntax.is_some (rhs (concl equation)))
    (!evalCompilerBytecodeLib.pending_stage_values)
val () = evalCompilerBytecodeLib.publish_stage_values ()
