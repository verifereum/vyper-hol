(* Exact use-site availability slice 12; the analysis and all queries
   come from the actual ABI-dynamic compiler output. *)
Theory evalCompilerBytecodeAbiDynamicAvailable12
Ancestors evalCompilerBytecodeAbiDynamicAnalysis codegenReadyCompute
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib compilerAbiDynamicAvailabilityEvalLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos,
   codegenReadyComputeTheory.def_available_at_exec_compute])

Theorem abi_dynamic_available_12:
  ^(abi_dynamic_available_slice 12)
Proof
  abi_dynamic_available_step >> abi_dynamic_available_step >> abi_dynamic_available_step >> abi_dynamic_available_step >> abi_dynamic_available_step >>
  abi_dynamic_available_step >> abi_dynamic_available_step >> abi_dynamic_available_step >> abi_dynamic_available_step >> abi_dynamic_available_step >>
  abi_dynamic_available_step >> abi_dynamic_available_step >> abi_dynamic_available_step >> abi_dynamic_available_step >>
  abi_dynamic_available_check
QED
