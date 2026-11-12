Theory bodyIntCallCompilerStaging
Ancestors
  bodyIntCallCompilerTypedMemory bodyIntCallCompilerUnwrap
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  bodyIntCallCompilerInterval exprLowering context compileEnv

(* RESTATED (train 17): 0.5.0b1 per-argument staging *)
Theorem intcall_interval_stage_intcall_args:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !cenv es flags tys a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_stage_intcall_args cfn cenv es flags tys a))
Proof
  cheat
QED




