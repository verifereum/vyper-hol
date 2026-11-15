Theory bodyIntCallCompilerStaging
Ancestors
  bodyIntCallCompilerTypedMemory bodyIntCallCompilerUnwrap
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  bodyIntCallCompilerInterval bodyIntCallStageCompile exprLowering context
  compileEnv

(* RESTATED (train 17): 0.5.0b1 per-argument staging *)
Theorem intcall_interval_stage_intcall_args:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !cenv es flags tys a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_stage_intcall_args cfn cenv es flags tys a))
Proof
  strip_tac >> Induct_on `es` >-
    simp[compile_stage_intcall_args_def, intcall_interval_return] >>
  rpt gen_tac >> strip_tac >>
  namedCases_on `flags` ["", "flag fs"] >>
  namedCases_on `tys` ["", "ty ts"] >>
  TRY (Cases_on `flag`) >>
  simp[intcall_stage_memory_cons] >>
  simp[compile_stage_intcall_args_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       asm_simp_tac (srw_ss())
         [intcall_interval_unwrap_value, intcall_interval_alloc_buffer,
          intcall_interval_store_memory, intcall_interval_return])
QED
