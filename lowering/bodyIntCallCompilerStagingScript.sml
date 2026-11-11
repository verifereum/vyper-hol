Theory bodyIntCallCompilerStaging
Ancestors
  bodyIntCallCompilerTypedMemory bodyIntCallCompilerUnwrap
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  bodyIntCallCompilerInterval exprLowering context compileEnv

Theorem intcall_interval_stage_intcall_args:
  !cenv vals flags tys k a.
    k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_stage_intcall_args cenv vals flags tys a))
Proof
  ho_match_mp_tac compile_stage_intcall_args_ind >> rpt conj_tac
  >- simp[Once compile_stage_intcall_args_def, intcall_interval_return]
  >- suspend "stack"
  >- suspend "memory"
  >- suspend "fallback1"
  >> suspend "fallback2"
QED

Resume intcall_interval_stage_intcall_args[stack]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_stage_intcall_args_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_unwrap_value, intcall_interval_return])
QED

Resume intcall_interval_stage_intcall_args[memory]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_stage_intcall_args_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_unwrap_value, intcall_interval_alloc_buffer,
            intcall_interval_return]) >>
  gvs[] >> rpt IF_CASES_TAC >>
  rpt (rpt strip_tac >>
       simp[intcall_interval_emit_void, intcall_interval_store_memory,
            intcall_interval_store_bytestring, intcall_interval_return] >>
       irule intcall_interval_bind_floor)
QED

Resume intcall_interval_stage_intcall_args[fallback1]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_stage_intcall_args_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_unwrap_value, intcall_interval_return])
QED

Resume intcall_interval_stage_intcall_args[fallback2]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_stage_intcall_args_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_unwrap_value, intcall_interval_return])
QED
Finalise intcall_interval_stage_intcall_args
