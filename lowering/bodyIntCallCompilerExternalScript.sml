Theory bodyIntCallCompilerExternal
Ancestors
  bodyIntCallCompilerExtOperands bodyIntCallCompilerAbiWrappers
  bodyIntCallCompilerDecoder bodyIntCallCompilerEncoder
  bodyIntCallCompilerTypedMemory bodyIntCallCompilerScalar
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  exprLowering compileEnv

Theorem intcall_interval_return_value_decode:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_return_value_decode lo hi a))
Proof
  strip_tac >> simp[compile_return_value_decode_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_select])
QED

Theorem intcall_interval_default_return_path:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_default_return_path ce rt dt buf res dv addr skip lo hi info a))
Proof
  strip_tac >> Cases_on `skip` >>
  simp[compile_default_return_path_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_emit_inst, intcall_interval_fresh_label,
            intcall_interval_new_block, intcall_interval_store_memory,
            intcall_interval_extcodesize_check, intcall_interval_return_value_decode,
            cj 1 intcall_interval_decode_family, intcall_interval_return])
QED

Theorem intcall_interval_external_call_kwargs:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_external_call_kwargs ce addr vs ts msz asz mid rsz
            lo rms static cv gas skip hd dv rt dt einfo dinfo a))
Proof
  strip_tac >>
  simp[compile_external_call_kwargs_def, comp_ignore_bind_def] >>
  irule intcall_interval_bind_floor >> simp[intcall_interval_alloc_buffer] >>
  rpt strip_tac >> irule intcall_interval_bind_floor >>
  simp[intcall_interval_emit_void] >>
  rpt strip_tac >> irule intcall_interval_bind_floor >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >> IF_CASES_TAC >> simp[intcall_interval_return] >>
      rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
           simp[intcall_interval_alloc_buffer, intcall_interval_extcall_store_values,
                intcall_interval_emit_op, cj 2 intcall_interval_encode_family])) >>
  rpt strip_tac >> irule intcall_interval_bind_floor >>
  simp[intcall_interval_emit_op] >>
  rpt strip_tac >> irule intcall_interval_bind_floor >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >> IF_CASES_TAC >>
      simp[intcall_interval_extcodesize_check, intcall_interval_return]) >>
  rpt strip_tac >> irule intcall_interval_bind_floor >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >> IF_CASES_TAC >> simp[intcall_interval_emit_op]) >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_emit_inst, intcall_interval_fresh_label,
            intcall_interval_new_block, intcall_interval_alloc_buffer]) >>
  rpt strip_tac >> Cases_on `rt = NoneT` >> Cases_on `hd` >>
  simp[intcall_interval_return] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_default_return_path,
            intcall_interval_return_value_decode,
            cj 1 intcall_interval_decode_family, intcall_interval_return])
QED
