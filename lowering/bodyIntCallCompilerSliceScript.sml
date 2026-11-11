Theory bodyIntCallCompilerSlice
Ancestors
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  builtinBytes builtinStrings compileEnv

Theorem intcall_interval_assert_slice_bounds:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_assert_slice_bounds x n len a))
Proof
  strip_tac >> simp[compile_assert_slice_bounds_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED

Theorem intcall_interval_bytestring_src:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_bytestring_src p a))
Proof
  strip_tac >> simp[compile_bytestring_src_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_return])
QED

Theorem intcall_interval_slice_data:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_slice_data len p x n sz a))
Proof
  strip_tac >> simp[compile_slice_data_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_assert_slice_bounds, intcall_interval_alloc_buffer,
            intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return])
QED

Theorem intcall_interval_slice_out_buf:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_slice_out_buf sz a))
Proof
  strip_tac >> simp[compile_slice_out_buf_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_emit_op,
            intcall_interval_return])
QED

Theorem intcall_interval_slice_calldata:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_slice_calldata x n sz a))
Proof
  strip_tac >> simp[compile_slice_calldata_def, comp_ignore_bind_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_slice_out_buf, pairTheory.FORALL_PROD] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_assert_slice_bounds, intcall_interval_emit_op,
            intcall_interval_emit_void, intcall_interval_return])
QED

Theorem intcall_interval_slice_code:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_slice_code x n sz a))
Proof
  strip_tac >> simp[compile_slice_code_def, comp_ignore_bind_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_slice_out_buf, pairTheory.FORALL_PROD] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_assert_slice_bounds, intcall_interval_emit_op,
            intcall_interval_emit_void, intcall_interval_return])
QED

Theorem intcall_interval_slice_extcode:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_slice_extcode addr x n buf data a))
Proof
  strip_tac >> simp[compile_slice_extcode_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_assert_slice_bounds, intcall_interval_emit_op,
            intcall_interval_emit_void, intcall_interval_return])
QED

Theorem intcall_interval_extract32_load:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_extract32_load len p x a))
Proof
  strip_tac >> simp[compile_extract32_load_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_assert_slice_bounds, intcall_interval_emit_op])
QED

Theorem intcall_interval_uint2str:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_uint2str v digits sz a))
Proof
  strip_tac >> simp[compile_uint2str_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_return,
            intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_emit_inst, intcall_interval_fresh_var,
            intcall_interval_fresh_label, intcall_interval_new_block])
QED
