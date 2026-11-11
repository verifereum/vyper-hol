Theory bodyIntCallCompilerConvert
Ancestors
  bodyIntCallCompilerScalar bodyIntCallCompilerContext bodyIntCallCompilerFloor
  bodyIntCallCompilerEmit exprLowering builtinSimple compileEnv

Theorem intcall_interval_load_bytestring_as_word:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (load_bytestring_as_word v opc a))
Proof
  strip_tac >> Cases_on `opc = SAR` >>
  simp[load_bytestring_as_word_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_return])
QED

Theorem intcall_interval_int_clamp:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_int_clamp sg bits v a))
Proof
  strip_tac >> Cases_on `sg` >>
  simp[compile_int_clamp_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return])
QED

Theorem intcall_interval_bytestring_widen_copy:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_bytestring_widen_copy dst v src a))
Proof
  strip_tac >> simp[compile_bytestring_widen_copy_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_copy_memory,
            intcall_interval_return])
QED

Theorem intcall_interval_zero_words:
  !n p k a. k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_zero_words p n a))
Proof
  Induct >> simp[compile_zero_words_def, intcall_interval_return,
                comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void])
QED

Theorem intcall_interval_builtin_empty_complex:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_builtin_empty_complex sz bs a))
Proof
  strip_tac >> Cases_on `bs` >>
  simp[compile_builtin_empty_complex_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_return,
            intcall_interval_zero_words, intcall_interval_emit_void])
QED

Theorem intcall_interval_clamp_basetype:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_clamp_basetype v ty a))
Proof
  strip_tac >> Cases_on `ty` >>
  simp[compile_clamp_basetype_def, intcall_interval_return] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_clamp_basetype_def, intcall_interval_return] >>
  rpt IF_CASES_TAC >>
  simp[compile_clamp_basetype_def, intcall_interval_clamp_return,
       intcall_interval_return, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return]) >>
  rename1 `BytesT bnd` >> Cases_on `bnd` >>
  simp[compile_clamp_basetype_def, intcall_interval_return, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> simp[intcall_interval_return] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return])
QED

Theorem intcall_interval_type_convert:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_type_convert v cv a))
Proof
  strip_tac >> Cases_on `cv` >>
  simp[compile_type_convert_def, comp_ignore_bind_def,
       intcall_interval_emit_op, intcall_interval_return] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (simp[pairTheory.FORALL_PROD] >> rpt strip_tac >> simp[pairTheory.FORALL_PROD,
            intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return, intcall_interval_int_clamp,
            intcall_interval_load_bytestring_as_word] >>
       rpt IF_CASES_TAC >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return, intcall_interval_int_clamp,
            intcall_interval_load_bytestring_as_word] >>
       irule intcall_interval_bind_floor)
QED
