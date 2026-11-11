Theory bodyIntCallCompilerLiteral
Ancestors
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  bodyIntCallCompilerScalar bodyIntCallCompilerUnwrap bodyIntCallCompilerInterval
  bodyIntCallCompilerAggregate exprLowering exprBopLowering compileEnv

Theorem intcall_interval_store_byte_chunks:
  !p bs off k a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (compile_store_byte_chunks p bs off a))
Proof
  ho_match_mp_tac compile_store_byte_chunks_ind >> rpt conj_tac >>
  rpt strip_tac >> simp[Once compile_store_byte_chunks_def, comp_ignore_bind_def,
                         intcall_interval_return] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_return]) >> gvs[]
QED

Theorem intcall_interval_bytelike_literal:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_bytelike_literal bs n a))
Proof
  strip_tac >> simp[compile_bytelike_literal_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_emit_void,
            intcall_interval_store_byte_chunks, intcall_interval_return])
QED

Theorem intcall_interval_literal_vv:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_literal_vv ty lit a))
Proof
  strip_tac >> Cases_on `lit` >> simp[compile_literal_vv_def, intcall_interval_return]
  >- (rename1 `BoolL b` >> Cases_on `b` >>
      simp[compile_literal_vv_def, intcall_interval_return])
  >- (Cases_on `ty` >> simp[compile_literal_vv_def] >>
      irule intcall_interval_bind_floor >>
      simp[intcall_interval_bytelike_literal, intcall_interval_return]) >>
  Cases_on `ty` >> simp[compile_literal_vv_def, intcall_interval_return] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_literal_vv_def, intcall_interval_return] >>
  rename1 `BytesT bnd` >> Cases_on `bnd` >>
  simp[compile_literal_vv_def, intcall_interval_return] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_bytelike_literal, intcall_interval_return]
QED

Theorem intcall_interval_name_vv:
  intcall_compiler_interval k a (SND (compile_name_vv ce ty id a))
Proof
  simp[compile_name_vv_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[intcall_interval_return]
  >- (irule intcall_compiler_interval_ignore_bind >>
      simp[intcall_interval_return] >> irule intcall_interval_emit_inst >> simp[]) >>
  rename1 `SOME vl` >> Cases_on `vl` >> simp[intcall_interval_return] >>
  irule intcall_compiler_interval_ignore_bind >>
  simp[intcall_interval_return] >> irule intcall_interval_emit_inst >> simp[]
QED

Theorem intcall_interval_addmod_names:
  k <= st.cs_next_var ==>
  intcall_compiler_interval k st
    (SND (compile_addmod_names ce rt aty a bty b mty m st))
Proof
  strip_tac >> simp[compile_addmod_names_def] >>
  rpt (irule intcall_interval_pair_bind_floor >>
       simp[intcall_interval_name_vv, intcall_interval_unwrap_value,
            as_stack_val_pair, intcall_interval_addmod] >> rpt strip_tac)
QED

Theorem intcall_interval_mulmod_names:
  k <= st.cs_next_var ==>
  intcall_compiler_interval k st
    (SND (compile_mulmod_names ce rt aty a bty b mty m st))
Proof
  strip_tac >> simp[compile_mulmod_names_def] >>
  rpt (irule intcall_interval_pair_bind_floor >>
       simp[intcall_interval_name_vv, intcall_interval_unwrap_value,
            as_stack_val_pair, intcall_interval_mulmod] >> rpt strip_tac)
QED

Theorem intcall_interval_powmod256_names:
  k <= st.cs_next_var ==>
  intcall_compiler_interval k st
    (SND (compile_powmod256_names ce rt aty a bty b st))
Proof
  strip_tac >> simp[compile_powmod256_names_def] >>
  rpt (irule intcall_interval_pair_bind_floor >>
       simp[intcall_interval_name_vv, intcall_interval_unwrap_value,
            as_stack_val_pair, intcall_interval_pow_mod256] >> rpt strip_tac)
QED
