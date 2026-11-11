(* TOP-LEVEL: mixed rows have exactly the head sizes and dynamic flags
   selected by the actual aggregate encoder. *)
Theory abiFieldComplexCode
Ancestors
  abiFieldDefs abiFlatComplexCode abiFlatFieldsDefs abiComplexCode abiFieldLayoutDefs
  abiEncoder compileEnv list pair arithmetic

Theorem abi_field_entries_head_size:
  !sfields cenv rows.
    SUM (MAP (\(_,head_size,_,_). head_size) (MAP (abi_field_entry sfields cenv) rows)) =
      abi_field_head_size (MAP abi_field_output rows)
Proof
  rpt gen_tac >> Induct_on `rows` >- simp[abi_field_head_size_def] >>
  qx_gen_tac `row` >> Cases_on `row`
  >- (rename1 `AbiFieldFlat leaf` >> Cases_on `leaf` >>
      simp[abi_field_entry_def, abi_field_output_def, abi_flat_entry_def, abi_flat_output_def, abi_field_head_size_def]) >>
  simp[abi_field_entry_def, abi_field_output_def, abi_field_head_size_def]
QED

Theorem abi_field_entries_dynamic:
  !sfields cenv rows.
    EXISTS (\(_,_,_,flag). flag) (MAP (abi_field_entry sfields cenv) rows) =
      EXISTS (\row. FST (abi_field_output row)) rows
Proof
  rpt gen_tac >> Induct_on `rows` >- simp[] >> qx_gen_tac `row` >> Cases_on `row`
  >- (rename1 `AbiFieldFlat leaf` >> Cases_on `leaf` >>
      simp[abi_field_entry_def, abi_field_output_def, abi_flat_entry_def, abi_flat_output_def]) >>
  simp[abi_field_entry_def, abi_field_output_def]
QED

Theorem compile_abi_field_complex_split:
  !sfields cenv rows dst src cs op cs'.
    EXISTS (\row. FST (abi_field_output row)) rows ==>
    (compile_abi_encode_to_buf dst src (AbiComplex (MAP (abi_field_entry sfields cenv) rows)) cs = (op,cs') <=>
    ?ret mid.
      compile_abi_encode_complex_elems dst src (MAP (abi_field_entry sfields cenv) rows) 0 0
        (Var (compiler_var_name cs.cs_next_var 0))
        (abi_complex_prefix_cut (abi_field_head_size (MAP abi_field_output rows)) cs) = (ret,mid) /\
      emit_op MLOAD [Var (compiler_var_name cs.cs_next_var 0)] mid = (op,cs'))
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`dst`, `src`, `MAP (abi_field_entry sfields cenv) rows`, `cs`, `op`, `cs'`]
    compile_abi_complex_dynamic_split) >> impl_tac >- simp[abi_field_entries_dynamic] >>
  simp[compile_abi_complex_prefix_result, abi_field_entries_head_size]
QED
