(* TOP-LEVEL: concrete field rows have exactly the metadata head sizes and
   dynamic flags consumed by the actual aggregate ABI dispatcher. *)
Theory abiFlatComplexCode
Ancestors
  abiFlatFieldsDefs abiComplexCode abiFieldLayoutDefs abiStaticLoopCode
  abiEncoder compileEnv list pair arithmetic

Theorem abi_flat_entries_head_size:
  !rows. SUM (MAP (\(_,head_size,_,_). head_size) (MAP abi_flat_entry rows)) =
    abi_field_head_size (MAP abi_flat_output rows)
Proof
  Induct_on `rows` >- simp[abi_field_head_size_def] >>
  qx_gen_tac `row` >> Cases_on `row` >>
  simp[abi_flat_entry_def, abi_flat_output_def, abi_field_head_size_def]
QED

Theorem abi_flat_entries_dynamic:
  !rows. EXISTS (\(_,_,_,flag). flag) (MAP abi_flat_entry rows) =
    EXISTS (\row. FST (abi_flat_output row)) rows
Proof
  Induct_on `rows` >- simp[] >> qx_gen_tac `row` >> Cases_on `row` >>
  simp[abi_flat_entry_def, abi_flat_output_def]
QED

Theorem compile_abi_flat_complex_split:
  !rows dst src cs op cs'.
    EXISTS (\row. FST (abi_flat_output row)) rows ==>
    (compile_abi_encode_to_buf dst src (AbiComplex (MAP abi_flat_entry rows)) cs = (op,cs') <=>
    ?ret mid.
      compile_abi_encode_complex_elems dst src (MAP abi_flat_entry rows) 0 0
        (Var (compiler_var_name cs.cs_next_var 0))
        (abi_complex_prefix_cut (abi_field_head_size (MAP abi_flat_output rows)) cs) = (ret,mid) /\
      emit_op MLOAD [Var (compiler_var_name cs.cs_next_var 0)] mid = (op,cs'))
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`dst`, `src`, `MAP abi_flat_entry rows`, `cs`, `op`, `cs'`] compile_abi_complex_dynamic_split) >>
  impl_tac >- simp[abi_flat_entries_dynamic] >>
  simp[compile_abi_complex_prefix_result, abi_flat_entries_head_size]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed concrete field metadata for the actual ABI dispatcher: " ^ name)
  end) (DB.thms "abiFlatComplexCode")
