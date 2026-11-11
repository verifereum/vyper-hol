(* TOP-LEVEL: actual aggregate ABI code splits into tail-counter setup,
   field traversal and final length load. Field traversal exposes the real
   source-address ADD, child encoder and remaining fields. *)
Theory abiComplexCode
Ancestors
  abiEncoder context abiStaticLoopCode compileEnv emitHelper venomInst list pair arithmetic
Libs monadsyntax pairLib

Definition compile_abi_complex_prefix_def:
  compile_abi_complex_prefix head_size =
    do alloc <- compile_alloc_buffer 32;
       let dyn_ptr = alloc.buf_operand in
       do emit_void MSTORE [dyn_ptr; Lit (n2w head_size)]; return dyn_ptr od
    od
End

Definition abi_complex_prefix_insts_def:
  abi_complex_prefix_insts head_size id var_base =
    [mk_inst id ALLOCA [Lit 32w] [compiler_var_name var_base 0];
     mk_inst (id + 1) MSTORE [Var (compiler_var_name var_base 0); Lit (n2w head_size)] []]
End

Definition abi_complex_prefix_cut_def:
  abi_complex_prefix_cut head_size cs =
    cs with <| cs_current_insts := cs.cs_current_insts ++
      abi_complex_prefix_insts head_size cs.cs_next_id cs.cs_next_var;
      cs_next_id := cs.cs_next_id + 2; cs_next_var := cs.cs_next_var + 1 |>
End

Theorem compile_abi_complex_prefix_result:
  !head_size cs.
    compile_abi_complex_prefix head_size cs =
      (Var (compiler_var_name cs.cs_next_var 0), abi_complex_prefix_cut head_size cs)
Proof
  simp[compile_abi_complex_prefix_def, compile_alloc_buffer_def, abi_complex_prefix_cut_def,
    abi_complex_prefix_insts_def, emit_op_def, emit_void_def, emit_def, fresh_var_def, fresh_id_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM, compiler_var_name_def] >>
  simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
QED

Definition abi_complex_field_cut_def:
  abi_complex_field_cut src source_offset cs =
    cs with <| cs_current_insts := cs.cs_current_insts ++
      [mk_inst cs.cs_next_id ADD [src; Lit (n2w source_offset)] [compiler_var_name cs.cs_next_var 0]];
      cs_next_id := cs.cs_next_id + 1; cs_next_var := cs.cs_next_var + 1 |>
End

Theorem emit_abi_complex_field_address:
  !src source_offset cs.
    emit_op ADD [src; Lit (n2w source_offset)] cs =
      (Var (compiler_var_name cs.cs_next_var 0), abi_complex_field_cut src source_offset cs)
Proof
  simp[abi_complex_field_cut_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, compiler_var_name_def]
QED

Theorem compile_abi_complex_dynamic_split:
  !dst src elems cs op cs'.
    EXISTS (\(_,_,_,flag). flag) elems ==>
    (compile_abi_encode_to_buf dst src (AbiComplex elems) cs = (op,cs') <=>
    ?dyn_ptr prefix traversal_result mid.
      compile_abi_complex_prefix (SUM (MAP (\(_,head_size,_,_). head_size) elems)) cs = (dyn_ptr,prefix) /\
      compile_abi_encode_complex_elems dst src elems 0 0 dyn_ptr prefix = (traversal_result,mid) /\
      emit_op MLOAD [dyn_ptr] mid = (op,cs'))
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `elems` >- fs[] >>
  rename1 `compile_abi_encode_to_buf dst src (AbiComplex (entry::rest)) cs = _` >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_encode_child_def])) >>
  asm_simp_tac bool_ss [LET_THM, compile_abi_complex_prefix_def,
    comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `compile_alloc_buffer 32 cs` >>
  rename1 `compile_alloc_buffer 32 cs = (alloc,after_alloc)` >>
  Cases_on `emit_void MSTORE [alloc.buf_operand;
    Lit (n2w (SUM (MAP (\(_,head_size,_,_). head_size)
      ((entry::rest):(abi_enc_info # num # num # bool) list))))] after_alloc` >>
  rename1 `emit_void MSTORE _ after_alloc = (ignored,after_store)` >>
  Cases_on `compile_abi_encode_complex_elems dst src (entry::rest) 0 0 alloc.buf_operand after_store` >>
  simp[comp_return_def]
QED

Theorem compile_abi_complex_fields_cons_split:
  !dst src info head_size mem_size is_dyn rest source_offset head_offset dyn_ptr cs ret cs'.
    compile_abi_encode_complex_elems dst src ((info,head_size,mem_size,is_dyn)::rest)
      source_offset head_offset dyn_ptr cs = (ret,cs') <=>
    ?field_src prefix child_result mid.
      emit_op ADD [src; Lit (n2w source_offset)] cs = (field_src,prefix) /\
      compile_abi_encode_child dst field_src info is_dyn head_offset dyn_ptr prefix = (child_result,mid) /\
      compile_abi_encode_complex_elems dst src rest (source_offset + mem_size) (head_offset + head_size)
        dyn_ptr mid = (ret,cs')
Proof
  rpt gen_tac >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_encode_child_def])) >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `emit_op ADD [src; Lit (n2w source_offset)] cs` >>
  rename1 `emit_op ADD [src; Lit (n2w source_offset)] cs = (field_src,prefix)` >>
  Cases_on `compile_abi_encode_child dst field_src info is_dyn head_offset dyn_ptr prefix` >> simp[]
QED
