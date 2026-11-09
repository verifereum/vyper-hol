(* Compiler slices for the dynamic memory-to-storage traversal. *)
Theory placeStorageLayoutCounted
Ancestors
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  typedArrayControlCounted fragExec words arithmetic list rich_list

Theorem dyn_storage_word_layout:
  compile_dynarray_to_storage src dst 1 em tr sa = ((),sb) ==>
  sb.cs_next_var = sa.cs_next_var + 11 /\
  sb.cs_next_id = sa.cs_next_id + 17 /\
  sb.cs_next_label = sa.cs_next_label + 3 /\
  LENGTH sb.cs_blocks = LENGTH sa.cs_blocks + 3 /\
  sb.cs_current_bb = fresh_label_output "dyn_exit" (sa.cs_next_label + 2) /\
  sb.cs_current_insts =
    [mk_inst (sa.cs_next_id + 16) (if tr then TSTORE else SSTORE)
      [dst; Var ("%" ++ toString sa.cs_next_var)] []]
Proof
  Cases_on `tr` >> simp[compile_dynarray_to_storage_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_label_def, fresh_var_def, fresh_id_def,
       emit_op_def, emit_void_def, emit_inst_def, emit_def, new_block_def] >>
  strip_tac >> gvs[]
QED
