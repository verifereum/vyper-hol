(* Location boundary for the immutable For element preparation.  The boolean
   constructor flag remains explicit: runtime uses DLOAD; constructors ILOAD. *)
Theory whitelistForIterImmCopy
Ancestors
  stmtLowering context compileEnv exprSimTopLevelImmutable
Libs
  monadsyntax

Theorem immutable_iter_small_copy:
  elem_size <= 32 ==>
  compile_iter_elem_copy cenv src dst elem_size LocCode F target_ty elem_ty =
    do v <- compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca src;
       emit_void MSTORE [dst; v]
    od
Proof
  simp[compile_iter_elem_copy_def, compile_ptr_load_def]
QED

Theorem immutable_iter_large_copy:
  32 < elem_size ==>
  compile_iter_elem_copy cenv src dst elem_size LocCode F target_ty elem_ty =
    compile_imm_copy_to_memory cenv.ce_is_ctor cenv.ce_imm_alloca
      src dst ((elem_size + 31) DIV 32) 0
Proof
  simp[compile_iter_elem_copy_def]
QED
