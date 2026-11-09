(* Diagnostic: syntactic views are not necessarily memory-located values.
   Nonmemory aggregate unwrapping allocates before the unstaged unpack.
   This is a compiler equation, not an ownership theorem. *)
Theory tuplePlaceFlagProbe
Ancestors
  tuplePlaceUnpack exprLowering stmtLowering context
Libs monadsyntax

Theorem tuple_place_storage_view_flag_probe:
  FLOOKUP cenv.ce_module_vars nsid = SOME (StorageLoc slot) ==>
  compile_expr cenv (TupleT tys) (TopLevelName (TupleT tys) nsid) sa =
    (LocatedValue (TupleT tys) (mk_ptr (Lit slot) LocStorage), sa) /\
  is_memory_view (TopLevelName (TupleT tys) nsid) /\
  vv_location (LocatedValue (TupleT tys) (mk_ptr (Lit slot) LocStorage)) <>
    SOME LocMemory
Proof
  simp[Once compile_expr_def, vyperASTTheory.expr_type_def,
    is_memory_view_def, vv_location_def, mk_ptr_def]
QED

Theorem tuple_place_storage_unwrap_probe:
  unwrap_value cenv (LocatedValue (TupleT tys) (mk_ptr src LocStorage)) =
  do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
     (if (type_memory_bytes cenv (TupleT tys) + 31) DIV 32 = 1 then
        do loaded <- emit_op SLOAD [src];
           emit_void MSTORE [buf.buf_operand; loaded] od
      else do compile_storage_to_memory src buf.buf_operand
                ((type_memory_bytes cenv (TupleT tys) + 31) DIV 32);
              comp_return () od);
     comp_return buf.buf_operand
  od
Proof
  simp[unwrap_value_def, compileEnvTheory.is_word_type_def, mk_ptr_def,
    compile_ensure_in_memory_def]
QED

Theorem tuple_place_unstaged_unpack_probe:
  compile_tuple_unpack cenv (TupleT ltys) F gs op =
  do elems <- compile_tuple_load_all cenv op ltys 0;
     compile_tuple_store_all cenv ltys gs elems od
Proof
  simp[compile_tuple_unpack_def, compileEnvTheory.comp_bind_def,
    compileEnvTheory.comp_return_def, compileEnvTheory.comp_ignore_bind_def,
    FUN_EQ_THM]
QED
