(* Honest total typed-copy boundary. Valid-domain dispatch is the frozen
   original dispatch, with unchanged metadata, field sizes, and copy helpers.
   Word and byte paths deliberately do not inspect irrelevant metadata. *)
Theory typedCopyAgreement
Ancestors
  context typedCopyDomain typedCopyCounterexample typedCopyProducer
  compileEnv emitHelper venomInst vyperAST list pair arithmetic
Libs
  monadsyntax

val () = enable_monad "compilation";
val () = enable_monadsyntax ();

Theorem compile_store_memory_typed_valid:
  acyclic_struct_metadata cenv.ce_struct_fields ==>
  compile_store_memory_typed cenv dst dst_ty src src_ty =
    (if is_word_type dst_ty then
      do val_op <- emit_op MLOAD [src]; emit_void MSTORE [dst; val_op] od
    else if is_bytestring_type dst_ty /\ is_bytestring_type src_ty then
      compile_store_bytestring src dst
    else case (dst_ty,src_ty) of
      (ArrayT dst_elem (Dynamic dst_cap), ArrayT src_elem (Dynamic _)) =>
        compile_copy_dynarray_typed cenv dst dst_elem dst_cap src src_elem
    | (ArrayT dst_elem (Fixed n), ArrayT src_elem (Fixed _)) =>
        compile_copy_sarray_typed cenv dst dst_elem src src_elem n
    | (TupleT dst_tys, TupleT src_tys) =>
        compile_typed_copy_fields cenv dst src dst_tys src_tys 0 0
    | (StructT dst_nsid, StructT src_nsid) =>
        let dst_fields = get_struct_fields cenv.ce_struct_fields (nsid_to_string dst_nsid);
            src_fields = get_struct_fields cenv.ce_struct_fields (nsid_to_string src_nsid)
        in compile_struct_typed_copy cenv dst src dst_fields src_fields 0 0
    | _ => compile_copy_memory dst src (type_memory_bytes cenv dst_ty))
Proof
  simp[Once compile_store_memory_typed_def]
QED

Theorem compile_store_memory_typed_word:
  is_word_type dst_ty ==>
  compile_store_memory_typed cenv dst dst_ty src src_ty =
  do val_op <- emit_op MLOAD [src]; emit_void MSTORE [dst; val_op] od
Proof
  simp[Once compile_store_memory_typed_def]
QED

Theorem compile_store_memory_typed_bytes:
  is_bytestring_type dst_ty /\ is_bytestring_type src_ty ==>
  compile_store_memory_typed cenv dst dst_ty src src_ty =
  compile_store_bytestring src dst
Proof
  Cases_on `dst_ty` >> simp[is_bytestring_type_def] >>
  Cases_on `b` >> simp[is_bytestring_type_def] >>
  TRY (Cases_on `b'` >> simp[is_bytestring_type_def]) >>
  simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]
QED

Theorem compile_store_memory_typed_invalid:
  ~is_word_type dst_ty /\
  ~(is_bytestring_type dst_ty /\ is_bytestring_type src_ty) /\
  ~acyclic_struct_metadata cenv.ce_struct_fields ==>
  compile_store_memory_typed cenv dst dst_ty src src_ty = emit_void INVALID []
Proof
  rpt strip_tac >> simp[Once compile_store_memory_typed_def]
QED

Theorem audit_cycle_total_invalid:
  compile_store_memory_typed cycle_env (Lit 0w) cycle_type (Lit 0w) cycle_type =
  emit_void INVALID []
Proof
  EVAL_TAC
QED

Theorem audit_cycle_finite_state:
  compile_store_memory_typed cycle_env (Lit 0w) cycle_type (Lit 0w) cycle_type st =
  ((), st with <|cs_next_id := st.cs_next_id + 1;
                cs_current_insts := st.cs_current_insts ++
                  [mk_inst st.cs_next_id INVALID [] []]|>)
Proof
  simp[audit_cycle_total_invalid, emit_void_def, emit_inst_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED
