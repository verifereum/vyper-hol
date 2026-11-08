(*
 * Seam of bodyPtrStructLit: a struct literal every element of which has
 * its post at its annotated type (no widened internal-call element).
 *
 * TOP-LEVEL:
 *   body_struct_lit_uniform_ptr
 *)
Theory bodyPtrStructLitSeamUniform
Ancestors
  bodyPtrStructLitCallPath bodyPtrStructLitCompiledContext
  bodyPtrStructLitCopyPath bodyPtrStructLitCreationFrames
  bodyPtrStructLitEmpty bodyPtrStructLitEndpointAllocation
  bodyPtrStructLitEntryStoreFrame bodyPtrStructLitIdentityRead
  bodyPtrStructLitInvoke bodyPtrStructLitLayoutTransfer
  bodyPtrStructLitOldWordFrame bodyPtrStructLitOwnershipAbiWrappers
  bodyPtrStructLitOwnershipBuiltinBody
  bodyPtrStructLitOwnershipConstructorEntry
  bodyPtrStructLitOwnershipConstructorTail
  bodyPtrStructLitOwnershipDeclarationRoute bodyPtrStructLitOwnershipDispatch
  bodyPtrStructLitOwnershipEntryPc bodyPtrStructLitOwnershipExprBody
  bodyPtrStructLitOwnershipExtraction bodyPtrStructLitOwnershipInitial
  bodyPtrStructLitOwnershipModuleEntry bodyPtrStructLitOwnershipRestrictions
  bodyPtrStructLitOwnershipSelectedPackages bodyPtrStructLitOwnershipStmtLoops
  bodyPtrStructLitOwnershipStructLoop bodyPtrStructLitOwnershipTypeCases
  bodyPtrStructLitPathBoundary bodyPtrStructLitPhaseInvariant
  bodyPtrStructLitRequestFrame bodyPtrStructLitResourceHandoff
  bodyPtrStructLitReturnBoundary bodyPtrStructLitReturnCertificate
  bodyPtrStructLitReturnShape bodyPtrStructLitRobustOldBuffer
  bodyPtrStructLitStagingWrites bodyPtrStructLitTupleFrame
  bodyPtrStructLitUnwrapFrame bodyPtrStructLitUnwrapSeparation
  bodyPtrStructLitWordCapacity bodyPtrStructLitWordStoreHandoff
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* A struct literal lowers like a tuple literal (bodyPtrMakeArray's
   literal_tuple_vv_sim_ptr on the s3-ptr tip): allocate the struct's
   buffer, then for each field compile the element, add the field's
   offset to the buffer and store the element's value there
   (compile_struct_lit, compile_store_memory at the element's
   lowered_value_type), and return the buffer's base pointer.
   S1's proof of the same case is exprSimAggregates' compile_struct_lit_case
   (compile_struct_lit_vv_case); the fields' expr_body_pre is
   exprSimAggregateSource's expr_body_pre_struct_field.
   S1's split there is int_calls_expr e = [] \/ lowered_value_type = expr_type
   per element; its loop uses that only to get lowered_value_type = expr_type
   \/ is_bytestring_type (expr_type e), and post_value_type = expr_type
   (exprSimAggregateLoops' aggregate_elem_lowered_type and its uses), both of
   which follow from this statement's hypothesis.
   Why it holds for the elements this adds (bytestring-typed widened calls,
   Concat/AbiEncode with calls): a bytestring field is stored by
   compile_store_bytestring, which ignores the source type and copies
   32 + ceil32(len) bytes, inside the source's ptr_mem_ok coverage and the
   field's slot (val_wf bounds len).  A non-word, non-bytestring element has
   lowered_value_type = expr_type here, so its copy is at the field's size
   and ptr_buf_ok covers the read.  The struct's own post_value_type is its
   expr_type, so its vv_post asks no vv_own; vv_storage_live is trivial for
   its LocMemory value.  Typing puts the keys in declaration order without
   duplicates, and alloc_limits_expr bounds the buffer size. *)
Theorem body_struct_lit_uniform_ptr:
  !cx v7 src_id_opt id kes d PG tops ctx func cenv env ty es.
    body_exprs_ptr_ok cx (MAP SND kes) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) es /\
    EVERY (\e. post_value_type cenv e = expr_type e) (MAP SND kes) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es
Proof
  cheat
QED
