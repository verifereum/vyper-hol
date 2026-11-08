(*
 * Seam of pop_expr_ptr_ok (bodyPtrPop): x.pop() with x a local, the
 * target a bare NameTarget.  The pointer twin of S1's
 * compile_pop_name_sim (exprSimPop; S1's case is exprSimPlaces'
 * compile_pop_name_case, used by bodySimExprCases' body_pop_case).
 *
 * TOP-LEVEL:
 *   pop_local_root_vv_ptr
 *)
Theory bodyPtrPopSeamLocalRoot
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs vyperAST

(* Hints, not part of the statement:
   - compile_expr runs compile_get_target_ptr on the local (its PtrVar
     from cenv.ce_vars, located in memory) and then
     compile_dynarray_pop hdr 32 ... LocMemory: MLOAD of the length, the
     ISZERO/ISZERO/ASSERT guard, SUB, MSTORE of the new length, then the
     element address ADD/MUL/ADD.
   - Proved counted pieces of exactly that suffix, from earlier runs:
     bodyPtrPopMemoryHeader (pop_memory_header_load), bodyPtrPopLengthGuard
     (pop_length_guard_path, pop_length_guard_empty_path,
     pop_length_guard_ghost), bodyPtrPopMemoryStore
     (pop_clean_header_store_path), bodyPtrPopLengthStore
     (pop_region_taint_pop_header), bodyPtrPopInteriorPointer
     (pop_emit_interior_pointer_path), bodyPtrPopLiveElement.
   - ghost_inv's val_in_memory for the local, under any memory agreeing
     outside tn.t_mem, makes the length word untainted.
   - The storage twin of the whole case is bodyPtrPopRootOutcome's
     compile_pop_storage_normalized_ptr; the memory-safety twin is
     alan-ref/mem/bodyMemPopLocal*.
   - Possibly vacuous instead: supported programs pop only top-level
     storage arrays (bodyPtrPopEffectClassification's
     pop_supported_target_shape), but the compiled-code window exclusion
     (bodyPtrPopContextExclusion) covers SLOAD/TLOAD windows only, not
     MLOAD ones. *)
Theorem pop_local_root_vv_ptr:
  !tops ctx cenv cx env ann id ty es d PG func.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Pop ann (NameTarget id)) es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann (NameTarget id)) es
Proof
  cheat
QED
