(* Consumer interface probe: supported For stores have IDENTICAL element
   types. Nested aggregates do not imply recursive typed-copy execution:
   compile_store_memory dispatches equal non-byte types to a flat copy. *)
Theory forPtrCopyInterface
Ancestors stmtLowering context supportedStmts

Theorem for_supported_array_element_type:
  supported_stmt tops bindings (For id ty (Array e) n ss) ==>
  ?name. e = Name (ArrayT ty (Fixed n)) name
Proof
  simp[supported_stmt_def, supported_iterator_def] >>
  Cases_on `e` >> simp[] >> rpt strip_tac >> gvs[] >>
  Cases_on `t` >> gvs[] >> rename1 `_ /\ bound = Fixed n` >>
  Cases_on `bound` >> gvs[]
QED

Theorem for_memory_element_copy_dispatch:
  compile_iter_elem_copy cenv src dst bytes LocMemory F ty ty =
  if is_word_type ty then
    do value <- emit_op MLOAD [src]; emit_void MSTORE [dst; value] od
  else if is_bytestring_type ty then compile_store_bytestring src dst
  else compile_copy_memory dst src (type_memory_bytes cenv ty)
Proof
  simp[compile_iter_elem_copy_def, compile_store_memory_def]
QED

(* Reviewed call-site classification (supersedes the overapproximation in
   forPtrBoundary's initial audit): stmtLowering:1245-1311 sets arr_elem_ty
   from expr_type; supported_iterator makes it exactly fty. S1
   array_for_source_ready:1036-1053 derives a local PtrVar binding and
   array_iter_layout supplies the memory-local path. Thus at LocMemory F:
   words use MLOAD/MSTORE; bytestrings use compile_store_bytestring;
   fixed/dynamic array, tuple and struct elements all use compile_copy_memory
   with identical types. Their nested layouts do NOT invoke recursive typed
   copying. No acyclic-metadata premise is needed to exclude INVALID here:
   compile_store_memory_typed is never selected. Type size agreement and
   nonwrapping remain required to justify addresses/copy extents.

   context:155-159 gives either no instruction (size=0) or one MCOPY;
   context:606-609 shows dynamic bulk copying is also one MCOPY, not a loop.
   Bytestring copying is MLOAD/ADD/AND/ADD/MCOPY (context:633-651).
   Existing array_iter_composite_copy_run (S1 stmtSimForArray:138-166)
   supplies a constructive run_inst_seq and code-layout witness for equal
   types. Need inst_seq_ptr for that SAME run, rather than conversion of a
   fixed-run safety theorem. ptr_inst_ok_mcopy_operand and
   mcopy_operand_ghost_frame (typedCopyPtr:529-580) supply the MCOPY checks
   and exact taint transport; ptr_inst_ok_copy_len_binop supplies arithmetic.

   Consumer-shaped bulk signature (all parameters universally quantified):
     compile_iter_elem_copy cenv (Var src) (Var dst) stride LocMemory F ty ty
       sa = ((),sb) /\ ~is_word_type ty /\
     fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
     s.vs_current_bb = sa.cs_current_bb /\
     s.vs_inst_idx = LENGTH sa.cs_current_insts /\
     not_fresh_at sa src /\ not_fresh_at sa dst /\
     lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
     evaluate_type (get_tenv cx) ty = SOME tv /\
     val_wf tv v /\ value_has_type tv v /\
     type_memory_bytes cenv ty = type_memory_size tv /\
     type_memory_size tv + 64 < dimword (:256) /\
     ptr_covers G tn src s (type_memory_size tv) /\
     ptr_covers G tn dst s (type_memory_size tv) /\
     (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory tv v (w2n a) mem)
     ==> ?Gf tnf sf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf)
       /\ sf.vs_current_bb = sb.cs_current_bb
       /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts
       /\ robust destination representation
       /\ exterior memory agreement outside destination type size
       /\ storage/transient taint unchanged
       /\ old-variable lookup/provenance/operand-taint frame.
   Here 'robust destination representation' is the same universal mem_agree
   implication at (w2n b), with tnf/sf. These descriptive output names are
   not new HOL predicates or admitted theorem skeletons. Exact frame
   conjuncts should reuse compile_store_word_framed_frag_ptr's shape.

   Bytestring signature specializes the same interface to is_bytestring_type
   ty. The copied count is 32 + ceil32(length), not full capacity; source
   robust representation fixes length bytes and makes MLOAD untainted.
   Payload taint is transported, not assumed absent. Coverage for full type
   size implies coverage for runtime copied extent once length<=capacity is
   derived. All other aggregate branches use the literal full type size.
   No disjointness is needed for a standalone MCOPY (overlap semantics), but
   loop-source snapshot preservation requires the new destination allocation
   disjoint from the source array allocation. Obtain this from fresh ALLOCA
   and stmt_state_rel allocation facts; it is not furnished by the two
   syntactic bridges proved above. Likewise actual element ptr_covers needs
   address/extent facts from fixed_array_element_address/extent, original
   ghost_inv, and arithmetic provenance; this probe does not certify those
   bridges. Source robust element representation follows pointwise in mem
   from fixed_array_element_in_memory applied to ghost_inv's outer array.
   Source allocation preservation across body callbacks must use the actual
   stmt_frag_ptr old-variable/ghost_inv post, never ghost_kept memory frame.
*)
