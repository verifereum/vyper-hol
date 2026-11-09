Theory bodyPtrIfExpCallerLayout
Ancestors
  bodyPtrIfExpRecursiveContract bodyPtrIfExpSourceTyping
  vyperTypeSystem context compileEnv

(* Unlike the address/fixed-bytes diagnostic, this mismatch is compatible
   with the actual internal-call widening direction. It is still NOT a
   reachable call simulation or a counterexample to the frozen target. *)
Theorem tuple_offset_probe_fits_call_annotation:
  arg_type_fits
    (TupleT [BaseT (BytesT (Dynamic 32)); BaseT (UintT 256)])
    (TupleT [BaseT (BytesT (Dynamic 64)); BaseT (UintT 256)])
Proof
  simp[arg_type_fits_def]
QED

Theorem tuple_offset_probe_layout_differs:
  !ce. ~same_memory_layout ce
    (TupleT [BaseT (BytesT (Dynamic 32)); BaseT (UintT 256)])
    (TupleT [BaseT (BytesT (Dynamic 64)); BaseT (UintT 256)])
Proof
  simp[same_memory_layout_def, punnable_def, type_memory_bytes_def]
QED

(* ACTUAL CALLER LAYOUT AUDIT.

   lowered_value_type_def (:161-174) is exhaustive:
   1. Literal StringL with StringT annotation: physical StringT LENGTH s.
      Outer compile_store_memory ignores src_ty for bytestring destination;
      BytesPost can use the semantic annotation on both sides. No physical
      source reinterpretation is needed. Literal BytesL/Dynamic BytesT is
      identical in this respect (bound LENGTH bs).
   2. TypeBuiltin AbiEncode: physical BaseT Dynamic BytesT with computed ABI
      bound (+4 for a method id). On a well-typed caller its annotation is
      byte-like; again outer bytes dispatch does not use source type.
   3. Call IntCall: physical type ce_func_return_type, annotation may widen
      it elementwise. ifexp_internal_call_return_bridge identifies physical
      type with sig.ret_ty using body_inv/expr_body_pre. The already checked
      ifexp_internal_call_lowered_typed supplies value_has_type, NOT memory.
   4. All other constructors, including non-IntCall calls: physical type
      equals expr_type. An actual allocating-arm guard excludes equal layout
      after annotation equality; semantic interpretation uses ptr_val_ok.
      No constructor-time materialization case is needed (~ce_is_ctor).

   Provenance of the premises at the selected-arm endpoint:
   - body_expr_ptr_ok gives expr_sim_ptr/expr_vv_sim_ptr. Their posts use
     expr_post/vv_post at expr_type arm; ptr_val_ok/ptr_vv_ok likewise use
     expr_type arm. ptr_buf_ok alone mentions lowered_value_type and states
     allocation bounds, not memory contents.
   - IfExp well_typed_expr inside expr_body_pre identifies the two arm
     annotations with the result annotation. It does not identify the
     callee's declared return type with that annotation.
   - well_typed_expr IntCall (:776) requires type_widens_to sig.ret_ty ty.
     tuple_offset_probe_fits_call_annotation verifies that the bytes32 to
     bytes64 tuple example passes the compatibility direction; it is unlike
     the earlier address/fixed-bytes pair, which cannot widen. The checked
     layout_differs theorem verifies this case selects conversion.
   - body_inv fixes return-type maps, code context and acyclic struct
     metadata. It has NO machine/ghost state argument and cannot itself
     describe physical memory at the returned pointer. In particular it
     rules out cyclic metadata but does not give a new result interpretation.
   - expr_post's expr_val_at bounds an allocation or local region for the
     ANNOTATION footprint. vv_post's vv_holds/vv_at also use expr_type arm.
     Neither adds a physical return-buffer interpretation. ghost_inv tracks
     live locals/storage and provenance; it does not state arbitrary callee
     result buffers' semantic contents at the declared return type.
   - Allocation source-frame transport preserves these existing facts; it
     does not strengthen annotation interpretation to physical layout.
     Memory no-op unwrap cannot manufacture that missing interpretation.

   Internal-call implementation has stronger intermediate interfaces, e.g.
   intret_mem_q and compile_internal_return_memory_frag describe callee
   return buffers. They are NOT exposed by the assumed operand judgment.
   Replaying a call would require callee-body simulation/framing premises
   not supplied by this frozen IfExp induction case. The S1 reference
   bodySimIfExpWidenedScript.sml.txt explicitly marks the same case HELD
   for a post_value_type interface wave (lines6-10,25-31); its admitted
   widened-arm theorem is not a pointer interpretation theorem.

   Status of the concrete tuple candidate: compatibility and unequal layout
   checked; double value typing and annotation memory with bad physical
   child offset checked in RecursiveContract. Not checked: existence of a
   complete supported module/context whose actual compiled call reaches
   this memory, or the global body_expr_ptr_ok call premise. Indeed real
   callee code may return physical-layout memory which cannot satisfy the
   annotation-based assumed post. Thus this is an interface obstruction,
   not evidence that the frozen implication is false. No new hypothesis
   or changed post is silently introduced here.

   Before full conversion implementation, strategist must choose a genuine
   source of physical representation (a caller-available theorem, a proof
   using actual execution plus sufficient callee premises, or a carefully
   scoped vacuity/reachability argument). Changing expr_post/ptr_val_ok to
   post_value_type is outside the task's domain constraints; it cannot be
   smuggled into a new helper. Do not start the recursive store proof on
   the basis of typing and buffer capacity alone.
*)
