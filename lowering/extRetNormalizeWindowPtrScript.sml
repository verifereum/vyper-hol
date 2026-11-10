Theory extRetNormalizeWindowPtr
Ancestors
  extRetRobustSourceChildrenPtr typedCopyLayoutPtr robustCopyTransportPtr
  valueEncoding valueEncodingProofs vyperTyping exprSimProps loweringPosts
  ptrDiscipline list arithmetic context compileEnv valueTypingMemoryProps

(* Source slots use the source element stride, independent of the destination
   layout.  A disjoint copy preserves the robust live child, not clean padding. *)
Theorem normalize_live_array_child_frame:
  value_has_type tv (EL i vs) /\ i < LENGTH vs /\ LENGTH vs <= cap /\
  (!m. mem_agree_outside ta mem m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) b m) /\
  (!j. b+32+i*type_memory_size tv <= j /\
       j < b+32+i*type_memory_size tv+val_footprint tv (EL i vs) ==>
       j NOTIN writes) /\
  (!j. j NOTIN writes ==> mem_bytes_at j 1 mem' = mem_bytes_at j 1 mem) /\
  (!j. j NOTIN writes ==> (j IN ta' <=> j IN ta)) ==>
  32+i*type_memory_size tv+val_store_size tv (EL i vs) <=
    32+cap*type_memory_size tv /\
  (!m. mem_agree_outside ta' mem' m ==>
    val_in_memory tv (EL i vs) (b+32+i*type_memory_size tv) m)
Proof
  strip_tac >> conj_tac
  >- (irule array_child_store_size_contained >> simp[]) >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- metis_tac[value_has_type_memory_wf] >>
  qexistsl_tac [`mem`, `mem'`, `ta`, `ta'`, `writes`] >> simp[] >>
  rpt strip_tac >>
  irule (SRULE [AC ADD_COMM ADD_ASSOC] robust_dynamic_source_child) >>
  simp[] >> qexistsl_tac [`Dynamic cap`, `ta`, `mem`] >> simp[]
QED

(* Nested dynamic arrays reserve complete source slots even when the live
   bytes child uses only a padded runtime prefix. No padding-clean claim. *)
Theorem normalize_nested_bytes_window_probe[local]:
  type_memory_size
    (ArrayTV (BaseTV (BytesT (Dynamic 96))) (Dynamic 2)) = 288 /\
  val_store_size (BaseTV (BytesT (Dynamic 96))) (BytesV [0w]) = 64 /\
  32 + 1 * type_memory_size (BaseTV (BytesT (Dynamic 96))) +
    val_store_size (BaseTV (BytesT (Dynamic 96))) (BytesV [0w]) <= 288 /\
  type_memory_size (TupleTV []) = 0 /\
  val_store_size (TupleTV []) (ArrayV (TupleV [])) = 0
Proof
  EVAL_TAC
QED

Theorem normalize_empty_fields_probe[local]:
  compile_typed_copy_fields ce dst src [] [] 0 0 sa = ((),sa)
Proof
  simp[Once compile_store_memory_typed_def, comp_return_def]
QED

(* Dispatch audit for the subsequent recursive counted-copy proof:
   - Word: extRetScalarCopyCountedPtr.compile_store_word_counted_ptr.
     Derive child cleanliness from robust representation, not root clean bytes.
   - Bytes/string: bodyPtrIfExpBytesPost.compile_store_bytestring_robust_gas_path_ptr.
     Runtime padded read fits the source child's slot by the theorem above.
   - Fixed-array batch: extRetBulkCopyCountedPtr.compile_copy_memory_counted_ptr;
     full source aggregate capacity covers count*source_stride. Per-element
     branch still needs a counted loop invariant, source/destination ADD
     provenance, strict nonwrapping offsets, and robust copied-prefix framing.
   - Dynamic-array header: robust_dynamic_source_length and its clean corollary;
     scalar counted MLOAD/MSTORE. Equal-element batch uses
     compile_copy_memory_dynamic_counted_ptr. Zero length still emits MCOPY:
     its zero-access/provenance premises must be derived, unlike static no-op.
     Different-element branch needs the same counted-loop machinery as above,
     with the source stride (not widened destination stride) in child windows.
   - Tuples: assign_base_typed_copy_fields_counted is conditional composition;
     robust_tuple_source_child and tuple_child_store_size_contained give reads.
     It is not an unconditional recursive child theorem.
   - Struct: robust_struct_source_child/structChildPtr give reads; metadata
     alignment, field-name lookup and source offset synchronization remain.
   - INVALID: store_memory_typed_invalid_counted is only abort evidence;
     successful normalization must derive acyclic metadata.
   - Fallback: compatible layouts must exclude mismatched aggregate tags or
     justify destination-sized source read and layout transfer. The existing
     widening size order alone goes in the WRONG direction for source coverage.
   These are exact missing producer/loop obligations, not premises to add to
   either frozen frame theorem. This leaf is a window probe, not a copy proof. *)
