(* Zero-size execution and conditional source-extent probes. *)
Theory tuplePlaceExtentProbe
Ancestors
  tuplePlaceHead tuplePlaceBounds annassignRelayoutPost
  abiEncoderInput stmtLowering context venomMemDefs
  vyperTypeSystem vyperValue exprLowering compileEnv valueEncodingProps
Libs monadsyntax

Theorem tuple_place_empty_tuple_accepted:
  evaluate_type tenv (TupleT []) = SOME (TupleTV []) /\
  ~is_word_type (TupleT []) /\
  type_memory_bytes cenv (TupleT []) = 0 /\
  type_memory_size (TupleTV []) = 0
Proof
  simp[evaluate_type_def, is_word_type_def, type_memory_bytes_def,
       valueEncodingTheory.type_memory_size_def, type_slot_size_def]
QED

Theorem tuple_place_empty_memory_direct:
  compile_assign_value cenv dst LocMemory src F NONE
    (TupleT []) (TupleT []) NONE 0 = comp_return ()
Proof
  simp[compile_assign_value_def, compile_store_memory_def,
       is_word_type_def, is_bytestring_type_def, type_memory_bytes_def,
       compile_copy_memory_def]
QED

(* Storage is NOT a zero-byte copy: even size zero goes through MLOAD. *)
Theorem tuple_place_empty_storage_reads:
  compile_assign_value cenv dst LocStorage src F NONE
    (TupleT []) (TupleT []) NONE 0 =
    do loaded <- emit_op MLOAD [src]; emit_void SSTORE [dst; loaded] od
Proof
  simp[compile_assign_value_def, is_bytestring_type_def] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

Theorem tuple_place_owned_element_extent:
  alloca_inv s /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  a + type_memory_size_list tvs <= b+sz /\ i < LENGTH tvs ==>
  a + SUM (MAP type_memory_size (TAKE i tvs)) + type_memory_size (EL i tvs)
    <= s.vs_alloca_next
Proof
  strip_tac >>
  qspecl_then [`type_memory_size`, `tvs`, `i`] mp_tac abi_encoder_prefix_sum_bound >>
  gvs[alloca_inv_def, alloca_next_valid_def,
      valueEncodingProofsTheory.type_memory_size_list_sum] >>
  first_x_assum drule >> decide_tac
QED

Theorem tuple_place_empty_memory_staged:
  compile_assign_value cenv dst LocMemory src F (SOME LocMemory)
    (TupleT []) (TupleT []) NONE 0 =
    do buf <- compile_alloc_buffer 0; comp_return () od
Proof
  simp[compile_assign_value_def, compile_store_memory_def,
       is_word_type_def, is_bytestring_type_def, type_memory_bytes_def,
       compile_copy_memory_def] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def] >>
  gen_tac >> pairarg_tac >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]
QED

Theorem tuple_place_length_layout_positive_probe:
  type_memory_size (BaseTV (BytesT (Dynamic 0))) = 32 /\
  type_memory_size (ArrayTV (TupleTV []) (Dynamic 0)) = 32 /\
  type_memory_size (TupleTV [TupleTV []]) = 0
Proof EVAL_TAC
QED

(* Source-extent audit, C1.3.4.3.7.2:
   WORDS: the snapshot is deliberately vacuous; every pending value is already
   loaded into a word operand. No memory source extent should be requested.
   ZERO: tuple_place_load_zero_path checks loading, using w2n_lt and total size
   zero, without any frontier hypothesis. arg_type_fits_zero_size_rigid
   (annassignRelayoutPost:8) proves source/destination layouts identical when
   the evaluated source has size zero. No recursive widening is needed here.
   The checked empty-tuple probes show direct memory assignment emits nothing,
   while a memory-view store still allocates a zero-byte buffer. Storage and
   transient branches with dynarray_info=NONE and copy_size=0 still MLOAD then
   SSTORE/TSTORE: they are NOT justified by zero-byte no-op reasoning.
   place_store_empty_run is a length-word store and is not this case.
   The positivity probe distinguishes zero-capacity dynamic arrays/bytes: their
   header still takes 32 bytes, so they do not belong to the ZERO disjunct.

   OWNED/STAGED: tuple_place_owned_element_extent combines the allocation
   certificate's containment with alloca_inv and abi_encoder_prefix_sum_bound.
   It uses full capacity, not val_footprint. stmt_state_rel supplies alloca_inv.
   BORROWED: bodyMemoryDefs.body_local_region_frontier (exported :78) gives
   b+sz <= s.vs_alloca_next from stmt_state_rel and the local_region witness.
   The same prefix-sum bound then gives each member end <= frontier. No site
   provenance is needed for extent (but it IS needed for future-allocation
   separation, the separate .7.3 audit). No new local-region helper is needed.

   Proposed interface: demand source-end <= frontier only on positive-size
   nonword sources. Dispatch zero source size to equal-layout memory empty-copy
   or staged-zero-allocation execution. For storage/transient, either derive
   positive type_slot_size from actual typed targets, excluding the empty-tuple
   example, or supply a separate dead-slot/read execution argument. These are
   unresolved runner obligations, not additional root hypotheses and not a
   counterexample to the frozen stmt_frag. The ZERO certificate alone cannot
   imply even w2n w <= frontier; do not attempt to initialize that field.
*)

(* C1.3.4.3.7.3: bounded allocation-provenance audit (not a runner proof).

   The universal future-id premise in tuple_place_value_run_frame is stronger
   than the allocation sites its staging/normalization consumers need:

   - compile_staging_prefix_forward (placeMemoryStaging) uses it only at
     aid = sa.cs_next_id, b = w2n tw, sz = n, after executing
     compile_alloc_buffer n sa. Its allocation result distinguishes lookup
     reuse from a fresh range starting at s.vs_alloca_next.
   - tuple_place_normalize_frame calls place_store_alloc_source_disjoint
     (placeStoreStorage) with that same allocation result. This helper only
     needs the reused entry at sa.cs_next_id; its universal premise is a
     sufficient interface, not evidence for instruction provenance.
   - tuple_place_memory_forward_frame's direct branch has no such allocation
     use. Its staged branch delegates the requirement to the staging prefix.

   Owned positive-size case: the snapshot has an allocation lookup at an id
   strictly before store entry, containing the whole source envelope.
   alloca_inv / allocas_non_overlapping gives numeric separation from ANY
   different allocation-map id, independently of instruction membership.
   Containment transfers this to the element envelope. Allocation age and
   compiler id monotonicity establish the required id inequality. Preserve
   these witnesses; no instruction/output provenance is needed in this case.

   Borrowed case: local_region is NOT an allocation-history assertion.
   local_ptrs_rel_alloca_disjoint additionally asks for MEM inst (fn_insts
   func), inst_outputs = [q], not_local_ptr cenv scopes q, and the lookup at
   inst_id. Neither an arbitrary FLOOKUP nor a numeric future-id inequality
   provides these facts. expr_val_at_alloca_disjoint has the same site/output
   requirements and protects val_footprint, not full local capacity.

   Proposed replacement obligation, NOT asserted/proved here:
     for each ACTUAL compile_alloc_buffer n sa = (buf,sm) in the store,
     at its allocation endpoint r with returned address tw,
       regions_disjoint src source_capacity (w2n tw) n.
   This is site-indexed, not universally quantified over future map entries.
   For a borrow, compile_alloc_buffer_forward already returns separation
   from every local_region at r, along with memory identity, old-variable
   preservation and the allocation lookup. Transfer the original borrow's
   whole local_region from s to r with local_region_frame_fwd, then restrict
   the full-region separation to the contained source envelope. This avoids
   reconstructing site witnesses manually. Alternatively buffer_alloc_code
   supplies the exact ALLOCA membership; output/nonlocal facts must still be
   proved from fresh_var and local_ptrs_reserved at that compiler state.

   A future task-local staging runner can use this endpoint separation plus
   compile_copy_memory_forward; a normalization runner can use it plus the
   typed-copy effect. Both must compose paths and return state relation and
   frames at the SAME endpoint. Source operand freshness, source extent and
   preservation of the borrowed local_region must be threaded to every
   actual allocation site; this audit does not certify those integrations.

   Zero-size caveat: regions_disjoint permits either size to be zero even
   when the numeric intervals' ordering disjunction is false. Do not convert
   it to numeric separation without positivity or a separate zero branch.
   The checked probes above show why storage zero is not a no-op. This is an
   interface diagnosis only, not a counterexample to the frozen theorem.
*)
