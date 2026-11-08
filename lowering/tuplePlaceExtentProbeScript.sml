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
