(* Destination slack audit.  This is not a counterexample to stmt_frag. *)
Theory tuplePlaceSlackProbe
Ancestors
  tuplePlaceBounds placeMemoryStoreEffect placeMemoryPrimitiveForward
  placeMemoryTypedPrimitive placeMemoryTypedForward valueCopy words

Theorem tuple_place_slack_not_implied:
  let b = dimword (:256) - 64; n = 32 in
    b + n < dimword (:256) /\ n + 64 < dimword (:256) /\
    ~(b + n + 64 < dimword (:256))
Proof simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

(* Destination +64 dependency trace, C1.3.4.3.7.1:

   tuple_place_memory_forward_frame (tuplePlaceMemoryFrame:13) passes the
   bound in its direct branch at :151 and staged branch at :229 to
   compile_store_memory_nonword_effect (placeMemoryStoreEffect:7).
   Staging allocates/copies the SOURCE; it does not improve destination slack.

   compile_store_memory_nonword_effect divides at :32-40:
   SAME TYPE -> compile_store_memory_same_type_forward (:46), whose only
     consuming call is compile_store_memory_run_capacity
     (placeMemoryPrimitiveForward:132).
     IMPORTANT: valueCopy also exports
       compile_store_memory_run_size_bound_with_capacity (:291),
     with IDENTICAL sequence/representation/variable/outside-byte/memory-growth
     outputs and only type_memory_size tv+64 < dimword.  This is an authorized
     inherited admission. The _capacity proof at valueCopy:427 and the
     size-only proof at :314 are both admitted in this checkout; do not invent
     an implementation argument from their hidden proofs. The size-only
     theorem itself IS an available weaker interface. straight_line_zero_gas_path
     and compile_store_memory_same_type_no_gas provide the same gas endpoint.
     Thus no lower-level strengthening is needed for a same-type replacement
     forward boundary: use the size-only admitted interface, then replay the
     short path/record lift. This covers equal fixed/dynamic/tuple/struct raw
     copies and equal bytestring copies; dynamic types at equal layout do NOT
     recurse into a dynamic loop in compile_store_memory.

   UNEQUAL BYTESTRING -> typed_memory_bytestring_forward
     (placeMemoryTypedPrimitive:81). Its bound is only forwarded at :116 to
     the same-type forward boundary after bytestring_val_in_memory_transfer
     and rewriting to compile_store_memory dty dty (:110-115). Thus the same
     size-only forward replacement removes destination slack here too.
     Underlying store_bytestring_run_exact (valueCopy:183) asks only the
     rounded copy LENGTH < dimword, never destination+length. Its proof is
     admitted, so no further proof inspection is possible/needed for use.

   UNEQUAL NONBYTESTRING -> typed_memory_child_forward_apply
     (placeMemoryChildForward:31), whose defining contract itself has +64.
     typed_memory_rank_forward (placeMemoryTypedForward:8) constructs it:
       word: typed_memory_word_forward has NO destination+64 premise;
       bytes: same-type interface as above;
       static fast array: typed_memory_sarray_fast_forward (:130 in
         placeMemoryTypedPrimitive) uses the bound ONLY to derive
         type_memory_size dtv < dimword at :167; compile_copy_memory_forward
         requires only copy length < dimword. Static widening equality is
         already proved by typed_memory_static_widening at :157-161.
       dynamic fast: typed_memory_dynarray_fast_forward
         (placeMemoryDynarrayForward:305) already requires only header-address
         no-wrap, capacity/count bounds, live-byte-count bound and separation;
         NO +64. Full source/destination ends plus size-only bounds can supply
         these numeric inputs, subject to evaluated-type facts.
       array slow: typed_memory_array_element_forward
         (placeMemoryArrayForward:27) needs +64 at :47; address no-wrap proof
         :67-73 uses only end bounds. The stronger margin is then passed into
         typed_memory_child_forward_apply at :77. Slow fixed (:351) and
         dynamic (:555) runners propagate it to that element boundary.
       tuple/struct: typed_memory_tuple_fields_forward
         (placeMemoryFieldsForward:286) carries +64 at :304, derives it for
         a child at :359 and applies typed_memory_child_forward_apply at :363.
         Address calculations :344-348 use only no-wrap. The struct adapter
         carries the same bound at :439.

   Weakest supported proposal for review (NOT implemented by this diagnostic):
   A task-local recursive child contract replacing destination+size+64 by
     destination+size < dimword AND size+64 < dimword
   should support current address calculations and primitive interfaces.
   Same-type and bytestring boundaries can instead use size+64 alone.
   To implement general widening, new leaf analogues are needed for:
     child predicate/apply and rank induction;
     same-type gas-path boundary and bytestring adapter;
     static-fast adapter (size-only arithmetic);
     array-element, slow fixed and slow dynamic runners;
     tuple-fields and struct-fields runners;
     nonword store effect; forwarding/staging wrapper and value-run wrapper.
   Dynamic-fast, word, copy-memory execution and control/layout interfaces
   already have compatible weaker bounds. Their aliases need not be duplicated.
   Source extent, newer-allocation provenance, and full frame endpoints remain
   separate obligations and are NOT discharged by this slack audit.

   No unsupported inference from tuple_place_memory_end_bound is used.
   In particular the checked arithmetic probe above rules out the tempting
   base+size bound inference; it says nothing about falsity of the frozen root.
*)
