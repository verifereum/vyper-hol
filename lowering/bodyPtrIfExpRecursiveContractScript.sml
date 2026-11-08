Theory bodyPtrIfExpRecursiveContract
Ancestors
  bodyPtrDefs typedCopyLayoutPtr typedCopyTuplePtr structChildPtr
  valueEncoding valueTypingMemoryProps context compileEnv

(* Diagnostic only: annotation-level interpretation does not provide the
   typed compiler's independent physical source offsets. Even widening
   bytes bounds keeps the logical value while moving a later tuple field.
   This is not a counterexample to a reachable expression frame. *)
Theorem tuple_source_offset_contract_probe:
  value_has_type
    (TupleTV [BaseTV (BytesT (Dynamic 64)); BaseTV (UintT 256)])
    (ArrayV (TupleV [BytesV []; IntV 42])) /\
  value_has_type
    (TupleTV [BaseTV (BytesT (Dynamic 32)); BaseTV (UintT 256)])
    (ArrayV (TupleV [BytesV []; IntV 42])) /\
  val_in_memory
    (TupleTV [BaseTV (BytesT (Dynamic 64)); BaseTV (UintT 256)])
    (ArrayV (TupleV [BytesV []; IntV 42])) 0
    (REPLICATE 127 (0w:word8) ++ [42w]) /\
  ~val_in_memory (BaseTV (UintT 256)) (IntV 42) 64
    (REPLICATE 127 (0w:word8) ++ [42w])
Proof
  EVAL_TAC >> simp[wordsTheory.word_0_n2w,
    wordsTheory.dimword_def, wordsTheory.dimindex_8] >> EVAL_TAC
QED

(* RECURSIVE STORE CONTRACT AUDIT (proposals, not admitted theorems).

   All five compiler functions in contextScript.sml:671-808 require a
   physical source representation premise. The checked diagnostic above
   refutes deriving even one nontrivial child from double typing and
   annotation memory: source tuple bytes32/uint has offset64, annotation
   tuple bytes64/uint has offset96. The latter stores int42 at byte127,
   whereas the former reads bytes64..95 (all zero). No compiler reachability
   or body_expr_ptr_ok counterexample is claimed.

   Shared proposed normal contract, instantiated separately at each mutual
   compiler equation F sa = ((),sb):

   F sa = ((),sb) /\ fn_has_code sa sb fn /\
   ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
   s.vs_current_bb = sa.cs_current_bb /\
   s.vs_inst_idx = LENGTH sa.cs_current_insts /\
   eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
   ptr_covers G tn sp s ns /\ ptr_covers G tn dp s nd /\
   src = Var sp /\ dst = Var dp /\
   w2n a + ns < dimword(:256) /\ w2n b + nd < dimword(:256) /\
   (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory stv v (w2n a) m) ==>
   ?Gf tnf sf.
     gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
     (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
          val_in_memory dtv v (w2n b) m) /\
     (!p. p < sa.cs_next_var ==>
       lookup_var p sf = lookup_var p s /\
       FLOOKUP Gf p = FLOOKUP G p /\
       (p IN tnf.t_var <=> p IN tn.t_var)) /\
     tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
     (!i. ~(w2n b <= i /\ i < w2n b+nd) ==>
       mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
       (i IN tnf.t_mem <=> i IN tn.t_mem))

   This schema is NOT yet sufficient: semantic type compatibility,
   metadata validity, disjointness and source/destination capacity must be
   caller-derived premises, and sf must be the exact compiler continuation
   position (including new blocks), not an arbitrary endpoint. Exceptions
   need a separate gas_outcome_ptr post agreeing with source evaluation;
   safe INVALID/ASSERT aborts alone are not that post.

   Instantiations and child-premise table:
   - compile_store_memory_typed: stv must evaluate src_ty, dtv dst_ty;
     ns/nd bound physical sizes. Current ptr_val_ok supplies interpretation
     at expr_type e, not src_ty=lowered_value_type cenv e. ptr_buf_ok supplies
     capacity only. Neither source typing nor capacity repairs the mismatch.
   - compile_typed_copy_fields: start at dst_off/src_off; for child i use
     respective offsets plus SUM of respective preceding type_memory_bytes.
     Equal list lengths and values_have_types on BOTH evaluated lists are
     needed for a full destination post. The [] source branch returns
     without storing remaining destination fields. Existing
     tuple_in_memory_robust_element supplies the child ONLY from robust
     tuple memory at the physical source evaluated list; the probe shows
     exactly why annotation tuple memory cannot substitute. Use existing
     tuple_child_footprint_contained for child access, not a new projection.
   - compile_struct_typed_copy: source offset advances by ALOOKUP-selected
     source size in DESTINATION field order, not by a fresh name search's
     positional offset. fields_in_memory_robust_metadata_element requires
     ordered names, list lengths and metadata size equalities. Those must
     identify this accumulated source offset with the physical prefix.
     Missing ALOOKUP uses destination type/size by default; no source value
     premise follows from that default. Reordered/missing fields need a
     reachability exclusion or a different post, not an assumed alignment.
   - compile_copy_sarray_typed: stv=ArrayTV sv (Fixed n),
     dtv=ArrayTV dv (Fixed n). Child at i uses sparse lookup/default value
     and source stride type_memory_size sv. The existing robust projection
     sarray_in_memory_robust_element requires physical sv memory; annotation
     element memory at a different stride does not supply it. Coverage uses
     array_child_footprint_contained plus physical whole-buffer coverage.
     The fast copy guard is equal sizes and non-ABI-dynamic DESTINATION,
     not semantic element equality: equal sizes alone cannot justify a
     destination reinterpretation, so a compatible-encoding fact is needed.
   - compile_copy_dynarray_typed: stv=ArrayTV sv (Dynamic sc),
     dtv=ArrayTV dv (Dynamic dc), LENGTH vs<=dc. Header load uses existing
     dynarray_in_memory_robust_length; source element i is at a+32+i*ss.
     dynarray_in_memory_robust_element requires physical sv representation,
     not just annotation representation. Header write follows capacity
     ASSERT, so capacity failure must match a source failure or be excluded.
     Fast path requires equal element types and sizes and copies live length
     only. Destination full buffer coverage comes from allocation separately.

   Runtime-loop invariant, separate from compiler destination-rank induction:
   At cond_lbl, counter=i, 0<=i<=n (n=count or LENGTH vs);
   source/destination base variables and dynamic length variable retain
   their entry values and provenance. Counter/length/arithmetic temporaries
   are untainted. For every j<i the destination has robust dv child v_j at
   b+h+j*ds; for every i<=j<n the source has robust sv child v_j at a+h+j*ss.
   h=0 fixed, h=32 dynamic; the dynamic destination header encodes n cleanly.
   Child source/destination pointers cover their windows; all base+offset
   and counter products are below dimword(:256), with exterior memory/taint
   and all sa-old registers/provenance preserved. Thread G_i,tn_i,s_i in
   gas_path_ptr to the EXACT cond block index0. A body iteration threads to
   cond block index0 with i+1; n-i decreases. At i=n the JNZ threads to exit
   block index0. Keep original-sa ghost_kept separate from this local cutoff.
   Existing footprint bounds discharge subwindows only AFTER the physical
   source representation and total size bound have been established.

   Conclusion: do not implement mutual recursion yet. The physical source
   interpretation/stride premise is unresolved at the actual arm caller.
   A reachability theorem about lowered_value_type and the operand judgment
   (or a reachable counterexample) is needed before these contracts can be
   promoted to implementation components. This audit does not weaken the
   frozen target and adds no definitions or duplicate projection lemmas.
*)
