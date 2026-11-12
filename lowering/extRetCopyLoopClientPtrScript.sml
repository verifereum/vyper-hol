(* This checks only the recursive child's interface: finish may name any
 * block/cursor, not necessarily the loop's body-entry block. It does not
 * establish the concrete instruction segments. *)
Theory extRetCopyLoopClientPtr
Ancestors extRetCopyCountedPtr venomState venomExecSemantics compileEnv arithmetic exprSimTypedAlloc

Theorem copy_path_ptr_loop_client:
  !count H B C I test ctr finish D lo ctx fn PG R.
    (!i G tn s. H i G tn s <=>
       s.vs_current_bb = test /\ s.vs_inst_idx = 0 /\
       lookup_var ctr s = SOME (n2w i) /\ ~s.vs_halted /\ I i G tn s) /\
    (!i G tn s. C i G tn s ==>
       s.vs_current_bb = (finish i).cs_current_bb /\
       s.vs_inst_idx = LENGTH (finish i).cs_current_insts) /\
    (!i. i < count ==>
       copy_path_ptr D lo ctx fn PG (H i) (B i) R /\
       copy_path_ptr D lo ctx fn PG (B i) (C i) R /\
       copy_path_ptr D lo ctx fn PG (C i) (H (SUC i)) R) ==>
    copy_path_ptr D lo ctx fn PG (H 0) (H count) R
Proof
  rpt gen_tac >> strip_tac >>
  irule copy_path_ptr_iterate >> simp[] >> rpt strip_tac >>
  irule copy_path_ptr_then >> qexists_tac `B i` >> conj_tac
  >- metis_tac[] >>
  irule copy_path_ptr_then >> qexists_tac `C i` >> metis_tac[]
QED

(* CONTRACT AUDIT (design output, NOT asserted as a theorem).
 *
 * Compiler-aligned induction: compile_store_memory_typed_ind has five
 * predicates and eight cases; exprOpenCopies$compile_store_memory_typed_open_family
 * lines 71-104 demonstrates its exact binder order. The measure in
 * contextScript.sml:812-822 is 3*type_rank of the DESTINATION at dispatch,
 * and 3*rank+1 at array helpers, or 3*SUM ranks+1 at field helpers.
 * Source type, capacity, operand and compilation state are not measures.
 *
 * Branch / child / preservation obligation:
 * - dispatch: word MLOAD/MSTORE; bytes compile_store_bytestring;
 *   acyclic complex dispatch to arrays/fields/struct; otherwise INVALID;
 *   unmatched constructors use compile_copy_memory of destination size.
 *   Valid widening must exclude mismatched-layout fallbacks, not assume
 *   arbitrary source/destination types yield a represented result.
 * - fields nil or source nil: no code. The latter requires equal lengths
 *   from widening to avoid silently accepting a truncated copy.
 * - fields cons: offsets via compile_with_byte_offset, child at dst_ty/src_ty,
 *   then tail at dst_off+dst_sz/src_off+src_sz. Tail writes must frame each
 *   previously established field's val_footprint. Robust assembly is
 *   extRetAggregateRobustPtr$tuple_in_memory_robust_from_elements.
 * - fixed array: same element size and non-ABI-dynamic destination gives
 *   one batch MCOPY; otherwise finite loop with child at element types.
 *   Fixed lengths agree by typedCopyPtr$type_widens_to_fixed_array_length.
 *   Guard count and products/offsets must fit words. Zero-size children
 *   still require loop termination/counter bounds, not byte cleanliness.
 * - dynamic array: MLOAD length; ASSERT length <= dst capacity; MSTORE header;
 *   add 32 to each pointer. Equal element types/sizes give dynamic MCOPY;
 *   otherwise finite loop on runtime length. Header must be robustly clean;
 *   child writes cannot destroy header or source. Capacity ordering comes
 *   from typedCopyPtr$type_widens_to_dynamic_array_capacity.
 * - struct nil: no code. Struct cons: lookup source field by name, defaulting
 *   to destination type/size if absent, then child and tail. Valid widening,
 *   field-name correspondence and numeric sizes must justify this lookup;
 *   arbitrary acyclic metadata alone is insufficient.
 *
 * Loop locations: typedCopyLoopLayoutPtr$compile_copy_sarray_typed_loop_layout
 * gives child start si and end se independently; tail backedge is emitted at
 * se.cs_current_bb after se.cs_current_insts, NOT at the original body entry.
 * typed_copy_loop_slice_locations requires test::entry::sa.cs_blocks at si,
 * back::se.cs_blocks at sz, matching labels/prefixes and fn_has_code sa sz.
 * It yields fn_has_code si se and lookup of test/entry/back. The checked
 * client above composes abstract header, child, backedge without identifying
 * child end with body entry. It proves no concrete instruction safety.
 *
 * Proposed sufficient recursive CP signature (schematic free variables are
 * implicitly universally quantified; this is text, not an admission):
 *
 * compile_store_memory_typed ce (Var dst) dty (Var src) sty sa = ((),sb) /\
 * fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
 * acyclic_struct_metadata ce.ce_struct_fields /\
 * sfields_tenv_consistent ce.ce_struct_fields tenv /\
 * (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
 *   ALL_DISTINCT (MAP FST fields) /\
 *   EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
 *     sz = type_memory_size tv) fields) /\
 * type_widens_to tenv sty dty /\
 * evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
 * value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
 * not_fresh_at sa src /\ not_fresh_at sa dst /\
 * lookup_var src s = SOME sw /\ lookup_var dst s = SOME dw /\
 * ptr_covers G tn src s (type_memory_size stv) /\
 * ptr_covers G tn dst s (type_memory_size dtv) /\
 * w2n sw + type_memory_size stv < dimword (:256) /\
 * w2n dw + type_memory_size dtv < dimword (:256) /\
 * (w2n sw + type_memory_size stv <= w2n dw \/
 *  w2n dw + type_memory_size dtv <= w2n sw) /\
 * (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
 *      val_in_memory stv v (w2n sw) m)
 * ==>
 * copy_path_ptr D lo ctx fn PG
 *   (\g t u. g=G /\ t=tn /\ u=s /\ ~u.vs_halted /\
 *      u.vs_current_bb=sa.cs_current_bb /\
 *      u.vs_inst_idx=LENGTH sa.cs_current_insts)
 *   (\g t u. u.vs_current_bb=sb.cs_current_bb /\
 *      u.vs_inst_idx=LENGTH sb.cs_current_insts /\
 *      (!m. mem_agree_outside t.t_mem u.vs_memory m ==>
 *           val_in_memory dtv v (w2n dw) m) /\
 *      copy_static u=copy_static s /\
 *      (!x. not_fresh_at sa x ==>
 *        lookup_var x u=lookup_var x s /\ FLOOKUP g x=FLOOKUP G x /\
 *        op_taint t (Var x)=op_taint tn (Var x)) /\
 *      (!i. i < w2n dw \/ w2n dw+type_memory_size dtv <= i ==>
 *        mem_bytes_at i 1 u.vs_memory=mem_bytes_at i 1 s.vs_memory /\
 *        (i IN t.t_mem <=> i IN tn.t_mem)) /\
 *      t.t_stor=tn.t_stor /\ t.t_trans=tn.t_trans /\ t.t_imm=tn.t_imm)
 *   (\gt r. F)
 *
 * The no-exit post requires showing ASSERT succeeds from value typing and
 * capacity widening. A version admitting justified exits must specify R;
 * arbitrary R cannot be used to hide failed safety checks.
 *
 * Normalization specialization: replace the compilation equation above by
 * compile_alloc_buffer (type_memory_bytes ce ty) sa=(buf,sm) /\
 * compile_store_memory_typed ce buf.buf_operand ty val_op sty sm=((),sb),
 * use dty=ty and introduce dst,dw,G1,tn1 after allocation. Its CP pre is
 * ghost_inv NONE ce cx es G tn s /\ ptr_val_ok cx sty v val_op G tn s /\
 * stmt_state_rel ctx fn ce cx es s with the entry cursor; its normal post
 * must include ghost_inv NONE ce cx es g t u /\
 * ptr_val_ok cx ty v buf.buf_operand g t u /\ the sb cursor, plus preserved
 * old variables and ghost facts. S1 compile_return_normalize_frag:331-369
 * lists additional type, layout, range, freshness and source-location inputs.
 * They are proof obligations, NOT available merely from this precondition.
 *
 * Premise provenance / unresolved interface:
 * - typing: typed_return_normalization_inputs gives arg_type_fits and
 *   well_formed_type, NOT assignable_type. No assignable premise is used in
 *   the proposed copy signature. If a backend helper requires it, prove it
 *   for the concrete call; supported empty structs are not assignable.
 * - evaluated destination/value: typed_return_normalization_layout gives
 *   evaluated type, typing at destination, default equality and footprint
 *   bounds; it does not give allocation bounds or padding cleanliness.
 * - robust source: ptr_val_ok/ptr_mem_ok supplies arbitrary-memory robustness
 *   and val_store_size coverage when footprint is nonzero. It does NOT
 *   supply full type_memory_size coverage or any strict dimword bound.
 * - placement: expr_post -> expr_val_at offers an allocation/local containing
 *   val_footprint, or a zero-footprint disjunct. It does NOT immediately imply
 *   the full-size source-location premise of the S1 normalization theorem.
 * - ptr_buf_ok gives whole LOWERED type coverage, conditional on nonzero size;
 *   compatibility with source expr_type and strict address bound still needs
 *   a lemma. Allocation well-formedness/local bounds must supply no-wrap.
 * - fresh destination/disjointness: S1 allocation facts supply ranges; counted
 *   allocation and ghost provenance are additional required interfaces.
 * - ambient ghost: exterior frame needs disjointness from local value
 *   footprints, memory and taint unchanged outside writes, and old-variable
 *   provenance/taint preservation. Allocation names alone do not suffice.
 *
 * CHECKPOINT: full-type coverage/no-wrap at source is unresolved. Do not
 * begin recursive implementation assuming the sufficient signature above
 * is dischargeable. Ask strategist to choose a read-window/footprint contract
 * or prove the missing source-context boundary, and retain all recursive
 * implementation/allocation/normalization obligations under C1.4.4.
 *)
