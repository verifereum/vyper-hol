(* Protected-tail persistence is syntactic output exclusion, not counter
   monotonicity. These boundaries do not assert a whole compiler invariant. *)
Theory bodyPtrBytestringBuiltinsImageProtectedIdentity
Ancestors bodyPtrBytestringBuiltinsImageTupleHistory
          bodyPtrBytestringBuiltinsAllocationOrigins compileEnv emitHelper
          venomInst list rich_list context

Theorem tail_alloc_excluded:
  EVERY (\inst. !i w v. b = Var v ==>
    inst <> mk_inst i ALLOCA [Lit w] [v]) added ==>
  ~tail_alloc b added
Proof
  strip_tac >> simp[tail_alloc_def] >> rpt strip_tac >>
  gvs[EVERY_APPEND] >> metis_tac[]
QED

Theorem tail_alloc_frame:
  EVERY (\inst. !i w v. b = Var v ==>
    inst <> mk_inst i ALLOCA [Lit w] [v]) added /\
  tail_alloc b (xs ++ added) ==> tail_alloc b xs
Proof
  Cases_on `added = []` >- simp[] >>
  `?ys inst. added = ys ++ [inst]` by metis_tac[SNOC_CASES, SNOC_APPEND] >>
  gvs[EVERY_APPEND, APPEND_ASSOC, tail_alloc_append] >> metis_tac[]
QED

Theorem tail_alloc_new_block:
  new_block lbl st = (old,t) ==> ~tail_alloc b t.cs_current_insts
Proof
  simp[new_block_def] >> rpt strip_tac >> gvs[tail_alloc_def]
QED

Theorem tail_alloc_fresh_alloca:
  saved <> STRING #"%" (toString st.cs_next_var) /\
  emit_op ALLOCA [Lit w] st = (op,t) ==>
  ~tail_alloc (Var saved) t.cs_current_insts
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >>
  gvs[tail_alloc_other]
QED

Theorem tail_alloc_alloc_buffer:
  saved <> STRING #"%" (toString st.cs_next_var) /\
  compile_alloc_buffer n st = (buf,t) ==>
  ~tail_alloc (Var saved) t.cs_current_insts
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[tail_alloc_fresh_alloca]
QED

Theorem tail_alloc_producer_frame:
  (u.cs_current_insts = st.cs_current_insts ++ added \/
   u.cs_current_insts = added) /\
  EVERY (\inst. !i w v. b = Var v ==>
    inst <> mk_inst i ALLOCA [Lit w] [v]) added ==>
  (tail_alloc b u.cs_current_insts ==> tail_alloc b st.cs_current_insts)
Proof
  metis_tac[tail_alloc_frame, tail_alloc_excluded]
QED

(* Source audit (not a compiler-preservation assertion):
   - compile_builtin_dispatch MakeArray NONE first calls compile_alloc_buffer,
     then compile_make_tuple compile_expr with offset 0 (exprLowering:3286-3294).
     The protected buffer is that fresh result; callbacks start after allocation.
   - emit appends; new_block finalizes the current block and resets to [], even
     for an existing label (compileEnv:641-655). These primitives never reopen
     or copy a saved instruction list into the current list.
   - compile_expr_ci_mono (exprLoweringProps:4549) gives cs_extends plus monotone
     variable/id counters. cs_extends (compileEnv:690) constrains an old prefix
     in the same block, or the oldest newly finalized block after a switch.
     It does NOT constrain outputs of new ALLOCAs or the new current list.
   - AllocationOrigins provides interval composition and primitive emit origins,
     but no compile_expr alloca_output_interval theorem. Thus the missing source
     contract is: new current-list allocations are fresh relative to callback
     entry, and current instructions are old-current ++ added or reset-added.
     Combining that with the saved buffer being old would discharge the EVERY
     premise above. Neither condition follows from ci_mono alone. Memory-place
     unwrap and lower_value need the same allocation-output contract; no full
     mutual compiler proof or tuple-copy closure is claimed here. *)
