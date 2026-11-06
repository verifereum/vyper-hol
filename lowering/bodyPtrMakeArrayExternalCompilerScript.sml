(* Finite compiler seams.  No runtime-mode assumption is hidden here. *)
Theory bodyPtrMakeArrayExternalCompiler
Ancestors
  bodyPtrMakeArrayExternalAggregateProbe loweringPosts exprLowering context compileEnv

Theorem unwrap_external_calldata_excluded:
  vv_post ctx func ce cx e es sa sb s0 es' raw (LocatedValue t p) s ==>
  p.ptr_location <> LocCalldata
Proof
  Cases_on `p.ptr_location` >> simp[vv_post_def, vv_holds_def]
QED

Theorem unwrap_storage_aggregate_split:
  unwrap_value ce (LocatedValue t p) sa = (op,sb) /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  ~is_word_type t ==>
  ?buf sm.
    compile_alloc_buffer (type_memory_bytes ce t) sa = (buf,sm) /\
    (if (type_memory_bytes ce t + 31) DIV 32 = 1 then
       ?loaded sl.
         emit_op (if tr then TLOAD else SLOAD) [p.ptr_operand] sm = (loaded,sl) /\
         emit_void MSTORE [buf.buf_operand; loaded] sl = ((),sb)
     else
       ?exit. compile_word_copy_loop p.ptr_operand buf.buf_operand
         ((type_memory_bytes ce t + 31) DIV 32)
         (if tr then LocTransient else LocStorage) LocMemory F sm = (exit,sb)) /\
    op = buf.buf_operand
Proof
  Cases_on `tr` >> strip_tac >>
  gvs[unwrap_value_def, compile_ensure_in_memory_def,
      compile_storage_to_memory_def, compile_transient_to_memory_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `(type_memory_bytes ce t + 31) DIV 32 = 1` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem unwrap_code_aggregate_split:
  unwrap_value ce (LocatedValue t p) sa = (op,sb) /\
  p.ptr_location = LocCode /\ ~is_word_type t ==>
  ?buf sm.
    compile_alloc_buffer (type_memory_bytes ce t) sa = (buf,sm) /\
    compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca p.ptr_operand
      buf.buf_operand ((type_memory_bytes ce t + 31) DIV 32) 0 sm = ((),sb) /\
    op = buf.buf_operand
Proof
  strip_tac >>
  gvs[unwrap_value_def, compile_ensure_in_memory_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

(* Caller-to-unwrap audit (C1.4.3.1).
   - Runtime mode: expr_vv_sim_ptr_def has ~ce.ce_is_ctor in its INPUT
     frame, as does the value simulation. body_inv alone does NOT imply
     it: body_inv_def equates ce_is_ctor with cx.in_deploy. Thus this
     exclusion is valid inside the pointer judgment, not from S1 vv_post.
   - Calldata: vv_post -> vv_holds excludes it, checked above. Located
     result type equals expr_type e by the same vv_holds equation.
   - Size: unwrap_value_materialise_sim takes the evaluated size identity
     explicitly; aggregate_unwrap_store_slice_sim also takes it explicitly.
     slot_count_of_memory_size (exprSimFieldLayout) supplies rounded slots
     AFTER that identity, not from an arbitrary compiler type alone.
     Widened StackValue results must not be identified with this located
     result equation; their store adapter remains a separate obligation.
   - Old source operand: copy_old_operand_def is exactly the universally
     quantified Var/not_fresh_at condition in the S1 materialise contract.
     Carry it through the intervening destination ADD using compiler
     freshness monotonicity; cleanliness additionally comes from ptr_vv_ok.
   - Installation: fn_has_code_split/mid restrict enclosing installation
     once cs_extends is known; unwrap_value_extends supplies the outer
     extension. emitted_insts_append requires BOTH current-instruction
     prefix equations. It does not assert same-block code for a CFG loop.
   - Storage/transient: the checked split uses the actual rounded memory
     count (including zero), NOT an unproved slot identity. The loop
     returns an exit LABEL (string), not unit. Its final cursor is the
     final compiler block, so the runtime straight-line endpoint formula
     SUC start_idx + LENGTH emitted_copy cannot be reused for this branch.
   Remaining integration bridges: derive evaluated size at the actual
   lowered child type; derive each subfragment's cs_extends and concrete
   installed prefix for allocation/runtime copy; transport old operands
   through ADD; construct the storage loop exit-block execution witness.
   The present finite splits certify none of the semantic/ghost endpoint.
*)
