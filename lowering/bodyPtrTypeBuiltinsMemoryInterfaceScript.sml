Theory bodyPtrTypeBuiltinsMemoryInterface
Ancestors exprLowering exprLoweringProps compileEnv
  bodyPtrDefs vyperAST vyperTypeSystem venomState

Theorem memory_convert_shapes:
  !src dst. is_bytestring_type src /\ is_bytestring_type dst ==>
  ?i n. (src = BaseT (BytesT (Dynamic i)) \/ src = BaseT (StringT i)) /\
    (dst = BaseT (BytesT (Dynamic n)) \/ dst = BaseT (StringT n)) /\
    mk_convert_op src dst = ConvBytestringCast n i
Proof
  rpt strip_tac >>
  Cases_on `src` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bs)` >> Cases_on `bs` >>
  gvs[is_bytestring_type_def] >>
  TRY (rename1 `is_bytestring_type (BaseT (BytesT bd))` >>
       Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
  Cases_on `dst` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def] >>
  TRY (rename1 `is_bytestring_type (BaseT (BytesT bd))` >>
       Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
  simp[mk_convert_op_def, is_bytestring_type_def]
QED

Theorem convert_outer_lowered_type:
  lowered_value_type cenv (TypeBuiltin ann Convert dst [e]) = ann
Proof
  simp[lowered_value_type_def, expr_type_def]
QED

Theorem convert_outer_buffer_restrict:
  ptr_buf_ok cenv e op G s /\
  type_memory_bytes cenv dst <= type_memory_bytes cenv (lowered_value_type cenv e) ==>
  ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) op G s
Proof
  simp[ptr_buf_ok_def, convert_outer_lowered_type] >>
  rpt strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem memory_convert_dispatch:
  is_bytestring_type (expr_type e) /\ is_bytestring_type dst /\
  ~is_word_type dst /\ lower_value cfn cenv (expr_type e) e sa = (x,s1) ==>
  compile_type_builtin_dispatch_body cfn cenv ann ty Convert dst [e] sa =
    if type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv dst
    then as_stack_val ann (compile_bytestring_widen_copy
      (type_memory_bytes cenv dst) x (type_memory_bytes cenv (lowered_value_type cenv e)) s1)
    else as_stack_val ann (compile_type_convert x (mk_convert_op (expr_type e) dst) s1)
Proof
  strip_tac >> Cases_on `dst` >> fs[is_bytestring_type_def] >>
  simp[compile_type_builtin_dispatch_body_def]
QED

(* Interface audit (C1.C.B.4.4.1).
   Valid memory conversions are dynamic Bytes -> dynamic Bytes/String and
   String -> String/dynamic Bytes. Same-kind casts require destination bound
   strictly below annotation bound; cross-kind casts permit either order.
   memory_convert_shapes identifies the common ConvBytestringCast operation;
   memory_convert_dispatch records the real lowered-size split. In particular
   annotation narrowing may still select copy if an internal-call result has
   a smaller lowered capacity. convert_outer_lowered_type and
   convert_outer_buffer_restrict isolate the outer buffer obligation.

   Child context required by the eventual continuation:
     expr_post ... e ... v x t0; ptr_val_ok cx (expr_type e) v x G tn t0;
     ptr_buf_ok cenv e x G t0; ghost_inv ... t0; ghost_kept ... G tn;
     compiler PC/code placement, local_ptrs_reserved and saved-return liveness;
     supported program/type frame to identify the actual lowered layout.
   This yields a Var src, lookup, robust annotation representation, clean
   header, and lowered-size pointer coverage (HeaderLoad/SourceTyping/FrameProbe).
   Output is the usual scalar dispatcher success post PLUS ptr_buf_ok cenv
   (TypeBuiltin dst Convert dst [e]) op H ss. Failure post is expr_exit.

   CastSemantic.convert_cast_converted_counted_certificate assumes BOTH an
   actual OK run and semantic INL result. It returns a counted path, unchanged
   memory/taint, robust destination representation and original coverage.
   Its ghost_inv/ptr_covers are at raw t, whereas its path endpoint is PC-shifted;
   continuation assembly must transport to that endpoint and compose ghost_kept.
   Cast.convert_cast_abort_path also assumes an actual Abort run.

   WidenSemantic.widen_copy_converted_counted_certificate likewise assumes an
   actual OK run and semantic INL result. Additional inputs are function-id
   distinctness, capacity<dimword, val_wf, footprint<=lowered source size and
   source expr_val_at. Output coverage is destination-sized at the shifted PC;
   robust destination representation uses the same final memory.

   Missing reusable semantic boundaries (not supplied by these certificates):
   1. Cast actual-state success/abort and convert_result correspondence with
      read-only frame. S1 convert_cast_narrow_run/abort_run work at arbitrary
      states; success_frame assumes fresh_vars_wrt and needs replay or a raw
      frame proof. Their exprSimConvertBytes theory currently fails immutable
      ancestry name resolution (expr_body_pre_def/expr_sim_inv_def), so cannot
      be imported here. Use raw opcode boundary or a new necessary leaf.
   2. Widen actual-state successful allocation+copy execution and outer
      expr_post framing, plus semantic success from footprint<=lowered size.
      S1 convert_widen_copy_run is local and in that same unavailable theory;
      its source construction is literal_alloc_buffer_run + buffer_emit_mcopy_run
      + run_inst_seq_append. No erased path is sufficient for pointer safety.
   3. Packaging memory suffix post (including whole-buffer coverage) is not
      scalar_suffix_expr_post: allocation changes memory and ownership.
   No full continuation, run existence or falsehood is claimed by this audit. *)
