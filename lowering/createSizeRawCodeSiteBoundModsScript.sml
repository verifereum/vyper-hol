(* The raw CREATE snapshot allocates at the lowered type but copies at
   the original VV tag. For an immutable source these widths coincide. *)
Theory createSizeRawCodeSiteBoundMods
Ancestors
  createSizeRawCodeSiteBound createExprSizeExitDefsMods
  createBlueprintRawCopyLayoutMods exprPtrUnwrapStorageShape exprPtrUnwrapCode
  exprPtrUnwrapAllocSeparation bufferAllocationExecution exprSimSource
  loweringPosts compileEnv context valueEncodingProps words arithmetic

Theorem create_raw_code_snapshot_site_bound_mods:
  expr_body_pre_mods mods ce cx env e es /\
  expr_type e = BaseT (BytesT (Dynamic k)) /\
  eval_expr cx e (es with gas_obs := obs) = (INL tv,p) /\
  read_result cx tv p = (INL (BytesV bytes),p) /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  vv_location vv = SOME LocCode /\
  vv_post_mods H ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
  compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a = (buf,sm) /\
  fn_has_code a sm func ==>
  w2n (n2w (buffer_allocation_base u a.cs_next_id) : bytes32) +
    32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) < dimword (:256)
Proof
  cheat
QED
