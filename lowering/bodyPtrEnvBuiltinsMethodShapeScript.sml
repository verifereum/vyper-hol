(* Typed selectors have exactly four payload bytes. *)
Theory bodyPtrEnvBuiltinsMethodShape
Ancestors
  bodyPtrEnvBuiltinsBoundary exprSimHypsDefs vyperTypeSystem
  exprLowering compileEnv vyperAST list keccak vyperTypeBytesCrypto

Theorem method_id_builtin_pre_shape:
  !cenv cx env ann args es.
    expr_body_pre cenv cx env (Builtin ann MethodId args) es ==>
    LENGTH args = 1 /\
    (ann = BaseT (BytesT (Dynamic 4)) \/ ann = BaseT (BytesT (Fixed 4)))
Proof
  rpt gen_tac >> simp[expr_body_pre_def, well_typed_expr_def,
    well_typed_builtin_app_def] >> metis_tac[]
QED

Theorem method_id_digest_length:
  !bs. LENGTH (TAKE 4 (Keccak_256_w64 bs)) = 4
Proof
  simp[LENGTH_TAKE, LENGTH_Keccak_256_w64]
QED

Theorem method_id_folded_allocation_size:
  !bs. 32 + ((LENGTH (TAKE 4 (Keccak_256_w64 bs)) + 31) DIV 32) * 32 = 64
Proof
  simp[method_id_digest_length]
QED

Theorem method_id_folded_allocation_capacity:
  !cenv args bs.
    type_memory_bytes cenv
      (lowered_value_type cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args)) =
    32 + ((LENGTH (TAKE 4 (Keccak_256_w64 bs)) + 31) DIV 32) * 32
Proof
  simp[method_id_dynamic_result_capacity, method_id_folded_allocation_size]
QED
