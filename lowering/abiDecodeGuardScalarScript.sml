(* Scalar certificate for the ABI decoder's lower-bound assertion. *)
Theory abiDecodeGuardScalar
Ancestors
  abiDecoderGuard bodyPtrBopScalarCompile bodyPtrBopScalarSeq
  loweringStateRelDefs emitHelper emitHelperProps exprLoweringProps
  compileEnv list pred_set

Theorem abi_decode_ge_guard_scalar:
  abi_decode_ge_guard a b sa = ((),sb) /\ a IN A /\ b IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B
Proof
  simp[abi_decode_ge_guard_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `emit_op LT [a;b] sa = (underflow,c1)` >>
  rename1 `emit_op ISZERO [underflow] c1 = (ok,c2)` >>
  `bop_scalar_seq R A (emitted_insts sa c2)
     (ok INSERT underflow INSERT A)` by
    (irule bop_scalar_seq_emit_iszero >> simp[] >>
     qexistsl_tac [`c1`, `LT`, `[a;b]`] >> simp[]) >>
  `bop_scalar_seq R (ok INSERT underflow INSERT A)
     (emitted_insts c2 sb) (ok INSERT underflow INSERT A)` by
    (irule bop_scalar_seq_emit_assert >> simp[] >> metis_tac[]) >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `emitted_insts sa c2 = emitted_insts sa c1 ++ emitted_insts c1 c2` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa c2 ++ emitted_insts c2 sb` by
    (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
  asm_rewrite_tac[] >> metis_tac[bop_scalar_seq_append]
QED
