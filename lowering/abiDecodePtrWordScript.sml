(* Primitive decoder certificates do not assume that the input passes its clamp. *)
Theory abiDecodePtrWord
Ancestors
  abiEncoder abiDecodePtrRead abiDecodePtrMemberFrame
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq exprLoweringProps
  emitHelperProps compileEnv freshWrites list pred_set

Theorem abi_decode_clamp_scalar:
  compile_abi_clamp_basetype value clamp sa = ((),sb) /\ value IN A /\
  (!w. Lit w IN A) /\ (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B /\ A SUBSET B /\
      sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
      same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  Cases_on `clamp`
  >- (simp[compile_abi_clamp_basetype_def, comp_return_def] >> strip_tac >>
      gvs[] >> qexists_tac `A` >> simp[emitted_insts_def, same_blocks_def]) >>
  TRY (rename1 `IntClamp bits signed` >> Cases_on `signed`) >>
  (simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_ignore_bind_def] >> strip_tac >>
  drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. T`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!x. x IN R ==> not_fresh_at m x` by metis_tac[not_fresh_at_mono] >>
      `value IN B` by metis_tac[SUBSET_DEF] >>
      Cases_on `v` >> drule bop_scalar_compile_emit_checked >> simp[]) >> simp[])
QED
