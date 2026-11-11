(* Relative guards share the scalar availability interface, including ASSERT
   failure; no source-validity or canonical-encoding premise is required. *)
Theory abiDecodePtrPrims
Ancestors
  abiDecoderRange bodyPtrBopScalarCompile
  abiEncoder emitHelper emitHelperProps exprLoweringProps compileEnv freshWrites
  list rich_list pred_set

Theorem abi_decode_range_scalar:
  compile_abi_decode_range_check src e hi st = ((),st') /\
  src IN A /\ e IN A /\ hi IN A /\
  (!x. x IN R ==> not_fresh_at st x) ==>
  ?B. bop_scalar_seq R A (emitted_insts st st') B
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `emit_op LT [e;src] st = (wrapped,c1)` >>
  rename1 `emit_op ISZERO [wrapped] c1 = (no_wrap,c2)` >>
  rename1 `emit_op GT [e;hi] c2 = (oob,c3)` >>
  rename1 `emit_op ISZERO [oob] c3 = (in_bounds,c4)` >>
  rename1 `emit_op AND [no_wrap;in_bounds] c4 = (ok,c5)` >>
  `!x. x IN R ==> not_fresh_at c1 x /\ not_fresh_at c2 x /\
     not_fresh_at c3 x /\ not_fresh_at c4 x /\ not_fresh_at c5 x` by
    (imp_res_tac emitted_insts_emit_op >> fs[not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `bop_scalar_seq R A (emitted_insts st c1) (wrapped INSERT A)` by
    (irule bop_scalar_seq_emit_op >>
     conj_tac >- (rpt strip_tac >> metis_tac[]) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `bop_scalar_seq R (wrapped INSERT A) (emitted_insts c1 c2)
     (no_wrap INSERT wrapped INSERT A)` by
    (irule bop_scalar_seq_emit_op >>
     conj_tac >- (rpt strip_tac >> metis_tac[]) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `bop_scalar_seq R (no_wrap INSERT wrapped INSERT A) (emitted_insts c2 c3)
     (oob INSERT no_wrap INSERT wrapped INSERT A)` by
    (irule bop_scalar_seq_emit_op >>
     conj_tac >- (rpt strip_tac >> metis_tac[]) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `bop_scalar_seq R (oob INSERT no_wrap INSERT wrapped INSERT A)
     (emitted_insts c3 c4)
     (in_bounds INSERT oob INSERT no_wrap INSERT wrapped INSERT A)` by
    (irule bop_scalar_seq_emit_op >>
     conj_tac >- (rpt strip_tac >> metis_tac[]) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `bop_scalar_seq R (in_bounds INSERT oob INSERT no_wrap INSERT wrapped INSERT A)
     (emitted_insts c4 c5)
     (ok INSERT in_bounds INSERT oob INSERT no_wrap INSERT wrapped INSERT A)` by
    (irule bop_scalar_seq_emit_op >>
     conj_tac >- (rpt strip_tac >> metis_tac[]) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `bop_scalar_seq R
     (ok INSERT in_bounds INSERT oob INSERT no_wrap INSERT wrapped INSERT A)
     (emitted_insts c5 st')
     (ok INSERT in_bounds INSERT oob INSERT no_wrap INSERT wrapped INSERT A)` by
    (irule bop_scalar_seq_emit_assert >> simp[] >> metis_tac[]) >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 c2 ++
     emitted_insts c2 c3 ++ emitted_insts c3 c4 ++
     emitted_insts c4 c5 ++ emitted_insts c5 st'` by
    (`emitted_insts st c2 = emitted_insts st c1 ++ emitted_insts c1 c2` by
       (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
     `emitted_insts st c3 = emitted_insts st c2 ++ emitted_insts c2 c3` by
       (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
     `emitted_insts st c4 = emitted_insts st c3 ++ emitted_insts c3 c4` by
       (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
     `emitted_insts st c5 = emitted_insts st c4 ++ emitted_insts c4 c5` by
       (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
     `emitted_insts st st' = emitted_insts st c5 ++ emitted_insts c5 st'` by
       (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
     asm_rewrite_tac[APPEND_ASSOC]) >>
  asm_rewrite_tac[] >>
  metis_tac[bop_scalar_seq_append]
QED
