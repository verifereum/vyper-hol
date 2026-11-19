(* Relative guards share the scalar availability interface, including ASSERT
   failure; no source-validity or canonical-encoding premise is required. *)
Theory abiDecodePtrPrims
Ancestors
  loweringStateRelDefs
  abiDecoderRange bodyPtrBopScalarCompile
  abiEncoder emitHelper emitHelperProps exprLoweringProps compileEnv freshWrites
  list rich_list pred_set venomInst arithmetic
  abiDecoderComplexHead bodyPtrBopScalarSeq

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

Theorem abi_decode_complex_bounded_split:
  hi <> Lit 0w /\
  compile_abi_decode_to_buf dst pos opc src hi (DecComplex dyn infos) sa = ((),last) ==>
  ?e sm sb.
    emit_op ADD [pos;Lit (n2w (FOLDR (\(_,asz:num,_:num) acc. asz+acc) 0 infos))]
      sa = (e,sm) /\
    compile_abi_decode_range_check pos e hi sm = ((),sb) /\
    compile_abi_decode_complex_elems dst pos opc src hi infos 0 0 sb = ((),last)
Proof
  strip_tac >>
  gvs[Once compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  ` (\(_:abi_dec_info,asz:num,_:num) acc. acc + asz) =
    (\(_:abi_dec_info,asz:num,_:num) acc. asz + acc)` by
    (simp[FUN_EQ_THM, pairTheory.FORALL_PROD, ADD_COMM]) >>
  pop_assum (fn th => pure_rewrite_tac[th]) >> metis_tac[]
QED

Theorem abi_decode_complex_header_shape:
  emit_op ADD [pos;Lit (n2w static_sz)] sa = (e,sm) /\
  compile_abi_decode_range_check pos e hi sm = ((),sb) ==>
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. (fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
    EVERY (not_fresh_at sb) i.inst_outputs) (emitted_insts sa sb)
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_return_def] >>
  strip_tac >> gvs[] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, fresh_write_op_def,
       not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem abi_decode_complex_header_scalar:
  emit_op ADD [pos;Lit (n2w static_sz)] sa = (e,sm) /\
  compile_abi_decode_range_check pos e hi sm = ((),sb) /\
  pos IN A /\ hi IN A /\ Lit (n2w static_sz) IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B
Proof
  strip_tac >>
  `bop_scalar_seq R A (emitted_insts sa sm) (e INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[pos;Lit (n2w static_sz)]`] >> simp[]) >>
  `!x. x IN R ==> not_fresh_at sm x` by
    (drule emitted_insts_emit_op >> strip_tac >> fs[not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `?B. bop_scalar_seq R (e INSERT A) (emitted_insts sm sb) B` by
    (irule abi_decode_range_scalar >> simp[] >> metis_tac[]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >>
     drule compile_abi_decode_range_check_shape >>
     drule inst_extends_emit_op >> simp[inst_extends_def]) >>
  qexists_tac `B` >> simp[] >> irule bop_scalar_seq_append >>
  qexists_tac `e INSERT A` >> simp[]
QED

Theorem abi_decode_complex_guard_scalar:
  abi_decode_complex_head_guard pos hi n sa = ((),sb) /\
  pos IN A /\ hi IN A /\ (!w. Lit w IN A) /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B
Proof
  Cases_on `hi = Lit 0w`
  >- (simp[abi_decode_complex_head_guard_def, comp_return_def] >>
      rpt strip_tac >> gvs[emitted_insts_def, DROP_LENGTH_NIL] >>
      qexists_tac `A` >> simp[]) >>
  simp[abi_decode_complex_head_guard_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any mp_tac abi_decode_complex_header_scalar) >>
  disch_then drule >> simp[]
QED
