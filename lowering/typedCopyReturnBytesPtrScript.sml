(* Counted bytestring copies, with frames on the counted endpoint. *)
Theory typedCopyReturnBytesPtr
Ancestors
  bodyPtrIfExpBytesPost bodyPtrTypeBuiltinsMemoryPlacement
  exprLoweringProps context compileEnv emitHelper fragExec
  typedMemoryCopy valueEncodingProps placeMemoryTypedPrimitive
  exprSimBufferStore venomState arithmetic list

Theorem store_bytestring_placement[local]:
  compile_store_bytestring src dst sa = ((),sb) /\ fn_has_code sa sb fn ==>
  sa.cs_current_bb = sb.cs_current_bb /\
  LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)
Proof
  strip_tac >> irule straight_line_suffix_placement >> simp[] >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
       comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
      comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
      comp_return_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
  strip_tac >> gvs[] >> simp[GSYM APPEND_ASSOC]
QED

Theorem store_bytestring_counted:
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  fn_has_code sa sb fn /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  n = 32 + 32 * ((len+31) DIV 32) /\
  len+31 < dimword(:256) /\ n < dimword(:256) /\ n <= cap /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n a) m) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    typed_copy_state_frame sa (w2n b) cap s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
         val_in_memory dtv v (w2n b) m) /\
    (!i. i < w2n b \/ w2n b+cap <= i ==>
       mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
       (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all store_bytestring_placement >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by gvs[] >>
  drule_all compile_store_bytestring_robust_gas_path_ptr >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tnf`,`sf with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  conj_tac >- gvs[] >>
  `sf.vs_current_bb = s.vs_current_bb /\ ~sf.vs_halted` by
    fs[venom_state_component_equality] >>
  simp[] >> conj_tac >-
    (simp[typed_copy_state_frame_def] >> conj_tac >-
       fs[venom_state_component_equality] >>
     conj_tac >- (simp[lookup_var_def] >> fs[lookup_var_def]) >>
     simp[typed_copy_frame_def] >> conj_tac >-
       (rpt strip_tac >> simp[mcopy_mem_bytes_at_disjoint] >>
        irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
     simp[mcopy_memory_length]) >>
  conj_tac >-
    (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[lookup_var_def] >> fs[lookup_var_def]
QED
