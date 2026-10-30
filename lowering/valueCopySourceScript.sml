(*
 * A memory copy bounded by its source's footprint as well as by its
 * destination's capacity.
 *
 * TOP-LEVEL:
 *   compile_store_memory_run_source_bound — the copy's run
 *)
Theory valueCopySource
Ancestors
  valueCopy valueCopyBytes valueTypingMemoryProps exprSim arithmetic

Theorem compile_store_memory_run_source_bound:
  !cenv src dst dty sty sa sb s tenv dtv stv v sw dw.
    compile_store_memory cenv src dst dty sty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv dty = SOME dtv /\
    evaluate_type tenv sty = SOME stv /\
    (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
    value_has_type dtv v /\ value_has_type stv v /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    (if is_word_type sty then sw = typed_val_to_w256 stv v
     else val_in_memory stv v (w2n sw) s.vs_memory) /\
    type_memory_size dtv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/
         w2n dw + MIN (type_memory_size stv) (type_memory_size dtv) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac
  >- (gvs[] >>
      `val_wf dtv v` by metis_tac[value_has_type_memory_wf] >>
      drule_all compile_store_memory_run_size_bound >> simp[]) >>
  `~is_word_type sty /\ ~is_word_type dty` by
    metis_tac[is_bytestring_word_type] >>
  `val_in_memory dtv v (w2n sw) s.vs_memory` by
    (fs[] >> metis_tac[bytestring_val_in_memory_transfer]) >>
  `val_footprint dtv v = val_footprint stv v` by
    metis_tac[bytestring_val_footprint_eq] >>
  `val_footprint dtv v <= MIN (type_memory_size stv) (type_memory_size dtv)` by
    (simp[MIN_DEF] >> metis_tac[val_footprint_le, value_has_type_memory_wf]) >>
  irule compile_store_memory_run_frame >> simp[value_has_type_memory_wf] >>
  qexistsl_tac [`cenv`, `dst`, `src`, `sw`, `tenv`, `dty`] >>
  simp[value_has_type_memory_wf] >>
  metis_tac[compile_store_memory_bytestring_src]
QED
