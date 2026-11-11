(* Concrete runtime continuation for self.code: semantic runs are proved
   separately from checked pointer sequences. *)
Theory bodyPtrCodeSliceSelfContinue
Ancestors
  bodyPtrCodeSliceSelfPrefix bodyPtrCodeSliceSelfSuffix
  exprSimSliceBounds exprSimCalldataSlice exprSimSliceSource
  fragGasSeqPtr gasSummaryComposePtr exprSimSliceExtcode
  emitHelperProps loweringShapeDefs venomState venomInst venomExecSemantics
  fragExec words loweringStateRelDefs exprLoweringProps
  exprLowering builtinBytes emitHelper freshWrites compileEnv

Theorem self_code_size_bounds_run:
  emit_op CODESIZE [] sa = (limit,sb) /\
  compile_assert_slice_bounds a n limit sb = ((),sc) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  (!x. a = Var x ==> not_fresh_at sa x) /\
  (!x. n = Var x ==> not_fresh_at sa x) /\
  LENGTH s.vs_code < dimword (:256) ==>
  if LENGTH s.vs_code < w2n wa + w2n wn then
    ?t. run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s = Abort Revert_abort t
  else
    ?t. run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s = OK t /\
      t = s with vs_vars := t.vs_vars /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qabbrev_tac `v = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `u = update_var v (n2w (LENGTH s.vs_code)) s` >>
  `~not_fresh_at sa v` by simp[Abbr `v`, not_fresh_at_def] >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op u = eval_operand op s` by
    (Cases >> simp[Abbr `u`, eval_operand_def, lookup_var_update_var] >>
     rpt strip_tac >> metis_tac[]) >>
  `eval_operand a u = SOME wa /\ eval_operand n u = SOME wn` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by simp[not_fresh_at_def] >>
  `eval_operand (Var v) u = SOME (n2w (LENGTH s.vs_code)) /\ not_fresh_at sb v` by
    simp[Abbr `u`, Abbr `v`, eval_operand_def, lookup_var_update_var, not_fresh_at_def] >>
  `((wa + wn <+ wa \/ n2w (LENGTH s.vs_code) <+ wa + wn) <=>
    LENGTH s.vs_code < w2n wa + w2n wn)` by
    (mp_tac (Q.SPECL [`dimword (:256)`, `w2n (wa:bytes32)`, `w2n (wn:bytes32)`,
       `LENGTH s.vs_code`] exprSimSliceBoundsTheory.slice_bounds_mod) >>
     simp[WORD_LO, word_add_def, w2n_n2w, w2n_lt] >> decide_tac) >>
  `run_inst_seq [mk_inst sa.cs_next_id CODESIZE [] [v]] s = OK u` by
    simp[run_inst_seq_def, Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def] >>
  `(!x. a = Var x ==> not_fresh_at sb x) /\
   (!x. n = Var x ==> not_fresh_at sb x) /\
   (!x. (Var v : operand) = Var x ==> not_fresh_at sb x)` by simp[] >>
  drule_all exprSimSliceBoundsTheory.slice_bounds_run_frame >>
  qpat_x_assum `(_ \/ _) <=> _` (fn th => pure_rewrite_tac[th]) >>
  Cases_on `LENGTH s.vs_code < w2n wa + w2n wn` >> simp[] >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id CODESIZE [] [v]) s = OK u` by
    simp[Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def] >>
  simp[Once run_inst_seq_def, mk_inst_def, is_terminator_def] >>
  conj_tac
  >- (gvs[Abbr `u`, update_var_def]) >>
  rpt strip_tac >>
  `lookup_var x t = lookup_var x u` by (gvs[lookup_var_def] >> metis_tac[]) >>
  simp[Abbr `u`, lookup_var_update_var] >> metis_tac[]
QED

Theorem self_code_copy_store_run:
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand len s = SOME n /\ eval_operand out s = SOME p /\
  w2n a + w2n n <= LENGTH s.vs_code ==>
  run_inst_seq [mk_inst id CODECOPY [dst;src;len] [];
                mk_inst sid MSTORE [out;len] []] s =
    OK (mstore (w2n p) n (write_memory_with_expansion (w2n d)
      (TAKE (w2n n) (DROP (w2n a) s.vs_code)) s))
Proof
  strip_tac >>
  `TAKE (w2n n) (DROP (w2n a) s.vs_code ++ REPLICATE (w2n n) 0w) =
    TAKE (w2n n) (DROP (w2n a) s.vs_code)` by
    (irule rich_listTheory.TAKE_APPEND1 >> simp[]) >>
  drule_all step_CODECOPY >> disch_then (qspec_then `id` assume_tac) >>
  simp[Once run_inst_seq_def, mk_inst_def, is_terminator_def] >>
  `eval_operand out (write_memory_with_expansion (w2n d)
     (TAKE (w2n n) (DROP (w2n a) s.vs_code)) s) = SOME p /\
   eval_operand len (write_memory_with_expansion (w2n d)
     (TAKE (w2n n) (DROP (w2n a) s.vs_code)) s) = SOME n` by
    (Cases_on `out` >> Cases_on `len` >>
     gvs[eval_operand_def, lookup_var_def, write_memory_with_expansion_def]) >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def]
QED

Theorem self_code_tail_layout:
  emit_op CODESIZE [] sa = (limit,sb) /\
  compile_assert_slice_bounds src len limit sb = ((),sc) /\
  emit_void CODECOPY [dst;src;len] sc = ((),sd) /\
  emit_void MSTORE [out;len] sd = ((),se) ==>
  se.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa se /\
  same_blocks sa se /\
  emitted_insts sa se = emitted_insts sa sb ++ emitted_insts sb sc ++
    [mk_inst sc.cs_next_id CODECOPY [dst;src;len] [];
     mk_inst sd.cs_next_id MSTORE [out;len] []] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa se)
Proof
  strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule exprSimSliceBoundsTheory.slice_bounds_shape >> strip_tac >>
  drule_all (emit_void_extends |> Q.SPECL [`CODECOPY`,`[dst;src;len]`,`sc`,`sd`]) >> strip_tac >>
  drule_all (emit_void_extends |> Q.SPECL [`MSTORE`,`[out;len]`,`sd`,`se`]) >> strip_tac >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> simp[]) >>
  `sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc` by
    simp[listTheory.APPEND_ASSOC] >>
  `emitted_insts sa sd = emitted_insts sa sc ++ emitted_insts sc sd` by
    (irule emitted_insts_append >> simp[]) >>
  `sd.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sd` by
    simp[listTheory.APPEND_ASSOC] >>
  `emitted_insts sa se = emitted_insts sa sd ++ emitted_insts sd se` by
    (irule emitted_insts_append >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule_all (emitted_insts_emit_void |> Q.SPECL [`CODECOPY`,`[dst;src;len]`,`sc`,`sd`]) >> strip_tac >>
  drule_all (emitted_insts_emit_void |> Q.SPECL [`MSTORE`,`[out;len]`,`sd`,`se`]) >> strip_tac >>
  rpt conj_tac
  >- simp[listTheory.APPEND_ASSOC]
  >- metis_tac[same_blocks_def]
  >- simp[listTheory.APPEND_ASSOC] >>
  simp[mk_inst_def, is_terminator_def]
QED
