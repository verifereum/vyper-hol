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
  exprSimHashBoundary stmtSimLogTopics exprSimSliceData exprSimProps
  exprSimWordArgs loweringPosts finite_map pred_set

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

Theorem self_code_tail_run:
  emit_op CODESIZE [] sa = (limit,sb) /\
  compile_assert_slice_bounds src len limit sb = ((),sc) /\
  emit_void CODECOPY [dst;src;len] sc = ((),sd) /\
  emit_void MSTORE [out;len] sd = ((),se) /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  eval_operand dst s = SOME b /\ eval_operand out s = SOME p /\
  (!v x. MEM v [src;len;dst;out] /\ v = Var x ==> not_fresh_at sa x) /\
  LENGTH s.vs_code < dimword (:256) ==>
  if LENGTH s.vs_code < w2n a + w2n n then
    ?t. run_inst_seq (emitted_insts sa se) s = Abort Revert_abort t
  else
    ?u. run_inst_seq (emitted_insts sa se) s =
      OK (mstore (w2n p) n (write_memory_with_expansion (w2n b)
        (TAKE (w2n n) (DROP (w2n a) s.vs_code)) u)) /\
      u = s with vs_vars := u.vs_vars /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all self_code_tail_layout >> strip_tac >>
  `(!x. src = Var x ==> not_fresh_at sa x) /\
   (!x. len = Var x ==> not_fresh_at sa x)` by simp[] >>
  drule_all self_code_size_bounds_run >>
  Cases_on `LENGTH s.vs_code < w2n a + w2n n` >> simp[] >> strip_tac
  >- (qexists_tac `t` >> irule EQ_TRANS >>
      qexists_tac `run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s` >>
      conj_tac >- (irule run_inst_seq_append_err >> simp[]) >> simp[]) >>
  `t.vs_labels = s.vs_labels /\ t.vs_code = s.vs_code` by
    (qpat_x_assum `t = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!v. MEM v [src;len;dst;out] ==> eval_operand v t = eval_operand v s` by
    (Cases >> simp[eval_operand_def] >> rpt strip_tac >> metis_tac[]) >>
  `eval_operand src t = SOME a /\ eval_operand len t = SOME n /\
   eval_operand dst t = SOME b /\ eval_operand out t = SOME p` by simp[] >>
  `t.vs_code = s.vs_code` by simp[] >>
  `w2n a + w2n n <= LENGTH t.vs_code` by simp[] >>
  `run_inst_seq [mk_inst sc.cs_next_id CODECOPY [dst;src;len] [];
     mk_inst sd.cs_next_id MSTORE [out;len] []] t =
     OK (mstore (w2n p) n (write_memory_with_expansion (w2n b)
       (TAKE (w2n n) (DROP (w2n a) s.vs_code)) t))` by
    metis_tac[self_code_copy_store_run] >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `run_inst_seq (_ ++ _) s = OK t`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `[mk_inst sc.cs_next_id CODECOPY [dst;src;len] [];
     mk_inst sd.cs_next_id MSTORE [out;len] []]` mp_tac) >>
  simp[listTheory.APPEND_ASSOC]
QED

Theorem self_code_tail_frame:
  emit_op CODESIZE [] sa = (limit,sb) /\
  compile_assert_slice_bounds src len limit sb = ((),sc) /\
  emit_void CODECOPY [dst;src;len] sc = ((),sd) /\
  emit_void MSTORE [out;len] sd = ((),se) /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  eval_operand out s = SOME p /\ eval_operand dst s = SOME (p+32w) /\
  (!v x. MEM v [src;len;dst;out] /\ v = Var x ==> not_fresh_at sa x) /\
  LENGTH s.vs_code < dimword (:256) /\ w2n a + w2n n <= LENGTH s.vs_code /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sbase /\ sbase.cs_next_var <= sa.cs_next_var /\
  sbase.cs_next_id <= sa.cs_next_id /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,cap) /\
  w2n p + cap < dimword (:256) /\ 32 + w2n n <= cap /\
  (!nm off sz. local_region cenv es.scopes s nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  (!id off sz. id < sbase.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
    regions_disjoint (w2n p) cap off sz) ==>
  ?t. run_inst_seq (emitted_insts sa se) s = OK t /\
    stmt_state_rel ctx fn cenv cx es t /\ wb_frame cenv es es sbase s t /\
    eval_operand out t = SOME p /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n p,cap) /\
    t.vs_memory = (mstore (w2n p) n (write_memory_with_expansion (w2n p+32)
      (TAKE (w2n n) (DROP (w2n a) s.vs_code)) s)).vs_memory
Proof
  strip_tac >> drule_all self_code_tail_run >> simp[] >> strip_tac >>
  `u with vs_vars := s.vs_vars = s` by
    (qpat_assum `u = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es u` by
    (irule hash_readonly_state_rel >> metis_tac[]) >>
  `!x. not_fresh_at sbase x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> first_x_assum irule >>
     irule not_fresh_at_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `wb_frame cenv es es sbase s u` by
    (irule log_readonly_frame >> simp[]) >>
  `w2n (p+32w) = w2n p+32` by
    (simp[word_add_def, w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `LENGTH (TAKE (w2n n) (DROP (w2n a) s.vs_code)) = w2n n` by simp[] >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory` by
    (qpat_assum `u = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!nm off sz. local_region cenv es.scopes u nm off sz ==>
     regions_disjoint (w2n p) cap off sz` by suspend "local" >>
  suspend "write"
QED

Resume self_code_tail_frame[local]:
  rpt strip_tac >> qpat_x_assum `!nm off sz. local_region _ _ s _ _ _ ==> _` irule >>
  qexists_tac `nm` >>
  gvs[local_region_def, local_ptrs_reserved_def, eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED

Resume self_code_tail_frame[write]:
  qabbrev_tac `bs = TAKE (w2n n) (DROP (w2n a) s.vs_code)` >>
  qabbrev_tac `z = mstore (w2n p) n (write_memory_with_expansion (w2n p+32) bs u)` >>
  `stmt_state_rel ctx fn cenv cx es z /\ wb_frame cenv es es sbase u z` by
    (simp[Abbr `z`] >>
     `n = n2w (LENGTH bs)` by simp[Abbr `bs`] >>
     pop_assum (fn th => once_rewrite_tac[th]) >>
     irule (SIMP_RULE std_ss [LET_THM] slice_allocated_bytes_write_frame) >>
     metis_tac[]) >>
  qexists_tac `z` >> simp[Abbr `z`, Abbr `bs`] >>
  conj_tac
  >- (irule wb_frame_trans >>
      conj_tac >- simp[] >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`es`,`sbase`,`u`] >> simp[]) >>
  conj_tac
  >- (`u.vs_labels = s.vs_labels` by
        (qpat_assum `u = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
      Cases_on `out` >> gvs[eval_operand_def, lookup_var_def,
        write_memory_with_expansion_def] >> metis_tac[]) >>
  qpat_x_assum `u.vs_memory = s.vs_memory` mp_tac >>
  rpt (pop_assum kall_tac) >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion off bs u` >>
  simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def, LET_THM]
QED

Finalise self_code_tail_frame
