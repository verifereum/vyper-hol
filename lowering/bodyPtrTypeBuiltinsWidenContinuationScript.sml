Theory bodyPtrTypeBuiltinsWidenContinuation
Ancestors
  bodyPtrTypeBuiltinsWidenPost bodyPtrEnvBuiltinsOperandFrame
  bodyPtrTypeBuiltinsWidenActual bodyPtrTypeBuiltinsWidenFrame exprSimConvertBytes
  bodyPtrSignedConvertSourceFrame stmtFragPtr
  bodyPtrTypeBuiltinsWidenCounted bodyPtrHashBuiltinsCursor
  bodyPtrEnvBuiltinsEntryFrame
  exprSimPtrLiteralBuffer gasSummaryComposePtr gasSummary exprSimDefs
  fragGasPathPtr rawCallBufferPtr bodyPtrTypeBuiltinsMemoryInterface
  exprLoweringProps bodyPtrDefs venomState loweringPosts exprLowering

Theorem widen_convert_modern_outcome_ptr:
  compile_bytestring_widen_copy capacity (Var src) n sa = (op,sb) /\
  fn_has_code sa sb fn /\ 0 < n /\
  stmt_state_rel ctx fn cenv cx ee s /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ capacity < dimword(:256) /\ n <= capacity /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  expr_val_at cenv cx (expr_type e) slo sa ee v (Var src) s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ ~is_word_type (expr_type e) /\
  val_wf tv v /\ val_footprint tv v <= n /\ lookup_var src s = SOME a /\
  ptr_covers G tn src s n /\ ghost_inv d cenv cx ee G tn s /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n a) m) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type target /\ ~is_word_type target /\
  evaluate_type (get_tenv cx) target = SOME tout /\ value_has_type tv v /\
  convert_result cx (expr_type e) target v = INL vout /\
  type_memory_size tout <= capacity /\ type_memory_bytes cenv target <= capacity /\
  expr_post ctx fn cenv cx e es ca sa s0 ee v (Var src) s /\
  stmt_state_rel ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv ca /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  ca.cs_next_var <= sa.cs_next_var /\ ca.cs_next_id <= sa.cs_next_id /\
  lower_value compile_expr cenv ty e ca = (Var src,sa) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  ghost_kept cenv es ca G0 tn0 s0 G tn /\ local_ptrs_rel fn cenv es.scopes s0 /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (\st. (convert_result cx (expr_type e) target v,st)) (ee,s,G,tn)
    (\res fin H th u. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin target Convert target [e]) es ca sb s0 fin vout op u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th u /\
      ptr_val_ok cx (post_value_type cenv (TypeBuiltin target Convert target [e])) vout op H th u /\
      (~is_word_type (post_value_type cenv (TypeBuiltin target Convert target [e])) ==>
        ptr_buf_ok cenv (TypeBuiltin target Convert target [e]) op H u) /\
      ghost_kept cenv es ca G0 tn0 s0 H th)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all widen_copy_actual_counted_certificate >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `lookup_var dst t = SOME b` by
    (fs[lookup_var_def]) >>
  `expr_post ctx fn cenv cx (TypeBuiltin target Convert target [e]) es ca sb s0
     (ee with gas_obs := []) vout (Var dst)
     (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule widen_convert_run_success_post >> metis_tac[]) >>
  `ghost_kept cenv es ca G0 tn0 s0 H th` by
    (irule (SRULE [expr_post_entry_gas_obs, ghost_kept_entry_gas_obs]
      (Q.INST [`es` |-> `es with gas_obs := gs`] operand_suffix_ghost_kept)) >>
     simp[] >> metis_tac[]) >>
  `val_wf tout vout` by (irule convert_bytestring_wf >> metis_tac[]) >>
  `ptr_val_ok cx target vout (Var dst) H th
     (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule ptr_val_ok_from_covers >> simp[] >> qexists_tac `capacity` >> simp[] >>
     conj_tac >- (irule arithmeticTheory.LESS_EQ_TRANS >>
       qexists_tac `type_memory_size tout` >> simp[exprSimPropsTheory.val_store_size_le]) >>
     rpt strip_tac >> gvs[lookup_var_def]) >>
  `ptr_buf_ok cenv (TypeBuiltin target Convert target [e]) (Var dst) H
     (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule ptr_buf_ok_from_covers >> simp[convert_outer_lowered_type] >>
     qexistsl_tac [`capacity`,`th`] >> fs[ptr_covers_def, lookup_var_def]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (drule_all widen_copy_straight_code >> strip_tac >>
     irule hash_run_inst_seq_current_bb >> metis_tac[]) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL vout`,`ee`,`H`,`th`,
    `OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))`] >>
  gvs[ghost_inv_gas_obs, post_value_type_not_int_call, vyperASTTheory.expr_type_def]
QED
