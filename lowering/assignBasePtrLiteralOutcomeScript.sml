Theory assignBasePtrLiteralOutcome
Ancestors assignBasePtrLiteralSource assignBasePtrLiteralPost
  assignBasePtrLiteralGhost fragGasSeqPtr ghostPcTransportPtr
  context emitHelper compileEnv loweringStateRelDefs exprSimAlloc ptrDiscipline ptrSafeRun
  venomExecSemantics venomInst instIdxIndep list words emitHelperProps fragExec exprLoweringProps venomState

Theorem assign_base_ptr_one_byte_sequence:
  !ctx func cenv cx es sa buf sb s PG G tn D.
    compile_bytelike_literal [1w] 1 sa = (buf,sb) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    ?t G' tn'.
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
      (?a p. buf.buf_operand = Var p /\ lookup_var p t = SOME a /\
        ptr_covers G' tn' p t 64 /\ w2n a + 64 < dimword (:256)) /\
      ?u.
        step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
          [STRING #"%" (toString sa.cs_next_var)]) s = OK u /\
        run_inst_seq (TL (emitted_insts sa sb)) u = OK t /\
        inst_seq_ptr D 0 ctx func PG
          (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
            [STRING #"%" (toString sa.cs_next_var)]) u)
          (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
            [STRING #"%" (toString sa.cs_next_var)]) s u tn)
          (TL (emitted_insts sa sb)) u G' tn'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_alloc_buffer 64 sa` >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all assign_base_ptr_alloc_buffer_sequence >>
  simp[] >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `D`] strip_assume_tac) >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, inst_seq_ptr_def, AllCaseEqs()] >>
  suspend "init"
QED

Resume assign_base_ptr_one_byte_sequence[init]:
  `STRING #"%" (toString sa.cs_next_var) <>
   STRING #"%" (toString (sa.cs_next_var + 1))` by
    simp[ASCIInumbersTheory.toString_11] >>
  drule_at (Pat `ptr_covers`) assign_base_ptr_one_byte_init_sequence >>
  simp[GSYM eval_operand_def] >>
  disch_then (qspecl_then [`ctx`, `func`, `PG`,
    `STRING #"%" (toString (sa.cs_next_var + 1))`] mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`sa.cs_next_id + 1`, `sa.cs_next_id + 2`,
                          `sa.cs_next_id + 3`, `D`] strip_assume_tac) >>
  drule assign_base_ptr_one_byte_code >> strip_tac >>
  qexistsl_tac [`t'`, `G'`, `tn'`] >>
  conj_tac >- simp[Once run_inst_seq_def] >>
  conj_tac >- simp[Once inst_seq_ptr_def] >>
  conj_tac >- (qexists_tac `w` >> simp[GSYM eval_operand_def]) >>
  simp[] >>
  first_x_assum (qspec_then `t.vs_inst_idx` mp_tac) >> simp[]
QED

Finalise assign_base_ptr_one_byte_sequence

Theorem assign_base_ptr_one_byte_endpoint:
  !ctx func cenv cx es sa buf sb s PG G tn d.
    compile_bytelike_literal [1w] 1 sa = (buf,sb) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    ghost_inv d cenv cx es G tn s /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    ?t G' tn'.
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      inst_seq_ptr (cx_dead cx) 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
      expr_post ctx func cenv cx
        (Literal (BaseT (BytesT (Dynamic 64))) (BytesL [1w]))
        es sa sb s es (BytesV [1w]) buf.buf_operand t /\
      ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es sa G tn s G' tn' /\
      ptr_val_ok cx (BaseT (BytesT (Dynamic 64))) (BytesV [1w]) buf.buf_operand G' tn' t /\
      ptr_buf_ok cenv (Literal (BaseT (BytesT (Dynamic 64))) (BytesL [1w]))
        buf.buf_operand G' t /\
      ?a p. buf.buf_operand = Var p /\ lookup_var p t = SOME a /\
        ptr_covers G' tn' p t 64 /\ w2n a + 64 < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_ptr_one_byte_sequence >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `cx_dead cx`] strip_assume_tac) >>
  drule_all assign_base_ptr_one_byte_run_post >> strip_tac >>
  drule assign_base_ptr_one_byte_code >> strip_tac >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
  `STRING #"%" (toString sa.cs_next_var) <>
   STRING #"%" (toString (sa.cs_next_var + 1))` by
    simp[ASCIInumbersTheory.toString_11] >>
  `!x. not_fresh_at sa x ==>
    x <> STRING #"%" (toString sa.cs_next_var) /\
    x <> STRING #"%" (toString (sa.cs_next_var + 1))` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL,
       arithmeticTheory.LESS_EQ_ADD]) >>
  suspend "ghost"
QED

Resume assign_base_ptr_one_byte_endpoint[ghost]:
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var)) /\
   not_local_ptr cenv es.scopes (STRING #"%" (toString (sa.cs_next_var + 1)))` by
    (conj_tac >> irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    x <> STRING #"%" (toString sa.cs_next_var) /\
    x <> STRING #"%" (toString (sa.cs_next_var + 1))` by metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    x <> STRING #"%" (toString sa.cs_next_var) /\
    x <> STRING #"%" (toString (sa.cs_next_var + 1))` by metis_tac[] >>
  gvs[] >>
  drule_at (Pat `inst_seq_ptr`) (SRULE [] assign_base_ptr_alloca_init_ghost) >>
  simp[] >> disch_then (qspecl_then [`d`, `cenv`, `cx`, `es`] mp_tac) >>
  disch_then (qspec_then `sa` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  simp[] >>
  drule_all assign_base_ptr_one_byte_ptr_value >> simp[] >> metis_tac[]
QED

Finalise assign_base_ptr_one_byte_endpoint

Theorem assign_base_ptr_expr_post_index:
  expr_post ctx func cenv cx e es sa sb s0 es' v op (s with vs_inst_idx := n) <=>
  expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  simp[loweringPostsTheory.expr_post_def, stmt_state_rel_inst_idx,
    loweringPostsTheory.expr_val_rel_def, loweringPostsTheory.expr_val_at_def,
    loweringPostsTheory.expr_val_own_def,
    exprSimPropsTheory.locals_kept_inst_idx, local_region_def, lookup_var_def]
QED

Theorem assign_base_ptr_value_index:
  ptr_val_ok cx ty v op G tn (s with vs_inst_idx := n) <=>
  ptr_val_ok cx ty v op G tn s
Proof
  simp[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def]
QED

Theorem assign_base_ptr_buffer_index:
  ptr_buf_ok cenv e op G (s with vs_inst_idx := n) <=> ptr_buf_ok cenv e op G s
Proof
  simp[bodyPtrDefsTheory.ptr_buf_ok_def]
QED

Theorem assign_base_ptr_ghost_index:
  ghost_inv d cenv cx es G tn (s with vs_inst_idx := n) <=>
  ghost_inv d cenv cx es G tn s
Proof
  simp[bodyPtrDefsTheory.ghost_inv_def, bodyPtrDefsTheory.stor_taint_ok_def,
    lookup_var_def] >> Cases_on `d` >> simp[bodyPtrDefsTheory.return_buf_ptr_def] >>
  PairCases_on `x` >> simp[bodyPtrDefsTheory.return_buf_ptr_def, lookup_var_def]
QED

Theorem assign_base_ptr_one_byte_alloca_member:
  compile_bytelike_literal [1w] 1 sa = (buf,sb) /\ fn_has_code sa sb func ==>
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >> drule exprSimLiteralBufferTheory.literal_bytelike_counted_shape >>
  strip_tac >> drule assign_base_ptr_one_byte_code >> strip_tac >>
  gvs[fn_has_code_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  qpat_x_assum `emitted_insts _ _ = _` mp_tac >>
  simp[emitted_insts_def] >> strip_tac
QED

Theorem assign_base_ptr_expr_post_gas_obs:
  expr_post ctx func cenv cx e es sa sb s0 (ee with gas_obs := gs) v op s <=>
  expr_post ctx func cenv cx e es sa sb s0 ee v op s
Proof
  simp[loweringPostsTheory.expr_post_def, stmt_state_rel_def, state_rel_gas_obs,
    loweringPostsTheory.expr_val_at_def,
    loweringPostsTheory.expr_val_own_def]
QED

Theorem assign_base_ptr_one_byte_outcome:
  !ctx PG func d cenv cx ty es sa sb op s G tn.
    lower_value compile_expr cenv ty
      (Literal (BaseT (BytesT (Dynamic 64))) (BytesL [1w])) sa = (op,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (bind (eval_expr cx (Literal (BaseT (BytesT (Dynamic 64))) (BytesL [1w])))
        (read_result cx)) (es,s,G,tn)
      (\res ee G' tn' t. ?v. res = INL v /\
        expr_post ctx func cenv cx
          (Literal (BaseT (BytesT (Dynamic 64))) (BytesL [1w]))
          es sa sb s ee v op t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        ghost_inv d cenv cx ee G' tn' t /\
        ptr_val_ok cx (BaseT (BytesT (Dynamic 64))) v op G' tn' t /\
        ptr_buf_ok cenv (Literal (BaseT (BytesT (Dynamic 64))) (BytesL [1w])) op G' t /\
        ghost_kept cenv es sa G tn s G' tn' /\
        ?a p. op = Var p /\ lookup_var p t = SOME a /\
          ptr_covers G' tn' p t 64 /\ w2n a + 64 < dimword (:256))
      (\res ee gt r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[assign_base_ptr_one_byte_lowering, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all assign_base_ptr_one_byte_alloca_member >> strip_tac >>
  drule_all assign_base_ptr_one_byte_endpoint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all assign_base_ptr_bytelike_counted_path >> strip_tac >>
  suspend "package"
QED

Resume assign_base_ptr_one_byte_outcome[package]:
  simp[fragGasPathPtrTheory.gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[fragGasPathPtrTheory.gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (BytesV [1w])`, `es`, `G'`, `tn'`,
    `OK (t with vs_inst_idx := LENGTH cs'.cs_current_insts)`] >>
  conj_tac >- suspend "source" >>
  simp[assign_base_ptr_expr_post_index, assign_base_ptr_expr_post_gas_obs,
    assign_base_ptr_ghost_index, stmtFragPtrTheory.ghost_inv_gas_obs,
    assign_base_ptr_value_index, assign_base_ptr_buffer_index, lookup_var_def] >>
  gvs[lookup_var_def]
QED

Resume assign_base_ptr_one_byte_outcome[source]:
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.read_result_def,
    vyperValueOperationTheory.evaluate_literal_def, vyperStateTheory.bind_def,
    vyperStateTheory.return_def, gasSummaryTheory.gas_explicit_def]
QED

Finalise assign_base_ptr_one_byte_outcome
