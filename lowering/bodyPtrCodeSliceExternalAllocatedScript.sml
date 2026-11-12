Theory bodyPtrCodeSliceExternalAllocated
Ancestors
  bodyPtrCodeSliceExternalAddress bodyPtrCodeSliceSelfPrefix
  exprSimSliceExtcodeEntry exprSimSliceExtcodeContinue bodyPtrDefs
  fragExec venomState words finite_map compileEnv loweringPosts
  fragGasSeqPtr gasSummaryComposePtr rich_list list exprSimSource gasExemptCert
  vyperState exprLoweringProps pair loweringStateRelDefs bodyPtrHashBuiltinsGhostFrame

(* The allocation is executed before the address operand.  Combine its
   semantic frame and pointer frame at the same deterministic endpoint. *)
Theorem external_code_output_entry_ptr:
  compile_slice_out_buf sz sa = ((Var out,Var dst),sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ 32 <= sz /\ sz < dimword (:256) /\
  ghost_inv d cenv cx es G tn s /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) ==>
  ?t G1 tn1 p.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G1 tn1 /\
    ghost_inv d cenv cx es G1 tn1 t /\ ghost_kept cenv es sa G tn s G1 tn1 /\
    ptr_covers G1 tn1 out t sz /\ ptr_covers G1 tn1 dst t (sz-32) /\
    eval_operand (Var out) t = SOME p /\ eval_operand (Var dst) t = SOME (p+32w) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n p,sz) /\
    w2n p+sz < dimword (:256) /\ sa.cs_next_id < sb.cs_next_id /\
    not_fresh_at sb out /\ not_fresh_at sb dst /\
    (!name off len. local_region cenv es.scopes t name off len ==>
      regions_disjoint (w2n p) sz off len) /\
    stmt_state_rel ctx fn cenv cx es t /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!j b len. j < sa.cs_next_id /\ FLOOKUP t.vs_allocas j = SOME (b,len) ==>
      regions_disjoint (w2n p) sz b len) /\
    wb_frame cenv es es sa s t
Proof
  strip_tac >> drule_all slice_extcode_output_entry >> strip_tac >>
  drule_all slice_extcode_out_owner_inst >> strip_tac >>
  drule_all self_code_out_buffer_checked >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem external_code_output_prefix_ptr:
  compile_slice_out_buf sz sa = ((out,dst),sb) /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G1 tn1 /\
  gas_outcome_ptr D tops (ctx,fn) PG source
    (es,t with vs_inst_idx := LENGTH sb.cs_current_insts,G1,tn1) Q R ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s,G,tn) Q R
Proof
  strip_tac >> drule slice_extcode_out_control >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1, rich_listTheory.IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  drule_all fragGasSeqPtrTheory.run_inst_seq_gas_path_ptr >> strip_tac >>
  irule gasSummaryComposePtrTheory.gas_outcome_ptr_prefix >>
  goal_assum (drule_at Any) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by simp[] >>
  metis_tac[]
QED


Theorem external_code_address_continue_ptr:
  expr_sim_ptr d ctx PG fn cenv cx ty a es /\
  expr_body_pre cenv cx env a es /\ expr_type a = BaseT AddressT /\
  lower_value compile_expr cenv ty a sa = (aop,sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G0 tn0 s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!bs ee G tn t.
    LENGTH bs = 20 /\
    expr_post ctx fn cenv cx a es sa sb s ee (BytesV bs) aop t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\ ghost_kept cenv es sa G0 tn0 s G tn /\
    ptr_val_ok cx (expr_type a) (BytesV bs) aop G tn t /\
    expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    eval_operand aop t = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
    op_taint tn aop = {} /\ op_prov G aop = NONE /\ ee.gas_obs = [] ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
      (next (BytesV bs)) (ee,t,G,tn) Q (\res ee gt r. expr_exit res r)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (bind (bind (eval_expr cx a) (read_result cx)) next) (es,s,G0,tn0)
    Q (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `gas_admissible (bind (eval_expr cx a) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_ptr_def] >> disch_then drule_all >> strip_tac >>
  irule code_slice_address_bind_ptr >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_error_value >>
    goal_assum (drule_at Any)) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> simp[]) >>
  simp[Once CONJ_COMM] >>
  qexists_tac `\v ee G tn t. t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ghost_inv d cenv cx ee G tn t /\
    ghost_kept cenv es sa G0 tn0 s G tn` >>
  qexists_tac `\res ee gt r. expr_exit res r` >>
  qexistsl_tac [`cenv`,`env`,`aop`,`sa`,`sb`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def] >>
    Cases_on `y` >> Cases_on `r` >> fs[exprSimDefsTheory.expr_exit_def] >>
    rename1 `Error err` >> Cases_on `err` >> fs[exprSimDefsTheory.expr_exit_def]) >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem external_code_allocated_address_ptr:
  compile_slice_out_buf sz sa = ((Var out,Var dst),sb) /\
  lower_value compile_expr cenv ty a sb = (aop,sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
  expr_sim_ptr d ctx PG fn cenv cx ty a es /\
  expr_body_pre cenv cx env a es /\ expr_type a = BaseT AddressT /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  32 <= sz /\ sz < dimword (:256) /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G0 tn0 s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!u G1 tn1 p bs ee G tn t.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    ghost_inv d cenv cx es G1 tn1 u /\ ghost_kept cenv es sa G0 tn0 s G1 tn1 /\
    ptr_covers G1 tn1 out u sz /\ ptr_covers G1 tn1 dst u (sz-32) /\
    eval_operand (Var out) u = SOME p /\ eval_operand (Var dst) u = SOME (p+32w) /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n p,sz) /\
    w2n p+sz < dimword (:256) /\ sa.cs_next_id < sb.cs_next_id /\
    not_fresh_at sb out /\ not_fresh_at sb dst /\
    (!name off len. local_region cenv es.scopes u name off len ==>
      regions_disjoint (w2n p) sz off len) /\
    stmt_state_rel ctx fn cenv cx es u /\ wb_frame cenv es es sa s u /\
    LENGTH bs = 20 /\
    expr_post ctx fn cenv cx a es sb sc
      (u with vs_inst_idx := LENGTH sb.cs_current_insts) ee (BytesV bs) aop t /\
    t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\
    ghost_kept cenv es sb G1 tn1 (u with vs_inst_idx := LENGTH sb.cs_current_insts) G tn /\
    ptr_val_ok cx (expr_type a) (BytesV bs) aop G tn t /\
    expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    eval_operand aop t = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
    op_taint tn aop = {} /\ op_prov G aop = NONE /\ ee.gas_obs = [] ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
      (next (BytesV bs)) (ee,t,G,tn) Q (\res ee gt r. expr_exit res r)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (bind (bind (eval_expr cx a) (read_result cx)) next) (es,s,G0,tn0)
    Q (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all external_code_output_entry_ptr >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  drule slice_extcode_out_control >> strip_tac >>
  `ci_mono sa sb` by metis_tac[ci_mono_compile_slice_out_buf, SND] >>
  `(!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sb x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sb x)` by
    (metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono]) >>
  `t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted` by
    (drule_all slice_extcode_out_run_control >> simp[]) >>
  irule external_code_output_prefix_ptr >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`Var dst`,`Var out`,`sz`] >> simp[] >>
  `LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) =
    LENGTH sb.cs_current_insts` by simp[] >>
  qpat_x_assum `sb.cs_current_insts = _` kall_tac >> simp[] >>
  irule external_code_address_continue_ptr >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`aop`,`cenv`,`d`,`env`,`sb`,`sc`,`ty`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[stmt_state_rel_inst_idx, hash_ghost_inv_inst_idx]
QED
