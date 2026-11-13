Theory bodyPtrCodeSliceExternalAllocated
Ancestors
  bodyPtrCodeSliceExternalAddress bodyPtrCodeSliceSelfPrefix
  exprSimSliceExtcodeEntry exprSimSliceExtcodeContinue bodyPtrDefs
  fragExec venomState words finite_map compileEnv loweringPosts
  fragGasSeqPtr gasSummaryComposePtr rich_list list exprSimSource gasExemptCert
  vyperState exprLoweringProps pair loweringStateRelDefs bodyPtrHashBuiltinsGhostFrame
  bodyPtrCodeSliceExternalTail wordArgsPtr bodyPtrCodeSliceSelfOperands exprSimWordArgs venomInst gasOutcomeMarkedPtr exprSimSliceOrdinaryContinue

(* Read the address operand, then continue in the address's post-state. *)
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
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
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
  qexists_tac `\v ee G tn t. ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ghost_inv d cenv cx ee G tn t /\
    ghost_kept cenv es sa G0 tn0 s G tn` >>
  qexists_tac `\res ee gt r. expr_exit res r` >>
  qexistsl_tac [`cenv`,`env`,`aop`,`sa`,`sb`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def] >>
    Cases_on `y` >> Cases_on `r` >> fs[exprSimDefsTheory.expr_exit_def] >>
    rename1 `Error err` >> Cases_on `err` >> fs[exprSimDefsTheory.expr_exit_def]) >>
  irule gas_outcome_ptr_marked_conseq >> goal_assum (drule_at Any) >>
  rpt strip_tac >> gvs[] >>
  drule gas_marked_exec_ptr_exec >>
  disch_then (assume_tac o MATCH_MP exprSimSliceOrdinaryContinueTheory.slice_marked_read_ok_not_halted) >>
  `post_value_type cenv a = BaseT AddressT` by
    (irule EQ_TRANS >> qexists_tac `expr_type a` >> conj_tac
     >- (irule post_value_type_word >> simp[is_word_type_def]) >>
     first_assum ACCEPT_TAC) >>
  metis_tac[]
QED
