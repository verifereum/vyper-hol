Theory bodyPtrBopInVvOutcome
Ancestors gasSummaryComposePtrAll gasStorage vyperStorageTrace gasSummary fragGasPath bodyPtrBopPairOutcome bodyPtrDefs gasSummaryComposePtr
  stmtSimProps exprSimDefs

(* Raw value/place evaluation: unlike bop_operand_outcome_ptr this does not
   insert read_result into the compiled haystack evaluation. *)
Theorem membership_vv_operand_outcome_ptr:
  post_value_type cenv e = expr_type e ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty e es /\
  compile_expr cenv ty e sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv H d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!gs rr ee. eval_expr cx e (es with gas_obs := gs) = (rr,ee) ==>
    P rr ee) /\
  (!tv ee G tn t.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv H d cenv cx ee G tn t /\
    ptr_vv_ok cx (expr_type e) tv vv ee G tn t /\
    (!t' op. vv = StackValue t' op /\ ~is_word_type (expr_type e) ==>
      ptr_buf_ok cenv e op G t) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn) /\
    P (INL tv) ee /\ ee.gas_obs = [] /\ ~t.vs_halted ==>
    gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx,func) PG cx st0
      (next tv) (ee,t,G,tn) Q (\H res ee gt r. expr_exit res r)) /\
  (!v. storage_trace_frame (next v)) /\
  (!marks err ee leaf fstate.
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (eval_expr cx e) (return ()))
      (es,s0) marks (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (eval_expr cx e) (\tv. ignore_bind (next tv) (return ())))
      (es,s0) marks (err,ee) (leaf,fstate)) /\
  (!left tv mid t right err ee leaf fstate.
    gas_marked_exec F (ctx,func) (eval_expr cx e)
      (es,s0) left (INL tv) mid (OK t) /\
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (next tv) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (eval_expr cx e) (\tv. ignore_bind (next tv) (return ())))
      (es,s0) (left ++ right) (err,ee) (leaf,fstate)) ==>
  gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx,func) PG cx st0
    (bind (eval_expr cx e) next) (es,s0,G0,tn0)
    Q (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- simp[] >> disch_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _`
    (fn th => match_mp_tac (MATCH_MP
      (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] gas_outcome_ptr_bind_all) th)) >>
  rpt conj_tac
  >- (rpt strip_tac >> gvs[])
  >- (rpt strip_tac >> Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type])
  >- simp[]
  >- (rpt gen_tac >> strip_tac >>
      `P (INL v) (mid with gas_obs := [])` by
        (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
         simp[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
         qpat_x_assum `!tail. _ = _` (qspec_then `[]` mp_tac) >>
         simp[] >> metis_tac[]) >>
      `~t.vs_halted` by
        (fs[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
         metis_tac[fragGasPathTheory.gas_path_normal]) >>
      qpat_x_assum `!tv ee G tn t. _` irule >> simp[] >>
      rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> simp[])
  >- metis_tac[] >>
  metis_tac[]
QED
