Theory exprExtRequestAllocatedRead
Ancestors
  exprExtRequestJointUnwrap exprExtRequestAllocationEndpoint
  exprExtRequestHistoryCompose exprExtRequestHistory exprSafeOperand
  exprLoweringProps exprSimProps exprSimDefs loweringPosts
  gasSummary fragGasMode fragGasPath freshWrites compileEnv venomState

Theorem extrequest_allocated_unwrap_read:
  compile_alloc_buffer sz sn = (buf,mid) /\
  unwrap_value cenv vv mid = (op,sb) /\
  fn_has_code sn mid func /\ fn_has_code mid sb func /\
  fn_inst_ids_distinct func /\ sz < dimword (:256) /\
  vv_post ctx func cenv cx e es sa sc s0 ec r vv tc /\
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  stmt_state_rel ctx func cenv cx ee t /\
  (case vv of StackValue ty a => safe_operand sc a
   | LocatedValue ty p => safe_operand sc p.ptr_operand) /\
  (!ty p tr w tv.
     vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
     eval_operand p.ptr_operand tc = SOME w /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     storage_read_live cx tr (get_storage cx ec tr) w tv) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
         type_memory_size tv < 2**64) /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?v z w. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
      [] (INL v) ee (OK z) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    extrequest_history_frame cenv cx ee sn t ee sb z /\
    eval_operand buf.buf_operand z = SOME w /\ w2n w + sz < dimword (:256)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ec tc` by fs[vv_post_def] >>
  `local_ptrs_reserved cenv sn` by fs[extrequest_history_frame_def] >>
  drule_all extrequest_allocation_endpoint >> strip_tac >>
  `extrequest_history_frame cenv cx ec sc tc ee mid u` by
    (irule extrequest_history_frame_trans >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`ee`, `sn`, `t`] >> simp[]) >>
  drule_all extrequest_joint_unwrap_read >> strip_tac >>
  `extrequest_history_frame cenv cx ee sn t ee sb u'` by
    (irule extrequest_history_frame_trans >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`ee`, `mid`, `u`] >> simp[]) >>
  `eval_operand buf.buf_operand u' = SOME w` by
    (gvs[extrequest_history_frame_def, eval_operand_def] >> metis_tac[]) >>
  `!n b len. local_region cenv ee.scopes t n b len <=>
              local_region cenv ee.scopes u n b len` by
    (rpt gen_tac >>
     qpat_assum `extrequest_history_frame cenv cx ee sn t ee mid u`
       (mp_then Any mp_tac extrequest_history_local_regions) >>
     metis_tac[]) >>
  qexistsl_tac [`v`, `u'`, `w`] >> simp[] >>
  conj_tac
  >- (fs[gas_marked_exec_def, gas_explicit_def] >>
      metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0]) >>
  fs[expr_post_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn x` by
        (fs[extrequest_history_frame_def] >> metis_tac[not_fresh_at_mono]) >>
      metis_tac[])
  >- metis_tac[]
  >> fs[locals_kept_def] >> metis_tac[]
QED
