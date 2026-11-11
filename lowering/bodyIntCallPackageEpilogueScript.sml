(* A normal void body landing takes the packaged implicit RET. *)
Theory bodyIntCallPackageEpilogue
Ancestors
  bodyIntCallPackageProducerExit bodyIntCallSharpReturn
  bodyIntCallJointContract compileEnv vyperTypeEvalSoundness gasSummary loweringPosts

Theorem intcall_void_epilogue:
  intcall_frame_ok fp /\ fp.jc_ret_ty = NoneT /\
  intcall_joint_res fp ce env ee sb u /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  emit_inst RET [fp.jc_rpc] [] sb = ((),sf) /\
  fn_has_code sb sf fp.jc_func ==>
  gas_path fp.jc_ctx fp.jc_func u 0
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u) /\
  intcall_stmt_exit fp (INR (ReturnException NoneV)) ee
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u)
Proof
  strip_tac >>
  `fp.jc_ret_tv = NoneTV /\ fp.jc_root_ce.ce_returns_count = 0 /\
   fp.jc_rb = NONE` by
    (fs[intcall_frame_ok_def, returns_stack_count_def,
        vyperValueTheory.evaluate_type_def] >> Cases_on `fp.jc_rb` >> gvs[]) >>
  conj_tac
  >- (irule emitted_memory_ret_path >>
      simp[] >> qexistsl [`fp.jc_rpc`, `sb`, `sf`] >> simp[] >>
      fs[intcall_frame_ok_def, intcall_joint_res_def, intcall_expr_res_def] >>
      metis_tac[]) >>
  irule intcall_joint_res_void_return >> metis_tac[]
QED

Theorem intcall_normal_epilogue:
  intcall_frame_ok fp /\
  (fp.jc_ret_ty = NoneT \/ stmts_no_fallthrough ss) /\
  gas_marked_exec F (fp.jc_ctx,fp.jc_func) (eval_stmts fp.jc_cx ss)
    (es,s0) marks res mid (OK u) /\
  stmt_lands NoLoop sb res u /\ ~u.vs_halted /\
  ~block_is_terminated sb /\ intcall_joint_res fp ce env ee sb u /\
  (if block_is_terminated sb then ((),sb)
   else if fp.jc_ret_ty = NoneT then emit_inst RET [fp.jc_rpc] [] sb
   else emit_inst INVALID [] [] sb) = ((),sf) /\
  fn_has_code sb sf fp.jc_func ==>
  res = INL () /\ ?r. gas_path fp.jc_ctx fp.jc_func u 0 r /\ exit_result r /\
    intcall_stmt_exit fp (INR (ReturnException NoneV)) ee r
Proof
  strip_tac >> fs[stmt_lands_def] >>
  `fp.jc_ret_ty = NoneT` by
    (Cases_on `fp.jc_ret_ty = NoneT` >> gvs[] >>
     fs[gas_marked_exec_def] >>
     qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
     metis_tac[cj 2 no_fallthrough_eval_no_success]) >>
  gvs[] >> drule_all intcall_void_epilogue >> strip_tac >>
  goal_assum (drule_at Any) >> simp[fragExecTheory.exit_result_def]
QED
