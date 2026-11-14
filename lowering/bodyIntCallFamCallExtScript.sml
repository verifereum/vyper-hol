(* Seam 2 joint induction, a family leaf of the call step: every other call target (external calls and send; the rest are not supported_expr). *)
Theory bodyIntCallFamCallExt
Ancestors
  bodyIntCallJointContract bodyIntCallJointCallCore bodyIntCallJointPurePath
  exprExtRequestHistory extcallProtFramePath exprSimSliceCompose

Theorem intcall_ext_history_cont[local]:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  extrequest_history_frame ce fp.jc_cx es sa s ee sb u /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u /\
  expr_sim_inv ce fp.jc_cx env ee /\ ee.immutables = es.immutables /\
  gas_marked_path F fp.jc_ctx fp.jc_func s n (OK u) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!a k. fp.jc_prot a k ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   allocas_above fp.jc_lo s` by fs[intcall_expr_res_def] >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    metis_tac[gas_marked_path_alloca_next_mono] >>
  `allocas_above fp.jc_lo u` by
    metis_tac[gas_marked_path_allocas_above] >>
  `!n b k. local_region ce es.scopes s n b k <=>
            local_region ce ee.scopes u n b k` by
    metis_tac[extrequest_history_local_regions] >>
  `!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s` by
    (rpt strip_tac >>
     `?x w. op = Var x /\ lookup_var x fp.jc_oorig = SOME w` by
       metis_tac[intcall_frame_ok_def] >>
     `not_fresh_at sa x /\ eval_operand op s = SOME w` by
       (fs[intcall_expr_res_def, venomStateTheory.eval_operand_def] >> metis_tac[]) >>
     gvs[venomStateTheory.eval_operand_def] >>
     metis_tac[extrequest_history_frame_def]) >>
  `intcall_expr_res fp ce env ee sb u` by
    (irule intcall_joint_res_frame >>
     simp[] >> qexistsl [`es`, `s`, `sa`] >>
     fs[extrequest_history_frame_def] >> metis_tac[]) >>
  `locals_kept ce es ee s u` by
    (`ee.scopes = es.scopes` by
       fs[extrequest_history_frame_def, exprExtRequestReadProbeTheory.extrequest_read_frame_def] >>
     `locals_kept ce es es s u` by
       (irule exprSimPropsTheory.locals_kept_regions >>
        fs[extrequest_history_frame_def] >> metis_tac[]) >>
     fs[loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def] >>
     metis_tac[]) >>
  fs[intcall_expr_cont_def, extrequest_history_frame_def,
     loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]
QED

Theorem intcall_ext_target_cps[local]:
  intcall_forced_producer fp e /\ intcall_frame_ok fp /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env e es /\ expr_type e = BaseT AddressT /\
  supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  lower_value compile_expr ce (BaseT AddressT) e sa = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  gas_admissible (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) kont)
    expr_vv_res_ok es /\
  intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v ee u.
    expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee v op u /\
    intcall_expr_cont fp ce env es sa s ee sb u /\ ee.gas_obs = [] /\
    (?used. !tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
      (es with gas_obs := used ++ tail) = (INL v,ee with gas_obs := tail)) ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (kont v) (ee,u) Q (\r ee z. expr_exit r z)) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) kont)
    (es,s) Q (\r ee z. expr_exit r z)
Proof
  strip_tac >>
  `gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
     expr_res_ok es` by metis_tac[slice_gas_admissible_expr_head] >>
  `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (es,s)
    (\res ee u. ?v. res = INL v /\
      expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee v op u /\
      intcall_expr_cont fp ce env es sa s ee sb u)
    (\res ee r. ?ex. res = INR ex /\ expr_exit (INR ex) r)` by
    (fs[intcall_forced_producer_def] >>
     first_x_assum (drule_all_then mp_tac) >>
     strip_tac >> irule slice_gas_outcome_conseq >>
     goal_assum (drule_at Any) >>
     qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!v ee u. _` kall_tac >>
     rpt conj_tac >> rpt gen_tac >> Cases_on `res` >>
     simp[exprSimDefsTheory.expr_exit_def] >> strip_tac >>
     gvs[loweringPostsTheory.expr_post_def, intcall_expr_cont_def,
         intcall_expr_res_def] >>
     metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  irule slice_gas_outcome_bind_value >>
  qexists `\v ee u. expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee v op u /\
    intcall_expr_cont fp ce env es sa s ee sb u` >>
  reverse conj_tac
  >- (BETA_TAC >> irule slice_gas_outcome_conseq >>
      goal_assum (drule_at Any) >> simp[] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum irule >> fs[] >>
  qexists `gas_explicit marks s.vs_gas_readings` >>
  gvs[gasSummaryTheory.gas_marked_exec_def]
QED

(* The operand hypotheses carry the internal frame, rather than exprs_case's
   universally quantified contract.  Execute each child with the smaller
   producer hypothesis, then reuse the canonical suffix:

   ExtCall: extrequest_compile_call_split exposes target, snapshot args,
   kwargs, tuple prefix, call and return.  At each raw eval_expr landing,
   intcall_vv_post_intro recovers vv_post and intcall_expr_cont retains the
   resource frame.  The snapshot word/cell-intro, unread, joint-unwrap and
   kwarg-suffix lemmas handle the remaining operand work.  Existing layout,
   gas-selection and protected tuple-prefix lemmas feed extcall_request_ready;
   extcall_call_step and extcall_return_values_owned finish with the real
   protected set.  Send's two or three word operands use the forced-producer
   hypothesis; retain memory, allocation-map and frontier equality across the
   canonical CALL/ASSERT steps when composing send_tail_path.

   intcall_joint_res_frame and intcall_expr_cont_vv_post repackage the final
   certificate.  The global expression root and a copy of its pure induction
   would inherit unrelated aggregate/subscript admission tags. *)
Theorem intcall_extcall_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a tgt args dflt. e = Call a tgt args dflt /\ !nsid. tgt <> IntCall nsid) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
