(* Seam 2 joint induction, a family leaf of the call step: every other call target (external calls and send; the rest are not supported_expr). *)
Theory bodyIntCallFamCallExt
Ancestors
  bodyIntCallJointContract bodyIntCallJointCallCore bodyIntCallJointPurePath
  exprExtRequestHistory extcallProtFramePath

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
