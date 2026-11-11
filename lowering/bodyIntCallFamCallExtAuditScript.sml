(* Applicability of the protected external-call stages at a joint entry. *)
Theory bodyIntCallFamCallExtAudit
Ancestors
  bodyIntCallJointContract supportedExprTraverse supportedExprs intCallFrame compileEnv
  bodyIntCallJointCallCore bodyIntCallJointPureCont bodyIntCallJointPurePath
  exprSimAggregateChildren loweringPosts vyperInterpreter exprSimHypsDefs fragGasPath

Theorem intcall_extcall_stage_entry:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  supportedExprs$supported_expr fp.jc_tops
    (Call ann (ExtCall stat skip sig opts) args dflt) ==>
  (!a k. fp.jc_prot a k ==>
     a + k <= s.vs_alloca_next /\
     !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
       regions_disjoint a k b sz) /\
  EVERY (\e. ~expr_has_effect e) args
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      fs[intcall_frame_ok_def, intcall_expr_res_def, allocas_above_def,
         regions_disjoint_def] >> res_tac >> decide_tac) >>
  PairCases_on `sig` >> Cases_on `dflt` >>
  gvs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
      supported_pure_exprs_every, listTheory.EVERY_MEM] >>
  metis_tac[supported_pure_expr_effect_free]
QED

(* Only source-invariant preservation and the protected byte frame are
   call-specific.  The counted execution and ordinary post give the rest. *)
Theorem intcall_vv_counted_endpoint:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  eval_expr fp.jc_cx e es = (res,ee) /\
  expr_sim_inv ce fp.jc_cx env ee /\ ee.immutables = es.immutables /\
  sa.cs_next_var <= sb.cs_next_var /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee tv vv u /\
  gas_path fp.jc_ctx fp.jc_func s n (OK u) /\
  u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!a k. fp.jc_prot a k ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  strip_tac >>
  `allocas_above fp.jc_lo u` by
    (drule gas_path_allocas_above >> gvs[intcall_expr_res_def]) >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    (drule gas_path_alloca_next_mono >> simp[]) >>
  `~u.vs_halted` by (drule gas_path_normal >> simp[]) >>
  `!op. fp.jc_reserved op ==>
     eval_operand op u = eval_operand op fp.jc_oorig` by
    (rpt strip_tac >> irule pure_reserved_operand_frame >>
     qexistsl [`fp.jc_reserved`, `s`, `sa`] >>
     gvs[intcall_frame_ok_def, intcall_expr_res_def, vv_post_def]) >>
  `!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s` by
    (fs[intcall_expr_res_def] >> metis_tac[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa` by gvs[intcall_expr_res_def] >>
  `!name b sz. local_region ce ee.scopes u name b sz ==>
     local_region ce es.scopes s name b sz` by
    (rpt strip_tac >> drule_all vv_post_local_region_backward >> simp[]) >>
  `intcall_expr_res fp ce env ee sb u` by
    (irule bodyIntCallJointCallCoreTheory.intcall_joint_res_frame >>
     simp[] >> reverse conj_tac >- gvs[vv_post_def] >>
     qexistsl [`es`, `s`, `sa`] >> gvs[vv_post_def]) >>
  drule_all intcall_expr_cont_vv_post >> simp[]
QED
