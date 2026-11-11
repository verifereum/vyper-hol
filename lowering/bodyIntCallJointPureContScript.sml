(* Effect-free endpoint transport for the joint resource invariant. *)
Theory bodyIntCallJointPureCont
Ancestors
  bodyIntCallJointContract bodyIntCallJointPurePath bodyIntCallJointPureSourceInv
  bodyIntCallJointPureSource exprSimExtCallCase exprSimAggregateChildren
  loweringPosts exprLoweringProps stmtSimProps bodyMemoryDefs
  venomState compileEnv loweringStateRelDefs intCallFrame exprSimHypsDefs fragGasPath

Theorem pure_reserved_operand_frame:
  (!op. reserved op ==> ?x w. op = Var x /\ lookup_var x origin = SOME w) /\
  (!op. reserved op ==> eval_operand op s = eval_operand op origin) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x u = SOME w) ==>
  !op. reserved op ==> eval_operand op u = eval_operand op origin
Proof
  strip_tac >> rpt strip_tac >>
  `?x w. op = Var x /\ lookup_var x origin = SOME w` by metis_tac[] >>
  gvs[eval_operand_def] >>
  qpat_x_assum `!op. reserved op ==> eval_operand op s = _`
    (qspec_then `Var x` mp_tac) >>
  simp[eval_operand_def] >> strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem pure_vv_post_protected:
  intcall_frame_ok fp /\ allocas_above fp.jc_lo u /\
  vv_post ctx func ce cx e es sa sb s ee tv vv u /\ ~expr_has_effect e /\
  fp.jc_prot a k ==>
  mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory
Proof
  strip_tac >> drule_all vv_post_pure_memory_frame >> strip_tac >>
  first_x_assum irule >> rpt strip_tac >>
  gvs[intcall_frame_ok_def, allocas_above_def, regions_disjoint_def] >>
  res_tac >> decide_tac
QED

Theorem pure_vv_post_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  ~expr_has_effect e /\ eval_expr fp.jc_cx e es = (res,ee) /\
  sa.cs_next_var <= sb.cs_next_var /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee tv vv u /\
  gas_path fp.jc_ctx fp.jc_func s n (OK u) /\
  u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  strip_tac >>
  `allocas_above fp.jc_lo u` by
    (drule gas_path_allocas_above >>
     gvs[intcall_joint_res_def, intcall_expr_res_def]) >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    (drule gas_path_alloca_next_mono >> simp[]) >>
  `~u.vs_halted` by (drule gas_path_normal >> simp[]) >>
  `expr_sim_inv ce fp.jc_cx env ee` by
    (irule effect_free_eval_expr_sim_inv >>
     qexistsl [`e`, `es`, `res`] >> gvs[intcall_joint_res_def, intcall_expr_res_def]) >>
  `ee with <|gas_obs := []; outcomes := NONE|> =
   es with <|gas_obs := []; outcomes := NONE|>` by
    (irule effect_free_eval_expr_frame >> qexistsl [`fp.jc_cx`, `e`, `res`] >> simp[]) >>
  `!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op fp.jc_oorig` by
    (rpt strip_tac >> irule pure_reserved_operand_frame >>
     qexistsl [`fp.jc_reserved`, `s`, `sa`] >>
     gvs[intcall_frame_ok_def, intcall_joint_res_def, intcall_expr_res_def, vv_post_def]) >>
  `!a k. fp.jc_prot a k ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory` by
    (rpt strip_tac >> drule_all pure_vv_post_protected >> simp[]) >>
  simp[intcall_expr_cont_def] >> reverse conj_tac
  >- (gvs[vv_post_def] >> metis_tac[]) >>
  `!nm b sz. local_region ce ee.scopes u nm b sz ==>
     local_region ce es.scopes s nm b sz` by
    (rpt strip_tac >> fs[intcall_joint_res_def, intcall_expr_res_def] >>
     drule_all vv_post_local_region_backward >> simp[]) >>
  fs[intcall_joint_res_def, intcall_expr_res_def, vv_post_def] >>
  `ee.scopes = es.scopes /\ ee.immutables = es.immutables` by
    (qpat_x_assum `_ with <|outcomes := NONE; gas_obs := []|> = _` mp_tac >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  simp[intcall_joint_res_def, intcall_expr_res_def] >>
  conj_tac >- (drule_all local_ptrs_reserved_next_var >> simp[]) >>
  conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (fs[intcall_frame_ok_def] >> metis_tac[]) >>
  conj_tac >- (irule ret_pc_ok_frame >> qexistsl [`ce`, `s`, `sa`] >> simp[]) >>
  conj_tac >- (irule return_buf_frame_frame >> qexistsl [`ce`, `s`, `sa`] >> simp[]) >>
  metis_tac[]
QED
