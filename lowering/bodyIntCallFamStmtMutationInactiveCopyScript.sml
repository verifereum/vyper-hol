(* Allocation-preserving writes to an inactive allocation retain expression resources. *)
Theory bodyIntCallFamStmtMutationInactiveCopy
Ancestors
  bodyIntCallJointAggCore bodyIntCallJointContract exprSimCopy
  exprSimStorageCopy placeMemoryCopyEffect compileEnv venomState

Theorem intcall_inactive_copy_resources:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  typed_copy_effect fp.jc_ctx fp.jc_func sa sb s t dst n /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  fp.jc_lo <= b /\ b <= dst /\ dst+n <= b+k /\
  (!name a z. local_region ce es.scopes s name a z ==>
     regions_disjoint b k a z) /\
  sa.cs_next_var <= sb.cs_next_var ==>
  intcall_expr_res fp ce env es sb t
Proof
  strip_tac >>
  `typed_copy_effect fp.jc_ctx fp.jc_func sa sb s t b k` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
  `copy_static t = copy_static s` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality, copy_static_def]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es t` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl [`b`, `inst`, `s`, `sa`, `k`] >>
     fs[intcall_expr_res_def, typed_copy_effect_def, regions_disjoint_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule intcall_joint_res_copy >>
  qexistsl [`dst`, `n`, `s`, `sa`] >> simp[] >>
  fs[intcall_frame_ok_def, regions_disjoint_def] >> rpt strip_tac >>
  qpat_x_assum `!a k. fp.jc_prot a k ==> a + k <= fp.jc_lo` drule >>
  decide_tac
QED
