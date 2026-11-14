(* Resource boundary and expression/store composition for joint copies. *)
Theory fullAssignCopyCompose
Ancestors
  fullAssignCopyFacts bodySimFull gasOutcomeFullCompose
  assignBasePtrBoundary exprOperandVar
  exprSimTypedAlloc bodyPtrDefs loweringPosts exprSimMemDefs
  stmtSimDefs exprSimDefs loweringStateRelDefs ptrDiscipline venomState
  valueEncodingProps exprLowering exprLoweringProps compileEnv words arithmetic
Libs monadsyntax

Theorem topcopy_store_entry_resources:
  lowered_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
  0 < type_memory_size tv /\
  expr_post H ctx func cenv cx e es sa sb s0 ee v op s /\
  expr_store_bound cx (expr_type e) v op s /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn s /\
  ptr_buf_ok cenv e op G s /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  local_ptrs_reserved cenv sa ==>
  ?root w.
    op = Var root /\ lookup_var root s = SOME w /\
    not_fresh_at sb root /\
    ptr_covers G tn root s (val_store_size tv v) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem) /\
    w2n w + type_memory_size tv < dimword(:256) /\
    w2n w + val_store_size tv v <= s.vs_alloca_next /\
    op_prov G (Lit slot) = NONE /\ op_taint tn (Lit slot) = {} /\
    eval_operand (Lit slot) s = SOME slot /\
    ~s.vs_call_ctx.cc_static
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by simp[post_value_type_lowered] >>
  `val_store_size tv v = type_memory_size tv` by
    metis_tac[topcopy_val_store_size] >>
  `val_footprint tv v = type_memory_size tv` by
    metis_tac[assign_base_nonbytes_footprint] >>
  `?w. eval_operand op s = SOME w` by
    fs[expr_post_def, expr_val_rel_def] >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  `0 < type_memory_bytes cenv (lowered_value_type cenv e)` by simp[] >>
  `val_store_size tv v <= type_memory_bytes cenv (lowered_value_type cenv e)` by simp[] >>
  drule_all assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
  strip_tac >> gvs[] >>
  qexists_tac `w` >>
  simp[op_taint_def, eval_operand_def] >> rpt conj_tac
  >- fs[eval_operand_def]
  >- metis_tac[compile_lower_value_var]
  >- (gvs[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def])
  >- (fs[expr_post_def] >> drule_all expr_val_at_bound >> simp[])
  >- (fs[expr_store_bound_def, eval_operand_def] >>
      first_x_assum (qspec_then `tv` mp_tac) >> simp[ADD_COMM]) >>
  fs[expr_post_def, stmt_state_rel_def, state_rel_def]
QED
