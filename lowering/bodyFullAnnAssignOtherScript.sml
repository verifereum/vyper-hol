(* Source-layout-equality preparation for the joint aggregate declaration. *)
Theory bodyFullAnnAssignOther
Ancestors
  bodySimFull bodyFullPreds bodyFullAllocaFresh bodyFullUnwrap
  annassignRelayoutSource memoryLocalRhsProps exprSimHyps exprSimHypsDefs
  stmtSimDeclTypedCode stmtSimDeclSourceSeparation externalNormalizePremises
  assignBasePtrBoundary
  exprOperandVar bodyPtrDefs exprSimMemDefs loweringPosts
  vyperTypeValues vyperTypeInvariants vyperTypeExprSoundness valueTypingMemoryProps
  compileEnv exprLowering stmtLowering vyperInterpreter vyperState
  vyperValue vyperAST finite_map list
Libs monadsyntax

Theorem annassign_other_typed_layout:
  expr_body_pre ce cx env e es /\ env.type_defs = get_tenv cx /\
  type_widens_to env.type_defs (expr_type e) typ /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  evaluate_type (get_tenv cx) typ = SOME dtv /\
  ~is_word_type typ /\ ~is_bytestring_type typ /\ expr_type e <> typ /\
  lowered_value_type ce e = expr_type e /\
  type_memory_bytes ce typ < 2 ** 64 ==>
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  post_value_type ce e = expr_type e /\
  type_memory_bytes ce (expr_type e) = type_memory_size stv /\
  type_memory_bytes ce typ = type_memory_size dtv /\
  0 < type_memory_size stv /\
  type_memory_size stv <= type_memory_size dtv /\
  type_memory_size stv < dimword (:256) /\
  (!gs v mid. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gs) = (INL v,mid) ==>
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    val_footprint stv v = type_memory_size stv)
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[normalize_return_source_kinds] >>
  `0 < type_memory_size stv` by metis_tac[normalize_return_source_positive] >>
  `type_widens_to (get_tenv cx) (expr_type e) typ` by metis_tac[] >>
  drule_all widening_memory_layout_bound >> strip_tac >>
  simp[post_value_type_lowered] >> rpt gen_tac >> strip_tac >>
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  `value_runtime_typed env (expr_type e) v /\ value_runtime_typed env typ v` by
    metis_tac[memory_rhs_read_annotation_typed, memory_rhs_read_destination_typed] >>
  `value_has_type stv v /\ value_has_type dtv v` by
    gvs[value_runtime_typed_def] >>
  simp[value_has_type_memory_wf] >>
  metis_tac[normalize_nonbytes_footprint]
QED

(* Adapt the actual nonbytes RHS, including a source in a live local, to
   the shared aggregate suffix.  Source and destination widths stay distinct. *)
Theorem annassign_other_typed_rhs_resources:
  lowered_value_type ce e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  type_memory_bytes ce (expr_type e) = type_memory_size stv /\
  0 < type_memory_size stv /\ value_has_type stv v /\
  expr_post H ctx func ce cx e es sa sb s0 mid v op s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  ptr_buf_ok ce e op G s /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sb) /\
  local_ptrs_reserved ce sa /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
  not_local_ptr ce mid.scopes p /\
  (inst.inst_id < sa.cs_next_id \/ sb.cs_next_id <= inst.inst_id) /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
  type_memory_size dtv <= sz ==>
  ?xs sw.
    op = Var xs /\ lookup_var xs s = SOME sw /\ not_fresh_at sb xs /\
    ptr_covers G tn xs s (type_memory_size stv) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory stv v (w2n sw) mem) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    (type_memory_size stv = 0 \/
      w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
    expr_val_at ce cx (expr_type e) sa sb mid v (Var xs) s /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw)
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `stmt_state_rel H ctx func ce cx mid s /\
   expr_val_at ce cx (expr_type e) sa sb mid v op s` by fs[expr_post_def] >>
  drule_all normalize_source_window >> strip_tac >> gvs[] >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  `?xs. op = Var xs /\ ptr_covers G tn xs s (type_memory_size stv)` by
    metis_tac[ptr_buf_ok_read_covers, arithmeticTheory.LESS_EQ_REFL] >>
  gvs[] >>
  `not_fresh_at sb xs` by metis_tac[compile_lower_value_var] >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[normalize_nonbytes_footprint] >>
  `0 < val_footprint stv v` by simp[] >>
  `w2n w + type_memory_size stv <= w2n dw \/ w2n dw+sz <= w2n w` by
    metis_tac[expr_val_at_alloca_outside_interval_separate] >>
  qexists_tac `w` >>
  fs[venomStateTheory.eval_operand_def, ptr_val_ok_def, ptr_mem_ok_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_MONO_ADD_EQ]
QED
