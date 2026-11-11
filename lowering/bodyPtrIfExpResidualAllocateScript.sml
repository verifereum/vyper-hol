Theory bodyPtrIfExpResidualAllocate
Ancestors
  bodyPtrIfExpResidualBytes bodyPtrIfExpResidual bodyPtrIfExpAllocCaller
  bodyPtrIfExpBytesAllocate bodyPtrIfExpBytesInputs bodyPtrIfExpUnwrapNoop
  bodyPtrDefs bodySim exprSimHypsDefs exprSimDefs exprLoweringProps
  exprLowering compileEnv fragExec vyperTypeSystem allocLimits vyperState exprSimUnwrap
  valueCopyBytes words context vyperAST

Theorem ifexp_residual_allocating_arm_ptr:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (IfExp ty cond a b) es_outer /\
  (arm = a \/ arm = b) /\ expr_body_pre ce cx env_arm arm es /\
  (int_calls_expr arm = [] \/
   same_memory_layout ce (lowered_value_type ce arm) (expr_type arm)) /\
  post_value_type ce arm = expr_type arm /\
  compile_expr ce rty arm sa = (vv,sb) /\
  eval_expr cx arm es = (INL raw,ee) /\ read_result cx raw ee = (INL v,er) /\
  ~is_word_type ty /\ ~same_memory_layout ce (lowered_value_type ce arm) ty /\
  compile_ifexp_arm ce ty (lowered_value_type ce arm) vv sb = (op,sd) /\
  fn_has_code sb sd fn /\ vv_post ctx fn ce cx arm es sa sb s0 ee raw vv s /\
  stmt_state_rel ctx fn ce cx es s0 /\ ghost_inv d ce cx ee G tn s /\
  ghost_kept ce es sa G0 tn0 s0 G tn /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ fn_inst_ids_distinct fn /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (expr_type arm) raw vv ee G tn s /\
  (!tag src. vv = StackValue tag src /\ ~is_word_type (expr_type arm) ==>
    ptr_buf_ok ce arm src G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce arm p.ptr_operand G s) ==>
  ?Gf tnf q.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK q) /\
    expr_post ctx fn ce cx (IfExp ty cond a b) es sa sd s0 ee v op q /\
    (~expr_has_effect arm ==> pure_frame ce fn es sa s0 q) /\
    ghost_inv d ce cx ee Gf tnf q /\ ghost_kept ce es sa G0 tn0 s0 Gf tnf /\
    ptr_val_ok cx ty v op Gf tnf q /\ ptr_buf_ok ce (IfExp ty cond a b) op Gf q /\
    q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts /\
    ~q.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `er = ee` by metis_tac[read_result_state] >>
  qpat_x_assum `er = ee` SUBST_ALL_TAC >>
  `expr_type arm = ty /\ type_alloc_ok ce ty` by
    gvs[expr_body_pre_def, well_typed_expr_def, alloc_limits_expr_def] >>
  drule_all ifexp_allocating_arm_bytes_inputs >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `tv` (qx_choose_then `len`
      (map_every assume_tac o CONJUNCTS)))) >>
  drule_all ifexp_arm_annotation_typed >> strip_tac >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (qpat_x_assum `evaluate_type _ (expr_type arm) = _` mp_tac >>
     simp[] >> strip_tac >> gvs[]) >>
  `val_footprint tv v <= type_memory_bytes ce ty` by
    (drule_all bytestring_val_footprint_le >> simp[]) >>
  `type_memory_bytes ce ty < dimword(:256)` by
    (gvs[type_alloc_ok_def, dimword_def] >> decide_tac) >>
  drule_all ifexp_selected_arm_allocation_premises >> strip_tac >>
  drule_all ifexp_allocating_noop_representation >> disch_tac >>
  suspend "apply"
QED

Resume ifexp_residual_allocating_arm_ptr[apply]:
  `sn = sc /\ src = vv_operand vv` by metis_tac[unwrap_value_noop_endpoint] >>
  `unwrap_value ce vv sc = (vv_operand vv,sc)` by metis_tac[] >>
  `compile_store_bytestring (vv_operand vv) buf.buf_operand sc = ((),sd)` by
    gvs[compile_store_memory_def] >>
  `fn_has_code sc sd fn` by
    (`cs_extends sb sc` by
       metis_tac[ci_mono_compile_alloc_buffer, ci_mono_def, pairTheory.SND] >>
     `cs_extends sc sd` by
       metis_tac[ci_mono_compile_store_memory, ci_mono_def, pairTheory.SND] >>
     drule_all fn_has_code_split >> simp[]) >>
  `is_bytestring_type (expr_type arm) /\
   evaluate_type (get_tenv cx) (expr_type arm) = SOME tv` by
    (qpat_x_assum `evaluate_type _ (expr_type arm) = _` kall_tac >> simp[]) >>
  `val_store_size tv v <= type_memory_bytes ce ty` by decide_tac >>
  `is_bytestring_type (expr_type (IfExp ty cond a b)) /\
   evaluate_type (get_tenv cx) (expr_type (IfExp ty cond a b)) = SOME tv /\
   type_memory_bytes ce (lowered_value_type ce (IfExp ty cond a b)) <= type_memory_bytes ce ty` by
    simp[expr_type_def, lowered_value_type_def] >>
  `post_value_type ce (IfExp ty cond a b) = expr_type (IfExp ty cond a b)` by
    simp[loweringPostsTheory.post_value_type_def] >>
  `~expr_has_effect (IfExp ty cond a b) ==> ~expr_has_effect arm` by
    (rewrite_tac[loweringPostsTheory.expr_has_effect_thm, DE_MORGAN_THM] >>
     strip_tac >>
     qpat_assum `arm = a \/ arm = b` (DISJ_CASES_THEN SUBST1_TAC) >>
     first_assum ACCEPT_TAC) >>
  drule_all ifexp_allocate_unwrap_bytes >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `q`] >> gvs[expr_type_def]
QED

Finalise ifexp_residual_allocating_arm_ptr
