Theory bodyPtrIfExpNonwordSuffix
Ancestors
  bodyPtrIfExpOldUnwrapPath bodyPtrIfExpResidualAllocate
  bodyPtrIfExpObservationFrame bodyPtrDefs bodySim exprSimHyps
  exprSimHypsDefs exprSimDefs exprLoweringProps exprLowering
  exprSimUnwrap loweringPosts allocLimits vyperState vyperAST vyperTypeSystem
  exprOperandVar

Theorem ifexp_expr_post_same_type:
  expr_type e = expr_type f ==>
  (expr_post ctx fn ce cx e es sa sb s0 ee v op s <=>
   expr_post ctx fn ce cx f es sa sb s0 ee v op s)
Proof
  simp[expr_post_def]
QED

Theorem ifexp_nonword_arm_suffix:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (IfExp ty c a b) es_outer /\
  (arm = a \/ arm = b) /\ expr_body_pre ce cx env_arm arm es /\
  ~is_word_type ty /\ ~ce.ce_is_ctor /\
  compile_expr ce (expr_type arm) arm sa = (vv,sm) /\
  compile_ifexp_arm ce ty (lowered_value_type ce arm) vv sm = (op,sd) /\
  eval_expr cx arm es = (INL raw,ee) /\ read_result cx raw ee = (INL v,ee) /\
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx arm es sa sm s0 ee raw vv s /\
  ptr_vv_ok cx (expr_type arm) raw vv ee G tn s /\
  (!tag src. vv = StackValue tag src /\ ~is_word_type (expr_type arm) ==>
    ptr_buf_ok ce arm src G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce arm p.ptr_operand G s) /\
  ghost_inv d ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_has_code sm sd fn /\ fn_inst_ids_distinct fn /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u H tt. gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK u) /\
    expr_post ctx fn ce cx arm es sa sd s0 ee v op u /\
    ptr_val_ok cx ty v op H tt u /\ ptr_buf_ok ce (IfExp ty c a b) op H u /\
    ghost_inv d ce cx ee H tt u /\ ghost_kept ce es sa G0 tn0 s0 H tt /\
    u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type arm = ty` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  Cases_on `same_memory_layout ce (lowered_value_type ce arm) ty`
  >- suspend "same" >>
  drule_all ifexp_residual_allocating_arm_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`q`, `Gf`, `tnf`] >> simp[] >>
  metis_tac[ifexp_expr_post_same_type, expr_type_def]
QED

Resume ifexp_nonword_arm_suffix[same]:
  `unwrap_value ce vv sm = (op,sd)` by
    gvs[compile_ifexp_arm_def] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    metis_tac[compile_expr_extends] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `!tv. evaluate_type (get_tenv cx) (expr_type arm) = SOME tv ==>
    type_memory_bytes ce (expr_type arm) = type_memory_size tv /\
    type_memory_size tv < 2**64` by suspend "size" >>
  `~is_word_type (expr_type arm)` by metis_tac[] >>
  `!tag src. vv = StackValue tag src ==> ptr_buf_ok ce arm src G s` by metis_tac[] >>
  drule_all ifexp_old_unwrap_nonword_path_capacity >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `H`, `tt`] >> simp[] >>
  gvs[ptr_buf_ok_def, lowered_value_type_def, expr_type_def]
QED

Resume ifexp_nonword_arm_suffix[size]:
  rpt strip_tac >>
  drule_all bodyPtrIfExpBytesInputsTheory.ifexp_arm_annotation_typed >> strip_tac >>
  `type_alloc_ok ce (expr_type arm)` by
    (irule alloc_limits_expr_type_alloc_ok >> gvs[expr_body_pre_def]) >>
  gvs[type_alloc_ok_def]
QED

Finalise ifexp_nonword_arm_suffix
