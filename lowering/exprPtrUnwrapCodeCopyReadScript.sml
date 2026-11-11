(* Runtime aggregate forcing composes a counted copy with the semantic endpoint. *)
Theory exprPtrUnwrapCodeCopyRead
Ancestors
  exprPtrUnwrapCodeCopyShape exprPtrUnwrapCodeCopyExecution
  exprPtrUnwrapCodeCopyRetained exprPtrUnwrapCodeCopySemantic exprPtrCleanBufferPost
  exprPtrCodeCopyEndpoint exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocSeparation
  exprPtrUnwrapAllocation exprPtrUnwrapCode exprPtrUnwrapCodeEdges exprSimCopy exprSimUnwrapProps exprSimUnwrap
  exprLoweringProps exprSimAlloc bodyPtrDefs loweringPosts compileEnv loweringStateRelDefs context words arithmetic finite_map
  gasSummaryComposePtr gasSummary vyperState venomState exprSimMemorySource

Theorem unwrap_code_ensure_marked_read_ptr:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  compile_ensure_in_memory p.ptr_operand LocCode nb n F imm sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!ty. evaluate_type (get_tenv cx) t = SOME ty ==>
    type_memory_bytes cenv t = type_memory_size ty) /\
  evaluate_type (get_tenv cx) t = SOME ty /\ val_wf ty v /\
  nb = type_memory_size ty /\ 32*((nb+31) DIV 32) = nb /\ nb < dimword (:256) /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= nb /\
  ptr_vv_ok cx (post_value_type cenv e) (Value v) (LocatedValue t p) ee G tn s /\
  ghost_inv ret cenv cx ee G tn s /\ ghost_kept cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?H tf z.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx (Value v))
      (ee,s,G,tn) [] (INL v) ee H tf (OK z) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv ret cenv cx ee H tf z /\
    ptr_val_ok cx (post_value_type cenv e) v op H tf z /\ ptr_buf_ok cenv e op H z /\
    ghost_kept cenv es sa Gi ti s0 H tf
Proof
  strip_tac >> drule_all vv_post_code_source >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  drule_all ensure_runtime_code_layout >> strip_tac >>
  `32*((nb+31) DIV 32) <= nb` by simp[] >>
  drule_all unwrap_runtime_code_execution >>
  disch_then (qspecl_then [`PG`, `G`, `cx_dead cx`] strip_assume_tac) >>
  rename1 `copy_runtime_frame mid alloc sb z` >>
  `expr_post ctx func cenv cx e es sa sb s0 ee v op z` by
    (irule unwrap_code_copy_endpoint_post >>
     ntac 4 (conj_tac >- simp[]) >>
     goal_assum (drule_at (Pat `copy_runtime_frame _ _ _ _`)) >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
     qexistsl [`SUC s.vs_inst_idx`, `root`] >> simp[]) >>
  drule_all unwrap_alloc_site_bound >> disch_tac >>
  `buffer_allocation_base s sm.cs_next_id < dimword (:256)` by decide_tac >>
  `u = update_var root (n2w (buffer_allocation_base s sm.cs_next_id))
    (buffer_allocation_fields s sm.cs_next_id nb)` by
    (drule_all unwrap_alloc_generated_step >> strip_tac >> gvs[]) >>
  drule unwrap_alloc_runtime_frame >>
  disch_then (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  qpat_assum `alloc = _` (fn th => rewrite_tac[GSYM th]) >>
  strip_tac >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    (drule_all buffer_alloc_code >> strip_tac >>
     drule unwrap_alloc_generated_code >> strip_tac >> gvs[]) >>
  drule_all unwrap_alloc_taint_frame >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  `tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    metis_tac[] >>
  `ptr_val_ok cx (post_value_type cenv e) v op H tf z /\ ptr_buf_ok cenv e op H z` by
    suspend "pointer" >>
  qexistsl [`H`, `tf`, `z with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  rpt conj_tac
  >- (simp[gas_marked_exec_ptr_def, gas_explicit_def] >>
      metis_tac[read_result_gas_obs, read_result_def, return_def])
  >- suspend "semantic"
  >- simp[]
  >- simp[]
  >- suspend "ghost"
  >- suspend "value"
  >- suspend "buffer"
  >> suspend "retained"
QED

Resume unwrap_code_ensure_marked_read_ptr[semantic]:
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[expr_post_def, stmt_state_rel_inst_idx, expr_val_rel_def,
    expr_val_at_def, expr_val_own_def, lookup_var_def, local_region_def, locals_kept_def] >>
  tautLib.TAUT_TAC
QED

Resume unwrap_code_ensure_marked_read_ptr[ghost]:
  `ghost_inv ret cenv cx ee H tf z` by
    (irule unwrap_code_ghost_inv >>
     goal_assum (drule_at (Pat `copy_runtime_frame _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
     goal_assum (drule_at (Pat `_ = step_prov _ _ _ _`)) >>
     goal_assum (drule_at (Pat `_ = step_taint _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `alloc = _`)) >>
     qexistsl [`d`, `((nb+31) DIV 32)`, `sa`] >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `ghost_inv ret cenv cx ee H tf z` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[ghost_inv_def, ptr_covers_def, return_buf_ptr_def, stor_taint_ok_def,
    lookup_var_def] >> Cases_on `ret`
  >- (simp[return_buf_ptr_def] >> tautLib.TAUT_TAC) >>
  rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
  simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def] >> tautLib.TAUT_TAC
QED

Resume unwrap_code_ensure_marked_read_ptr[pointer]:
  `eval_operand (Var root) z = SOME d` by
    (drule_all allocated_copy_operands_old >> strip_tac >>
     fs[copy_runtime_frame_def, eval_operand_def]) >>
  `!i. w2n d <= i /\ i < w2n d+nb ==> i NOTIN tf.t_mem` by
    (qpat_x_assum `tf.t_mem = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `op = Var root` by metis_tac[] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[] >> disch_tac >> asm_rewrite_tac[] >>
  irule clean_buffer_pointer_posts >>
  (conj_tac >- metis_tac[]) >>
  (reverse conj_tac >-
    (goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)))) >>
  qexistsl [`nb`, `ty`, `d`] >> simp[] >> metis_tac[]
QED

Resume unwrap_code_ensure_marked_read_ptr[value]:
  qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def, lookup_var_def]
QED

Resume unwrap_code_ensure_marked_read_ptr[buffer]:
  qpat_x_assum `ptr_buf_ok _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[ptr_buf_ok_def, eval_operand_def, lookup_var_def]
QED

Resume unwrap_code_ensure_marked_read_ptr[retained]:
  irule unwrap_code_retained_post >>
  (conj_tac >- simp[]) >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `copy_runtime_frame _ _ _ _`)) >>
  goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  goal_assum (drule_at (Pat `_ = step_prov _ _ _ _`)) >>
  goal_assum (drule_at (Pat `_ = step_taint _ _ _ _`)) >>
  qexistsl [`d`, `SUC s.vs_inst_idx`, `((nb+31) DIV 32)`] >> asm_rewrite_tac[]
QED

Finalise unwrap_code_ensure_marked_read_ptr
