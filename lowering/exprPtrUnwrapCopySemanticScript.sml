(* Specialize the shared semantic copy transport to the retained ALLOCA witness. *)
Theory exprPtrUnwrapCopySemantic
Ancestors
  exprPtrUnwrapAllocSemantic exprPtrUnwrapRuntimeFrame exprSimCopy
  exprPtrUnwrapAllocEntry exprPtrUnwrapAllocation exprSimAlloc loweringPosts exprLoweringProps compileEnv context
  venomState venomInst finite_map words arithmetic

Theorem unwrap_copy_semantic_post:
  vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel ctx func cenv cx es' s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
  nb < dimword (:256) /\ 32*n <= nb /\ buf.buf_operand = Var root /\
  u = update_var root d (buffer_allocation_fields s sm.cs_next_id nb) /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ slot_copy_runtime_frame mid d n a z /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  val_wf ty v /\ val_in_memory ty v (w2n d) z.vs_memory /\
  val_footprint ty v <= nb /\ eval_operand op z = SOME d ==>
  expr_post ctx func cenv cx e es sa sb s0 es' v op z
Proof
  strip_tac >> drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  drule_all slot_copy_semantic_frame >> strip_tac >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  `root = STRING #"%" (toString sm.cs_next_var)` by fs[] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    (simp[] >> irule buffer_alloc_code >> goal_assum drule >> simp[]) >>
  qpat_x_assum `u = update_var _ _ _` kall_tac >>
  qpat_x_assum `root = STRING _ _` kall_tac >>
  qpat_x_assum `out = STRING _ _` kall_tac >>
  qpat_x_assum `buf.buf_size = nb` kall_tac >>
  irule copy_buffer_post_transport >> simp[] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]`,
    `mid`, `nb`, `a`] >>
  gvs[mk_inst_def, stmt_state_rel_inst_idx, lookup_var_def, local_region_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
