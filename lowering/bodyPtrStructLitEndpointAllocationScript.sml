Theory bodyPtrStructLitEndpointAllocation
Ancestors bodyPtrStructLitAllocationBridge exprSimAlloc localPtrsProps
  loweringPosts exprLoweringProps compileEnv emitHelper finite_map words
  venomInst venomState fragExec

Theorem structlit_alloc_buffer_nonlocal:
  compile_alloc_buffer N sa = (buf,sb) /\ buf.buf_operand = Var root /\
  local_ptrs_reserved ce sa ==> not_local_ptr ce scopes root
Proof
  strip_tac >> drule structlit_alloc_buffer_cursor >> strip_tac >>
  `~not_fresh_at sa root` by gvs[not_fresh_at_def] >>
  gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem structlit_expr_post_allocated:
  expr_post ctx fn ce cx e es sb su t ee v value s1 /\
  FLOOKUP t.vs_allocas aid = SOME (b,N) ==>
  FLOOKUP s1.vs_allocas aid = SOME (b,N)
Proof
  simp[expr_post_def] >> metis_tac[]
QED

(* Distinct IDs are an enclosing expr_sim/expr_vv_sim input, not a
   consequence of stmt_state_rel. The binding is the actual producer output. *)
Theorem structlit_endpoint_allocation_disjoint:
  compile_alloc_buffer N sa = (buf,sb) /\ buf.buf_operand = Var root /\
  local_ptrs_reserved ce sa /\ fn_has_code sa sb fn /\
  fn_inst_ids_distinct fn /\
  expr_post ctx fn ce cx e es sb su t ee v value s1 /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,N) /\
  local_region ce ee.scopes s1 name lo sz ==>
  regions_disjoint b N lo sz
Proof
  strip_tac >>
  `not_local_ptr ce ee.scopes root` by
    (irule structlit_alloc_buffer_nonlocal >> metis_tac[]) >>
  `FLOOKUP s1.vs_allocas sa.cs_next_id = SOME (b,N)` by
    (irule structlit_expr_post_allocated >> metis_tac[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)` by
    (irule buffer_alloc_code >> metis_tac[]) >>
  drule structlit_alloc_buffer_cursor >> strip_tac >>
  gvs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  irule local_ptrs_rel_alloca_disjoint >>
  goal_assum (drule_at Any) >> simp[mk_inst_def] >> metis_tac[]
QED
