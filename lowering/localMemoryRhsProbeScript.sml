(* Memory RHS resources at a transported joint expression endpoint. *)
Theory localMemoryRhsProbe
Ancestors
  bodyPtrDefs loweringPosts exprSimMemDefs exprSimProps exprLoweringProps
  compileEnv context exprLowering venomState words arithmetic

Theorem memory_rhs_store_resources:
  vv_post H ctx func cenv cx e origin start sa s0 es raw
    (LocatedValue ty (mk_ptr (Var xs) LocMemory)) s /\
  post_value_type cenv e = ty /\ lowered_value_type cenv e = ty /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  read_result cx raw es = (INL v,es) /\
  ptr_vv_ok cx ty raw (LocatedValue ty (mk_ptr (Var xs) LocMemory)) es G tn s /\
  ptr_buf_ok cenv e (Var xs) G s /\
  vv_store_bound cx ty ty es raw
    (LocatedValue ty (mk_ptr (Var xs) LocMemory)) s /\
  0 < type_memory_size tv ==>
  ?sw.
    lookup_var xs s = SOME sw /\ val_wf tv v /\
    expr_val_at cenv cx ty start sa es v (Var xs) s /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n sw) mem) /\
    ptr_covers G tn xs s (type_memory_size tv) /\
    w2n sw+type_memory_size tv <= s.vs_alloca_next /\
    w2n sw+type_memory_size tv < dimword (:256) /\
    unwrap_value cenv (LocatedValue ty (mk_ptr (Var xs) LocMemory)) sa =
      (Var xs,sa)
Proof
  strip_tac >>
  `vv_at cenv cx ty start sa es raw
    (LocatedValue ty (mk_ptr (Var xs) LocMemory)) s` by fs[vv_post_def] >>
  `expr_val_at cenv cx ty start sa es v (Var xs) s` by
    (drule vv_at_memory_val_at >> simp[mk_ptr_def] >> metis_tac[]) >>
  `val_wf tv v /\ ?sw. lookup_var xs s = SOME sw` by
    (fs[vv_at_def,mk_ptr_def,eval_operand_def] >> metis_tac[]) >>
  `ptr_covers G tn xs s (type_memory_size tv)` by
    (gvs[ptr_vv_ok_def,ptr_mem_ok_def,ptr_buf_ok_def,ptr_covers_def,
        mk_ptr_def,eval_operand_def] >> metis_tac[]) >>
  qexists_tac `sw` >>
  simp[unwrap_value_def,mk_ptr_def,comp_return_def] >>
  gvs[ptr_vv_ok_def,ptr_mem_ok_def,vv_store_bound_def,mk_ptr_def,
     eval_operand_def] >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt,stmt_state_rel_def,vv_post_def] >>
  res_tac >> decide_tac
QED
