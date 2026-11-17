(* One-way ghost framing retains a saved memory RHS across a pure target. *)
Theory localMemoryTransportProbe
Ancestors
  targetPurePostTransport bodyPtrArgumentFootprint bodyPtrBopRepresentationFrame
  bodyPtrDefs loweringPosts exprSimMemDefs exprSimProps exprLoweringProps
  context compileEnv venomState words

Theorem target_saved_memory_ptr_transport:
  vv_post H ctx func cenv cx e origin sa sm s0 es raw
    (LocatedValue ty (mk_ptr (Var xs) LocMemory)) s /\
  post_value_type cenv e = ty /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  read_result cx raw es = (INL v,es) /\
  ptr_vv_ok cx ty raw (LocatedValue ty (mk_ptr (Var xs) LocMemory)) es G tn s /\
  ptr_buf_ok cenv e (Var xs) G s /\
  vv_store_bound cx ty lt es raw
    (LocatedValue ty (mk_ptr (Var xs) LocMemory)) s /\
  wb_frame cenv es es sm s u /\
  ghost_kept_at lo cenv es sm G tn s G' tn' /\
  not_fresh_at sm xs /\ lookup_var xs u = lookup_var xs s /\
  s.vs_alloca_next <= u.vs_alloca_next ==>
  ptr_vv_ok cx ty raw (LocatedValue ty (mk_ptr (Var xs) LocMemory)) es G' tn' u /\
  ptr_buf_ok cenv e (Var xs) G' u /\
  vv_store_bound cx ty lt es raw
    (LocatedValue ty (mk_ptr (Var xs) LocMemory)) u
Proof
  strip_tac >>
  `vv_at cenv cx ty sa sm es raw
    (LocatedValue ty (mk_ptr (Var xs) LocMemory)) s` by fs[vv_post_def] >>
  `expr_val_at cenv cx ty sa sm es v (Var xs) s` by
    (drule vv_at_memory_val_at >> simp[mk_ptr_def] >> metis_tac[]) >>
  `val_wf tv v /\ ?sw. lookup_var xs s = SOME sw` by
    (fs[vv_at_def,mk_ptr_def,eval_operand_def] >> metis_tac[]) >>
  `eval_operand (Var xs) s = SOME sw` by simp[eval_operand_def] >>
  `FLOOKUP G' xs = FLOOKUP G xs /\
   op_taint tn' (Var xs) = op_taint tn (Var xs)` by fs[ghost_kept_at_def] >>
  `ptr_mem_ok cx ty v (Var xs) G tn s` by
    (gvs[ptr_vv_ok_def,mk_ptr_def]) >>
  `mem_bytes_at (w2n sw) (val_footprint tv v) u.vs_memory =
   mem_bytes_at (w2n sw) (val_footprint tv v) s.vs_memory` by
    (irule target_saved_value_region_bytes >>
     qexistsl_tac [`ty`,`cenv`,`cx`,`es`,`mk_ptr (Var xs) LocMemory`,
       `raw`,`sa`,`sm`,`ty`] >>
     simp[mk_ptr_def,eval_operand_def]) >>
  `ptr_mem_ok cx ty v (Var xs) G' tn' u` by
    (irule bop_ptr_mem_ok_frame >>
     qexistsl_tac [`G`,`s`,`tn`,`tv`] >> simp[eval_operand_def] >>
     rpt strip_tac >> drule_all pure_argument_taint_kept >> simp[]) >>
  conj_tac
  >- (simp[ptr_vv_ok_def,mk_ptr_def] >>
      fs[ptr_vv_ok_def,mk_ptr_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[ptr_buf_ok_def,eval_operand_def] >> metis_tac[]) >>
  irule vv_store_bound_frame_mem_src >>
  qexists_tac `s` >> simp[vv_operand_def,mk_ptr_def,eval_operand_def]
QED
