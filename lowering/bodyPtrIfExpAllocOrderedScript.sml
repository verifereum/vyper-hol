Theory bodyPtrIfExpAllocOrdered
Ancestors
  bodyPtrIfExpAllocResources bodyPtrIfExpAllocSeparation
  bodyPtrIfExpAllocCompiler bodyPtrDefs loweringPosts compileEnv
  exprSimUnwrap venomState finite_map

Theorem compile_alloc_buffer_vv_ordered_frame:
  !D d ctx fn PG G0 tn0 G tn cenv cx e es sa sb s0 es' tv vv s n buf sc.
    post_value_type cenv e = expr_type e /\
    vv_post ctx fn cenv cx e es sa sb s0 es' tv vv s /\
    ghost_inv d cenv cx es' G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
    local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
    n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\ fn_inst_ids_distinct fn /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
    ptr_vv_ok cx (expr_type e) tv vv es' G tn s /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
        ptr_buf_ok cenv e op G s) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G s) ==>
    ?out G1 tn1 t.
      buf.buf_operand = Var out /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
      ptr_covers G1 tn1 out t n /\ ghost_inv d cenv cx es' G1 tn1 t /\
      ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
      vv_post ctx fn cenv cx e es sa sc s0 es' tv vv t /\
      ptr_vv_ok cx (expr_type e) tv vv es' G1 tn1 t /\
      (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
          ptr_buf_ok cenv e op G1 t) /\
      (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G1 t) /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
      t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      lookup_var out t = SOME (n2w (buffer_allocation_base s sb.cs_next_id)) /\
      buffer_allocation_base s sb.cs_next_id + n < dimword (:256) /\
      (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
        off+sz <= buffer_allocation_base s sb.cs_next_id \/
        buffer_allocation_base s sb.cs_next_id+n <= off) /\
      (!name p sz. local_region cenv es.scopes s0 name p sz ==>
        p+sz <= buffer_allocation_base s sb.cs_next_id \/
        buffer_allocation_base s sb.cs_next_id+n <= p) /\
      MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
      FLOOKUP t.vs_allocas sb.cs_next_id = SOME (buffer_allocation_base s sb.cs_next_id,n) /\
      sa.cs_next_id <= sb.cs_next_id /\ sb.cs_next_id < sc.cs_next_id /\
      not_local_ptr cenv es'.scopes out
Proof
  rpt strip_tac >>
  drule_all compile_alloc_buffer_vv_source_frame >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `stmt_state_rel ctx fn cenv cx es' s` by gvs[vv_post_def] >>
  drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[] >>
  `not_local_ptr cenv es'.scopes out` by
    (drule_all compile_alloc_buffer_frame_separation >> simp[]) >>
  `n < dimword (:256)` by decide_tac >>
  `sb.cs_next_id < sc.cs_next_id` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  qexistsl_tac [`G1`, `tn1`, `t`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all ifexp_alloca_original_site_separate >> simp[]) >>
  rpt strip_tac >> drule_all ifexp_alloca_original_local_separate >> simp[]
QED
