Theory bodyPtrBytestringBuiltinsBuffer
Ancestors
  bodyPtrBytestringBuiltinsAllocation loweringHalt emitHelperProps
  context emitHelper compileEnv fragExec venomInst list
  normalizationAllocPtr loweringPosts builtinBytes bodyPtrDefs
  exprSimLiteralBuffer exprSimPtrLiteralBuffer exprLoweringProps

Theorem compile_alloc_buffer_counted_edge_covers:
  compile_alloc_buffer n sa = (buf,sb) /\ buf.buf_operand = Var out /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
  ptr_covers
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)
    out (u with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  rpt gen_tac >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]]` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out])
     (fn_insts func)` by
    (irule lookup_block_fn_insts >> qexists_tac `bb` >> simp[] >>
     gvs[get_instruction_def] >> metis_tac[MEM_EL]) >>
  irule alloca_counted_edge_covers >> metis_tac[]
QED

(* The resource interface supplies successful execution; the counted edge
   retains its ghost endpoint rather than erasing the allocation step. *)
Theorem compile_alloc_buffer_expr_counted:
  expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
  fresh_vars_wrt sb s /\ fn_inst_ids_distinct func /\
  compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc func /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ val_wf tv v /\ n < dimword (:256) /\
  eval_operand op s = SOME w /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n w) m) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?out u G1 tn1.
    buf.buf_operand = Var out /\
    step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    G1 = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u /\
    tn1 = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn /\
    gas_path_ptr_edge D 0 ctx func PG G tn s 0 G1 tn1
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
    ptr_covers G1 tn1 out (u with vs_inst_idx := SUC s.vs_inst_idx) n /\
    (!p k. ptr_covers G tn p s k ==> ptr_covers G1 tn1 p u k) /\
    (!m. mem_agree_outside tn1.t_mem u.vs_memory m ==>
      val_in_memory tv v (w2n w) m) /\
    (stor_taint_ok cx tn s ==> stor_taint_ok cx tn1 u)
Proof
  strip_tac >>
  drule_all compile_alloc_buffer_expr_resources >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx es' s` by fs[expr_post_def] >>
  qpat_x_assum `i = _` SUBST_ALL_TAC >>
  drule_all compile_alloc_buffer_counted_edge_covers >> strip_tac >>
  qexistsl_tac [`out`, `s1`, `G1`, `tn1`] >> gvs[]
QED

Theorem emit_pointer_offset_counted_covers:
  !root off sa out sb func ctx s a G tn total n D PG.
  emit_op ADD [Var root; Lit (n2w off)] sa = (Var out,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s total /\
  off + n <= total /\ w2n a + off < dimword (:256) ==>
  gas_path_ptr_edge D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn)
    (OK ((update_var out (a + n2w off) s) with vs_inst_idx := SUC s.vs_inst_idx)) /\
  ptr_covers
    (step_prov PG G (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn)
    out ((update_var out (a + n2w off) s) with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  rpt gen_tac >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out]]` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  conj_tac
  >- (irule pointer_offset_counted_edge >>
      gvs[ptr_covers_def] >> metis_tac[]) >>
  irule pointer_offset_covers >> metis_tac[]
QED

Theorem compile_slice_out_buf_parts:
  compile_slice_out_buf n sa = ((root,data),sb) ==>
  ?buf sm.
    compile_alloc_buffer n sa = (buf,sm) /\
    root = buf.buf_operand /\
    emit_op ADD [root; Lit 32w] sm = (data,sb)
Proof
  simp[compile_slice_out_buf_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

(* Unlike the operand-resource specialization above, this interface applies
   before operand evaluation, as required by adhoc slice allocation. *)
Theorem compile_alloc_buffer_counted:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out u G1 tn1.
    buf.buf_operand = Var out /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) u /\
    tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn /\
    gas_path_ptr_edge D 0 ctx func PG G tn s 0 G1 tn1
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
    ptr_covers G1 tn1 out (u with vs_inst_idx := SUC s.vs_inst_idx) n /\
    stmt_state_rel ctx func cenv cx es u /\ u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (?a. FLOOKUP u.vs_allocas sa.cs_next_id = SOME (a,n) /\
      a+n < dimword (:256) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
        regions_disjoint a n b len))
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]] /\
   emitted_insts sa sb = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]]` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def, emitted_insts_def] >> strip_tac >> gvs[rich_listTheory.DROP_APPEND1]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule lookup_block_fn_insts >> qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >>
     simp[get_instruction_def] >> metis_tac[MEM_EL]) >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    (gvs[run_inst_seq_def, mk_inst_def, is_terminator_def, AllCaseEqs()]) >>
  drule_all compile_alloc_buffer_counted_edge_covers >> strip_tac >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`, `t`,
    `step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]) t`,
    `step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]) s t tn`] >>
  gvs[] >> rpt strip_tac >> first_x_assum irule >> goal_assum drule
QED
