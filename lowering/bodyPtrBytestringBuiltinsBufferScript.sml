Theory bodyPtrBytestringBuiltinsBuffer
Ancestors
  bodyPtrBytestringBuiltinsAllocation loweringHalt emitHelperProps
  context emitHelper compileEnv fragExec venomInst list
  normalizationAllocPtr loweringPosts builtinBytes bodyPtrDefs
  exprSimLiteralBuffer exprLoweringProps venomState
  fragGasPathPtr fragGasSeqPtr typedCopyPtr bodyPtrAttributeAdd
  venomExecSemantics words ptrDiscipline

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
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tv /\
  ~is_word_type (post_value_type cenv e) /\ val_wf tv v /\ n < dimword (:256) /\
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
  !root off delta sa out sb func ctx s a G tn total n D PG.
  emit_op ADD [Var root; delta] sa = (Var out,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s total /\
  eval_operand delta s = SOME (n2w off) /\ op_taint tn delta = {} /\
  off + n <= total /\ w2n a + off < dimword (:256) ==>
  gas_path_ptr_edge D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ADD [Var root; delta] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst sa.cs_next_id ADD [Var root; delta] [out]) s
      (update_var out (a + n2w off) s) tn)
    (OK ((update_var out (a + n2w off) s) with vs_inst_idx := SUC s.vs_inst_idx)) /\
  ptr_covers
    (step_prov PG G (mk_inst sa.cs_next_id ADD [Var root; delta] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst sa.cs_next_id ADD [Var root; delta] [out]) s
      (update_var out (a + n2w off) s) tn)
    out ((update_var out (a + n2w off) s) with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  rpt gen_tac >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ADD [Var root; delta] [out]]` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id ADD [Var root; delta] [out])` by
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
      a+n < dimword (:256) /\ lookup_var out u = SOME (n2w a) /\
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
  gvs[eval_operand_def] >> rpt strip_tac >> first_x_assum irule >> goal_assum drule
QED

Theorem compile_slice_out_buf_compiler_parts:
  compile_slice_out_buf n sa = ((root,data),sb) ==>
  ?buf sm r p.
    compile_alloc_buffer n sa = (buf,sm) /\
    root = Var r /\ buf.buf_operand = Var r /\ data = Var p /\
    emit_op ADD [Var r; Lit 32w] sm = (Var p,sb) /\
    r <> p /\ cs_extends sa sm /\ cs_extends sm sb /\
    sm.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_bb = sm.cs_current_bb /\
    LENGTH sm.cs_current_insts = LENGTH sa.cs_current_insts + 1 /\
    LENGTH sb.cs_current_insts = LENGTH sm.cs_current_insts + 1
Proof
  strip_tac >> drule compile_slice_out_buf_parts >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  `cs_extends sm sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
    emit_def] >> strip_tac >> gvs[]
QED

Theorem slice_out_buf_runtime_frame[local]:
  compile_slice_out_buf n sa = ((Var r,Var p),sb) /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [r]) s = OK u /\
  lookup_var r u = SOME a /\
  t = ((update_var p (a + 32w) u) with vs_inst_idx := s.vs_inst_idx + 2) ==>
  (fresh_vars_wrt sa s ==> fresh_vars_wrt sb t) /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_code = s.vs_code /\
  t.vs_accounts = s.vs_accounts /\
  lookup_var r t = SOME a /\ lookup_var p t = SOME (a + 32w)
Proof
  strip_tac >>
  qpat_x_assum `compile_slice_out_buf _ _ = _` mp_tac >>
  simp[compile_slice_out_buf_def, compile_alloc_buffer_def, emit_op_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
    fresh_var_def, emit_def] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def, lookup_var_def, fresh_vars_wrt_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[]
QED

Theorem compile_slice_out_buf_counted:
  compile_slice_out_buf n sa = ((root,data),sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  32 <= n /\ n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?buf sm r p u a G1 tn1 G2 tn2 t.
    compile_alloc_buffer n sa = (buf,sm) /\
    root = Var r /\ buf.buf_operand = Var r /\ data = Var p /\
    emit_op ADD [Var r; Lit 32w] sm = (Var p,sb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [r]) s = OK u /\
    lookup_var r u = SOME a /\ w2n a + n < dimword (:256) /\
    G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [r]) u /\
    tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [r]) s u tn /\
    G2 = step_prov PG G1 (mk_inst sm.cs_next_id ADD [Var r; Lit 32w] [p])
      (update_var p (a + 32w) (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
    tn2 = step_taint (mk_inst sm.cs_next_id ADD [Var r; Lit 32w] [p])
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (update_var p (a + 32w) (u with vs_inst_idx := SUC s.vs_inst_idx)) tn1 /\
    t = ((update_var p (a + 32w) u) with vs_inst_idx := s.vs_inst_idx + 2) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G2 tn2 (OK t) /\
    ptr_covers G2 tn2 r t n /\ ptr_covers G2 tn2 p t (n - 32) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
      op_taint tn2 (Var x) = op_taint tn (Var x)) /\
    (!x k. not_fresh_at sa x /\ ptr_covers G tn x s k ==>
      ptr_covers G2 tn2 x t k) /\
    stmt_state_rel ctx func cenv cx es t /\ t.vs_memory = s.vs_memory /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op t = eval_operand op s /\
      op_prov G2 op = op_prov G op /\ op_taint tn2 op = op_taint tn op) /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sb t) /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_code = s.vs_code /\
    t.vs_accounts = s.vs_accounts /\
    lookup_var r t = SOME a /\ lookup_var p t = SOME (a + 32w) /\
    tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm
Proof
  strip_tac >> drule compile_slice_out_buf_compiler_parts >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all compile_alloc_buffer_counted >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  suspend "offset"
QED

Resume compile_slice_out_buf_counted[offset]:
  `out = r` by gvs[] >>
  qpat_x_assum `out = r` SUBST_ALL_TAC >>
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_def, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
     strip_tac >> gvs[update_var_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ (OK uh)` >>
  `~uh.vs_halted /\ uh.vs_current_bb = sm.cs_current_bb /\
   uh.vs_inst_idx = LENGTH sm.cs_current_insts /\
   lookup_var r uh = SOME (n2w a) /\ w2n (n2w a : 256 word) + 32 < dimword (:256)` by
    (fs[Abbr `uh`, lookup_var_def] >>
     `a < dimword (:256)` by decide_tac >> simp[w2n_n2w] >> decide_tac) >>
  `32 + (n - 32) <= n` by decide_tac >>
  `eval_operand (Lit 32w) uh = SOME (n2w 32) /\ op_taint tn1 (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all emit_pointer_offset_counted_covers >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  suspend "compose"
QED

Resume compile_slice_out_buf_counted[compose]:
  qmatch_asmsub_abbrev_tac
    `gas_path_ptr_edge D 0 ctx func PG G1 tn1 uh 0 G2 tn2 (OK t)` >>
  `~t.vs_halted` by simp[Abbr `t`, update_var_def] >>
  `ptr_covers G2 tn2 r t n` by
    (simp_tac pure_ss [Abbr `t`] >> irule attribute_ptr_covers_update >>
     conj_tac >- simp[] >> qexistsl_tac [`G1`, `tn1`] >>
     simp[Abbr `G2`, Abbr `tn2`, copy_len_binop_ghost_frame]) >>
  `gas_path_ptr D 0 ctx func PG G2 tn2 t 0 G2 tn2 (OK t)` by
    simp[gas_path_ptr_rules] >>
  `gas_path_ptr D 0 ctx func PG G1 tn1 uh 0 G2 tn2 (OK t)` by
    (drule_at (Pat `gas_path_ptr_edge _ _ _ _ _ G1 _ _ _ _ _ _`)
       (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[]) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G2 tn2 (OK t)` by
    (qpat_assum `gas_path_ptr_edge _ _ _ _ _ G tn s _ _ _ _` mp_tac >>
     qpat_assum `gas_path_ptr _ _ _ _ _ G1 tn1 uh _ _ _ _` mp_tac >>
     metis_tac[cj 2 gas_path_ptr_rules, arithmeticTheory.ADD_0]) >>
  suspend "finish"
QED

Resume compile_slice_out_buf_counted[finish]:
  `a < dimword (:256)` by decide_tac >>
  `t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\
   t = ((update_var p (n2w a + 32w) u) with vs_inst_idx := s.vs_inst_idx + 2)` by
    simp[Abbr `t`, Abbr `uh`, update_var_def, arithmeticTheory.ADD1,
      arithmeticTheory.ADD_ASSOC] >>
  suspend "frame"
QED

Resume compile_slice_out_buf_counted[frame]:
  `!x. not_fresh_at sa x ==> x <> r /\ x <> p` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
    op_taint tn2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x <> r /\ x <> p` by simp[] >>
     simp[Abbr `t`, Abbr `uh`, lookup_var_update_var] >>
     simp[Abbr `G2`, Abbr `tn2`, copy_len_binop_ghost_frame] >>
     gvs[alloca_old_register_ghost_frame, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `!x k. not_fresh_at sa x /\ ptr_covers G tn x s k ==>
    ptr_covers G2 tn2 x t k` by
    (rpt strip_tac >> simp[ptr_covers_def] >> fs[ptr_covers_def]) >>
  `not_local_ptr cenv es.scopes p` by
    (fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qpat_assum `t = _` SUBST1_TAC >> simp[stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `t.vs_memory = s.vs_memory` by simp[Abbr `t`, Abbr `uh`, update_var_def] >>
  `u.vs_labels = s.vs_labels` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_def, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
     strip_tac >> gvs[update_var_def]) >>
  `t.vs_labels = s.vs_labels` by simp[Abbr `t`, Abbr `uh`, update_var_def] >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op t = eval_operand op s /\
    op_prov G2 op = op_prov G op /\ op_taint tn2 op = op_taint tn op` by
    (Cases >> simp[eval_operand_def, op_prov_def, op_taint_def]) >>
  `compile_slice_out_buf n sa = ((Var r,Var p),sb)` by simp[] >>
  drule_all slice_out_buf_runtime_frame >> strip_tac >>
  qexistsl_tac [`buf`, `sm`, `r`, `p`, `u`, `n2w a`, `G1`, `tn1`,
    `G2`, `tn2`, `t`] >>
  gvs[Abbr `G2`, Abbr `tn2`, Abbr `uh`, w2n_n2w] >>
  simp[step_taint_def, mk_inst_def, store_taint_def, adopt_reset_def,
    imm_taint_def]
QED

Finalise compile_slice_out_buf_counted
