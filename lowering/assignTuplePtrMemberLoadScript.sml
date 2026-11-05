(* Typed read-only tuple member execution; no tuple index arithmetic here. *)
Theory assignTuplePtrMemberLoad
Ancestors
  assignTuplePtrLoadStep context compileEnv emitHelper exprLoweringProps
  exprSimProps bodyPtrDefs fragGasPathPtr words stateFrame
  venomState valueEncoding

Theorem compile_tuple_member_typed_path_ptr:
  emit_op ADD [Var src; Lit off] sa = (pv,sm) /\
  compile_load_memory pv (is_word_type ty) sm = (op,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME w /\ op_taint tn (Var src) = {} /\
  FLOOKUP G src = SOME (b,sz) /\ w2n (w+off) = a /\ b <= a /\
  a + type_memory_size tv <= b+sz /\ a + type_memory_size tv < dimword (:256) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v a m) ==>
  ?out t G' tn'. op = Var out /\ not_fresh_at sb out /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    op_taint tn' (Var out) = {} /\
    (if is_word_type ty then lookup_var out t = SOME (typed_val_to_w256 tv v)
     else lookup_var out t = SOME (n2w a) /\ FLOOKUP G' out = SOME (b,sz))
Proof
  strip_tac >> drule_all emit_add_member_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `pv = Var out` >>
  reverse (Cases_on `is_word_type ty`)
  >- (qpat_x_assum `compile_load_memory _ _ _ = _` mp_tac >>
      asm_rewrite_tac[compile_load_memory_def, comp_return_def] >>
      pure_rewrite_tac [pairTheory.PAIR_EQ] >> strip_tac >>
      qpat_x_assum `sm = sb` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `Var out = op` (SUBST_ALL_TAC o SYM) >>
      qexistsl_tac [`out`, `t`, `G'`, `tn'`] >> asm_rewrite_tac[] >>
      metis_tac[n2w_w2n]) >>
  qpat_x_assum `compile_load_memory _ _ _ = _` mp_tac >>
  asm_rewrite_tac[compile_load_memory_def] >> strip_tac >>
  `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >>
  `ptr_covers G' tn' out t 32` by
    (simp[ptr_covers_def] >> qexistsl_tac [`w+off`, `b`, `sz`] >> simp[]) >>
  drule_all robust_typed_word_clean >> strip_tac >>
  `!i. w2n (w+off) <= i /\ i < w2n (w+off)+32 ==> i NOTIN tn'.t_mem`
    by asm_rewrite_tac[] >>
  `t.vs_current_bb = sm.cs_current_bb` by asm_rewrite_tac[] >>
  drule_all emit_mload_member_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`out'`, `t'`, `G''`, `tn''`] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- (drule_all gas_path_ptr_then >> simp[])
  >- suspend "frame"
  >- suspend "old_vars"
  >> suspend "word"
QED

Resume compile_tuple_member_typed_path_ptr[frame]:
  qpat_x_assum `state_frame t' = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `state_frame t = _` mp_tac >>
  simp[state_frame_def]
QED

Resume compile_tuple_member_typed_path_ptr[old_vars]:
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `emit_op ADD _ _ = _`
      (mp_tac o MATCH_MP emitted_insts_emit_op_local) >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at sm p` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Resume compile_tuple_member_typed_path_ptr[word]:
  qpat_x_assum `!m. mem_agree_outside _ _ m ==> mem_word_at _ m = _`
    (qspec_then `s.vs_memory` mp_tac) >>
  asm_rewrite_tac[mem_agree_outside_def] >>
  simp[mload_def, mem_word_at_def]
QED

Finalise compile_tuple_member_typed_path_ptr
