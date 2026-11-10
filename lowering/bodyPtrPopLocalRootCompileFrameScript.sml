Theory bodyPtrPopLocalRootCompileFrame
Ancestors
  bodyPtrPopLocalRootCompile bodyPtrPopLocalRootAddressFrame
  bodyPtrPopLocalRootGuardFrame bodyPtrPopLocalRootFrame
  fragExec fragGasPathPtr emitHelperProps emitHelper compileEnv loweringStateRelDefs list words venomState ptrDiscipline

Theorem pop_local_compile_nonempty_exact:
  compile_dynarray_pop (Var root) 32 esz ctor imm LocMemory sa = (res,sj) /\
  fn_has_code sa sj fn /\ not_fresh_at sa root /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn root s bytes /\
  lookup_var root s = SOME a /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  mem_word_at (w2n a) s.vs_memory = n2w len0 /\
  0 < len0 /\ len0 < dimword(:256) /\
  32+(len0-1)*esz < bytes /\ 32+(len0-1)*esz+esz <= bytes /\
  w2n a+bytes <= dimword(:256) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
      (w2n a) mem) ==>
  ?out t G' tn'. res = Var out /\ not_fresh_at sj out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
                 vs_inst_idx := t.vs_inst_idx|> /\
    lookup_var out t = SOME (n2w (w2n a+32+(len0-1)*esz)) /\
    ptr_covers G' tn' out t esz /\
    ~t.vs_halted /\ t.vs_current_bb = sj.cs_current_bb /\
    t.vs_inst_idx = LENGTH sj.cs_current_insts /\
    t.vs_memory = (mstore (w2n a) (n2w (len0-1)) s).vs_memory /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_labels = s.vs_labels /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all pop_local_compile_code >> strip_tac >>
  `32 <= bytes /\ (n2w len0:bytes32) <> 0w /\
   (n2w len0:bytes32)-1w = n2w (len0-1)` by
    (simp[GSYM n2w_sub] >> decide_tac) >>
  drule_all pop_local_header_exact >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var root t = SOME a /\ ptr_covers G' tn' root t bytes /\
   (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn'.t_mem)` by
    (drule bodyPtrPopMemoryHeaderTheory.pop_robust_dynarray_header_clean >>
     gvs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `!v. len = Var v ==> not_fresh_at sb v` by simp[] >>
  `eval_operand len t = SOME (n2w len0) /\ not_fresh_at sb root` by simp[] >>
  drule_all pop_local_guard_store_exact >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `!v. not_fresh_at sb v ==> not_fresh_at sg v` by
    (gvs[emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
         comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
         comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  `lookup_var root t' = SOME a /\ not_fresh_at sg root /\
   eval_operand new_len t' = SOME (n2w (len0-1))` by (simp[] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G'' tn'' (OK t')` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  drule_all pop_local_address_suffix_exact >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`out'`, `t''`, `G'''`, `tn'''`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `t'' = t' with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
      qpat_x_assum `t' = t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>` SUBST1_TAC >>
      qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >> simp[]) >>
  simp[mstore_def] >> metis_tac[]
QED
