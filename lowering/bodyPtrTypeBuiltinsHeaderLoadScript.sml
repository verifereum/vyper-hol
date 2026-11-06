Theory bodyPtrTypeBuiltinsHeaderLoad
Ancestors
  bodyPtrTypeBuiltinsLoad bodyPtrTypeBuiltinsBytesRead exprSimPtrProps
  bodyPtrDefs ptrDiscipline venomState venomInst

Theorem mload_counted_ghost_frame:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [out]) /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\ src <> out /\ 
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p. not_fresh_at sa p ==> p <> out) ==>
  ?H th t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th (OK t) /\
    op_prov H (Var out) = NONE /\ op_taint th (Var out) = {} /\
    lookup_var out t = SOME (mload (w2n a) s) /\
    t.vs_inst_idx = SUC s.vs_inst_idx /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    ghost_inv d cenv cx es H th t /\ ghost_kept cenv es sa G tn s H th /\
    ptr_covers H th src t 32 /\
    (!p n. p <> out /\ ptr_covers G tn p s n ==> ptr_covers H th p t n) /\
    (!p. p <> out ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all mload_counted_clean_ambient >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`,`tn'`,`t`] >> simp[] >> conj_tac
  >- (irule ghost_inv_fresh_frame >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac >- (simp[ghost_kept_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]
QED

Theorem ptr_buf_ok_covers:
  ptr_buf_ok cenv e (Var src) G s /\ op_taint tn (Var src) = {} /\
  lookup_var src s = SOME a /\ 0 < n /\
  n <= type_memory_bytes cenv (lowered_value_type cenv e) ==>
  ptr_covers G tn src s n
Proof
  strip_tac >>
  `type_memory_bytes cenv (lowered_value_type cenv e) <> 0` by decide_tac >>
  qpat_x_assum `ptr_buf_ok _ _ _ _ _` mp_tac >>
  simp[ptr_buf_ok_def, eval_operand_def] >> strip_tac >>
  simp[ptr_covers_def] >> goal_assum (drule_at Any) >> decide_tac
QED
