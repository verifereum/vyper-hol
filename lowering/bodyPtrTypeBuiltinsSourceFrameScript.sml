Theory bodyPtrTypeBuiltinsSourceFrame
Ancestors
  bodyPtrTypeBuiltinsSourcePrefix bodyPtrDefs finite_map

Theorem ghost_inv_readonly_frame:
  !P d cenv cx es G tn s G' tn' s'.
    s'.vs_memory = s.vs_memory /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_transient = s.vs_transient /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. P p ==> lookup_var p s' = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> P p) /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> P p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> P p) /\
    ghost_inv d cenv cx es G tn s ==>
    ghost_inv d cenv cx es G' tn' s'
Proof
  rpt gen_tac >> strip_tac >>
  `!p sz. P p ==> (ptr_covers G' tn' p s' sz <=> ptr_covers G tn p s sz)` by
    (rpt strip_tac >> simp[ptr_covers_def]) >>
  gvs[ghost_inv_def, stor_taint_ok_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      metis_tac[]) 
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[return_buf_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ghost_kept_readonly_frame:
  !P cenv es sa G0 tn0 s0 G tn G' tn'.
    tn'.t_mem = tn.t_mem /\
    (!p. P p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!p. not_fresh_at sa p ==> P p) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn ==>
    ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  simp[ghost_kept_def] >> metis_tac[]
QED

Theorem bytestring_source_prefix_ghost_frame:
  !D ctx fn PG G tn s bb id1 id2 src len data a capacity
   d cenv cx es es0 sa G0 tn0 s0.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id1 MLOAD [Var src] [len]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst id2 ADD [Var src; Lit 32w] [data]) /\
    ALL_DISTINCT [src;len;data] /\ lookup_var src s = SOME a /\
    ptr_covers G tn src s capacity /\ 32 <= capacity /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
    ghost_inv d cenv cx es G tn s /\
    ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
    ~not_fresh_at sa len /\ ~not_fresh_at sa data /\
    (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
      p <> len /\ p <> data) /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==>
      p <> len /\ p <> data) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
      p <> len /\ p <> data) ==>
    ?G' tn' t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
      lookup_var len t = SOME (mload (w2n a) s) /\
      op_taint tn' (Var len) = {} /\ lookup_var data t = SOME (a+32w) /\
      t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
      tn'.t_imm = tn.t_imm /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = SUC (SUC s.vs_inst_idx) /\
      (!p. p <> len /\ p <> data ==> lookup_var p t = lookup_var p s /\
        FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p)) /\
      (!n. 32 < capacity /\ 32+n <= capacity /\ w2n a+32 < dimword(:256) ==>
        ptr_covers G' tn' data t n) /\
      ghost_inv d cenv cx es G' tn' t /\
      ghost_kept cenv es0 sa G0 tn0 s0 G' tn'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all bytestring_source_prefix_counted >>
  disch_then (qspecl_then [`D`,`PG`]
    (qx_choose_then `G'` (qx_choose_then `tn'`
      (qx_choose_then `t` strip_assume_tac)))) >>
  `ghost_inv d cenv cx es G' tn' t` by
    (irule ghost_inv_readonly_frame >>
     qexistsl_tac [`G`,`\p. p <> len /\ p <> data`,`s`,`tn`] >>
     simp[] >> metis_tac[]) >>
  `ghost_kept cenv es0 sa G0 tn0 s0 G' tn'` by
    (irule ghost_kept_readonly_frame >>
     qexistsl_tac [`G`,`\p. p <> len /\ p <> data`,`tn`] >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`G'`,`tn'`,`t`] >> simp[]
QED
