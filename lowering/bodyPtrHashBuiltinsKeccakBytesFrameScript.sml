(* Match the read-only S1 hash run with the counted pointer run. *)
Theory bodyPtrHashBuiltinsKeccakBytesFrame
Ancestors bodyPtrHashBuiltinsKeccakBytesRun bodyPtrHashBuiltinsGhostFrame
  bodyPtrHashBuiltinsCursor
  exprSimHash exprSimVVFrame bodyPtrDefs venomState words

Theorem hash_bytes_keccak_ptr_frame:
  !D ctx fn PG G tn s bb x sa op sb b base cap bs cenv cx es d.
    compile_keccak256_bytes (Var x) sa = (op,sb) /\ not_fresh_at sa x /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (base,cap) /\ base <= b /\
    b+32+LENGTH bs <= base+cap /\
    b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
    stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    ghost_inv d cenv cx es G tn s /\
    (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?t G' tn'. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t.vs_current_bb = s.vs_current_bb /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
      eval_operand op t = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
      stmt_state_rel ctx fn cenv cx es t /\
      ghost_inv d cenv cx es G' tn' t /\
      ghost_kept cenv es sa G tn s G' tn' /\ op_taint tn' op = {} /\
      op_prov G' op = NONE /\
      ghost_inv d cenv cx es G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))
Proof
  rpt gen_tac >> strip_tac >>
  `!z. Var x = Var z ==> not_fresh_at sa z` by simp[] >>
  drule_all compile_keccak256_bytes_frame >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule hash_run_inst_seq_current_bb >>
     goal_assum (drule_at Any) >> metis_tac[keccak_suffix_shape]) >>
  drule_all hash_keccak_bytes_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `ghost_inv d cenv cx es G' tn' t` by
    (irule hash_readonly_ghost_inv >> qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
     simp[] >> metis_tac[]) >>
  `ghost_kept cenv es sa G tn s G' tn'` by
    (irule hash_ghost_kept_frame >> simp[]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[hash_ghost_inv_inst_idx]
QED

Theorem hash_bytes_keccak_ptr_post:
  !D ctx fn PG G tn s bb x sm op sb b base cap bs cenv cx es es' d
    e sa s0 v.
    expr_post ctx fn cenv cx e es sa sm s0 es' v (Var x) s /\
    lower_value compile_expr cenv (expr_type e) e sa = (Var x,sm) /\
    compile_keccak256_bytes (Var x) sm = (op,sb) /\ not_fresh_at sm x /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (base,cap) /\ base <= b /\
    b+32+LENGTH bs <= base+cap /\
    b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
    ghost_inv d cenv cx es' G tn s /\
    (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
    (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?t G' tn'.
      t.vs_current_bb = s.vs_current_bb /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))) /\
      vv_post ctx fn cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
        es sa sb s0 es' (Value (BytesV (Keccak_256_w64 bs)))
        (StackValue (BaseT (BytesT (Fixed 32))) op)
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
      ghost_inv d cenv cx es' G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
      ghost_kept cenv es' sm G tn s G' tn' /\ op_taint tn' op = {} /\
      op_prov G' op = NONE
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx fn cenv cx es' s` by fs[loweringPostsTheory.expr_post_def] >>
  drule_all hash_bytes_keccak_ptr_frame >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  drule_all keccak_memory_post_run >> strip_tac >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> gvs[]
QED
