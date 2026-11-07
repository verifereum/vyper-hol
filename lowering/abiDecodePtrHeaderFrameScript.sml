(* Successful builtin headers: existence, pointer certification and body frames. *)
Theory abiDecodePtrHeaderFrame
Ancestors
  abiDecodePtrSetup abiBuiltinDecodeHeader abiBuiltinPrefix abiDecoderContract
  assignTuplePtrLoadStep exprSimPtrProps bodyPtrDefs exprLoweringProps
  emitHelperProps compileEnv ptrDiscipline venomState stateFrame list

Theorem abi_builtin_decode_header_frame_ptr:
  abi_builtin_decode_header (Var p) mn mx sa = ((len,src),sh) /\
  fn_has_code sa sh func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var p s = SOME w /\ not_fresh_at sa p /\
  ptr_covers G tn p s (32+n) /\
  w2n w + 32+n < dimword (:256) /\
  (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tn.t_mem) /\
  mload (w2n w) s = n2w cnt /\ mn <= cnt /\ cnt <= mx /\
  mx < dimword (:256) /\ abi_decoder_operand_live sa.cs_next_var (Var p) /\
  sh.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u G' tn' q r.
    src = Var q /\ len = Var r /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK u) /\
    fresh_vars_wrt limit_st u /\ stmt_state_rel ctx func cenv cx es u /\
    ghost_inv d cenv cx es G' tn' u /\
    ~u.vs_halted /\ u.vs_current_bb = sh.cs_current_bb /\
    u.vs_inst_idx = LENGTH sh.cs_current_insts /\
    eval_operand (Var r) u = SOME (n2w cnt) /\
    op_prov G' (Var r) = NONE /\ op_taint tn' (Var r) = {} /\
    lookup_var q u = SOME (w+32w) /\ ptr_covers G' tn' q u n /\
    not_fresh_at sh q /\ not_fresh_at sh r /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\
    state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule_all abi_builtin_decode_header >> strip_tac >>
  fs[abi_builtin_prefix_def] >>
  drule_all (abi_builtin_decode_header_success_path_ptr |>
    SRULE [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule stmt_state_rel_old_vars_frame_ptr >>
     qexistsl_tac [`s`, `sa`] >> simp[]) >>
  `ghost_inv d cenv cx es G' tn' (t with vs_inst_idx := LENGTH sh.cs_current_insts)` by
    (irule ghost_inv_fresh_frame >>
     goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
     qexists_tac `sa` >> fs[lookup_var_def]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sh.cs_current_insts`, `G'`, `tn'`, `q`, `r`] >>
  gvs[fresh_vars_wrt_def, ptr_covers_def, eval_operand_def, lookup_var_def,
      stmt_state_rel_inst_idx]
QED
