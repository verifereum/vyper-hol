(* Consumer boundary for the counted selector-buffer construction. *)
Theory bodyPtrEnvBuiltinsSelectorCounted
Ancestors bodyPtrEnvBuiltinsSelectorSuffix bodyPtrEnvBuiltinsScalar
  ghostPcTransportPtr fragGasSeqPtr bodyPtrDefs venomState venomInst
  list words

Theorem ptr_val_ok_inst_idx[simp]:
  ptr_val_ok cx ty v op G tn (s with vs_inst_idx := k) <=>
  ptr_val_ok cx ty v op G tn s
Proof
  simp[ptr_val_ok_def, ptr_mem_ok_def]
QED

Theorem ptr_buf_ok_inst_idx[simp]:
  ptr_buf_ok cenv e op G (s with vs_inst_idx := k) <=>
  ptr_buf_ok cenv e op G s
Proof
  simp[ptr_buf_ok_def]
QED

Theorem selector_suffix_counted:
  code = [mk_inst ia ALLOCA [Lit 64w] [p];
          mk_inst il MSTORE [Var p; Lit 4w] [];
          mk_inst ip ADD [Var p; Lit 32w] [q];
          mk_inst iw MSTORE [Var q; value] []] /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_inst_ids_distinct fn /\
  MEM (mk_inst ia ALLOCA [Lit 64w] [p]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
  ~not_fresh_at sa p /\ ~not_fresh_at sa q /\ p <> q /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. value = Var x ==> x <> p /\ x <> q) /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  LENGTH bs = 4 /\ TAKE 4 (word_to_bytes w T) = bs /\
  run_inst_seq code s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  t' = t with vs_inst_idx := s.vs_inst_idx + LENGTH code ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t') /\
    ghost_inv d cenv cx es G' tn' t' /\
    ghost_kept cenv es sa G tn s G' tn' /\
    ptr_val_ok cx (BaseT (BytesT (Dynamic 4))) (BytesV bs) (Var p) G' tn' t' /\
    ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args) (Var p) G' t'
Proof
  strip_tac >>
  drule_all selector_suffix_certificate >>
  disch_then (qspecl_then [`args`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[mk_inst_def]
QED
