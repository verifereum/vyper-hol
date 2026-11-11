Theory extRetDynamicPreparePtr
Ancestors
  abiEncoderArrayTail extRetAbiBytesCountedPtr extRetBytesCopyCountedPtr
  extRetBulkCopyCountedPtr extRetLoopScalarAmbientPtr
  fragGasPathPtr fragExec bodyPtrDefs ptrDiscipline ptrSafeRun
  emitHelperProps exprLoweringProps emitHelper compileEnv
  venomExecSemantics venomState venomInst words finite_map pred_set arithmetic

(* The real two-instruction tail phase: a clean cursor read followed by
   pointer addition.  No recursive encoder or allocation is executed here. *)
Theorem abi_array_tail_ambient_counted_ptr:
  abi_encode_array_tail (Var data) (Var cursor) sa =
    ((Var offset,Var child),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa data /\
  lookup_var data s = SOME a /\ ptr_covers G tn data s cap /\
  lookup_var cursor s = SOME (n2w p) /\ p < dimword(:256) /\
  ptr_covers G tn cursor s 32 /\ mload p s = n2w k /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
  k+n <= cap /\ w2n a+k < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var offset sf = SOME (n2w k) /\ op_taint tnf (Var offset) = {} /\
    lookup_var child sf = SOME (n2w (w2n a+k)) /\
    ptr_covers Gf tnf child sf n /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_memory = s.vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
    sf.vs_call_ctx = s.vs_call_ctx /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_array_tail _ _ _ = _` mp_tac >>
  simp[abi_encode_array_tail_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `fn_has_code sa sb fn` >>
  rename1 `emit_op MLOAD [Var cursor] sa = (Var offset,sc)` >>
  `cs_extends sa sc /\ cs_extends sc sb` by
    metis_tac[cj 2 cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sb fn` by
    (irule fn_has_code_split >> simp[]) >>
  `not_fresh_at sc offset /\
   (!v. not_fresh_at sa v ==> not_fresh_at sc v)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
  `!i. w2n (n2w p : bytes32) <= i /\
    i < w2n (n2w p : bytes32)+32 ==> i NOTIN tn.t_mem` by
    simp[w2n_n2w, LESS_MOD] >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var data sf = SOME a /\ ptr_covers Gf tnf data sf cap /\
   lookup_var offset sf = SOME (n2w k)` by
    (gvs[ptr_covers_def, w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  `w2n a+k < dimword(:256)` by decide_tac >>
  drule_all abi_bytes_lastptr_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf'`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  simp[] >> metis_tac[]
QED
