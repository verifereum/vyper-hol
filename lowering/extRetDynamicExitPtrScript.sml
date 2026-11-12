Theory extRetDynamicExitPtr
Ancestors
  abiEncoderArrayCode extRetBulkCopyCountedPtr extRetBytesCopyCountedPtr
  fragGasPathPtr fragExec emitHelperProps exprLoweringProps emitHelper compileEnv
  ptrDiscipline bodyPtrDefs venomState venomExecSemantics venomInst
  words finite_map pred_set arithmetic

Theorem abi_array_dynamic_exit_ambient_counted_ptr:
  abi_encode_array_dynamic_exit (Var src) (Var cursor) sa = (Var out,sd) /\
  fn_has_code sa sd fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa cursor /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  lookup_var cursor s = SOME (n2w p) /\ p < dimword(:256) /\
  ptr_covers G tn cursor s 32 /\ mload p s = n2w k /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sd.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (n2w (32+k)) /\ op_taint tnf (Var out) = {} /\
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
  qpat_x_assum `abi_encode_array_dynamic_exit _ _ _ = _` mp_tac >>
  simp[abi_encode_array_dynamic_exit_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [Var src] sa = (unused,sb)` >>
  rename1 `emit_op MLOAD [Var cursor] sb = (offset,sc)` >>
  `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd` by
    metis_tac[cj 2 cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sa sc` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn` by
    (irule fn_has_code_split >> simp[]) >>
  `?u. unused = Var u` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  `?off. offset = Var off` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >> gvs[] >>
  `not_fresh_at sc off /\
   (!v. not_fresh_at sa v ==> not_fresh_at sb v) /\
   (!v. not_fresh_at sb v ==> not_fresh_at sc v)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `lookup_var cursor sf = SOME (n2w p) /\ ptr_covers Gf tnf cursor sf 32 /\
   mload p sf = n2w k /\
   (!i. w2n (n2w p : bytes32) <= i /\ i < w2n (n2w p : bytes32)+32 ==>
     i NOTIN tnf.t_mem)` by
    (gvs[ptr_covers_def, mload_def, w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `eval_operand (Lit 32w) sf' = SOME 32w /\
   eval_operand (Var off) sf' = SOME (n2w k) /\
   op_taint tnf' (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def, w2n_n2w, LESS_MOD] >>
  drule_all (emit_copy_len_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`Gf'`,`D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf' tnf' (OK sf')` by
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[]) >>
  qexistsl_tac [`Gf''`,`tnf''`,`sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`,`sf'`,`tnf'`] >> simp[]) >>
  simp[GSYM word_add_n2w, WORD_ADD_COMM] >> metis_tac[]
QED
