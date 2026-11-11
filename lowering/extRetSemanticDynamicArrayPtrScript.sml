Theory extRetSemanticDynamicArrayPtr
Ancestors
  extRetDynamicExitPtr extRetBytesCopyCountedPtr extRetBulkCopyCountedPtr
  extRetDynamicArrayPhasePtr extRetDynamicArrayInitFramePtr
  extRetDynamicArrayEntryPtr extRetDynamicArrayCountPtr
  extRetSemanticDynamicLoopPtr
  extRetScratchInitPtr fragGasPathPtr fragExec emitHelperProps exprLoweringProps
  emitHelper compileEnv bodyPtrDefs ptrDiscipline venomState venomExecSemantics
  venomMemDefs venomMemProps valueEncoding words finite_map pred_set arithmetic

(* The final four instructions of the outer array encoder.  The parent
   cursor is local scratch, initialized to zero before the array loop. *)
Theorem encoder_dynamic_parent_finish_counted_ptr:
  emit_op MLOAD [Var parent] sa = (Var old,sb) /\
  emit_op ADD [Var old;Var encoded] sb = (Var sumv,sc) /\
  emit_void MSTORE [Var parent;Var sumv] sc = ((),sd) /\
  emit_op MLOAD [Var parent] sd = (Var out,se) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  fn_has_code sc sd fn /\ fn_has_code sd se fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa parent /\ not_fresh_at sa encoded /\
  lookup_var parent s = SOME (n2w p) /\ p < dimword(:256) /\
  ptr_covers G tn parent s 32 /\ mload p s = 0w /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
  lookup_var encoded s = SOME (n2w n) /\ op_taint tn (Var encoded) = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = se.cs_current_bb /\
    sf.vs_inst_idx = LENGTH se.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (n2w n) /\ op_taint tnf (Var out) = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (mstore p (n2w n) s).vs_memory /\
    (!i. i < p \/ p+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `(!v. not_fresh_at sa v ==> not_fresh_at sb v) /\
   (!v. not_fresh_at sb v ==> not_fresh_at sc v) /\
   (!v. not_fresh_at sc v ==> not_fresh_at sd v)` by
    (gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
         fresh_var_def, fresh_id_def, emit_def, comp_return_def,
         not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!i. w2n (n2w p : bytes32) <= i /\
     i < w2n (n2w p : bytes32)+32 ==> i NOTIN tn.t_mem` by
    simp[w2n_n2w, LESS_MOD] >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `eval_operand (Var old) sf = SOME 0w /\
   eval_operand (Var encoded) sf = SOME (n2w n) /\
   op_taint tnf (Var encoded) = {}` by
    simp[eval_operand_def, w2n_n2w, LESS_MOD] >>
  drule_all (emit_copy_len_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`Gf`,`D`] strip_assume_tac) >>
  `lookup_var parent sf' = SOME (n2w p) /\
   ptr_covers Gf' tnf' parent sf' 32 /\
   eval_operand (Var sumv) sf' = SOME (n2w n)` by
    (gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  drule_all emit_mstore_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `lookup_var parent sf'' = SOME (n2w p) /\
   ptr_covers Gf' tnf'' parent sf'' 32 /\
   mload p sf'' = n2w n /\
   (!i. w2n (n2w p : bytes32) <= i /\
     i < w2n (n2w p : bytes32)+32 ==> i NOTIN tnf''.t_mem)` by
    (gvs[ptr_covers_def, w2n_n2w, LESS_MOD] >>
     metis_tac[mload_def, mload_mstore_same]) >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf' tnf' (OK sf')` by
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf' tnf'' (OK sf'')` by
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`,`sf'`,`tnf'`] >> simp[]) >>
  qexistsl_tac [`Gf''`,`tnf'''`,`sf'''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`,`sf''`,`tnf''`] >> simp[]) >>
  simp[w2n_n2w, LESS_MOD] >>
  simp[mstore_def, write_memory_with_expansion_def]
QED
