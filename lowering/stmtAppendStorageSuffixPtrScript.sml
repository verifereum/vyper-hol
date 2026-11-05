(* Binary arithmetic boundary for the storage append suffix. *)
Theory stmtAppendStorageSuffixPtr
Ancestors stmtAppendStorageGuardPtr stmtAppendStorageRunPtr instSeqComposePtr
  exprLoweringProps emitHelperProps freshWrites stateFrame venomInst venomState
  ptrDiscipline finite_map list arithmetic compileEnv

Theorem emit_append_binary_uniform_ptr:
  !opc a b st rop st' s t tn ctx.
  emit_op opc [a;b] st = (rop,st') /\ (opc = ADD \/ opc = MUL) /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ ~ctx_has_dalloca ctx ==>
  !D fn PG G. ?G' tn'.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st')
            (s with vs_inst_idx := k) G' tn') /\
    op_taint tn' rop = {} /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  rpt strip_tac >> irule emit_append_arith_uniform_ptr >> simp[] >>
  qexistsl_tac [`opc`, `[a;b]`] >> simp[] >> rpt strip_tac >> gvs[]
QED
