(* Instruction boundary probes for the hash builtin counted suffixes. *)
Theory bodyPtrHashBuiltinsBoundary
Ancestors
  bodyPtrDefs ptrDiscipline ptrSafeRun venomInst venomState
  contextCodegenRel codegenRel memLocDefs finite_map words

Theorem hash_sha3_access:
  !id p len out s G tn fn w n b sz.
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    FLOOKUP G p = SOME (b,sz) /\
    b <= w2n w /\ w2n w + w2n n <= b + sz ==>
    access_ok 0 G fn (mk_inst id SHA3 [Var p; len] [out]) s
Proof
  rpt strip_tac >>
  simp[access_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, memory_range_of_operands_def,
       mem_read_ops_def, mk_inst_def] >>
  rpt strip_tac >> qexistsl [`p`, `b`, `sz`] >> simp[]
QED

Theorem hash_sha3_taint:
  !id p len out s tn fn w n.
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    op_taint tn (Var p) = {} /\ op_taint tn len = {} /\
    (!i. w2n w <= i /\ i < w2n w + w2n n ==> i NOTIN tn.t_mem) ==>
    taint_ok fn tn (mk_inst id SHA3 [Var p; len] [out]) s
Proof
  rpt strip_tac >>
  simp[taint_ok_def, source_memory_read_ranges_def,
       memory_range_of_operands_def, mk_inst_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem hash_staticcall_access:
  !id gas addr p len q retlen out s G fn w n r m b sz c cap.
    eval_operand gas s <> NONE /\ eval_operand addr s <> NONE /\
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\ eval_operand retlen s = SOME m /\
    FLOOKUP G p = SOME (b,sz) /\ FLOOKUP G q = SOME (c,cap) /\
    b <= w2n w /\ w2n w + w2n n <= b + sz /\
    c <= w2n r /\ w2n r + w2n m <= c + cap ==>
    access_ok 0 G fn
      (mk_inst id STATICCALL [gas; addr; Var p; len; Var q; retlen] [out]) s
Proof
  rpt strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  simp[access_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, memory_range_of_operands_def,
       mem_read_ops_def, mem_write_ops_def, mk_inst_def] >>
  Cases_on `eval_operand gas s` >> gvs[] >>
  Cases_on `eval_operand addr s` >> gvs[]
QED

Theorem hash_staticcall_taint:
  !id gas addr p len q retlen out s tn fn w n.
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    (!op. MEM op [gas; addr; Var p; len; Var q; retlen] ==>
          op_taint tn op = {}) /\
    (!i. w2n w <= i /\ i < w2n w + w2n n ==> i NOTIN tn.t_mem) ==>
    taint_ok fn tn
      (mk_inst id STATICCALL [gas; addr; Var p; len; Var q; retlen] [out]) s
Proof
  rpt strip_tac >> gvs[listTheory.MEM] >>
  simp[taint_ok_def, source_memory_read_ranges_def,
       memory_range_of_operands_def, mk_inst_def] >>
  Cases_on `eval_operand gas s` >> simp[] >>
  Cases_on `eval_operand addr s` >> simp[] >>
  Cases_on `eval_operand (Var q) s` >> simp[] >>
  Cases_on `eval_operand retlen s` >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

(* The call writes only the returned prefix. In particular, success alone
   does not clean an entire output buffer; its returned length is needed. *)
Theorem hash_staticcall_mem_taint:
  !id ops outs tn s s'.
    mem_taint tn (mk_inst id STATICCALL ops outs) s s' =
      (tn.t_mem UNION new_site_bytes s s') DIFF
      range_bytes (MAP (\(off,len). (off, MIN len (LENGTH s'.vs_returndata)))
        (source_memory_write_ranges (mk_inst id STATICCALL ops outs) s))
Proof
  simp[mem_taint_def, step_writes_def, written_taint_def, mk_inst_def] >>
  Cases_on `ops` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem hash_staticcall_output_clean:
  !id ops outs tn s s' off len.
    source_memory_write_ranges (mk_inst id STATICCALL ops outs) s =
      [(off,len)] /\ len <= LENGTH s'.vs_returndata ==>
    !i. off <= i /\ i < off + len ==>
      i NOTIN mem_taint tn (mk_inst id STATICCALL ops outs) s s'
Proof
  simp[hash_staticcall_mem_taint, range_bytes_def] >>
  rpt strip_tac >> simp[arithmeticTheory.MIN_DEF] >> gvs[]
QED

Theorem hash_noninvoke_failed_ghost:
  !fuel ctx PG G tn inst s.
    inst.inst_opcode <> INVOKE /\
    (!s'. step_inst fuel ctx inst s <> OK s') ==>
    ghost_step fuel ctx PG G tn inst s = (G,tn)
Proof
  rpt strip_tac >> simp[ghost_step_def] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[]
QED
