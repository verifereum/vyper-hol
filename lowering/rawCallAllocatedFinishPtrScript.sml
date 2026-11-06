(* Allocation-predecessor consumers of the checked finish branches. *)
Theory rawCallAllocatedFinishPtr
Ancestors
  rawCallFinishTotalPtr rawCallFinishAdaptersPtr callReadinessPtr
  rawCallOutcomeLengthPtr gasSummaryComposePtr rawCallAllocationProofPtr

(* The preservation clause is the one exported by outbuf_ready_stage.
   Keep the preallocation operands together instead of rebuilding their
   evaluation/provenance/taint facts separately in each finish branch. *)
Theorem raw_call_allocation_request_checks:
  EVERY (\arg. (!z. arg = Var z ==> not_fresh_at sa z) /\
    (!l. arg <> Label l) /\ op_taint tn arg = {})
    (if stat then [gas;addr;dp;dl] else [gas;addr;value;dp;dl]) /\
  (!arg. (!z. arg = Var z ==> not_fresh_at sa z) /\ (!l. arg <> Label l) ==>
    eval_operand arg u = eval_operand arg s /\
    op_prov H arg = op_prov G arg /\ op_taint un arg = op_taint tn arg) /\
  eval_operand dp s = SOME (n2w (b+32)) /\
  eval_operand dl s = SOME (n2w (LENGTH bs)) /\
  op_prov G dp = SOME (region_base,sz) /\ region_base <= b /\
  b+32+LENGTH bs <= region_base+sz /\ b+32 < dimword(:256) /\
  LENGTH bs < dimword(:256) /\ cap < dimword(:256) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\ u.vs_memory = s.vs_memory /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN un.t_mem) /\
  eval_operand (Var rp) u = SOME ro /\ ptr_covers H un rp u cap ==>
  read_memory (w2n (n2w (b+32):bytes32))
    (w2n (n2w (LENGTH bs):bytes32)) u = bs /\
  (!iid outs.
    access_ok 0 H func (mk_inst iid (if stat then STATICCALL else CALL)
      (if stat then [gas;addr;dp;dl;Var rp;Lit (n2w cap)]
       else [gas;addr;value;dp;dl;Var rp;Lit (n2w cap)]) outs) u /\
    taint_ok func un (mk_inst iid (if stat then STATICCALL else CALL)
      (if stat then [gas;addr;dp;dl;Var rp;Lit (n2w cap)]
       else [gas;addr;value;dp;dl;Var rp;Lit (n2w cap)]) outs) u)
Proof
  strip_tac >>
  `EVERY (\arg. eval_operand arg u = eval_operand arg s /\
      op_prov H arg = op_prov G arg /\ op_taint un arg = {})
    (if stat then [gas;addr;dp;dl] else [gas;addr;value;dp;dl])` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `!arg. (!z. arg = Var z ==> _) /\ _ ==> _` kall_tac >>
  conj_tac >- (irule mem_bytes_at_read_memory_words >> gvs[]) >>
  rpt gen_tac >> conj_tac
  >- (irule (SRULE[] (GEN_ALL canonical_call_access_ok_ptr)) >>
      Cases_on `stat` >> fs[] >>
      simp[venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w] >>
      Cases_on `dp` >> gvs[ptrDisciplineTheory.op_prov_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  irule (SRULE[] (GEN_ALL canonical_call_taint_ok_ptr)) >>
  Cases_on `stat` >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, ptrDisciplineTheory.op_taint_def,
      venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w]
QED

