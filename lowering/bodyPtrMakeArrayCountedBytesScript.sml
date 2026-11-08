Theory bodyPtrMakeArrayCountedBytes
Ancestors
  bodyPtrMakeArrayCountedLength bodyPtrMakeArrayBulkFrame
  bodyPtrMakeArrayPrimitiveInstall exprSimBufferStore context compileEnv
  emitHelperProps exprLoweringProps fragExec fragGasPathPtr ptrDiscipline bodyPtrDefs
  venomState venomInst venomExecSemantics finite_map

Theorem bytestring_store_split_installed:
  compile_store_bytestring src dst sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?out mid.
    compile_bytestring_copy_len src sa = (out,mid) /\
    emit_void MCOPY [dst;src;out] mid = ((),sb) /\
    fn_has_code sa mid fn /\ fn_has_code mid sb fn
Proof
  strip_tac >> Cases_on `compile_bytestring_copy_len src sa` >>
  gvs[compile_store_bytestring_def, comp_bind_def] >>
  rename1 `compile_bytestring_copy_len src sa = (out,mid)` >>
  `cs_extends sa mid` by
    (drule buffer_copy_len_shape >> strip_tac >>
     irule cs_extends_same_block >>
     gvs[same_blocks_def] >> simp[]) >>
  `cs_extends mid sb` by
    (drule emit_void_extends >> strip_tac >>
     irule cs_extends_same_block >> gvs[same_blocks_def] >> simp[]) >>
  drule_all fn_has_code_split >> simp[] >> metis_tac[]
QED

Theorem bytestring_store_counted:
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  fn_has_code sa sb fn /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  n = 32 + 32 * ((len + 31) DIV 32) /\
  len + 31 < dimword (:256) /\ n < dimword (:256) /\
  mload (w2n a) s = n2w len /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    sf.vs_current_bb = sb.cs_current_bb /\ ~sf.vs_halted /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_tx_ctx = s.vs_tx_ctx /\
    sf.vs_block_ctx = s.vs_block_ctx /\
    sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_returndata = s.vs_returndata /\
    sf.vs_logs = s.vs_logs /\ sf.vs_outcomes = s.vs_outcomes /\
    sf.vs_requests = s.vs_requests /\
    sf.vs_pending_deletions = s.vs_pending_deletions /\
    sf.vs_immutables = s.vs_immutables /\ sf.vs_code = s.vs_code /\
    sf.vs_call_entry_fmp = s.vs_call_entry_fmp /\
    sf.vs_initial_fmp = s.vs_initial_fmp /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!i. i < n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!x size. not_fresh_at sa x /\ ptr_covers G tn x s size ==>
      ptr_covers Gf tnf x sf size)
Proof
  strip_tac >> drule_all bytestring_store_split_installed >> strip_tac >>
  `ptr_covers G tn src s 32` by
    (fs[ptr_covers_def] >> decide_tac) >>
  drule_all bytestring_copy_len_counted_exact >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choose_then `G1` (qx_choose_then `tn1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `!x size. not_fresh_at sa x /\ ptr_covers G tn x s size ==>
    ptr_covers G1 tn1 x s1 size` by
      (rpt strip_tac >> fs[ptr_covers_def] >> metis_tac[]) >>
  drule_all emit_void_fetch_boundary >> strip_tac >>
  `lookup_var src s1 = SOME a /\ lookup_var dst s1 = SOME b` by metis_tac[] >>
  `ptr_covers G1 tn1 src s1 (w2n (n2w n : bytes32)) /\
   ptr_covers G1 tn1 dst s1 (w2n (n2w n : bytes32))` by (gvs[] >> metis_tac[]) >>
  `get_instruction bb s1.vs_inst_idx =
    SOME (mk_inst mid.cs_next_id MCOPY [Var dst;Var src;out] []) /\
   lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_at (Pat `get_instruction _ _ = _`) mcopy_operand_framed_ptr_path >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choose_then `G2` (qx_choose_then `tn2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >>
  conj_tac >- (metis_tac[SRULE []
    (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)]) >>
  `s2.vs_inst_idx = LENGTH sb.cs_current_insts /\
   s2.vs_current_bb = sb.cs_current_bb /\ ~s2.vs_halted /\
   s2.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory` by
    simp[mcopy_def, write_memory_with_expansion_def] >>
  simp[mcopy_def, write_memory_with_expansion_def] >>
  gvs[] >> metis_tac[]
QED
