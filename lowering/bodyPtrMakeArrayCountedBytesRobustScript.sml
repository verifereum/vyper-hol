Theory bodyPtrMakeArrayCountedBytesRobust
Ancestors
  bodyPtrMakeArrayCountedBytes bodyPtrMakeArrayBytesTransport
  typedCopyRobustTransportPtr bodyPtrDefs valueCopyBytes valueEncodingProps
  fragGasPathPtr venomState

Theorem bytestring_store_robust_counted:
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  fn_has_code sa sb fn /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  n = 32 + 32 * ((len + 31) DIV 32) /\
  len + 31 < dimword (:256) /\ n < dimword (:256) /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv v (w2n a) m) ==>
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
      ptr_covers Gf tnf x sf size) /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory dtv v (w2n b) m) /\
    (!ft fv p. val_wf ft fv /\
      (p + type_memory_size ft <= w2n b \/ w2n b + n <= p) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory ft fv p m) ==>
      !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory ft fv p m)
Proof
  disch_tac >>
  `mload (w2n a) s = n2w len /\
   (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
   (!i. w2n a + 32 <= i /\ i < w2n a + 32 + len ==> i NOTIN tn.t_mem)` by
    (irule robust_bytestring_source_live >> metis_tac[]) >>
  qpat_x_assum `_ /\ _` (map_every assume_tac o CONJUNCTS) >>
  drule_all bytestring_store_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `32 <= n /\ 32 + len <= n` by
    (qspec_then `32` mp_tac arithmeticTheory.DIVISION >>
     (impl_tac >- decide_tac) >>
     disch_then (qspec_then `len+31` strip_assume_tac) >>
     qpat_x_assum `n = _` SUBST1_TAC >> decide_tac) >>
  `!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
     val_in_memory dtv v (w2n b) m` by
    (rpt strip_tac >> drule_all robust_bytestring_copied_endpoint >> simp[]) >>
  `!i. ~(w2n b <= i /\ i < w2n b+n) ==>
    mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory` by metis_tac[] >>
  `!i. ~(w2n b <= i /\ i < w2n b+n) ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem)` by metis_tac[] >>
  drule robust_representation_exterior_frame >> disch_then drule >>
  disch_then (assume_tac o SIMP_RULE bool_ss [AND_IMP_INTRO]) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac[] >> gvs[] >> metis_tac[]
QED
