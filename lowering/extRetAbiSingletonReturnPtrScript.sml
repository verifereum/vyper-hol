(* Counted singleton bytes encoding and its immediately emitted RETURN.
   Destination allocation and all source/cursor resources remain explicit. *)
Theory extRetAbiSingletonReturnPtr
Ancestors
  extRetAbiSingletonLivePtr extRetAbiStorageFramePtr extRetAbiSingletonWrapperPtr extRetAbiReturnConsumerPtr
  extRetCountedPtr emitHelperProps exprLoweringProps abiBuiltinAllocation
  bodyPtrDefs ptrDiscipline venomState compileEnv emitHelper exprLowering
  valueEncodingProofs words finite_map pred_set arithmetic

Theorem compile_abi_encode_singleton_bytes_live_return_counted_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src)
    (AbiComplex [(AbiBytestring maxlen,32,cap,T)]) sa = (out,sb) /\
  emit_inst RETURN [Var dst;out] [] sb = (u,sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
  ptr_covers G tn src s (32+LENGTH bs) /\ ptr_covers G tn dst s (64+ceil32 (LENGTH bs)) /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (cursor,32) /\ cursor+32 < dimword(:256) /\
  (cursor+32 <= a \/ a+(32+LENGTH bs) <= cursor) /\
  (cursor+32 <= b \/ b+64+ceil32 (LENGTH bs) <= cursor) /\
  32+LENGTH bs <= cap /\ LENGTH bs <= dimword(:256)-32 /\
  32+ceil32 (LENGTH bs) < dimword(:256) /\
  a+(32+LENGTH bs) < dimword(:256) /\ b+64+ceil32 (LENGTH bs) < dimword(:256) /\
  (a+(32+LENGTH bs) <= b \/ b+64+ceil32 (LENGTH bs) <= a) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a cap mem') /\
  stor_taint_ok cx tn s ==>
  ?Gf tnf t.
    gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 Gf tnf (Halt t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?len. out = Var len` by
    (drule_all abi_singleton_wrapper_context >> strip_tac >>
     metis_tac[emitted_insts_emit_op]) >>
  qpat_x_assum `out = Var _` SUBST_ALL_TAC >>
  drule_all compile_abi_encode_singleton_bytes_live_stor_counted_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `lookup_var dst sf = SOME (n2w b)` by metis_tac[] >>
  `64+ceil32 (LENGTH bs) < dimword(:256) /\ b < dimword(:256)` by decide_tac >>
  `lookup_var len sf = SOME (n2w (64+ceil32 (LENGTH bs)))` by
    fs[eval_operand_def] >>
  `!i. b <= i /\ i < b+(64+ceil32 (LENGTH bs)) ==> i NOTIN tnf.t_mem` by
    metis_tac[ADD_ASSOC] >>
  drule_all gas_path_ptr_then_emit_return_clean >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `t`] >> simp[]
QED

Theorem compile_abi_encode_singleton_bytes_return_counted_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src)
    (AbiComplex [(AbiBytestring maxlen,32,cap,T)]) sa = (out,sb) /\
  emit_inst RETURN [Var dst;out] [] sb = (u,sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
  ptr_covers G tn src s cap /\ ptr_covers G tn dst s (64+ceil32 (LENGTH bs)) /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (cursor,32) /\ cursor+32 < dimword(:256) /\
  (cursor+32 <= a \/ a+cap <= cursor) /\
  (cursor+32 <= b \/ b+64+ceil32 (LENGTH bs) <= cursor) /\
  32+LENGTH bs <= cap /\ LENGTH bs <= dimword(:256)-32 /\
  32+ceil32 (LENGTH bs) < dimword(:256) /\
  a+cap < dimword(:256) /\ b+64+ceil32 (LENGTH bs) < dimword(:256) /\
  (a+cap <= b \/ b+64+ceil32 (LENGTH bs) <= a) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a cap mem') /\
  stor_taint_ok cx tn s ==>
  ?Gf tnf t.
    gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 Gf tnf (Halt t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_covers G tn src s (32+LENGTH bs)` by
    (qpat_assum `ptr_covers G tn src s cap` mp_tac >>
     rewrite_tac[ptr_covers_def] >> rpt strip_tac >>
     simp[] >> qexistsl_tac [`w`, `b'`, `sz'`] >> simp[] >> decide_tac) >>
  `a+(32+LENGTH bs) < dimword(:256)` by decide_tac >>
  Q.SUBGOAL_THEN `(cursor+32 <= a \/ a+(32+LENGTH bs) <= cursor)` assume_tac
  >- decide_tac >>
  Q.SUBGOAL_THEN `(a+(32+LENGTH bs) <= b \/ b+64+ceil32 (LENGTH bs) <= a)` assume_tac
  >- decide_tac >>
  drule_all compile_abi_encode_singleton_bytes_live_return_counted_ptr >> simp[]
QED
