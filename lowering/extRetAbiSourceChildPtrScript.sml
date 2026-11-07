Theory extRetAbiSourceChildPtr
Ancestors extRetAbiChildComposePtr extRetAbiSourceBytesCountedPtr
  abiEncoderChildContext abiEncoderChildCode robustCopyTransportPtr
  exprLoweringProps emitHelperProps bodyPtrDefs loweringPosts valueEncoding vyperTyping
  emitHelper compileEnv ptrDiscipline venomState words list finite_map pred_set arithmetic

Theorem abi_dynamic_bytes_source_child_counted_ptr:
  compile_abi_encode_child (Var dst) (Var src)
    (type_to_abi_enc_info fields ce (BaseT (BytesT (Dynamic N)))) T h (Var ip) sa = (out,sb) /\
  n = 32+ceil32 (LENGTH bs) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\ not_fresh_at sa dst /\
  lookup_var dst s = SOME (n2w b) /\ b+cap < dimword(:256) /\
  ptr_covers G tn dst s cap /\ h+32 <= cap /\ k <= cap /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor < dimword(:256) /\
  ptr_covers G tn ip s 32 /\ mload cursor s = n2w k /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tn.t_mem) /\
  h+32 <= k /\ k+n < dimword(:256) /\ k+n <= cap /\
  (cursor+32 <= b+k \/ b+k+n <= cursor) /\
  not_fresh_at sa src /\ lookup_var src s = SOME a /\
  ptr_covers G tn src s (32+LENGTH bs) /\
  32+LENGTH bs <= type_memory_size (BaseTV (BytesT (Dynamic N))) /\
  LENGTH bs <= dimword(:256)-32 /\ n < dimword(:256) /\
  w2n a+(32+LENGTH bs) < dimword(:256) /\
  (w2n a+(32+LENGTH bs) <= b+k \/ b+k+n <= w2n a) /\
  (w2n a+(32+LENGTH bs) <= b+h \/ b+h+32 <= w2n a) /\
  (w2n a+(32+LENGTH bs) <= cursor \/ cursor+32 <= w2n a) /\
  value_has_type (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV bs) /\
  val_wf (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV bs) /\ N < dimword(:256) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV bs) (w2n a) mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    mload cursor sf = n2w (k+n) /\
    (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem) /\
    (!i. b+k <= i /\ i < b+k+n ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside ({i | b+k <= i /\ i < b+k+n} UNION
      {i | b+h <= i /\ i < b+h+32} UNION {i | cursor <= i /\ i < cursor+32})
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN ({i | b+k <= i /\ i < b+k+n} UNION
      {i | b+h <= i /\ i < b+h+32} UNION {i | cursor <= i /\ i < cursor+32}) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      val_in_memory (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV bs) (w2n a) mem')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    mload cursor sf = n2w (k+n) /\
    (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem) /\
    (!i. b+k <= i /\ i < b+k+n ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside ({i | b+k <= i /\ i < b+k+n} UNION
      {i | b+h <= i /\ i < b+h+32} UNION {i | cursor <= i /\ i < cursor+32})
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN ({i | b+k <= i /\ i < b+k+n} UNION
      {i | b+h <= i /\ i < b+h+32} UNION {i | cursor <= i /\ i < cursor+32}) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))` by
    (irule abi_dynamic_child_compose_counted_ptr >> simp[] >>
     qexistsl_tac [`cap`, `dst`] >>
     goal_assum (drule_at (Pat `compile_abi_encode_child _ _ _ _ _ _ _ = _`)) >> simp[] >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `not_fresh_at sc head /\ not_fresh_at sc off /\ not_fresh_at sc child /\
      (!v. not_fresh_at sa v ==> not_fresh_at sc v)` by
       (qpat_x_assum `abi_encode_child_prefix _ _ _ _ = _` mp_tac >>
        simp[abi_encode_child_prefix_def, comp_bind_def, comp_return_def,
          emit_op_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
        rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[not_fresh_at_def] >> decide_tac) >>
     `fn_has_code sc sd fn` by
       (drule_all abi_encoder_dynamic_child_context >> strip_tac >> gvs[]) >>
     `not_fresh_at sc src /\ not_fresh_at sc ip /\
      lookup_var src sp = SOME a /\ ptr_covers Gp tnp src sp (32+LENGTH bs) /\
      lookup_var ip sp = SOME (n2w cursor) /\ ptr_covers Gp tnp ip sp 32 /\
      ptr_covers Gp tnp child sp (32+ceil32 (LENGTH bs))` by
       (simp[] >> rpt conj_tac
        >- (qpat_x_assum `ptr_covers G tn src s _` mp_tac >> simp[ptr_covers_def])
        >- (qpat_x_assum `ptr_covers G tn ip s _` mp_tac >> simp[ptr_covers_def]) >>
        qpat_x_assum `ptr_covers Gp tnp child sp _` mp_tac >>
        simp[ptr_covers_def] >> rpt strip_tac >> qexists_tac `b'` >>
        goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >> decide_tac) >>
     `w2n (n2w (b+k) : bytes32) = b+k` by (simp[w2n_n2w] >> decide_tac) >>
     `w2n (n2w (b+k) : bytes32)+32+ceil32 (LENGTH bs) < dimword(:256)` by
       (simp[] >> decide_tac) >>
     `32+ceil32 (LENGTH bs) < dimword(:256) /\
      (!mem'. mem_agree_outside tnp.t_mem sp.vs_memory mem' ==>
       val_in_memory (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV bs) (w2n a) mem')` by
       (simp[] >> decide_tac) >>
     drule compile_abi_encode_source_bytes_counted_ptr >>
     disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
     disch_then (drule_at (Pat `ptr_covers _ _ _ _ (32+LENGTH _)`)) >>
     disch_then (drule_at (Pat `lookup_var child _ = _`)) >>
     disch_then (drule_at (Pat `lookup_var src _ = _`)) >>
     disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
     disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
     (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
     qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
     rpt conj_tac >> rpt strip_tac >> simp[]
     >- (qpat_x_assum `ptr_covers Gp tnp head sp 32` mp_tac >> simp[ptr_covers_def])
     >- (qpat_x_assum `ptr_covers Gp tnp ip sp 32` mp_tac >> simp[ptr_covers_def]) >>
     qpat_x_assum `mem_agree_outside _ sf.vs_memory sp.vs_memory` mp_tac >> simp[]) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- asm_rewrite_tac[] >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
    `{i | b+k <= i /\ i < b+k+n} UNION {i | b+h <= i /\ i < b+h+32} UNION
     {i | cursor <= i /\ i < cursor+32}`] >>
  simp[val_footprint_def] >>
  qpat_x_assum `mem_agree_outside _ sf.vs_memory s.vs_memory` mp_tac >>
  simp[mem_agree_outside_def] >> metis_tac[]
QED

Theorem source_string_memory_as_bytes[local]:
  val_in_memory (BaseTV (StringT N)) (StringV text) a mem <=>
  val_in_memory (BaseTV (BytesT (Dynamic N)))
    (vyperValue$BytesV (MAP (n2w o ORD) text)) a mem
Proof
  simp[val_in_memory_def]
QED

Theorem abi_dynamic_string_source_child_counted_ptr:
  compile_abi_encode_child (Var dst) (Var src)
    (type_to_abi_enc_info fields ce (BaseT (StringT N))) T h (Var ip) sa = (out,sb) /\
  n = 32+ceil32 (LENGTH text) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\ not_fresh_at sa dst /\
  lookup_var dst s = SOME (n2w b) /\ b+cap < dimword(:256) /\
  ptr_covers G tn dst s cap /\ h+32 <= cap /\ k <= cap /\
  lookup_var ip s = SOME (n2w cursor) /\ cursor < dimword(:256) /\
  ptr_covers G tn ip s 32 /\ mload cursor s = n2w k /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tn.t_mem) /\
  h+32 <= k /\ k+n < dimword(:256) /\ k+n <= cap /\
  (cursor+32 <= b+k \/ b+k+n <= cursor) /\
  not_fresh_at sa src /\ lookup_var src s = SOME a /\
  ptr_covers G tn src s (32+LENGTH text) /\
  32+LENGTH text <= type_memory_size (BaseTV (StringT N)) /\
  LENGTH text <= dimword(:256)-32 /\ n < dimword(:256) /\
  w2n a+(32+LENGTH text) < dimword(:256) /\
  (w2n a+(32+LENGTH text) <= b+k \/ b+k+n <= w2n a) /\
  (w2n a+(32+LENGTH text) <= b+h \/ b+h+32 <= w2n a) /\
  (w2n a+(32+LENGTH text) <= cursor \/ cursor+32 <= w2n a) /\
  value_has_type (BaseTV (StringT N)) (StringV text) /\
  val_wf (BaseTV (StringT N)) (StringV text) /\ N < dimword(:256) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (BaseTV (StringT N)) (StringV text) (w2n a) mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    mload cursor sf = n2w (k+n) /\
    (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem) /\
    (!i. b+k <= i /\ i < b+k+n ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside ({i | b+k <= i /\ i < b+k+n} UNION
      {i | b+h <= i /\ i < b+h+32} UNION {i | cursor <= i /\ i < cursor+32})
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN ({i | b+k <= i /\ i < b+k+n} UNION
      {i | b+h <= i /\ i < b+h+32} UNION {i | cursor <= i /\ i < cursor+32}) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      val_in_memory (BaseTV (StringT N)) (StringV text) (w2n a) mem')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  pure_rewrite_tac [source_string_memory_as_bytes] >>
  irule abi_dynamic_bytes_source_child_counted_ptr >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [source_string_memory_as_bytes,
    value_has_type_def, val_wf_def, type_memory_size_def]) >>
  simp[value_has_type_def, val_wf_def, type_memory_size_def] >>
  qexistsl_tac [`cap`, `ce`, `dst`, `fields`, `ip`, `out`, `src`] >>
  gvs[exprLoweringTheory.type_to_abi_enc_info_def]
QED
