(* Typed semantic adapter for the one-field counted bytestring path. *)
Theory assignBasePtrTypedBytesField
Ancestors assignBasePtrBytesField typedCopyAgreement valueCopyBytes
  valueTypingMemoryProps representationCleanPtr typedCopyRobustTransportPtr
  valueEncoding valueEncodingProps loweringPosts vyperTyping vfmConstants
  venomState bodyPtrDefs ptrDiscipline words list arithmetic

Theorem assign_base_typed_bytes_source[local]:
  !tenv ty tv v len n tn s p.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ n = 32+32*((len+31) DIV 32) /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v p m) ==>
    val_wf tv v /\ val_footprint tv v <= n /\
    n = 32+32*word_size len /\ mload p s = n2w len /\
    (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem)
Proof
  rpt gen_tac >> strip_tac >>
  `val_wf tv v` by metis_tac[value_has_type_memory_wf] >>
  `val_in_memory tv v p s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  qspec_then `len` assume_tac word_size_capacity >>
  drule_all bytestring_type_value >> strip_tac >>
  gvs[value_has_type_def, val_footprint_def, word_size_def] >>
  (conj_tac >- fs[val_in_memory_def, mem_word_at_eq_mload] >>
   FIRST [drule robust_val_in_memory_bytes_clean,
          drule robust_val_in_memory_string_clean] >> simp[])
QED

Theorem assign_base_typed_bytestring_field_counted:
  !ctx PG D fn cenv dst src doff soff sa sb sc sd dp sp G tn s a b
   dtotal stotal n len tenv sty dty stv dtv v.
    compile_with_byte_offset (Var dst) doff sa = (dp,sb) /\
    compile_with_byte_offset (Var src) soff sb = (sp,sc) /\
    compile_store_memory_typed cenv dp dty sp sty sc = ((),sd) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s dtotal /\ ptr_covers G tn src s stotal /\
    doff < dtotal /\ doff+n <= dtotal /\
    soff < stotal /\ soff+n <= stotal /\
    w2n b+doff < dimword(:256) /\ w2n a+soff < dimword(:256) /\
    n = 32+32*((len+31) DIV 32) /\
    len+31 < dimword(:256) /\ n < dimword(:256) /\
    is_bytestring_type sty /\ is_bytestring_type dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a+soff) m) /\
    fn_has_code sa sd fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx ==>
    cs_extends sa sd /\ sa.cs_next_var <= sd.cs_next_var /\
    ?Gf tnf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
      sf.vs_current_bb = sd.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~sf.vs_halted /\
      (!i. ~(w2n b+doff <= i /\ i < w2n b+doff+n) ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!i. ~(w2n b+doff <= i /\ i < w2n b+doff+n) ==>
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b+doff) m) /\
      (!ft fv p. val_wf ft fv /\
        (p+type_memory_size ft <= w2n b+doff \/ w2n b+doff+n <= p) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          val_in_memory ft fv p m) ==>
        !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
          val_in_memory ft fv p m)
Proof
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `compile_store_bytestring sp dp sc = ((),sd)` by
    metis_tac[compile_store_memory_typed_bytes] >>
  drule_all assign_base_typed_bytes_source >> strip_tac >>
  drule_all assign_base_bytestring_field_robust_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  simp[] >> qexistsl_tac [`Gf`, `tf`, `u`] >>
  suspend "post"
QED

Resume assign_base_typed_bytestring_field_counted[post]:
  `!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
     val_in_memory dtv v (w2n b+doff) m` by
    (rpt strip_tac >> metis_tac[bytestring_val_in_memory_transfer]) >>
  `!i. ~(w2n b+doff <= i /\ i < w2n b+doff+n) ==>
     mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!i. ~(w2n b+doff <= i /\ i < w2n b+doff+n) ==>
     (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!ft fv p. val_wf ft fv /\
     (p+type_memory_size ft <= w2n b+doff \/ w2n b+doff+n <= p) /\
     (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory ft fv p m) ==>
     !m. mem_agree_outside tf.t_mem u.vs_memory m ==>
       val_in_memory ft fv p m` by
    (drule robust_representation_exterior_frame >>
     disch_then drule >> metis_tac[]) >>
  qpat_x_assum `n = 32+32*((len+31) DIV 32)` kall_tac >>
  qpat_x_assum `(?bs. _) \/ _` kall_tac >>
  qpat_x_assum `n = _` SUBST_ALL_TAC >>
  full_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM] >> metis_tac[]
QED

Finalise assign_base_typed_bytestring_field_counted
