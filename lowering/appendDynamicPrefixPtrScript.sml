(* Finite same-element Dynamic copy prefix, before MCOPY. *)
Theory appendDynamicPrefixPtr
Ancestors appendDynamicPointerAddPtr appendDynamicHeaderStorePtr
  appendDynamicPurePtr typedCopyAmbientFramePtr fragExecPtr
  valueEncodingProps bodyPtrDefs loweringStateRelDefs contextCodegenRel
  compileEnv context emitHelper venomState venomInst words finite_map fragGasSeqPtr
  abiDecodeStaticProps emitHelperProps exprLoweringProps list rich_list

Theorem dynamic_emit_op_fields[local]:
  !opc ops sa out sb.
    emit_op opc ops sa = (Var out,sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ [mk_inst sa.cs_next_id opc ops [out]] /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sa.cs_next_var <= sb.cs_next_var /\ not_fresh_at sb out /\ cs_extends sa sb
Proof
  rpt strip_tac >>
  drule loweringShapeRulesTheory.emit_op_facts >> strip_tac >> gvs[] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def, cs_extends_def]
QED

Theorem dynamic_emit_void_fields[local]:
  !opc ops sa sb.
    emit_void opc ops sa = ((),sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ [mk_inst sa.cs_next_id opc ops []] /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_next_var = sa.cs_next_var /\ cs_extends sa sb
Proof
  rpt strip_tac >>
  gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
      comp_return_def, cs_extends_def]
QED

Theorem append_dynamic_prefix_shape:
  !sa s1 s2 s3 s4 s5 s6 s7 sb src dst len gt ok sd dd cnt dn esz.
    emit_op MLOAD [Var src] sa = (Var len,s1) /\
    emit_op GT [Var len;Lit (n2w dn)] s1 = (Var gt,s2) /\
    emit_op ISZERO [Var gt] s2 = (Var ok,s3) /\
    emit_void ASSERT [Var ok] s3 = ((),s4) /\
    emit_void MSTORE [Var dst;Var len] s4 = ((),s5) /\
    emit_op ADD [Var src;Lit 32w] s5 = (Var sd,s6) /\
    emit_op ADD [Var dst;Lit 32w] s6 = (Var dd,s7) /\
    emit_op MUL [Var len;Lit (n2w esz)] s7 = (Var cnt,sb) ==>
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id MLOAD [Var src] [len];
       mk_inst s1.cs_next_id GT [Var len;Lit (n2w dn)] [gt];
       mk_inst s2.cs_next_id ISZERO [Var gt] [ok];
       mk_inst s3.cs_next_id ASSERT [Var ok] [];
       mk_inst s4.cs_next_id MSTORE [Var dst;Var len] [];
       mk_inst s5.cs_next_id ADD [Var src;Lit 32w] [sd];
       mk_inst s6.cs_next_id ADD [Var dst;Lit 32w] [dd];
       mk_inst s7.cs_next_id MUL [Var len;Lit (n2w esz)] [cnt]] /\
    sb.cs_current_bb = sa.cs_current_bb /\ cs_extends sa sb /\
    sa.cs_next_var <= s1.cs_next_var /\
    s1.cs_next_var <= s2.cs_next_var /\
    s2.cs_next_var <= s3.cs_next_var /\
    s3.cs_next_var = s4.cs_next_var /\
    s4.cs_next_var = s5.cs_next_var /\
    s5.cs_next_var <= s6.cs_next_var /\
    s6.cs_next_var <= s7.cs_next_var /\
    s7.cs_next_var <= sb.cs_next_var /\ not_fresh_at s1 len /\
    not_fresh_at s6 sd /\ not_fresh_at s7 dd /\ not_fresh_at sb cnt /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
    cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s5 s6 /\
    cs_extends s6 s7 /\ cs_extends s7 sb
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  imp_res_tac dynamic_emit_op_fields >>
  imp_res_tac dynamic_emit_void_fields >>
  conj_tac >-
    simp[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[] >> metis_tac[cs_extends_trans]
QED

Theorem dynamic_inst_seq_advanced_cons[local]:
  !v s i PG G H tn tm D lo ctx fn code Gf tf.
    v.vs_inst_idx = SUC s.vs_inst_idx /\
    step_inst_base i s = OK (v with vs_inst_idx := s.vs_inst_idx) /\
    step_prov PG G i (v with vs_inst_idx := s.vs_inst_idx) = H /\
    step_taint i s (v with vs_inst_idx := s.vs_inst_idx) tn = tm /\
    ptr_inst_ok D lo 0 ctx fn G tn i s /\
    inst_seq_ptr D lo ctx fn PG H tm code v Gf tf ==>
    inst_seq_ptr D lo ctx fn PG G tn (i::code) s Gf tf
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `((v with vs_inst_idx := s.vs_inst_idx) with
      vs_inst_idx := SUC s.vs_inst_idx) = v` by
    (qpat_assum `v.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >> simp[NoAsms]) >>
  pure_once_rewrite_tac [inst_seq_ptr_def] >>
  asm_rewrite_tac [] >> simp[]
QED

Theorem dynamic_run_advanced_cons[local]:
  !i s v code w.
    step_inst_base i s = OK (v with vs_inst_idx := s.vs_inst_idx) /\
    EVERY (\i. ~is_terminator i.inst_opcode) code /\
    run_inst_seq code v = OK (w with vs_inst_idx := v.vs_inst_idx) ==>
    run_inst_seq (i::code) s = OK (w with vs_inst_idx := s.vs_inst_idx)
Proof
  rpt strip_tac >>
  simp[Once run_inst_seq_def] >>
  drule fragExecTheory.run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`v`, `s.vs_inst_idx`] mp_tac) >>
  simp[instIdxIndepTheory.exec_result_map_def]
QED

Theorem dynamic_restore_trans[local]:
  !a b c.
    (c with <|vs_vars := b.vs_vars; vs_memory := b.vs_memory;
      vs_inst_idx := b.vs_inst_idx|>) = b /\
    (b with <|vs_vars := a.vs_vars; vs_memory := a.vs_memory;
      vs_inst_idx := a.vs_inst_idx|>) = a ==>
    (c with <|vs_vars := a.vs_vars; vs_memory := a.vs_memory;
      vs_inst_idx := a.vs_inst_idx|>) = a
Proof
  rpt strip_tac >>
  `c with <|vs_vars := a.vs_vars; vs_memory := a.vs_memory;
      vs_inst_idx := a.vs_inst_idx|> =
   (c with <|vs_vars := b.vs_vars; vs_memory := b.vs_memory;
      vs_inst_idx := b.vs_inst_idx|>) with
      <|vs_vars := a.vs_vars; vs_memory := a.vs_memory;
        vs_inst_idx := a.vs_inst_idx|>` by simp[NoAsms] >>
  metis_tac[]
QED

Theorem append_dynamic_prefix_core:
  !cx ctx PG R G tn s sa s1 s2 s3 s4 s5 s6 s7 sb
    src dst len gt ok sd dd count a b l sn dn esz.
    emit_op MLOAD [Var src] sa = (Var len,s1) /\
    emit_op GT [Var len;Lit (n2w dn)] s1 = (Var gt,s2) /\
    emit_op ISZERO [Var gt] s2 = (Var ok,s3) /\
    emit_void ASSERT [Var ok] s3 = ((),s4) /\
    emit_void MSTORE [Var dst;Var len] s4 = ((),s5) /\
    emit_op ADD [Var src;Lit 32w] s5 = (Var sd,s6) /\
    emit_op ADD [Var dst;Lit 32w] s6 = (Var dd,s7) /\
    emit_op MUL [Var len;Lit (n2w esz)] s7 = (Var count,sb) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (32+sn*esz) /\
    ptr_covers G tn dst s (32+dn*esz) /\
    mload (w2n a) s = n2w l /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
    l <= sn /\ sn <= dn /\ dn < dimword(:256) /\
    l*esz < dimword(:256) /\
    w2n a+32 < dimword(:256) /\ w2n b+32 < dimword(:256) /\
    (w2n a+32+sn*esz <= w2n b \/ w2n b+32+dn*esz <= w2n a) ==>
    ?Gf tnf sf.
      sf.vs_inst_idx = s.vs_inst_idx + 8 /\
      (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_inst_idx := s.vs_inst_idx|>) = s /\
      run_inst_seq (emitted_insts sa sb) s = OK (sf with vs_inst_idx := s.vs_inst_idx) /\
      (!D ctx fn. ~ctx_has_dalloca ctx ==>
        inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf) /\
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      lookup_var sd sf = SOME (n2w (w2n a+32)) /\
      lookup_var dd sf = SOME (n2w (w2n b+32)) /\
      ptr_covers Gf tnf sd sf (l*esz) /\
      ptr_covers Gf tnf dd sf (l*esz) /\
      lookup_var count sf = SOME (n2w (l*esz)) /\
      op_taint tnf (Var count) = {} /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        mem_word_at (w2n b) m = n2w l) /\
      mem_bytes_at (w2n a) (32+sn*esz) sf.vs_memory =
        mem_bytes_at (w2n a) (32+sn*esz) s.vs_memory /\
      (!i. i < w2n b \/ w2n b+32 <= i ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      cs_extends sa sb /\ not_fresh_at sb sd /\ not_fresh_at sb dd /\
      not_fresh_at sb count /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all append_dynamic_prefix_shape >> strip_tac >>

  qpat_x_assum `_ \/ _` strip_assume_tac >>
  `ptr_covers G tn src s 32` by
    (gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
      arithmeticTheory.LESS_EQ_ADD]) >>
  drule_all emit_mload_clean_ambient_core >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `v1` strip_assume_tac)))) >>
  `eval_operand (Var len) v1 = SOME (n2w l)` by simp[eval_operand_def] >>
  drule_all (CONV_RULE (STRIP_QUANT_CONV (LAND_CONV (SIMP_CONV (srw_ss()) [])))
    (Q.SPECL [`GT`, `(\a b. bool_to_word (w2n a > w2n b))`]
      emit_dynamic_binop_clean_core)) >>
  disch_then (qspec_then `G1` mp_tac) >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`]
    (qx_choose_then `G2` (qx_choose_then `tn2` (qx_choose_then `v2` strip_assume_tac)))) >>
  `l < dimword(:256)` by decide_tac >>
  `eval_operand (Var gt) v2 = SOME 0w` by
    (simp[eval_operand_def, arithmeticPropsTheory.bool_to_word_eq_0w] >> decide_tac) >>
  drule_all emit_dynamic_iszero_clean_core >>
  disch_then (qspec_then `G2` mp_tac) >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`]
    (qx_choose_then `G3` (qx_choose_then `tn3` (qx_choose_then `v3` strip_assume_tac)))) >>
  `eval_operand (Var ok) v3 = SOME 1w` by
    simp[eval_operand_def, arithmeticPropsTheory.bool_to_word_T] >>
  `(1w:bytes32) <> 0w` by simp[] >>
  drule_all emit_dynamic_assert_true_ptr >>
  disch_then (qspecl_then [`G3`, `cx`, `ctx`, `PG`, `R`] assume_tac) >>
  drule_all dynamic_assert_true_step_ptr >>
  disch_then (qspecl_then [`G3`, `s3.cs_next_id`, `PG`] strip_assume_tac) >>
  qabbrev_tac `v4 = v3 with vs_inst_idx := SUC v3.vs_inst_idx` >>
  `!p. not_fresh_at sa p ==> not_fresh_at s1 p /\
    not_fresh_at s2 p /\ not_fresh_at s3 p /\ not_fresh_at s4 p /\
    not_fresh_at s5 p /\ not_fresh_at s6 p /\ not_fresh_at s7 p` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `not_fresh_at s2 len /\ not_fresh_at s3 len /\ not_fresh_at s4 len /\
   not_fresh_at s5 len /\ not_fresh_at s6 len /\ not_fresh_at s7 len` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `lookup_var dst v4 = SOME b /\ eval_operand (Var len) v4 = SOME (n2w l) /\
   op_taint tn3 (Var len) = {}` by
    (simp[Abbr `v4`, lookup_var_def, eval_operand_def] >>
     metis_tac[lookup_var_def]) >>
  `ptr_covers G3 tn3 dst v4 32` by
    (gvs[ptr_covers_def, Abbr `v4`, lookup_var_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  drule_all emit_dynamic_header_store_core >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`]
    (qx_choose_then `tn5` (qx_choose_then `v5` strip_assume_tac))) >>
  `lookup_var src v5 = SOME a /\ lookup_var dst v5 = SOME b /\
   ptr_covers G3 tn5 src v5 (32+sn*esz) /\
   ptr_covers G3 tn5 dst v5 (32+dn*esz)` by
    (gvs[ptr_covers_def, Abbr `v4`, lookup_var_def] >> metis_tac[]) >>
  `32+l*esz <= 32+sn*esz /\ 32+l*esz <= 32+dn*esz` by
    (simp[] >> conj_tac >> irule arithmeticTheory.LESS_MONO_MULT2 >> decide_tac) >>
  `not_fresh_at s5 src /\ not_fresh_at s6 dst` by metis_tac[] >>
  qpat_x_assum `emit_op ADD _ s6 = _` mp_tac >>
  drule_all (Q.GENL [`cx`, `ctx`, `PG`, `R`]
    (CONV_RULE (STRIP_QUANT_CONV (LAND_CONV (SIMP_CONV (srw_ss()) []))) (Q.INST [`n` |-> `l*esz`, `off` |-> `32`]
      (SPEC_ALL emit_dynamic_pointer_add_core)))) >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`]
    (qx_choose_then `G6` (qx_choose_then `tn6` (qx_choose_then `v6` strip_assume_tac)))) >>
  disch_tac >>
  qpat_x_assum `emit_op ADD _ s5 = _` mp_tac >>
  `lookup_var dst v6 = SOME b /\ ptr_covers G6 tn6 dst v6 (32+dn*esz)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  drule_all (Q.GENL [`cx`, `ctx`, `PG`, `R`]
    (CONV_RULE (STRIP_QUANT_CONV (LAND_CONV (SIMP_CONV (srw_ss()) []))) (Q.INST [`n` |-> `l*esz`, `off` |-> `32`, `root` |-> `dst`,
      `s` |-> `v6`] (SPEC_ALL emit_dynamic_pointer_add_core)))) >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`]
    (qx_choose_then `G7` (qx_choose_then `tn7` (qx_choose_then `v7` strip_assume_tac)))) >>
  disch_tac >>
  `eval_operand (Var len) v7 = SOME (n2w l) /\ op_taint tn7 (Var len) = {}` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  drule_all (CONV_RULE (STRIP_QUANT_CONV (LAND_CONV (SIMP_CONV (srw_ss()) [])))
    (Q.SPECL [`MUL`, `word_mul`] emit_dynamic_binop_clean_core)) >>
  disch_then (qspec_then `G7` mp_tac) >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`]
    (qx_choose_then `G8` (qx_choose_then `tn8` (qx_choose_then `v8` strip_assume_tac)))) >>
  qexistsl_tac [`G8`, `tn8`, `v8`] >>
  (conj_tac >- (simp[Abbr `v4`] >> decide_tac)) >>
  (conj_tac >-
    (`v4 with <|vs_vars := v3.vs_vars; vs_memory := v3.vs_memory;
        vs_inst_idx := v3.vs_inst_idx|> = v3` by simp[Abbr `v4`, NoAsms] >>
     irule dynamic_restore_trans >> qexists_tac `v7` >> asm_rewrite_tac[] >>
     irule dynamic_restore_trans >> qexists_tac `v6` >> asm_rewrite_tac[] >>
     irule dynamic_restore_trans >> qexists_tac `v5` >> asm_rewrite_tac[] >>
     irule dynamic_restore_trans >> qexists_tac `v4` >> asm_rewrite_tac[] >>
     irule dynamic_restore_trans >> qexists_tac `v3` >> asm_rewrite_tac[] >>
     irule dynamic_restore_trans >> qexists_tac `v2` >> asm_rewrite_tac[] >>
     irule dynamic_restore_trans >> qexists_tac `v1` >> asm_rewrite_tac[])) >>
  (conj_tac >-
    (qpat_assum `emitted_insts _ _ = _` (fn th => pure_rewrite_tac[th]) >>
     rpt (qpat_x_assum `_.vs_inst_idx = _` kall_tac) >>
     irule dynamic_run_advanced_cons >>
     (reverse conj_tac >- simp[mk_inst_def, is_terminator_def]) >> qexists_tac `v1` >>
     asm_rewrite_tac [] >>
     irule dynamic_run_advanced_cons >>
     (reverse conj_tac >- simp[mk_inst_def, is_terminator_def]) >> qexists_tac `v2` >>
     asm_rewrite_tac [] >>
     irule dynamic_run_advanced_cons >>
     (reverse conj_tac >- simp[mk_inst_def, is_terminator_def]) >> qexists_tac `v3` >>
     asm_rewrite_tac [] >>
     `v4 with vs_inst_idx := v3.vs_inst_idx = v3` by simp[Abbr `v4`, NoAsms] >>
     irule dynamic_run_advanced_cons >>
     (reverse conj_tac >- simp[mk_inst_def, is_terminator_def]) >> qexists_tac `v4` >>
     asm_rewrite_tac [] >>
     irule dynamic_run_advanced_cons >>
     (reverse conj_tac >- simp[mk_inst_def, is_terminator_def]) >> qexists_tac `v5` >>
     asm_rewrite_tac [] >>
     irule dynamic_run_advanced_cons >>
     (reverse conj_tac >- simp[mk_inst_def, is_terminator_def]) >> qexists_tac `v6` >>
     asm_rewrite_tac [] >>
     irule dynamic_run_advanced_cons >>
     (reverse conj_tac >- simp[mk_inst_def, is_terminator_def]) >> qexists_tac `v7` >>
     asm_rewrite_tac [] >>
     simp[run_inst_seq_def])) >>
  (conj_tac >-
    (rpt strip_tac >>
     qpat_x_assum `emitted_insts _ _ = _` (fn th => pure_rewrite_tac[th]) >>
     irule dynamic_inst_seq_advanced_cons >>
     (conj_tac >- metis_tac[]) >>
     qexistsl_tac [`G1`, `tn1`, `v1`] >> asm_rewrite_tac [] >>
     irule dynamic_inst_seq_advanced_cons >>
     (conj_tac >- metis_tac[]) >>
     qexistsl_tac [`G2`, `tn2`, `v2`] >> asm_rewrite_tac [] >>
     irule dynamic_inst_seq_advanced_cons >>
     (conj_tac >- metis_tac[]) >>
     qexistsl_tac [`G3`, `tn3`, `v3`] >> asm_rewrite_tac [] >>
     `v4.vs_inst_idx = SUC v3.vs_inst_idx /\
      (v4 with vs_inst_idx := v3.vs_inst_idx) = v3` by
       simp[Abbr `v4`, NoAsms] >>
     irule dynamic_inst_seq_advanced_cons >>
     (conj_tac >- metis_tac[]) >>
     qexistsl_tac [`G3`, `tn3`, `v4`] >> asm_rewrite_tac [] >>
     irule dynamic_inst_seq_advanced_cons >>
     (conj_tac >- metis_tac[]) >>
     qexistsl_tac [`G3`, `tn5`, `v5`] >> asm_rewrite_tac [] >>
     irule dynamic_inst_seq_advanced_cons >>
     (conj_tac >- metis_tac[]) >>
     qexistsl_tac [`G6`, `tn6`, `v6`] >> asm_rewrite_tac [] >>
     irule dynamic_inst_seq_advanced_cons >>
     (conj_tac >- metis_tac[]) >>
     qexistsl_tac [`G7`, `tn7`, `v7`] >> asm_rewrite_tac [] >>
     irule dynamic_inst_seq_advanced_cons >>
     (conj_tac >- metis_tac[]) >>
     qexistsl_tac [`G8`, `tn8`, `v8`] >> asm_rewrite_tac [] >>
     simp[inst_seq_ptr_def])) >>
  qpat_x_assum `emitted_insts _ _ = _` kall_tac >>
  (conj_tac >-
    (irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ s7 sb _ _ _` (irule_at Any) >>
     simp[] >> (conj_tac >- metis_tac[cs_extends_trans]) >>
     irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ s6 s7 _ _ _` (irule_at Any) >>
     simp[] >> (conj_tac >- metis_tac[cs_extends_trans]) >>
     irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ s5 s6 _ _ _` (irule_at Any) >>
     simp[] >> (conj_tac >- metis_tac[cs_extends_trans]) >>
     irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ s4 s5 _ _ _` (irule_at Any) >>
     simp[] >> (conj_tac >- metis_tac[cs_extends_trans]) >>
     irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ s3 s4 _ _ _` (irule_at Any) >>
     simp[] >> (conj_tac >- metis_tac[cs_extends_trans]) >>
     irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ s2 s3 _ _ _` (irule_at Any) >>
     simp[] >> (conj_tac >- metis_tac[cs_extends_trans]) >>
     irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ s1 s2 _ _ _` (irule_at Any) >>
     simp[] >> metis_tac[])) >>
  rpt (qpat_x_assum `step_inst_base _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `step_prov _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `step_taint _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `!D fuel ctx fn. _` kall_tac) >>
  rpt (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = _` kall_tac) >>
  `not_fresh_at s7 sd /\ not_fresh_at sb sd /\ not_fresh_at sb dd` by
    (gvs[not_fresh_at_def] >> decide_tac) >>
  rename1 `emit_op MUL _ s7 = (Var bytecount,sb)` >>
  `not_fresh_at sb bytecount` by
    (qpat_assum `emit_op MUL _ s7 = _`
       (mp_then Any mp_tac loweringShapeRulesTheory.emit_op_facts) >> simp[]) >>
  rpt (qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_void _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `step_inst_base _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `step_prov _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `step_taint _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `!D fuel ctx fn. _` kall_tac) >>
  rpt (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = _` kall_tac) >>
  gvs[Abbr `v4`, GSYM word_mul_n2w] >>
  (conj_tac >- (gvs[ptr_covers_def] >> metis_tac[])) >>
  (conj_tac >- (gvs[ptr_covers_def] >> metis_tac[])) >>
  (conj_tac >-
    (irule mem_bytes_at_bytewise >> rpt strip_tac >>
     `i < w2n b \/ w2n b+32 <= i` by decide_tac >> metis_tac[])) >>
  (conj_tac >- metis_tac[]) >>
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

Theorem append_dynamic_prefix_ptr_conditional:
  !cx ctx PG R G tn s sa s1 s2 s3 s4 s5 s6 s7 sb
    src dst len gt ok sd dd count a b l sn dn esz.
    emit_op MLOAD [Var src] sa = (Var len,s1) /\
    emit_op GT [Var len;Lit (n2w dn)] s1 = (Var gt,s2) /\
    emit_op ISZERO [Var gt] s2 = (Var ok,s3) /\
    emit_void ASSERT [Var ok] s3 = ((),s4) /\
    emit_void MSTORE [Var dst;Var len] s4 = ((),s5) /\
    emit_op ADD [Var src;Lit 32w] s5 = (Var sd,s6) /\
    emit_op ADD [Var dst;Lit 32w] s6 = (Var dd,s7) /\
    emit_op MUL [Var len;Lit (n2w esz)] s7 = (Var count,sb) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (32+sn*esz) /\
    ptr_covers G tn dst s (32+dn*esz) /\
    mload (w2n a) s = n2w l /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
    l <= sn /\ sn <= dn /\ dn < dimword(:256) /\
    l*esz < dimword(:256) /\
    w2n a+32 < dimword(:256) /\ w2n b+32 < dimword(:256) /\
    (w2n a+32+sn*esz <= w2n b \/ w2n b+32+dn*esz <= w2n a) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      lookup_var sd sf = SOME (n2w (w2n a+32)) /\
      lookup_var dd sf = SOME (n2w (w2n b+32)) /\
      ptr_covers Gf tnf sd sf (l*esz) /\
      ptr_covers Gf tnf dd sf (l*esz) /\
      lookup_var count sf = SOME (n2w (l*esz)) /\
      op_taint tnf (Var count) = {} /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        mem_word_at (w2n b) m = n2w l) /\
      mem_bytes_at (w2n a) (32+sn*esz) sf.vs_memory =
        mem_bytes_at (w2n a) (32+sn*esz) s.vs_memory /\
      (!i. i < w2n b \/ w2n b+32 <= i ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      cs_extends sa sb /\ not_fresh_at sb sd /\ not_fresh_at sb dd /\
      not_fresh_at sb count /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all append_dynamic_prefix_core >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac []
QED
