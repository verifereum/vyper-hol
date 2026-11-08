(* Pointer checks and ghost frames for the bytes encoder's arithmetic phases. *)
Theory logAbiPrefixPtr
Ancestors
  logInstSeqPtr abiEncoderBytesCode abiEncoderRounding bodyPtrDefs
  typedCopyPtr fragExecPtr fragExec ptrDiscipline ptrSafeRun
  emitHelperProps emitHelper compileEnv context exprLoweringProps
  venomExecSemantics venomState venomInst finite_map words list arithmetic

Theorem abi_encode_round_seq_ptr:
  abi_encode_round len sa = (out,sb) /\
  eval_operand len s = SOME w /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    eval_operand out sf = SOME
      (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w && (31w+w)) /\
    op_taint tnf out = {} /\ op_prov Gf out = NONE /\
    sf.vs_memory = s.vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  simp_tac bool_ss [abi_encode_round_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [Lit 31w;len] sa = (arg,sm)` >>
  `?tmp. arg = Var tmp` by (qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> metis_tac[]) >>
  `?res. out = Var res` by
    (qpat_assum `emit_op AND _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> metis_tac[]) >>
  gvs[] >>
  `eval_operand (Lit 31w) s = SOME 31w /\ op_taint tn (Lit 31w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    emit_copy_len_binop_seq_ptr)) >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `t` strip_assume_tac)))) >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)` >>
  `eval_operand (Var tmp) u = SOME (31w+w) /\
   eval_operand (Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w) u =
     SOME 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w /\
   op_taint tn1 (Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w) = {}` by
    gvs[Abbr `u`, eval_operand_def, lookup_var_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `AND`, `f` |-> `word_and`]
    emit_copy_len_binop_seq_ptr)) >>
  disch_then (qspecl_then [`fn`, `PG`, `G1`, `D`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `v` strip_assume_tac)))) >>
  qexistsl_tac [`Gf`, `tnf`, `v with vs_inst_idx := t.vs_inst_idx`] >>
  conj_tac >- suspend "run" >>
  conj_tac >- suspend "checks" >>
  suspend "frame"
QED

Resume abi_encode_round_seq_ptr[run]:
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (imp_res_tac emitted_insts_emit_op >> irule emitted_insts_append >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (qpat_assum `emit_op AND _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sm)` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  qunabbrev_tac `u` >> drule_all successful_seq_ptr_append >> simp[]
QED
Resume abi_encode_round_seq_ptr[checks]:
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (imp_res_tac emitted_insts_emit_op >> irule emitted_insts_append >> simp[]) >>
  once_asm_rewrite_tac[] >> irule inst_seq_ptr_append >>
  conj_tac >-
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`G1`, `t`, `tn1`] >> gvs[Abbr `u`]
QED
Resume abi_encode_round_seq_ptr[frame]:
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  gvs[Abbr `u`, eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED
Finalise abi_encode_round_seq_ptr

Theorem ptr_covers_offset_transport:
  ptr_covers G tn p s (off+n) /\ lookup_var p s = SOME w /\
  w2n w + off < dimword(:256) /\
  lookup_var q s' = SOME (w + n2w off) /\
  FLOOKUP G' q = FLOOKUP G p /\ op_taint tn' (Var q) = {} ==>
  ptr_covers G' tn' q s' n
Proof
  strip_tac >> `off < dimword(:256)` by decide_tac >>
  gvs[ptr_covers_def] >>
  simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD] >> decide_tac
QED

Theorem emit_addr_add_seq_ptr:
  emit_op ADD [Var dst;offset] sa = (Var out,sb) /\
  ptr_covers G tn dst s (off+n) /\ lookup_var dst s = SOME a /\
  eval_operand offset s = SOME (n2w off) /\ op_taint tn offset = {} /\
  w2n a + off < dimword(:256) /\ ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    lookup_var out sf = SOME (a + n2w off) /\
    FLOOKUP Gf out = FLOOKUP G dst /\ ptr_covers Gf tnf out sf n /\
    op_taint tnf (Var out) = {} /\ sf.vs_memory = s.vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id ADD [Var dst;offset] [out]]` by
    (drule emitted_insts_emit_op >> simp[] >> metis_tac[]) >>
  `!p. not_fresh_at sa p ==> p <> out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  `op_taint tn (Var dst) = {} /\ ?b cap. FLOOKUP G dst = SOME (b,cap)` by
    gvs[ptr_covers_def] >>
  qabbrev_tac `t = update_var out (a + n2w off) s` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [Var dst;offset] [out]` >>
  `step_inst_base i s = OK t` by
    simp[Abbr `i`, Abbr `t`, step_inst_base_opcode_eqs, mk_inst_def,
         exec_pure2_def, eval_operand_def] >>
  `FLOOKUP (step_prov PG G i t) out = FLOOKUP G dst` by
    simp[Abbr `i`, step_prov_def, set_prov_def, out_prov_def,
         first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE] >>
  `op_taint (step_taint i s t tn) (Var out) = {}` by
    simp[Abbr `i`, Abbr `t`, copy_len_binop_ghost_frame] >>
  `lookup_var out t = SOME (a + n2w off)` by
    simp[Abbr `t`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `ptr_covers (step_prov PG G i t) (step_taint i s t tn) out t n` by
    (drule_all ptr_covers_offset_transport >> simp[]) >>
  qexistsl_tac [`step_prov PG G i t`, `step_taint i s t tn`, `t`] >>
  conj_tac >- simp[run_inst_seq_def] >>
  conj_tac >-
    (simp[] >> irule inst_seq_ptr_singleton >> simp[Abbr `i`] >>
     irule ptr_inst_ok_copy_len_binop >> simp[eval_operand_def]) >>
  simp[Abbr `i`, Abbr `t`, copy_len_binop_ghost_frame,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[copy_len_binop_ghost_frame, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_encode_bytes_suffix_seq_ptr:
  abi_encode_bytes_suffix len sa = (out,sb) /\
  eval_operand len s = SOME w /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    eval_operand out sf = SOME
      (32w + (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w && (31w+w))) /\
    op_taint tnf out = {} /\ op_prov Gf out = NONE /\
    sf.vs_memory = s.vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  simp_tac bool_ss [abi_encode_bytes_suffix_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_encode_round len sa = (rounded,sm)` >>
  drule_all abi_encode_round_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`]
    (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `t` strip_assume_tac)))) >>
  `?res. out = Var res` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> metis_tac[]) >>
  gvs[] >> qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)` >>
  `eval_operand rounded u = SOME
     (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w && (31w+w)) /\
   eval_operand (Lit 32w) u = SOME 32w /\ op_taint tm (Lit 32w) = {}` by
    (Cases_on `rounded` >> gvs[Abbr `u`, eval_operand_def, lookup_var_def, op_taint_def]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    emit_copy_len_binop_seq_ptr)) >>
  disch_then (qspecl_then [`fn`, `PG`, `H`, `D`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `v` strip_assume_tac)))) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sm)` by
    (drule abi_encode_round_shape >> simp[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (drule abi_encode_round_shape >> strip_tac >>
     qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     irule emitted_insts_append >> simp[] >>
     qpat_x_assum `isPREFIX _ _` mp_tac >> rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >>
     strip_tac >> asm_rewrite_tac[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  qunabbrev_tac `u` >> drule_all successful_seq_ptr_append >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `v with vs_inst_idx := t.vs_inst_idx`] >>
  simp[eval_operand_def, lookup_var_def, first_prov_def, op_prov_def] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (drule abi_encode_round_shape >> simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  gvs[lookup_var_def] >> metis_tac[]
QED

Theorem abi_encode_bytes_prefix_seq_ptr:
  abi_encode_bytes_prefix (Var dst) (Var src) sa = (ops,sb) /\
  not_fresh_at sa dst /\ ptr_covers G tn src s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  (!j. w2n a <= j /\ j < w2n a + 32 ==> j NOTIN tn.t_mem) /\
  rw = (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w &&
        (31w + mload (w2n a) s)) /\
  ptr_covers G tn dst s (w2n rw + 32) /\
  w2n b + w2n rw < dimword(:256) /\ ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    eval_operand (FST ops) sf = SOME (mload (w2n a) s) /\
    eval_operand (SND ops) sf = SOME (b+rw) /\
    op_taint tnf (FST ops) = {} /\ op_taint tnf (SND ops) = {} /\
    (?p. SND ops = Var p /\ ptr_covers Gf tnf p sf 32) /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  simp_tac bool_ss [abi_encode_bytes_prefix_def, comp_bind_def, comp_return_def, LET_THM] >>
  ntac 3 (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [Var src] sa = (len,sm)` >>
  rename1 `abi_encode_round len sm = (rounded,sc)` >>
  `?lv pv. len = Var lv /\ lastptr = Var pv` by suspend "outputs" >>
  gvs[] >> rename1 `emit_op ADD [Var dst;rounded] sc = (Var pv,sb)` >>
  qmatch_asmsub_abbrev_tac `ptr_covers G tn dst s (w2n rw + 32)` >>
  drule_all emit_mload_clean_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`]
    (qx_choose_then `H1` (qx_choose_then `tm1` (qx_choose_then `t1` strip_assume_tac)))) >>
  qabbrev_tac `u1 = t1 with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)` >>
  `eval_operand (Var lv) u1 = SOME (mload (w2n a) s)` by
    gvs[Abbr `u1`, eval_operand_def, lookup_var_def] >>
  drule_all abi_encode_round_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `H1`, `D`]
    (qx_choose_then `H2` (qx_choose_then `tm2` (qx_choose_then `t2` strip_assume_tac)))) >>
  qabbrev_tac `u2 = t2 with vs_inst_idx := u1.vs_inst_idx + LENGTH (emitted_insts sm sc)` >>
  `ptr_covers H2 tm2 dst u2 (w2n rw + 32) /\
   lookup_var dst u2 = SOME b /\ eval_operand rounded u2 = SOME (n2w (w2n rw))` by
    suspend "add_inputs" >>
  drule_all emit_addr_add_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `t3` strip_assume_tac)))) >>
  `run_inst_seq (emitted_insts sa sb) s = OK (t3 with vs_inst_idx := t1.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf` by suspend "compose" >>
  qexistsl_tac [`Gf`, `tnf`, `t3 with vs_inst_idx := t1.vs_inst_idx`] >>
  simp[] >> suspend "post"
QED

Resume abi_encode_bytes_prefix_seq_ptr[outputs]:
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >>
  metis_tac[]
QED

Resume abi_encode_bytes_prefix_seq_ptr[add_inputs]:
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (qpat_assum `emit_op MLOAD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `lookup_var dst t2 = lookup_var dst s /\ FLOOKUP H2 dst = FLOOKUP G dst /\
   op_taint tm2 (Var dst) = op_taint tn (Var dst)` by
    (gvs[Abbr `u1`, lookup_var_def] >> metis_tac[]) >>
  conj_tac >- gvs[ptr_covers_def, Abbr `u2`, lookup_var_def] >>
  conj_tac >- gvs[Abbr `u2`, lookup_var_def] >>
  Cases_on `rounded` >>
  gvs[Abbr `u2`, Abbr `rw`, eval_operand_def, lookup_var_def]
QED

Resume abi_encode_bytes_prefix_seq_ptr[compose]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sc)` by
    (drule abi_encode_round_shape >> simp[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc sb)` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `emitted_insts sm sb = emitted_insts sm sc ++ emitted_insts sc sb` by
    (drule abi_encode_round_shape >> strip_tac >>
     qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     irule emitted_insts_append >> simp[] >>
     qpat_x_assum `isPREFIX _ _` mp_tac >> rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >>
     strip_tac >> asm_rewrite_tac[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  qunabbrev_tac `u2` >> drule_all successful_seq_ptr_append >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sm)` by
    (qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (asm_rewrite_tac[EVERY_APPEND] >>
     qpat_x_assum `EVERY _ (emitted_insts sm sc)` mp_tac >> simp[EVERY_MEM]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (qpat_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_assum `abi_encode_round _ _ = _` mp_tac >>
     qpat_assum `emit_op ADD _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     imp_res_tac emit_op_extends >> drule abi_encode_round_shape >> strip_tac >>
     gvs[rich_listTheory.IS_PREFIX_APPEND] >>
     irule emitted_insts_append >> conj_tac >- asm_rewrite_tac[] >>
     pure_rewrite_tac[emitted_insts_def] >> once_asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND,
                      rich_listTheory.DROP_APPEND1, LENGTH_APPEND] >>
     simp_tac list_ss [rich_listTheory.DROP_APPEND1] >>
     pure_rewrite_tac[GSYM LENGTH_APPEND] >> simp_tac list_ss []) >>
  `run_inst_seq (emitted_insts sm sb) u1 = OK (t3 with vs_inst_idx := t2.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG H1 tm1 (emitted_insts sm sb) u1 Gf tnf` by
    metis_tac[] >>
  qunabbrev_tac `u1` >> drule_all successful_seq_ptr_append >> simp[]
QED

Resume abi_encode_bytes_prefix_seq_ptr[post]:
  `sm.cs_next_var = sa.cs_next_var + 1 /\
   lv = STRING #"%" (toString sa.cs_next_var)` by
    (qpat_assum `emit_op MLOAD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >> gvs[]) >>
  `sc.cs_next_var = sm.cs_next_var + 2` by
    (drule abi_encode_round_shape >> simp[]) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p /\ not_fresh_at sc p` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `not_fresh_at sm lv /\ not_fresh_at sc lv` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> gvs[]) >>
  gvs[Abbr `u1`, Abbr `u2`, eval_operand_def, lookup_var_def,
      ptr_covers_def, Abbr `rw`] >> metis_tac[]
QED
Finalise abi_encode_bytes_prefix_seq_ptr
