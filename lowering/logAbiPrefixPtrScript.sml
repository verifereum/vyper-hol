(* Pointer checks and ghost frames for the bytes encoder's arithmetic phases. *)
Theory logAbiPrefixPtr
Ancestors
  assignTuplePtrCopyLen logInstSeqPtr abiEncoderBytesCode abiEncoderRounding bodyPtrDefs
  typedCopyPtr fragExecPtr fragExec ptrDiscipline ptrSafeRun
  emitHelperProps emitHelper compileEnv loweringStateRelDefs context exprLoweringProps
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

Theorem emit_op_fresh_frame[local]:
  emit_op opc ops sa = (Var v,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\ not_fresh_at sb v /\
  (!p. not_fresh_at sa p ==> p <> v) /\
  (!p. not_fresh_at sa p ==> not_fresh_at sb p)
Proof
  strip_tac >> rpt conj_tac
  >- (imp_res_tac emitted_insts_emit_op >> decide_tac)
  >- (drule typedMemoryCopyTheory.typed_copy_emit_op_fresh >> simp[])
  >- (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
      metis_tac[LESS_EQ_REFL]) >>
  qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

(* contractABI$ceil32 as main emits it: NOT 31, ADD 31, AND with the mask. *)
Theorem not31_word[local]:
  (~31w:256 word) = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
Proof
  blastLib.BBLAST_TAC
QED

Theorem abi_encode_ceil32_seq_ptr:
  abi_encode_ceil32 len sa = (out,sb) /\
  eval_operand len s = SOME w /\ op_taint tn len = {} /\
  (!v. len = Var v ==> not_fresh_at sa v) /\
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
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sa.cs_next_var <= sb.cs_next_var
Proof
  simp_tac bool_ss [abi_encode_ceil32_def, comp_bind_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op NOT [Lit 31w] sa = (mask,s1)` >>
  rename1 `emit_op ADD [len;Lit 31w] s1 = (arg,s2)` >>
  `?vm va vr. mask = Var vm /\ arg = Var va /\ out = Var vr` by
    (imp_res_tac emitted_insts_emit_op >> simp[]) >>
  gvs[] >>
  qpat_assum `emit_op NOT _ _ = _` (strip_assume_tac o MATCH_MP emit_op_fresh_frame) >>
  qpat_assum `emit_op ADD _ _ = _` (strip_assume_tac o MATCH_MP emit_op_fresh_frame) >>
  qpat_assum `emit_op AND _ _ = _` (strip_assume_tac o MATCH_MP emit_op_fresh_frame) >>
  `emitted_insts sa s1 = [mk_inst sa.cs_next_id NOT [Lit 31w] [vm]] /\
   emitted_insts s1 s2 = [mk_inst s1.cs_next_id ADD [len; Lit 31w] [va]] /\
   emitted_insts s2 sb = [mk_inst s2.cs_next_id AND [Var va; Var vm] [vr]]` by
    (imp_res_tac emitted_insts_emit_op >> gvs[]) >>
  `emitted_insts s1 sb = emitted_insts s1 s2 ++ emitted_insts s2 sb` by
    (imp_res_tac emitted_insts_emit_op >> irule emitted_insts_append >> gvs[]) >>
  `emitted_insts sa sb = emitted_insts sa s1 ++ emitted_insts s1 sb` by
    (imp_res_tac emitted_insts_emit_op >> irule emitted_insts_append >> gvs[]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (imp_res_tac emitted_insts_emit_op >> gvs[]) >>
  `!v. len = Var v ==> vm <> v` by metis_tac[] >>
  (* NOT [Lit 31w] *)
  qspecl_then [`D`, `ctx`, `fn`, `PG`, `G`, `tn`, `s`, `sa.cs_next_id`,
               `Lit 31w`, `vm`, `31w`] mp_tac copy_len_not_seq_ptr >>
  impl_tac >- simp[eval_operand_def, op_taint_def] >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `t1`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts sa s1) s = OK t1 /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa s1) s G1 tn1` by
    (qpat_assum `emitted_insts sa s1 = _` SUBST1_TAC >> conj_tac >>
     first_assum ACCEPT_TAC) >>
  (* ADD [len; Lit 31w] *)
  `eval_operand len
     (t1 with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa s1)) = SOME w /\
   op_taint tn1 len = {}` by
    (Cases_on `len` >>
     gvs[eval_operand_def, op_taint_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE]) >>
  mp_tac (Q.INST [`left` |-> `len`, `right` |-> `Lit 31w`, `out` |-> `va`,
     `sa` |-> `s1`, `sb` |-> `s2`,
     `s` |-> `t1 with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa s1)`,
     `G` |-> `G1`, `tn` |-> `tn1`, `a` |-> `w`, `b` |-> `31w`]
     (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
        emit_copy_len_binop_seq_ptr))) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[eval_operand_def, op_taint_def]) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `t2`] strip_assume_tac) >>
  (* AND [Var va; Var vm] *)
  `eval_operand (Var va)
     (t2 with vs_inst_idx :=
        (t1 with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa s1)).vs_inst_idx +
        LENGTH (emitted_insts s1 s2)) = SOME (w + 31w) /\
   eval_operand (Var vm)
     (t2 with vs_inst_idx :=
        (t1 with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa s1)).vs_inst_idx +
        LENGTH (emitted_insts s1 s2)) = SOME (~31w) /\
   op_taint tn2 (Var va) = {} /\ op_taint tn2 (Var vm) = {}` by
    (simp[eval_operand_def] >>
     fs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  mp_tac (Q.INST [`left` |-> `Var va`, `right` |-> `Var vm`, `out` |-> `vr`,
     `sa` |-> `s2`, `sb` |-> `sb`,
     `s` |-> `t2 with vs_inst_idx :=
        (t1 with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa s1)).vs_inst_idx +
        LENGTH (emitted_insts s1 s2)`,
     `G` |-> `G2`, `tn` |-> `tn2`, `a` |-> `w + 31w`, `b` |-> `~31w`]
     (SRULE [] (Q.INST [`opc` |-> `AND`, `f` |-> `word_and`]
        emit_copy_len_binop_seq_ptr))) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  disch_then (qx_choosel_then [`G3`, `tn3`, `t3`] strip_assume_tac) >>
  (* compose ADD;AND, then NOT before it *)
  mp_tac (Q.INST [`xs` |-> `emitted_insts s1 s2`, `ys` |-> `emitted_insts s2 sb`,
     `s` |-> `t1 with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa s1)`,
     `t` |-> `t2`, `u` |-> `t3`, `lo` |-> `0`, `G` |-> `G1`, `tn` |-> `tn1`,
     `H` |-> `G2`, `tm` |-> `tn2`, `Gf` |-> `G3`, `tk` |-> `tn3`]
     successful_seq_ptr_append) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[mk_inst_def, is_terminator_def]) >>
  strip_tac >>
  mp_tac (Q.INST [`xs` |-> `emitted_insts sa s1`,
     `ys` |-> `emitted_insts s1 s2 ++ emitted_insts s2 sb`,
     `t` |-> `t1`, `u` |-> `t3 with vs_inst_idx := t2.vs_inst_idx`, `lo` |-> `0`,
     `H` |-> `G1`, `tm` |-> `tn1`, `Gf` |-> `G3`, `tk` |-> `tn3`]
     successful_seq_ptr_append) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[mk_inst_def, is_terminator_def]) >>
  strip_tac >>
  qexistsl_tac [`G3`, `tn3`,
    `(t3 with vs_inst_idx := t2.vs_inst_idx) with vs_inst_idx := t1.vs_inst_idx`] >>
  `emitted_insts sa sb =
     emitted_insts sa s1 ++ (emitted_insts s1 s2 ++ emitted_insts s2 sb)` by
    (qpat_assum `emitted_insts sa sb = _` SUBST1_TAC >>
     qpat_assum `emitted_insts s1 sb = _` SUBST1_TAC >> REFL_TAC) >>
  conj_tac >-
    (qpat_assum `emitted_insts sa sb = _ ++ (_ ++ _)` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `emitted_insts sa sb = _ ++ (_ ++ _)` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  conj_tac >-
    (simp[eval_operand_def] >> fs[lookup_var_def] >>
     PURE_REWRITE_TAC [not31_word] >>
     simp[AC WORD_ADD_ASSOC WORD_ADD_COMM, AC WORD_AND_ASSOC WORD_AND_COMM]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >-
    (rpt strip_tac >>
     `p <> vm /\ not_fresh_at s1 p /\ not_fresh_at s2 p` by metis_tac[] >>
     fs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  conj_tac >-
    (qpat_assum `emitted_insts sa sb = _ ++ (_ ++ _)` SUBST1_TAC >>
     simp[mk_inst_def, is_terminator_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  decide_tac
QED

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
  (!v. len = Var v ==> not_fresh_at sa v) /\
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
  rename1 `abi_encode_ceil32 len sa = (rounded,sm)` >>
  drule_all abi_encode_ceil32_seq_ptr >>
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
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     irule emitted_insts_append >> simp[]) >>
  qunabbrev_tac `u` >> drule_all successful_seq_ptr_append >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `v with vs_inst_idx := t.vs_inst_idx`] >>
  simp[eval_operand_def, lookup_var_def, first_prov_def, op_prov_def] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
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
  `w2n b + w2n rw < dimword(:256)` by simp[] >>
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
