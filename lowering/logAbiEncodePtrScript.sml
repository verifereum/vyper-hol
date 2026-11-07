(* Whole bytestring encoder assembled from certified pointer sequences. *)
Theory logAbiEncodePtr
Ancestors
  logAbiBytesPtr logAbiPrefixPtr logAbiCopyPtr logTopicScalarPtr abiEncoderBytesPrefix
  abiEncoderBytesCode abiEncoderRounding bodyPtrDefs logInstSeqPtr
  abiEncoderMemory abiDecoderContract fragGasSeqPtr valueEncodingProps
  emitHelper emitHelperProps exprLoweringProps compileEnv venomExecSemantics
  venomState venomInst abiEncoder ptrDiscipline words arithmetic list pred_set

Theorem abi_bytes_prefix_live:
  abi_encode_bytes_prefix dst src sa = (ops,sb) ==>
  ?lv pv. FST ops = Var lv /\ SND ops = Var pv /\
    not_fresh_at sb lv /\ not_fresh_at sb pv /\
    (!p. not_fresh_at sa p ==> not_fresh_at sb p)
Proof
  simp[abi_encode_bytes_prefix_def, abi_encode_round_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM, emit_op_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac
QED

Theorem compile_abi_bytes_immutable_taint_frame:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) sa = (out,sb) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H tm ==>
  tm.t_imm = tn.t_imm
Proof
  strip_tac >> irule inst_seq_ptr_immutable_taint_frame >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem compile_abi_bytes_seq_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) sa = (out,sb) /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\
  lookup_var dst s = SOME (n2w dest) /\ lookup_var src s = SOME (n2w srcpos) /\
  mload srcpos s = n2w cnt /\ cnt <= maxlen /\
  ptr_covers G tn dst s (32+contractABI$ceil32 cnt) /\
  ptr_covers G tn src s (32+cnt) /\
  (!i. srcpos <= i /\ i < srcpos+32+cnt ==> i NOTIN tn.t_mem) /\
  dest+32+contractABI$ceil32 cnt < dimword(:256) /\
  srcpos+32+cnt < dimword(:256) /\ 32+cnt < dimword(:256) /\
  (dest+32+contractABI$ceil32 cnt <= srcpos \/ srcpos+32+cnt <= dest) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    eval_operand out sf = SOME (n2w (32+contractABI$ceil32 cnt)) /\
    op_taint tnf out = {} /\ op_prov Gf out = NONE /\
    (!i. dest <= i /\ i < dest+32+contractABI$ceil32 cnt ==> i NOTIN tnf.t_mem) /\
    (!i. ~(dest <= i /\ i < dest+32+contractABI$ceil32 cnt) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    mem_agree_outside {i | dest <= i /\ i < dest+32+contractABI$ceil32 cnt}
      sf.vs_memory s.vs_memory /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule abi_encode_bytes_trace >> strip_tac >>
  `cnt <= contractABI$ceil32 cnt /\ cnt+31 < dimword(:256) /\
   contractABI$ceil32 cnt < dimword(:256) /\
   dest+contractABI$ceil32 cnt < dimword(:256) /\
   srcpos < dimword(:256)` by
    (mp_tac (Q.INST [`cnt` |-> `cnt`] abi_encoder_ceil32_bounds) >> decide_tac) >>
  `ptr_covers G tn src s 32` by
    (gvs[ptr_covers_def] >> metis_tac[LESS_EQ_ADD]) >>
  `!i. w2n ((n2w srcpos):256 word) <= i /\
    i < w2n ((n2w srcpos):256 word)+32 ==> i NOTIN tn.t_mem` by
    (simp[w2n_n2w] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `w2n ((n2w (contractABI$ceil32 cnt)):256 word) = contractABI$ceil32 cnt /\
   w2n ((n2w dest):256 word) = dest` by simp[w2n_n2w] >>
  `n2w (contractABI$ceil32 cnt) =
   (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w:256 word) &&
     (31w + mload (w2n ((n2w srcpos):256 word)) s)` by
    simp[w2n_n2w, abi_encoder_round_ceil32] >>
  `ptr_covers G tn dst s (w2n ((n2w (contractABI$ceil32 cnt)):256 word)+32) /\
   w2n ((n2w dest):256 word) + w2n ((n2w (contractABI$ceil32 cnt)):256 word) < dimword(:256)` by
    (pure_asm_rewrite_tac[] >> conj_tac >- metis_tac[ADD_COMM] >> decide_tac) >>
  drule_all abi_encode_bytes_prefix_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `t` strip_assume_tac)))) >>
  suspend "copy"
QED
Resume compile_abi_bytes_seq_ptr[copy]:
  markerLib.RESUME_TAC >> (
  drule abi_bytes_prefix_live >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa ready)` >>
  `not_fresh_at ready dst /\ not_fresh_at ready src` by metis_tac[] >>
  `lookup_var dst u = SOME (n2w dest) /\ lookup_var src u = SOME (n2w srcpos) /\
   lookup_var lv u = SOME (n2w cnt) /\
   lookup_var pv u = SOME (n2w (dest+contractABI$ceil32 cnt)) /\
   op_taint tm (Var lv) = {}` by
    (gvs[Abbr `u`, eval_operand_def, lookup_var_def, word_add_n2w, w2n_n2w] >> metis_tac[]) >>
  `ptr_covers H tm dst u (32+contractABI$ceil32 cnt) /\
   ptr_covers H tm src u (32+cnt) /\ ptr_covers H tm pv u 32` by
    suspend "copy_coverage" >>
  `!i. srcpos <= i /\ i < srcpos+32+cnt ==> i NOTIN tm.t_mem` by metis_tac[] >>
  `abi_encode_bytes_copy (Var dst) (Var src) (Var lv) (Var pv) ready = ((),copied)` by metis_tac[] >>
  drule_all abi_encode_bytes_copy_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `J` (qx_choose_then `tk` (qx_choose_then `v` strip_assume_tac)))) >>
  suspend "suffix")
QED
Resume compile_abi_bytes_seq_ptr[copy_coverage]:
  markerLib.RESUME_TAC >> (
  `FLOOKUP H dst = FLOOKUP G dst /\ FLOOKUP H src = FLOOKUP G src /\
   op_taint tm (Var dst) = op_taint tn (Var dst) /\
   op_taint tm (Var src) = op_taint tn (Var src)` by metis_tac[] >>
  gvs[ptr_covers_def, Abbr `u`, lookup_var_def])
QED
Resume compile_abi_bytes_seq_ptr[suffix]:
  markerLib.RESUME_TAC >> (
  qabbrev_tac `w = v with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts ready copied)` >>
  `eval_operand (FST ops) w = SOME (n2w cnt) /\ op_taint tk (FST ops) = {}` by
    (gvs[Abbr `w`, eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  drule_all abi_encode_bytes_suffix_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`J`,`D`]
    (qx_choose_then `Gf` (qx_choose_then `tf` (qx_choose_then `z` strip_assume_tac)))) >>
  suspend "compose")
QED
Resume compile_abi_bytes_seq_ptr[compose]:
  markerLib.RESUME_TAC >> (
  `emitted_insts sa copied = emitted_insts sa ready ++ emitted_insts ready copied /\
   emitted_insts sa sb = emitted_insts sa copied ++ emitted_insts copied sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by suspend "code" >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa ready) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts ready copied) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa copied) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts copied sb)` by
    (gvs[EVERY_APPEND, EVERY_MEM] >> metis_tac[]) >>
  qunabbrev_tac `u` >> drule_all successful_seq_ptr_append >> strip_tac >>
  `run_inst_seq (emitted_insts sa copied) s = OK (v with vs_inst_idx := t.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa copied) s J tk` by metis_tac[] >>
  suspend "compose_last")
QED
Resume compile_abi_bytes_seq_ptr[code]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  qpat_x_assum `abi_encode_bytes_prefix _ _ _ = _` mp_tac >>
  qpat_x_assum `abi_encode_bytes_copy _ _ (FST _) _ _ = _` mp_tac >>
  qpat_x_assum `abi_encode_bytes_suffix _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  imp_res_tac abi_encode_bytes_prefix_shape >>
  imp_res_tac abi_encode_bytes_copy_shape >>
  imp_res_tac abi_encode_bytes_suffix_shape >>
  imp_res_tac abi_encode_bytes_shape >>
  gvs[inst_extends_def] >>
  `emitted_insts sa copied = emitted_insts sa ready ++ emitted_insts ready copied` by
    (irule emitted_insts_append >> simp[]) >>
  simp[] >> qpat_x_assum `EVERY _ (emitted_insts sa sb)` mp_tac >>
  simp[EVERY_MEM] >> metis_tac[])
QED
Resume compile_abi_bytes_seq_ptr[compose_last]:
  markerLib.RESUME_TAC >> (
  qabbrev_tac `r = v with vs_inst_idx := t.vs_inst_idx` >>
  `w = r with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa copied)` by
    (qpat_x_assum `Abbrev (r = _)` mp_tac >>
     qpat_x_assum `Abbrev (w = _)` mp_tac >>
     qpat_x_assum `emitted_insts sa copied = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [markerTheory.Abbrev_def] >> rpt strip_tac >>
     pure_rewrite_tac [venom_state_fupdfupds, combinTheory.K_o_THM,
       venom_state_accfupds, combinTheory.K_THM, LENGTH_APPEND, ADD_ASSOC] >> REFL_TAC) >>
  qpat_x_assum `Abbrev (w = _)` kall_tac >>
  qpat_x_assum `w = _` SUBST_ALL_TAC >> qunabbrev_tac `r` >>
  drule_all successful_seq_ptr_append >> strip_tac >>
  `tf.t_imm = tn.t_imm` by
    (irule compile_abi_bytes_immutable_taint_frame >>
     goal_assum (drule_at Any) >>
     qpat_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[th]) >>
     goal_assum (drule_at Any)) >>
  qexistsl_tac [`Gf`,`tf`,`z with vs_inst_idx := t.vs_inst_idx`] >>
  conj_tac >-
    (qpat_x_assum `run_inst_seq (_ ++ _) s = OK (z with vs_inst_idx := _)` mp_tac >>
     pure_rewrite_tac [venom_state_accfupds, combinTheory.K_THM] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >> suspend "post")
QED
Resume compile_abi_bytes_seq_ptr[post]:
  markerLib.RESUME_TAC >> (
  rpt (qpat_x_assum `run_inst_seq _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` kall_tac) >>
  conj_tac >-
    (`(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w:256 word) &&
      (31w+n2w cnt) = n2w (contractABI$ceil32 cnt)` by
       (irule abi_encoder_round_ceil32 >> simp[]) >>
     qpat_x_assum `eval_operand out z = _` mp_tac >>
     qpat_x_assum `_ && (31w+n2w cnt) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     pure_asm_rewrite_tac[] >>
     simp[eval_operand_def, lookup_var_def, word_add_n2w]) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "memory" >> suspend "vars")
QED
Resume compile_abi_bytes_seq_ptr[memory]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `z.vs_memory = _` mp_tac >>
  qpat_x_assum `v.vs_memory = _` mp_tac >>
  qpat_x_assum `t.vs_memory = _` mp_tac >>
  qpat_x_assum `cnt <= contractABI$ceil32 cnt` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  `i+1 <= dest \/ dest+32+cnt <= i` by decide_tac >>
  `i+1 <= dest+contractABI$ceil32 cnt \/ dest+contractABI$ceil32 cnt+32 <= i` by decide_tac >>
  simp[mcopy_mem_bytes_at_disjoint, mstore_mem_bytes_at_disjoint])
QED
Resume compile_abi_bytes_seq_ptr[vars]:
  markerLib.RESUME_TAC >> (
  `!p. not_fresh_at ready p ==> not_fresh_at copied p` by
    (drule abi_encode_bytes_copy_shape >> simp[not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qpat_x_assum `!p. not_fresh_at copied p ==> _` mp_tac >>
  qpat_x_assum `!p. not_fresh_at ready p ==> lookup_var _ _ = _ /\ _` mp_tac >>
  qpat_x_assum `!p. not_fresh_at sa p ==> lookup_var _ _ = _ /\ _` mp_tac >>
  qpat_x_assum `!p. not_fresh_at ready p ==> _` mp_tac >>
  qpat_x_assum `!p. not_fresh_at sa p ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[lookup_var_def] >> metis_tac[])
QED
Finalise compile_abi_bytes_seq_ptr


Theorem compile_abi_bytes_gas_path_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) sa = (out,sb) /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\
  lookup_var dst s = SOME (n2w dest) /\ lookup_var src s = SOME (n2w srcpos) /\
  mload srcpos s = n2w cnt /\ cnt <= maxlen /\
  ptr_covers G tn dst s (32+contractABI$ceil32 cnt) /\
  ptr_covers G tn src s (32+cnt) /\
  (!i. srcpos <= i /\ i < srcpos+32+cnt ==> i NOTIN tn.t_mem) /\
  dest+32+contractABI$ceil32 cnt < dimword(:256) /\
  srcpos+32+cnt < dimword(:256) /\ 32+cnt < dimword(:256) /\
  (dest+32+contractABI$ceil32 cnt <= srcpos \/ srcpos+32+cnt <= dest) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))) Gf tnf
      (OK (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    eval_operand out sf = SOME (n2w (32+contractABI$ceil32 cnt)) /\
    op_taint tnf out = {} /\ op_prov Gf out = NONE /\
    (!i. dest <= i /\ i < dest+32+contractABI$ceil32 cnt ==> i NOTIN tnf.t_mem) /\
    (!i. ~(dest <= i /\ i < dest+32+contractABI$ceil32 cnt) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    mem_agree_outside {i | dest <= i /\ i < dest+32+contractABI$ceil32 cnt}
      sf.vs_memory s.vs_memory /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_abi_bytes_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by
    (drule abi_encode_bytes_shape >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> simp[]
QED
