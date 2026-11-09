(* Pointer-certified dynamic child setup and bookkeeping. *)
Theory logAbiChildPtr
Ancestors
  wordLoadStorePtr logAbiEncodePtr logAbiPrefixPtr logInstSeqPtr logTopicScalarPtr logAbiChildPostPtr
  abiEncoder abiEncoderChildCode abiEncoderChildPrefix abiDecoderReentry
  abiEncoderBytesCode bodyPtrDefs fragGasSeqPtr
  emitHelperProps emitHelper exprLoweringProps compileEnv
  venomExecSemantics venomState venomInst ptrDiscipline ptrSafeRun
  finite_map words arithmetic list rich_list typedCopyPtr venomMemProps

Theorem abi_encode_child_prefix_seq_ptr:
  abi_encode_child_prefix (Var dst) ho (Var dp) sa = (ops,sb) /\
  not_fresh_at sa dst /\ not_fresh_at sa dp /\
  lookup_var dst s = SOME (n2w db) /\ lookup_var dp s = SOME (n2w p) /\
  mload p s = n2w r /\ ptr_covers G tn dst s cap /\
  ptr_covers G tn dp s 32 /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
  ho+32 <= cap /\ r+n <= cap /\ db+cap < dimword(:256) /\
  p < dimword(:256) /\ ~ctx_has_dalloca ctx ==>
  ?H tm t hv rv tv.
    ops = (Var hv,Var rv,Var tv) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm /\
    lookup_var hv t = SOME (n2w (db+ho)) /\
    lookup_var rv t = SOME (n2w r) /\ lookup_var tv t = SOME (n2w (db+r)) /\
    ptr_covers H tm hv t 32 /\ ptr_covers H tm tv t n /\
    op_taint tm (Var rv) = {} /\ op_prov H (Var rv) = NONE /\
    t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP H v = FLOOKUP G v /\
      op_taint tm (Var v) = op_taint tn (Var v))
Proof
  simp_tac bool_ss [abi_encode_child_prefix_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [Var dst;Lit (n2w ho)] sa = (head,sm)` >>
  rename1 `emit_op MLOAD [Var dp] sm = (offset,sc)` >>
  `?hv rv tv. head = Var hv /\ offset = Var rv /\ child_dst = Var tv` by
    (imp_res_tac emitted_insts_emit_op >> metis_tac[]) >> gvs[] >>
  `ptr_covers G tn dst s (ho+32) /\ w2n ((n2w db):256 word) = db /\
   eval_operand (Lit (n2w ho)) s = SOME (n2w ho) /\
   op_taint tn (Lit (n2w ho)) = {} /\ db+ho < dimword(:256)` by
    (gvs[ptr_covers_def, eval_operand_def, op_taint_def, w2n_n2w] >> decide_tac) >>
  `w2n ((n2w db):256 word)+ho < dimword(:256)` by simp[] >>
  drule_all emit_addr_add_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `J` (qx_choose_then `tk` (qx_choose_then `u` strip_assume_tac)))) >>
  suspend "load"
QED
Resume abi_encode_child_prefix_seq_ptr[load]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `u1 = u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)` >>
  `ptr_covers J tk dp u1 32 /\ lookup_var dp u1 = SOME (n2w p)` by
    (gvs[ptr_covers_def, Abbr `u1`, lookup_var_def] >> metis_tac[]) >>
  `!i. w2n ((n2w p):256 word) <= i /\
    i < w2n ((n2w p):256 word)+32 ==> i NOTIN tk.t_mem` by simp[w2n_n2w] >>
  drule_all emit_mload_clean_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `J2` (qx_choose_then `tl` (qx_choose_then `v` strip_assume_tac)))) >>
  suspend "tail"
QED
Resume abi_encode_child_prefix_seq_ptr[tail]:
  markerLib.RESUME_TAC >>
  rename1 `emit_op ADD [Var dst;Var rv] sc = (Var tv,sb)` >>
  `not_fresh_at sm hv /\ not_fresh_at sc rv /\
   (!x. not_fresh_at sa x ==> not_fresh_at sm x) /\
   (!x. not_fresh_at sm x ==> not_fresh_at sc x)` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
      [`emit_op ADD _ sa = _`, `emit_op MLOAD _ sm = _`] >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def, not_fresh_at_def] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  qabbrev_tac `v1 = v with vs_inst_idx := u1.vs_inst_idx + LENGTH (emitted_insts sm sc)` >>
  `ptr_covers J2 tl dst v1 (r+n) /\ lookup_var dst v1 = SOME (n2w db) /\
   eval_operand (Var rv) v1 = SOME (n2w r) /\
   w2n ((n2w db):256 word)+r < dimword(:256)` by
    (gvs[ptr_covers_def, Abbr `v1`, Abbr `u1`, lookup_var_def,
       eval_operand_def, mload_def, w2n_n2w] >> metis_tac[LESS_EQ_LESS_TRANS, LESS_EQ_ADD]) >>
  drule_all emit_addr_add_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `w` strip_assume_tac)))) >>
  suspend "compose"
QED
Resume abi_encode_child_prefix_seq_ptr[compose]:
  markerLib.RESUME_TAC >>
  `emitted_insts sm sb = emitted_insts sm sc ++ emitted_insts sc sb /\
   emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sm) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sc) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc sb)` by
    suspend "code" >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (simp[EVERY_APPEND] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  qunabbrev_tac `v1` >> drule_all successful_seq_ptr_append >> strip_tac >>
  `run_inst_seq (emitted_insts sm sb) u1 = OK (w with vs_inst_idx := v.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG J tk (emitted_insts sm sb) u1 H tm` by metis_tac[] >>
  `run_inst_seq (emitted_insts sa sb) s = OK (w with vs_inst_idx := u.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm` by
    suspend "outer" >>
  qexistsl_tac [`H`,`tm`,`w with vs_inst_idx := u.vs_inst_idx`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  suspend "frame"
QED
Resume abi_encode_child_prefix_seq_ptr[outer]:
  markerLib.RESUME_TAC >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`run_inst_seq (emitted_insts sa sm) _ = _`,
     `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts sa sm) _ _ _`,
     `run_inst_seq (emitted_insts sm sb) _ = _`,
     `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts sm sb) _ _ _`,
     `emitted_insts sa sb = _`,
     `EVERY _ (emitted_insts sa sm)`, `EVERY _ (emitted_insts sm sb)`,
     `Abbrev (u1 = _)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  qpat_x_assum `emitted_insts sa sb = _` (fn th => once_rewrite_tac[th]) >>
  `w with vs_inst_idx := u.vs_inst_idx =
    (w with vs_inst_idx := v.vs_inst_idx) with vs_inst_idx := u.vs_inst_idx` by
    simp[venom_state_fupdfupds, combinTheory.K_o_THM] >>
  pop_assum SUBST1_TAC >> irule successful_seq_ptr_append >>
  simp[Abbr `u1`] >> qexistsl_tac [`J`,`tk`] >> metis_tac[ADD_COMM]
QED
Resume abi_encode_child_prefix_seq_ptr[code]:
  markerLib.RESUME_TAC >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`emit_op ADD _ sc = _`, `emit_op MLOAD _ sm = _`, `emit_op ADD _ sa = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, DROP_APPEND, mk_inst_def, is_terminator_def]
QED
Resume abi_encode_child_prefix_seq_ptr[frame]:
  markerLib.RESUME_TAC >>
  `tm.t_imm = tn.t_imm` by
    (irule inst_seq_ptr_immutable_taint_frame >> goal_assum (drule_at Any) >>
     map_every (fn pat => qpat_x_assum pat mp_tac)
       [`emit_op ADD _ sc = _`, `emit_op MLOAD _ sm = _`, `emit_op ADD _ sa = _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     imp_res_tac emitted_insts_emit_op >> simp[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def]) >>
  gvs[Abbr `u1`, lookup_var_def, eval_operand_def, word_add_n2w,
      w2n_n2w, mload_def] >>
  conj_tac >- (gvs[ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  gvs[op_prov_def] >> metis_tac[]
QED
Finalise abi_encode_child_prefix_seq_ptr

Theorem abi_encode_child_suffix_seq_ptr:
  abi_encode_child_suffix (Var hd) (Var dp) (Var off) (Var len) sa = (out,sb) /\
  not_fresh_at sa hd /\ not_fresh_at sa dp /\
  not_fresh_at sa off /\ not_fresh_at sa len /\
  ptr_covers G tn hd s 32 /\ ptr_covers G tn dp s 32 /\
  lookup_var hd s = SOME h /\ lookup_var dp s = SOME p /\
  lookup_var off s = SOME r /\ lookup_var len s = SOME n /\
  op_taint tn (Var off) = {} /\ op_taint tn (Var len) = {} /\
  op_prov G (Var off) = NONE /\ op_prov G (Var len) = NONE /\
  ~ctx_has_dalloca ctx ==>
  ?H tm t.
    out = Var len /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm /\
    t.vs_memory = (mstore (w2n p) (r+n) (mstore (w2n h) r s)).vs_memory /\
    tm.t_mem = tn.t_mem DIFF
      ({i | w2n h <= i /\ i < w2n h+32} UNION
       {i | w2n p <= i /\ i < w2n p+32}) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP H v = FLOOKUP G v /\
      op_taint tm (Var v) = op_taint tn (Var v))
Proof
  simp_tac bool_ss [abi_encode_child_suffix_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_void MSTORE [Var hd;Var off] sa = ((),sm)` >>
  rename1 `emit_op ADD [Var off;Var len] sm = (next,sc)` >>
  `?nv. next = Var nv` by
    (imp_res_tac emitted_insts_emit_op >> metis_tac[]) >> gvs[] >>
  `eval_operand (Var off) s = SOME r` by simp[eval_operand_def] >>
  drule_all emit_mstore_clean_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `tk` (qx_choose_then `u` strip_assume_tac))) >>
  suspend "add"
QED
Resume abi_encode_child_suffix_seq_ptr[add]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `u1 = u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)` >>
  `eval_operand (Var off) u1 = SOME r /\ eval_operand (Var len) u1 = SOME n /\
   op_taint tk (Var off) = {} /\ op_taint tk (Var len) = {}` by
    gvs[Abbr `u1`, eval_operand_def, lookup_var_def, mstore_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    emit_copy_len_binop_seq_ptr)) >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`]
    (qx_choose_then `H` (qx_choose_then `tl` (qx_choose_then `v` strip_assume_tac)))) >>
  suspend "store"
QED
Resume abi_encode_child_suffix_seq_ptr[store]:
  markerLib.RESUME_TAC >>
  rename1 `emit_void MSTORE [Var dp;Var nv] sc = ((),sb)` >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (qpat_x_assum `emit_void _ _ sa = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def, not_fresh_at_def] >> rpt strip_tac >> gvs[]) >>
  qabbrev_tac `v1 = v with vs_inst_idx := u1.vs_inst_idx + LENGTH (emitted_insts sm sc)` >>
  `ptr_covers H tl dp v1 32 /\ lookup_var dp v1 = SOME p /\
   eval_operand (Var nv) v1 = SOME (r+n)` by
    (gvs[ptr_covers_def, Abbr `v1`, Abbr `u1`, mstore_def,
      lookup_var_def, eval_operand_def, op_taint_def] >> metis_tac[]) >>
  drule_all emit_mstore_clean_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `tm` (qx_choose_then `w` strip_assume_tac))) >>
  suspend "compose"
QED
Resume abi_encode_child_suffix_seq_ptr[compose]:
  markerLib.RESUME_TAC >>
  `emitted_insts sm sb = emitted_insts sm sc ++ emitted_insts sc sb /\
   emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sm) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sc) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc sb)` by
    suspend "code" >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (simp[EVERY_APPEND] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  qunabbrev_tac `v1` >> drule_all successful_seq_ptr_append >> strip_tac >>
  `run_inst_seq (emitted_insts sm sb) u1 = OK (w with vs_inst_idx := v.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tk (emitted_insts sm sb) u1 H tm` by metis_tac[] >>
  `run_inst_seq (emitted_insts sa sb) s = OK (w with vs_inst_idx := u.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm` by
    suspend "outer" >>
  qexistsl_tac [`H`,`tm`,`w with vs_inst_idx := u.vs_inst_idx`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> suspend "frame"
QED
Resume abi_encode_child_suffix_seq_ptr[outer]:
  markerLib.RESUME_TAC >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`run_inst_seq (emitted_insts sa sm) _ = _`,
     `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts sa sm) _ _ _`,
     `run_inst_seq (emitted_insts sm sb) _ = _`,
     `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts sm sb) _ _ _`,
     `emitted_insts sa sb = _`,
     `EVERY _ (emitted_insts sa sm)`, `EVERY _ (emitted_insts sm sb)`,
     `Abbrev (u1 = _)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  qpat_x_assum `emitted_insts sa sb = _` (fn th => once_rewrite_tac[th]) >>
  `w with vs_inst_idx := u.vs_inst_idx =
    (w with vs_inst_idx := v.vs_inst_idx) with vs_inst_idx := u.vs_inst_idx` by
    simp[venom_state_fupdfupds, combinTheory.K_o_THM] >>
  pop_assum SUBST1_TAC >> irule successful_seq_ptr_append >>
  simp[Abbr `u1`] >> qexistsl_tac [`G`,`tk`] >> metis_tac[ADD_COMM]
QED
Resume abi_encode_child_suffix_seq_ptr[code]:
  markerLib.RESUME_TAC >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`emit_void _ _ sc = _`, `emit_op _ _ sm = _`, `emit_void _ _ sa = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, DROP_APPEND, mk_inst_def, is_terminator_def]
QED
Resume abi_encode_child_suffix_seq_ptr[frame]:
  markerLib.RESUME_TAC >>
  `tm.t_imm = tn.t_imm` by
    (irule inst_seq_ptr_immutable_taint_frame >> goal_assum (drule_at Any) >>
     map_every (fn pat => qpat_x_assum pat mp_tac)
       [`emit_void _ _ sc = _`, `emit_op _ _ sm = _`, `emit_void _ _ sa = _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def]) >>
  rpt (qpat_x_assum `run_inst_seq _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `ptr_covers _ _ _ _ _` kall_tac) >>
  conj_tac >- suspend "memory" >>
  conj_tac >- (simp[pred_setTheory.EXTENSION, pred_setTheory.IN_DIFF,
    pred_setTheory.IN_UNION] >> metis_tac[]) >>
  gvs[Abbr `u1`, mstore_def, lookup_var_def, op_taint_def] >> metis_tac[]
QED
Resume abi_encode_child_suffix_seq_ptr[memory]:
  markerLib.RESUME_TAC >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`w = _`, `u = _`, `v.vs_memory = _`, `Abbrev (u1 = _)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  qunabbrev_tac `u1` >>
  asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
    [mstore_def, venom_state_accfupds, combinTheory.K_THM, LET_THM]
QED
Finalise abi_encode_child_suffix_seq_ptr


Theorem abi_encode_bytes_result_var_live:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) sa = (out,sb) ==>
  ?v. out = Var v /\ not_fresh_at sb v
Proof
  simp[Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[not_fresh_at_def]
QED

(* The bytes phase retains precisely the live bookkeeping registers needed by
   the suffix.  Padding in the input is deliberately not required clean. *)
Theorem abi_bytes_child_suffix_ready_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) sa = (out,sb) /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\
  lookup_var dst s = SOME (n2w dest) /\ lookup_var src s = SOME (n2w a) /\
  mload a s = n2w cnt /\ cnt <= maxlen /\
  ptr_covers G tn dst s (32+contractABI$ceil32 cnt) /\
  ptr_covers G tn src s (32+cnt) /\
  (!i. a <= i /\ i < a+32+cnt ==> i NOTIN tn.t_mem) /\
  dest+32+contractABI$ceil32 cnt < dimword(:256) /\
  a+32+cnt < dimword(:256) /\ 32+cnt < dimword(:256) /\
  (dest+32+contractABI$ceil32 cnt <= a \/ a+32+cnt <= dest) /\
  not_fresh_at sa hd /\ not_fresh_at sa dp /\ not_fresh_at sa off /\
  lookup_var hd s = SOME h /\ lookup_var dp s = SOME p /\
  lookup_var off s = SOME r /\ ptr_covers G tn hd s 32 /\
  ptr_covers G tn dp s 32 /\ op_taint tn (Var off) = {} /\
  op_prov G (Var off) = NONE /\ ~ctx_has_dalloca ctx ==>
  ?H tm t lv.
    out = Var lv /\ not_fresh_at sb lv /\
    not_fresh_at sb hd /\ not_fresh_at sb dp /\ not_fresh_at sb off /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm /\
    lookup_var lv t = SOME (n2w (32+contractABI$ceil32 cnt)) /\
    op_taint tm (Var lv) = {} /\ op_prov H (Var lv) = NONE /\
    lookup_var hd t = SOME h /\ lookup_var dp t = SOME p /\
    lookup_var off t = SOME r /\ ptr_covers H tm hd t 32 /\
    ptr_covers H tm dp t 32 /\ op_taint tm (Var off) = {} /\
    op_prov H (Var off) = NONE /\
    (!i. dest <= i /\ i < dest+32+contractABI$ceil32 cnt ==> i NOTIN tm.t_mem) /\
    (!i. ~(dest <= i /\ i < dest+32+contractABI$ceil32 cnt) ==>
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    mem_agree_outside {i | dest <= i /\ i < dest+32+contractABI$ceil32 cnt}
      t.vs_memory s.vs_memory /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all compile_abi_bytes_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `t` strip_assume_tac)))) >>
  drule abi_encode_bytes_result_var_live >> strip_tac >> gvs[] >>
  drule abi_encode_bytes_shape >> strip_tac >>
  `not_fresh_at sb hd /\ not_fresh_at sb dp /\ not_fresh_at sb off` by
    (gvs[not_fresh_at_def] >> decide_tac) >>
  qexistsl_tac [`H`,`tm`] >>
  gvs[eval_operand_def, ptr_covers_def, op_prov_def] >> metis_tac[]
QED

(* Compose the already certified bytes phase with the finite bookkeeping
   suffix.  The exact two-store endpoint is retained for functional framing. *)
Theorem abi_bytes_child_finish_seq_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) sa = (Var lv,sc) /\
  abi_encode_child_suffix (Var hd) (Var dp) (Var off) (Var lv) sc = (out,sb) /\
  run_inst_seq (emitted_insts sa sc) s = OK v /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc) s J tk /\
  not_fresh_at sc hd /\ not_fresh_at sc dp /\ not_fresh_at sc off /\
  lookup_var hd v = SOME h /\ lookup_var dp v = SOME p /\
  lookup_var off v = SOME r /\ lookup_var lv v = SOME n /\
  ptr_covers J tk hd v 32 /\ ptr_covers J tk dp v 32 /\
  op_taint tk (Var off) = {} /\ op_prov J (Var off) = NONE /\
  op_taint tk (Var lv) = {} /\ op_prov J (Var lv) = NONE /\
  ~ctx_has_dalloca ctx ==>
  ?H tm t.
    out = Var lv /\
    run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sa sc ++ emitted_insts sc sb) s H tm /\
    lookup_var lv t = SOME n /\ op_taint tm (Var lv) = {} /\
    op_prov H (Var lv) = NONE /\
    t.vs_memory = (mstore (w2n p) (r+n) (mstore (w2n h) r v)).vs_memory /\
    tm.t_mem = tk.t_mem DIFF
      ({i | w2n h <= i /\ i < w2n h+32} UNION
       {i | w2n p <= i /\ i < w2n p+32}) /\
    tm.t_stor = tk.t_stor /\ tm.t_trans = tk.t_trans /\ tm.t_imm = tk.t_imm /\
    (!x. not_fresh_at sc x ==>
      lookup_var x t = lookup_var x v /\ FLOOKUP H x = FLOOKUP J x /\
      op_taint tm (Var x) = op_taint tk (Var x))
Proof
  strip_tac >> drule abi_encode_bytes_result_var_live >> strip_tac >> gvs[] >>
  drule abi_encode_bytes_shape >> strip_tac >>
  qabbrev_tac `v1 = v with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sc)` >>
  `ptr_covers J tk hd v1 32 /\ ptr_covers J tk dp v1 32 /\
   lookup_var hd v1 = SOME h /\ lookup_var dp v1 = SOME p /\
   lookup_var off v1 = SOME r /\ lookup_var lv v1 = SOME n` by
    gvs[Abbr `v1`, ptr_covers_def, lookup_var_def] >>
  drule_all abi_encode_child_suffix_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `w` strip_assume_tac)))) >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sc) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc sb)` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s =
      OK (w with vs_inst_idx := v.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tn
     (emitted_insts sa sc ++ emitted_insts sc sb) s H tm` by
    (irule successful_seq_ptr_append >> qunabbrev_tac `v1` >>
     asm_simp_tac bool_ss [] >> qexistsl_tac [`J`,`tk`] >>
     asm_simp_tac bool_ss [] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `w.vs_memory = (mstore (w2n p) (r+n) (mstore (w2n h) r v)).vs_memory` by
    (qpat_x_assum `w.vs_memory = _` mp_tac >>
     simp_tac (pure_ss ++ boolSimps.BOOL_ss)
       [Abbr `v1`, mstore_def, venom_state_accfupds, combinTheory.K_THM, LET_THM]) >>
  qexistsl_tac [`H`,`tm`,`w with vs_inst_idx := v.vs_inst_idx`] >>
  simp[lookup_var_def] >>
  qpat_x_assum `!x. not_fresh_at sc x ==> _` mp_tac >>
  gvs[Abbr `v1`, lookup_var_def, op_prov_def] >> metis_tac[]
QED

Theorem abi_child_two_store_memory_frame:
  t.vs_memory = (mstore p (r+n) (mstore h r v)).vs_memory /\
  regions_disjoint (h,32) (p,32) /\
  mem_agree_outside writes v.vs_memory s.vs_memory ==>
  mload h t = r /\ mload p t = r+n /\
  mem_agree_outside
    (writes UNION {i | h <= i /\ i < h+32} UNION {i | p <= i /\ i < p+32})
    t.vs_memory s.vs_memory
Proof
  strip_tac >>
  `mload h t = mload h (mstore p (r+n) (mstore h r v)) /\
   mload p t = mload p (mstore p (r+n) (mstore h r v))` by
    simp[mload_def] >>
  `regions_disjoint (p,32) (h,32)` by
    (gvs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac >- simp[mload_mstore_disjoint, mload_mstore_same] >>
  conj_tac >- simp[mload_mstore_same] >>
  qspecl_then [`v`,`h`,`r`] assume_tac mstore_memory_frame >>
  qspecl_then [`mstore h r v`,`p`,`r+n`] assume_tac mstore_memory_frame >>
  gvs[mem_agree_outside_def] >> rpt strip_tac >>
  fs[pred_setTheory.IN_UNION] >> metis_tac[]
QED

Theorem abi_child_tail_and_cells_frame:
  t.vs_memory = (mstore p (r+n) (mstore h r v)).vs_memory /\
  regions_disjoint (h,32) (p,32) /\
  mem_agree_outside {i | dest <= i /\ i < dest+len} v.vs_memory s.vs_memory /\
  (!i. dest <= i /\ i < dest+len ==> i NOTIN tk.t_mem) /\
  (!i. ~(dest <= i /\ i < dest+len) ==> (i IN tk.t_mem <=> i IN tn.t_mem)) /\
  tm.t_mem = tk.t_mem DIFF
    ({i | h <= i /\ i < h+32} UNION {i | p <= i /\ i < p+32}) ==>
  mload h t = r /\ mload p t = r+n /\
  mem_agree_outside
    {i | (h <= i /\ i < h+32) \/ (dest <= i /\ i < dest+len) \/
         (p <= i /\ i < p+32)} t.vs_memory s.vs_memory /\
  (!i. (h <= i /\ i < h+32) \/ (dest <= i /\ i < dest+len) \/
       (p <= i /\ i < p+32) ==> i NOTIN tm.t_mem) /\
  (!i. ~((h <= i /\ i < h+32) \/ (dest <= i /\ i < dest+len) \/
         (p <= i /\ i < p+32)) ==> (i IN tm.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >> drule_all abi_child_two_store_memory_frame >> strip_tac >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >-
    (qpat_x_assum `mem_agree_outside (_ UNION _ UNION _) _ _` mp_tac >>
     `({i | dest <= i /\ i < dest+len} UNION
       {i | h <= i /\ i < h+32} UNION {i | p <= i /\ i < p+32}) =
      {i | (h <= i /\ i < h+32) \/ (dest <= i /\ i < dest+len) \/
           (p <= i /\ i < p+32)}` by SET_TAC[] >> simp[]) >>
  simp[pred_setTheory.IN_DIFF, pred_setTheory.IN_UNION] >> metis_tac[]
QED

(* Prefix and bytes execution retain both append boundaries explicitly. *)
Theorem abi_bytes_child_prefix_ready_seq_ptr:
  abi_encode_child_prefix (Var dst) ho (Var dp) sa = (ops,prepared) /\
  compile_abi_encode_to_buf (SND (SND ops)) (Var src) (AbiBytestring maxlen) prepared = (out,sc) /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\ not_fresh_at sa dp /\
  lookup_var dst s = SOME (n2w db) /\ lookup_var src s = SOME (n2w a) /\
  lookup_var dp s = SOME (n2w p) /\ mload p s = n2w r /\ mload a s = n2w cnt /\
  cnt <= maxlen /\ ptr_covers G tn dst s cap /\
  ptr_covers G tn src s (32+cnt) /\ ptr_covers G tn dp s 32 /\
  (!i. a <= i /\ i < a+32+cnt ==> i NOTIN tn.t_mem) /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
  ho+32 <= r /\ r+32+contractABI$ceil32 cnt <= cap /\
  db+cap < dimword(:256) /\ a+32+cnt < dimword(:256) /\ p+32 < dimword(:256) /\
  (db+cap <= a \/ a+32+cnt <= db) /\ ~ctx_has_dalloca ctx ==>
  ?J tk u K tl v hv rv tv lv.
    ops = (Var hv,Var rv,Var tv) /\ out = Var lv /\
    run_inst_seq (emitted_insts sa prepared) s = OK u /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa prepared) s J tk /\
    run_inst_seq (emitted_insts prepared sc)
      (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa prepared)) = OK v /\
    inst_seq_ptr D 0 ctx fn PG J tk (emitted_insts prepared sc)
      (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa prepared)) K tl /\
    not_fresh_at sc hv /\ not_fresh_at sc dp /\ not_fresh_at sc rv /\
    lookup_var hv v = SOME (n2w (db+ho)) /\ lookup_var dp v = SOME (n2w p) /\
    lookup_var rv v = SOME (n2w r) /\
    lookup_var lv v = SOME (n2w (32+contractABI$ceil32 cnt)) /\
    ptr_covers K tl hv v 32 /\ ptr_covers K tl dp v 32 /\
    op_taint tl (Var rv) = {} /\ op_prov K (Var rv) = NONE /\
    op_taint tl (Var lv) = {} /\ op_prov K (Var lv) = NONE /\
    (!i. db+r <= i /\ i < db+r+32+contractABI$ceil32 cnt ==> i NOTIN tl.t_mem) /\
    (!i. ~(db+r <= i /\ i < db+r+32+contractABI$ceil32 cnt) ==>
      (i IN tl.t_mem <=> i IN tn.t_mem)) /\
    mem_agree_outside {i | db+r <= i /\ i < db+r+32+contractABI$ceil32 cnt}
      v.vs_memory s.vs_memory /\
    tl.t_stor = tn.t_stor /\ tl.t_trans = tn.t_trans /\ tl.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> not_fresh_at sc x /\
      lookup_var x v = lookup_var x s /\ FLOOKUP K x = FLOOKUP G x /\
      op_taint tl (Var x) = op_taint tn (Var x))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ho+32 <= cap /\ r+(32+contractABI$ceil32 cnt) <= cap /\ p < dimword(:256)` by decide_tac >>
  drule_all abi_encode_child_prefix_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `J` (qx_choose_then `tk` (qx_choose_then `u` strip_assume_tac)))) >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [pairTheory.FST, pairTheory.SND]) >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  drule abi_encode_child_prefix_live >> disch_then (strip_assume_tac o SRULE []) >>
  `not_fresh_at prepared hv /\ not_fresh_at prepared rv /\ not_fresh_at prepared tv /\
   (!x. not_fresh_at sa x ==> not_fresh_at prepared x)` by
    (gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  qabbrev_tac `u1 = u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa prepared)` >>
  `lookup_var tv u1 = SOME (n2w (db+r)) /\ lookup_var src u1 = SOME (n2w a) /\
   ptr_covers J tk tv u1 (32+contractABI$ceil32 cnt) /\
   ptr_covers J tk src u1 (32+cnt) /\ mload a u1 = n2w cnt /\
   lookup_var hv u1 = SOME (n2w (db+ho)) /\ lookup_var dp u1 = SOME (n2w p) /\
   lookup_var rv u1 = SOME (n2w r) /\ ptr_covers J tk hv u1 32 /\
   ptr_covers J tk dp u1 32 /\
   (!i. a <= i /\ i < a+32+cnt ==> i NOTIN tk.t_mem)` by
    (gvs[ptr_covers_def, Abbr `u1`, lookup_var_def, mload_def] >> metis_tac[]) >>
  `not_fresh_at prepared src /\ not_fresh_at prepared dp /\
   (db+r)+32+contractABI$ceil32 cnt < dimword(:256) /\ 32+cnt < dimword(:256)` by
    (simp[] >> decide_tac) >>
  SUBGOAL_THEN ``(db+r)+32+contractABI$ceil32 cnt <= a \/ a+32+cnt <= db+r`` assume_tac
    >- decide_tac >>
  drule_all (Q.INST [`hd` |-> `hv`, `dp` |-> `dp`] abi_bytes_child_suffix_ready_ptr) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `J2` (qx_choose_then `tl` (qx_choose_then `v` strip_assume_tac)))) >>
  qexistsl_tac [`J`,`tk`,`u`,`J2`,`tl`,`v`,`hv`,`rv`,`tv`,`lv`] >>
  asm_simp_tac bool_ss [Abbr `u1`] >>
  `(!x. not_fresh_at prepared x ==> not_fresh_at sc x) /\
   (!x. not_fresh_at sa x ==> not_fresh_at sc x)` by
    (drule abi_encode_bytes_shape >> strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  gvs[lookup_var_def, ptr_covers_def, op_prov_def] >> metis_tac[]
QED

Theorem compile_abi_bytes_child_seq_ptr:
  compile_abi_encode_child (Var dst) (Var src) (AbiBytestring maxlen) T ho (Var dp) sa = (out,sb) /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\ not_fresh_at sa dp /\
  lookup_var dst s = SOME (n2w db) /\ lookup_var src s = SOME (n2w a) /\
  lookup_var dp s = SOME (n2w p) /\ mload p s = n2w r /\ mload a s = n2w cnt /\
  cnt <= maxlen /\ ptr_covers G tn dst s cap /\
  ptr_covers G tn src s (32+cnt) /\ ptr_covers G tn dp s 32 /\
  (!i. a <= i /\ i < a+32+cnt ==> i NOTIN tn.t_mem) /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
  ho+32 <= r /\ r+32+contractABI$ceil32 cnt <= cap /\
  db+cap < dimword(:256) /\ a+32+cnt < dimword(:256) /\ p+32 < dimword(:256) /\
  (db+cap <= a \/ a+32+cnt <= db) /\
  (db+cap <= p \/ p+32 <= db) /\ ~ctx_has_dalloca ctx ==>
  ?H tm t.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm /\
    eval_operand out t = SOME (n2w (32+contractABI$ceil32 cnt)) /\
    op_taint tm out = {} /\ op_prov H out = NONE /\
    (!i. (db+ho <= i /\ i < db+ho+32) \/
         (db+r <= i /\ i < db+r+32+contractABI$ceil32 cnt) \/
         (p <= i /\ i < p+32) ==> i NOTIN tm.t_mem) /\
    (!i. ~((db+ho <= i /\ i < db+ho+32) \/
           (db+r <= i /\ i < db+r+32+contractABI$ceil32 cnt) \/
           (p <= i /\ i < p+32)) ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP H v = FLOOKUP G v /\
      op_taint tm (Var v) = op_taint tn (Var v)) /\
    mload (db+ho) t = n2w r /\ mload p t = n2w (r+32+contractABI$ceil32 cnt) /\
    mem_agree_outside
      {i | (db+ho <= i /\ i < db+ho+32) \/
           (db+r <= i /\ i < db+r+32+contractABI$ceil32 cnt) \/
           (p <= i /\ i < p+32)} t.vs_memory s.vs_memory
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule abi_encode_dynamic_child_trace >> strip_tac >>
  drule_all abi_bytes_child_prefix_ready_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `J` (qx_choose_then `tk` (qx_choose_then `u`
    (qx_choose_then `J2` (qx_choose_then `tl` (qx_choose_then `v` strip_assume_tac))))))) >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [pairTheory.FST, pairTheory.SND]) >>
  qpat_x_assum `child_len = _` SUBST_ALL_TAC >> drule_all abi_bytes_child_finish_seq_ptr >>
  disch_then (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `w` strip_assume_tac))) >>
  map_every (drule_then strip_assume_tac)
    [abi_encode_child_prefix_shape, abi_encode_bytes_shape, abi_encode_child_suffix_shape] >>
  `inst_extends prepared sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts prepared sb = emitted_insts prepared child_end ++ emitted_insts child_end sb /\
   emitted_insts sa sb = emitted_insts sa prepared ++ emitted_insts prepared sb` by
    (conj_tac >> irule emitted_insts_append >> gvs[inst_extends_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa prepared) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts prepared sb)` by
    (gvs[EVERY_MEM, EVERY_APPEND] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK (w with vs_inst_idx := u.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm` by
    (qpat_x_assum `emitted_insts sa sb = _` (fn th => once_rewrite_tac[th]) >>
     irule successful_seq_ptr_append >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`J`,`tk`] >> asm_simp_tac bool_ss [] >>
     qpat_x_assum `emitted_insts prepared sb = _` (fn th => rewrite_tac[th]) >>
     asm_simp_tac bool_ss []) >>
  qexistsl_tac [`H`,`tm`,`w with vs_inst_idx := u.vs_inst_idx`] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  `db+ho < dimword(:256) /\ p < dimword(:256) /\
   regions_disjoint (db+ho,32) (p,32)` by
    (gvs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `w2n ((n2w (db+ho)):256 word) = db+ho /\ w2n ((n2w p):256 word) = p` by simp[w2n_n2w] >>
  qpat_x_assum `w2n (n2w (db+ho)) = _` (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `w2n (n2w p) = _` (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  drule_all (PURE_REWRITE_RULE [ADD_ASSOC]
    (Q.INST [`dest` |-> `db+roff`, `len` |-> `32+contractABI$ceil32 cnt`]
      abi_child_tail_and_cells_frame)) >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x w = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    (qpat_x_assum `!x. not_fresh_at sa x ==> _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at child_end x ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm` by simp[] >>
  drule_all (PURE_REWRITE_RULE [ADD_ASSOC]
    (Q.INST [`dest` |-> `db+roff`, `len` |-> `32+contractABI$ceil32 cnt`]
      abi_child_post_inst_idx)) >>
  disch_then (qspec_then `u.vs_inst_idx` assume_tac) >>
  qpat_x_assum `out = _` SUBST_ALL_TAC >> first_assum ACCEPT_TAC
QED
