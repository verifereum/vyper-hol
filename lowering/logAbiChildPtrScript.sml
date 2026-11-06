(* Pointer-certified dynamic child setup and bookkeeping. *)
Theory logAbiChildPtr
Ancestors
  logAbiEncodePtr logAbiPrefixPtr logInstSeqPtr logTopicScalarPtr
  abiEncoderChildCode abiEncoderBytesCode bodyPtrDefs fragGasSeqPtr
  emitHelperProps emitHelper exprLoweringProps compileEnv
  venomExecSemantics venomState venomInst ptrDiscipline ptrSafeRun
  finite_map words arithmetic list rich_list

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
