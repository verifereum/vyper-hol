(* Pointer checks for indexed log topic hashing. *)
Theory logTopicPtr
Ancestors
  logInstSeqPtr logValueFramePtr bodyPtrDefs codegenRel ptrCoverage ptrSafeRun ptrDiscipline
  venomExecSemantics venomInstProofs venomInst venomState
  contextCodegenRelProps contextCodegenRel memLocDefs finite_map words
  exprSimHash emitHelperProps emitHelper compileEnv context fragExec arithmetic exprLoweringProps logAbiPrefixPtr list rich_list fragGasSeqPtr fragGasPathPtr

Theorem ptr_inst_ok_sha3_clean:
  ptr_covers G tn src s (w2n n) /\
  lookup_var src s = SOME a /\ eval_operand len s = SOME n /\
  op_taint tn len = {} /\
  (!i. w2n a <= i /\ i < w2n a + w2n n ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id SHA3 [Var src;len] [out]) s
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, eval_operand_def] >>
  simp[memory_range_of_operands_def, eval_operand_def] >>
  conj_tac
  >- (rpt strip_tac >> gvs[mem_read_ops_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds] >>
  simp[eval_operand_def, update_var_def] >> rpt strip_tac >> gvs[]
QED

Theorem sha3_ghost_frame:
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  op_taint (step_taint (mk_inst id SHA3 [src;len] [out]) s t tn) (Var out) = {} /\
  (step_taint (mk_inst id SHA3 [src;len] [out]) s t tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id SHA3 [src;len] [out]) s t tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id SHA3 [src;len] [out]) s t tn).t_trans = tn.t_trans /\
  (!p. p <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id SHA3 [src;len] [out]) t) p = FLOOKUP G p /\
    op_taint (step_taint (mk_inst id SHA3 [src;len] [out]) s t tn) (Var p) =
      op_taint tn (Var p))
Proof
  strip_tac >>
  simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       step_prov_def, set_prov_def, out_prov_def,
       mk_inst_def, mem_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, store_taint_def,
       adopt_reset_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, FLOOKUP_DEF] >>
  rpt strip_tac >> Cases_on `eval_operand src s` >>
  simp[pred_setTheory.EXTENSION, SF CONJ_ss, FDOM_DRESTRICT, DRESTRICT_DEF, FAPPLY_FUPDATE_THM]
QED

Theorem emit_sha3_clean_seq_ptr:
  emit_op SHA3 [Var src;len] sa = (Var out,sb) /\
  ptr_covers G tn src s (w2n n) /\
  lookup_var src s = SOME a /\ eval_operand len s = SOME n /\
  op_taint tn len = {} /\
  (!i. w2n a <= i /\ i < w2n a + w2n n ==> i NOTIN tn.t_mem) /\
  mem_bytes_at (w2n a) (w2n n) s.vs_memory = bs /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    lookup_var out sf = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    op_taint tnf (Var out) = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id SHA3 [Var src;len] [out]]` by
    (drule emitted_insts_emit_op >> simp[] >> metis_tac[]) >>
  `!p. not_fresh_at sa p ==> p <> out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  qabbrev_tac `t = update_var out
    (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) s` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id SHA3 [Var src;len] [out]` >>
  `step_inst_base i s = OK t` by
    (simp[Abbr `i`, Abbr `t`] >> irule step_SHA3_bytes >>
     simp[eval_operand_def]) >>
  qexistsl_tac [`step_prov PG G i t`, `step_taint i s t tn`, `t`] >>
  conj_tac >- simp[run_inst_seq_def] >>
  conj_tac >-
    (simp[] >> irule inst_seq_ptr_singleton >> simp[Abbr `i`] >>
     irule ptr_inst_ok_sha3_clean >> simp[]) >>
  `op_taint (step_taint i s t tn) (Var out) = {} /\
   (step_taint i s t tn).t_mem = tn.t_mem /\
   (step_taint i s t tn).t_stor = tn.t_stor /\
   (step_taint i s t tn).t_trans = tn.t_trans /\
   (!p. p <> out ==>
     FLOOKUP (step_prov PG G i t) p = FLOOKUP G p /\
     op_taint (step_taint i s t tn) (Var p) = op_taint tn (Var p))` by
    (simp[Abbr `i`] >> irule sha3_ghost_frame >> simp[Abbr `t`, update_var_def]) >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem compile_encode_log_topic_bytes_seq_ptr:
  compile_encode_log_topic (Var src) T sa = (out,sb) /\
  not_fresh_at sa src /\ ptr_covers G tn src s (32 + LENGTH bs) /\
  lookup_var src s = SOME a /\ mload (w2n a) s = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a + 32) (LENGTH bs) s.vs_memory = bs /\
  w2n a + 32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
  (!i. w2n a <= i /\ i < w2n a + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    eval_operand out sf = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    op_taint tnf out = {} /\ sf.vs_memory = s.vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  simp_tac bool_ss [compile_encode_log_topic_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [Var src;Lit 32w] sa = (data,sm)` >>
  rename1 `emit_op MLOAD [Var src] sm = (len,sn)` >>
  `?dp. data = Var dp` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> metis_tac[]) >>
  `?lp. len = Var lp` by
    (qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> metis_tac[]) >>
  `?res. out = Var res` by
    (qpat_assum `emit_op SHA3 _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> metis_tac[]) >>
  gvs[] >>
  `eval_operand (Lit 32w) s = SOME (n2w 32) /\ op_taint tn (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  `ptr_covers G tn src s (32 + LENGTH bs)` by simp[] >>
  drule_all (Q.INST [`off` |-> `32`] emit_addr_add_seq_ptr) >>
  disch_then (qspecl_then [`fn`, `PG`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `t` strip_assume_tac)))) >>
  suspend "load"
QED

Resume compile_encode_log_topic_bytes_seq_ptr[load]:
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)` >>
  `lookup_var src u = SOME a /\ ptr_covers G1 tn1 src u 32 /\
   (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn1.t_mem)` by
    (gvs[Abbr `u`, ptr_covers_def, lookup_var_def] >> metis_tac[ADD_COMM, LESS_EQ_ADD, LESS_LESS_EQ_TRANS]) >>
  drule_all emit_mload_clean_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`]
    (qx_choose_then `G2` (qx_choose_then `tn2` (qx_choose_then `v` strip_assume_tac)))) >>
  suspend "hash"
QED
Resume compile_encode_log_topic_bytes_seq_ptr[hash]:
  `not_fresh_at sm dp /\ (!p. not_fresh_at sa p ==> not_fresh_at sm p) /\
   (!p. not_fresh_at sm p ==> not_fresh_at sn p)` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
       [`emit_op ADD _ _ = _`, `emit_op MLOAD _ _ = _`] >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  qabbrev_tac `w = v with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts sm sn)` >>
  `lookup_var dp w = SOME (a+32w) /\
   ptr_covers G2 tn2 dp w (w2n (n2w (LENGTH bs):bytes32)) /\
   eval_operand (Var lp) w = SOME (n2w (LENGTH bs)) /\
   (!i. w2n (a+32w) <= i /\ i < w2n (a+32w) + w2n (n2w (LENGTH bs):bytes32)
        ==> i NOTIN tn2.t_mem) /\
   mem_bytes_at (w2n (a+32w)) (w2n (n2w (LENGTH bs):bytes32)) w.vs_memory = bs` by
    (gvs[Abbr `w`, Abbr `u`, ptr_covers_def, eval_operand_def, lookup_var_def,
         mload_def, w2n_add_2, w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  drule_all emit_sha3_clean_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `z` strip_assume_tac)))) >>
  suspend "compose"
QED
Resume compile_encode_log_topic_bytes_seq_ptr[compose]:
  `emitted_insts sm sb = emitted_insts sm sn ++ emitted_insts sn sb /\
   emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (imp_res_tac emitted_insts_emit_op >> conj_asm1_tac
     >- (irule emitted_insts_append >> simp[]) >>
     irule emitted_insts_append >> simp[APPEND_ASSOC]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts sa sm) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts sm sn) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sn sb)` by
    (imp_res_tac emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]) >>
  `run_inst_seq (emitted_insts sm sb) u = OK (z with vs_inst_idx := v.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G1 tn1 (emitted_insts sm sb) u Gf tnf` by
    (once_asm_rewrite_tac[] >> irule successful_seq_ptr_append >>
     gvs[Abbr `w`] >> qexistsl_tac [`G2`, `tn2`] >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (simp[EVERY_APPEND] >> fs[EVERY_MEM]) >>
  `run_inst_seq (emitted_insts sa sb) s =
      OK (z with vs_inst_idx := t.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf` by
    (once_asm_rewrite_tac[] >> qunabbrev_tac `u` >>
     drule_all successful_seq_ptr_append >> simp[]) >>
  qexistsl_tac [`Gf`, `tnf`, `z with vs_inst_idx := t.vs_inst_idx`] >>
  simp[] >> suspend "frame"
QED
Resume compile_encode_log_topic_bytes_seq_ptr[frame]:
  gvs[Abbr `u`, Abbr `w`, eval_operand_def, lookup_var_def] >> metis_tac[]
QED
Finalise compile_encode_log_topic_bytes_seq_ptr

Theorem compile_encode_log_topic_bytes_path_ptr:
  compile_encode_log_topic (Var src) T sa = (out,sb) /\
  not_fresh_at sa src /\ ptr_covers G tn src s (32 + LENGTH bs) /\
  lookup_var src s = SOME a /\ mload (w2n a) s = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a + 32) (LENGTH bs) s.vs_memory = bs /\
  w2n a + 32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
  (!i. w2n a <= i /\ i < w2n a + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    eval_operand out sf = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    op_taint tnf out = {} /\ sf.vs_memory = s.vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule_all compile_encode_log_topic_bytes_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `t` strip_assume_tac)))) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (qpat_x_assum `compile_encode_log_topic _ _ _ = _` mp_tac >>
     simp[compile_encode_log_topic_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[emitted_insts_def] >>
     CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
     simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)`] >>
  conj_tac >- (drule_all run_inst_seq_gas_path_ptr >> simp[]) >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem compile_encode_log_topic_word_path_ptr:
  compile_encode_log_topic x F sa = (out,sb) /\ ~s.vs_halted /\
  eval_operand x s = SOME w /\ op_taint tn x = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK s) /\
  eval_operand out s = SOME w /\ op_taint tn out = {} /\ sb = sa
Proof
  simp[compile_encode_log_topic_def, comp_return_def] >> strip_tac >>
  gvs[] >> irule (cj 1 gas_path_ptr_rules) >> simp[]
QED
