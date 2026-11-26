(* Dynamic RawLog: transport the prepared prefix, then execute LOG at its
   actual instruction cursor and reservation bound. *)
Theory bodyRawLogDynamicSuffixPathMods
Ancestors
  bodyFullLog bodyFullLogSuffix fragGasCopySeqLiftProps fragGasOriginPtrLoop
  ghostPcTransportPtr exprLoweringProps emitHelperProps emitHelper compileEnv fragExec
  ptrDiscipline venomExecSemantics venomInst venomState memSafeRun
  vyperEvent words list rich_list arithmetic

Theorem dynamic_log_suffix_layout[local]:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = ((),sb) /\
  fn_has_code sm sb func ==>
  s2.cs_current_bb = sm.cs_current_bb /\
  LENGTH s2.cs_current_insts = LENGTH sm.cs_current_insts + LENGTH (emitted_insts sm s2) /\
  fn_has_code s2 sb func /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS /\ i.inst_opcode <> DALLOCA)
    (emitted_insts sm s2) /\
  ?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sm s2) (DROP (LENGTH sm.cs_current_insts) bb.bb_instructions)
Proof
  strip_tac >>
  `cs_extends sm s1 /\ cs_extends s1 s2` by
    (qpat_assum `emit_op MLOAD _ _ = _` (strip_assume_tac o MATCH_MP emit_op_extends) >>
     qpat_assum `emit_op ADD _ _ = _` (strip_assume_tac o MATCH_MP emit_op_extends) >>
     fs[same_blocks_def] >>
     conj_tac >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `fn_has_code s2 sb func` by
    (drule cs_extends_emit_inst >> strip_tac >>
     `cs_extends sm s2` by metis_tac[cs_extends_trans] >>
     drule_all fn_has_code_split >> simp[]) >>
  gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  simp[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  simp[mk_inst_def, is_terminator_def] >>
  qpat_x_assum `fn_has_code sm _ func` (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  qexists_tac `bb` >> simp[] >>
  gvs[IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[mk_inst_def]
QED

Theorem raw_log_dynamic_suffix_path_mods:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = ((),sb) /\
  fn_has_code sm sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm s2) s = OK p /\
  run_inst_seq_mem_ok (emitted_insts sm s2) s /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sm s2) s Gp tp /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (p with vs_vars := s.vs_vars) = s /\
  LENGTH ops < dimword (:256) /\ off < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  eval_operands ops p = SOME (MAP event_value_to_word vals) /\
  eval_operand ptr_op p = SOME (n2w off) /\
  eval_operand len_op p = SOME (n2w (LENGTH bs)) /\
  EVERY (\op. op_taint tp op = {}) (ptr_op::len_op::ops) /\
  (LENGTH bs <> 0 ==> ?x. ptr_op = Var x /\ ptr_covers Gp tp x p (LENGTH bs)) /\
  (!i. off <= i /\ i < off + LENGTH bs ==> i NOTIN tp.t_mem) /\
  off + LENGTH bs <= p.vs_alloca_next /\
  mem_bytes_at off (LENGTH bs) p.vs_memory = bs /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s.vs_call_ctx.cc_static = cx.txn.is_static /\ s.vs_call_ctx.cc_address = cx.txn.target ==>
  let q = p with vs_inst_idx := LENGTH s2.cs_current_insts in
  let ev = encode_raw_event_values cx.txn.target vals bs in
  let fin = q with <|vs_logs := q.vs_logs ++ [ev]; vs_inst_idx := LENGTH sb.cs_current_insts|> in
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    ((if cx.txn.is_static then Abort ExHalt_abort (halt_state (set_returndata [] q))
      else OK fin),Gp,tp)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all dynamic_log_suffix_layout >> strip_tac >>
  `s2.cs_current_bb = s.vs_current_bb` by simp[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sm s2) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `(ctx_has_dalloca ctx ==> !pre i post u. emitted_insts sm s2 = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     qpat_x_assum `EVERY _ (emitted_insts sm s2)` mp_tac >> simp[EVERY_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
     (emitted_insts sm s2)` by fs[EVERY_MEM] >>
  qabbrev_tac `q = p with vs_inst_idx := LENGTH s2.cs_current_insts` >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Gp,tp) /\
   allocas_from lo p` by
    (drule_all run_inst_seq_origin_ptr_lift >> simp[Abbr `q`]) >>
  `p = s with vs_vars := p.vs_vars` by
    (qpat_x_assum `p with vs_vars := _ = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `~q.vs_halted /\ q.vs_current_bb = s2.cs_current_bb /\
   q.vs_inst_idx = LENGTH s2.cs_current_insts /\ allocas_from lo q /\
   lo <= q.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
   q.vs_call_ctx.cc_static = cx.txn.is_static /\ q.vs_call_ctx.cc_address = cx.txn.target` by
    (simp[Abbr `q`, allocas_from_def] >>
     qpat_assum `p = s with vs_vars := _` SUBST1_TAC >>
     `allocas_below_fmp (s with vs_vars := p.vs_vars) = allocas_below_fmp s` by
       simp[allocas_below_fmp_def] >> simp[]) >>
  `eval_operands ops q = SOME (MAP event_value_to_word vals) /\
   eval_operand ptr_op q = SOME (n2w off) /\
   eval_operand len_op q = SOME (n2w (LENGTH bs)) /\
   (LENGTH bs <> 0 ==> ?x. ptr_op = Var x /\ ptr_covers Gp tp x q (LENGTH bs)) /\
   off + LENGTH bs <= q.vs_alloca_next /\ mem_bytes_at off (LENGTH bs) q.vs_memory = bs` by
    simp[Abbr `q`] >>
  irule gas_origin_ptr_path_trans >> qexistsl [`Gp`,`q`,`tp`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qabbrev_tac `ow = n2w off : 256 word` >>
  qabbrev_tac `nw = n2w (LENGTH bs) : 256 word` >>
  `(w2n nw <> 0 ==> ?x. ptr_op = Var x /\ ptr_covers Gp tp x q (w2n nw)) /\
   (!i. w2n ow <= i /\ i < w2n ow + w2n nw ==> i NOTIN tp.t_mem) /\
   w2n ow + w2n nw <= q.vs_alloca_next` by
    simp[Abbr `ow`, Abbr `nw`, w2n_n2w, LESS_MOD, ADD_COMM] >>
  qpat_assum `w2n ow + w2n nw <= q.vs_alloca_next`
    (fn th => assume_tac (DISJ2 ``w2n (nw:256 word) = 0`` th)) >>
  Cases_on `cx.txn.is_static` >> simp[]
  >- (`q.vs_call_ctx.cc_static` by simp[] >>
      drule_all compile_log_emit_static_origin_ptr_path >> simp[]) >>
  `~q.vs_call_ctx.cc_static` by simp[] >>
  drule_all compile_log_emit_origin_ptr_path >>
  simp[encode_raw_event_values_def, encode_raw_event_def,
       Abbr `ow`, Abbr `nw`, w2n_n2w, LESS_MOD]
QED
