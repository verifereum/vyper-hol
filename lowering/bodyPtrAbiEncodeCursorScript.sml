(* Scalar cursor offsets obtain provenance only by addition to a covered root. *)
Theory bodyPtrAbiEncodeCursor
Ancestors
  bodyPtrAbiEncodeWindow bodyPtrAbiEncodeEndpoint bodyPtrAbiEncodeOffset
  abiEncoderChildCode abiEncoderChildPrefix abiEncoderChildSuffixReach
  typedCopyPtr exprLoweringProps emitHelperProps context compileEnv emitHelper
  fragGasSeqPtr fragGasPathPtr fragExecPtr bodyPtrDefs ptrDiscipline ptrSafeRun
  venomExecSemantics venomInst venomState finite_map words arithmetic list rich_list

Theorem abi_encode_scalar_add_coverage[local]:
  !root right s a G tn total off n PG id p.
  lookup_var root s = SOME a /\ eval_operand right s = SOME (n2w off) /\
  ptr_covers G tn root s total /\
  off < total /\ off+n <= total /\ w2n a+off < dimword(:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root;right] [p])
      (update_var p (a+n2w off) s))
    (step_taint (mk_inst id ADD [Var root;right] [p]) s
      (update_var p (a+n2w off) s) tn)
    p (update_var p (a+n2w off) s) n
Proof
  rpt gen_tac >> strip_tac >>
  `off < dimword(:256)` by decide_tac >>
  simp[ptr_covers_def, copy_len_binop_ghost_frame] >>
  gvs[ptr_covers_def] >>
  simp[step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
       lookup_var_def, update_var_def, w2n_add_2, w2n_n2w,
       arithmeticTheory.LESS_MOD] >> decide_tac
QED

Theorem abi_encode_scalar_add_sequence_checks:
  !op st st' root right s a G tn total off n ctx D fn PG.
  emit_op ADD [Var root;right] st = (op,st') /\
  not_fresh_at st root /\ lookup_var root s = SOME a /\
  eval_operand right s = SOME (n2w off) /\
  op_taint tn (Var root) = {} /\ op_taint tn right = {} /\
  off+n <= total /\
  (0<n ==> ptr_covers G tn root s total /\ w2n a+off < dimword(:256)) /\
  ~ctx_has_dalloca ctx ==>
  ?p t Gf tnf.
    op = Var p /\
    run_inst_seq (emitted_insts st st') s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s Gf tnf /\
    lookup_var p t = SOME (a+n2w off) /\ op_taint tnf (Var p) = {} /\
    (0<n ==> ptr_covers Gf tnf p t n) /\ not_fresh_at st' p /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_labels = s.vs_labels /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!q. not_fresh_at st q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >> rename1 `off+n <= capacity` >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qabbrev_tac `p = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `t = update_var p (a+n2w off) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst st.cs_next_id ADD [Var root;right] [p]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst st.cs_next_id ADD [Var root;right] [p]) s t tn` >>
  `0<n ==> ptr_covers Gf tnf p t n` by
    (strip_tac >>
     `off<capacity` by decide_tac >>
     qpat_x_assum `0<n ==> _` (drule_then strip_assume_tac) >>
     simp[Abbr `Gf`, Abbr `tnf`, Abbr `t`] >>
     irule abi_encode_scalar_add_coverage >> simp[] >>
     qexists_tac `capacity` >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst st.cs_next_id ADD [Var root;right] [p]) s` by
    (irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  `step_inst_base (mk_inst st.cs_next_id ADD [Var root;right] [p]) s = OK t` by
    simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def,
         eval_operand_def, Abbr `t`] >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, Abbr `Gf`, Abbr `tnf`,
       Abbr `t`, copy_len_binop_ghost_frame, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE] >>
  conj_tac >- simp[not_fresh_at_def, Abbr `p`] >>
  rpt strip_tac >>
  `q <> p` by (gvs[not_fresh_at_def, Abbr `p`] >> metis_tac[]) >>
  simp[GSYM update_var_def, copy_len_binop_ghost_frame]
QED

Theorem abi_encode_scalar_add_fresh_vars:
  emit_op ADD [Var root;right] st = (op,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  lookup_var root s = SOME a /\ eval_operand right s = SOME b /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
      exec_pure2_def, eval_operand_def] >>
  irule fresh_vars_wrt_update_var >> simp[] >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem abi_encode_scalar_add_checked_ptr_path:
  !op st st' root right s a G tn total off n ctx D fn PG bb limit_st.
  emit_op ADD [Var root;right] st = (op,st') /\
  not_fresh_at st root /\ lookup_var root s = SOME a /\
  eval_operand right s = SOME (n2w off) /\
  op_taint tn (Var root) = {} /\ op_taint tn right = {} /\
  off+n <= total /\
  (0<n ==> ptr_covers G tn root s total /\ w2n a+off < dimword(:256)) /\
  ~ctx_has_dalloca ctx /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?p t Gf tnf.
    op = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx+1)) /\
    lookup_var p t = SOME (a+n2w off) /\ op_taint tnf (Var p) = {} /\
    (0<n ==> ptr_covers Gf tnf p t n) /\
    not_fresh_at st' p /\ fresh_vars_wrt limit_st t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_labels = s.vs_labels /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    run_inst_seq (emitted_insts st st') s = OK t /\
    (!q. not_fresh_at st q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_encode_scalar_add_sequence_checks >>
  disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
  `fresh_vars_wrt limit_st t` by
    (drule_all abi_encode_scalar_add_fresh_vars >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def] >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`] >> gvs[]
QED

Theorem abi_encode_cursor_load_sequence_checks:
  !op st st' cursor s a G tn ctx D fn PG.
  emit_op MLOAD [Var cursor] st = (op,st') /\
  lookup_var cursor s = SOME a /\ ptr_covers G tn cursor s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?p t Gf tnf.
    op = Var p /\
    run_inst_seq (emitted_insts st st') s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s Gf tnf /\
    lookup_var p t = SOME (mload (w2n a) s) /\ op_taint tnf (Var p) = {} /\
    not_fresh_at st' p /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_labels = s.vs_labels /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!q. not_fresh_at st q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qabbrev_tac `p = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `t = update_var p (mload (w2n a) s) s` >>
  qabbrev_tac `Gf = step_prov PG G (mk_inst st.cs_next_id MLOAD [Var cursor] [p]) t` >>
  qabbrev_tac `tnf = step_taint (mk_inst st.cs_next_id MLOAD [Var cursor] [p]) s t tn` >>
  `op_taint tnf (Var p) = {} /\ tnf.t_mem = tn.t_mem /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans` by
    (simp[Abbr `tnf`, Abbr `t`] >> irule mload_ghost_clean >> simp[eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst st.cs_next_id MLOAD [Var cursor] [p]) s` by
    (irule ptr_inst_ok_mload >> simp[]) >>
  `step_inst_base (mk_inst st.cs_next_id MLOAD [Var cursor] [p]) s = OK t` by
    simp[Once step_inst_base_def, mk_inst_def, exec_read1_def, eval_operand_def, Abbr `t`] >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, Abbr `Gf`, Abbr `tnf`,
       Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[not_fresh_at_def, Abbr `p`] >>
  rpt strip_tac >>
  `q <> p` by (gvs[not_fresh_at_def, Abbr `p`] >> metis_tac[]) >>
  simp[step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, set_var_taint_def, mk_inst_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE, op_taint_def]
QED

Theorem abi_encode_cursor_load_fresh_vars:
  emit_op MLOAD [Var cursor] st = (op,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  lookup_var cursor s = SOME a /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
      exec_read1_def, eval_operand_def] >>
  irule fresh_vars_wrt_update_var >> simp[] >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem abi_encode_cursor_load_checked_ptr_path:
  !op st st' cursor s a G tn ctx D fn PG bb limit_st.
  emit_op MLOAD [Var cursor] st = (op,st') /\
  lookup_var cursor s = SOME a /\ ptr_covers G tn cursor s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?p t Gf tnf.
    op = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx+1)) /\
    lookup_var p t = SOME (mload (w2n a) s) /\ op_taint tnf (Var p) = {} /\
    not_fresh_at st' p /\ fresh_vars_wrt limit_st t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_labels = s.vs_labels /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    run_inst_seq (emitted_insts st st') s = OK t /\
    (!q. not_fresh_at st q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_encode_cursor_load_sequence_checks >>
  disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
  `fresh_vars_wrt limit_st t` by
    (drule_all abi_encode_cursor_load_fresh_vars >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def] >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`] >> gvs[]
QED

Theorem abi_encode_cursor_prefix_trace:
  abi_encode_child_prefix dst ho cursor st = (ops,st') ==>
  ?head offset child_dst c1 c2.
    ops = (head,offset,child_dst) /\
    emit_op ADD [dst;Lit (n2w ho)] st = (head,c1) /\
    emit_op MLOAD [cursor] c1 = (offset,c2) /\
    emit_op ADD [dst;offset] c2 = (child_dst,st') /\
    c1.cs_next_var = st.cs_next_var+1 /\
    c2.cs_next_var = c1.cs_next_var+1 /\
    st'.cs_next_var = c2.cs_next_var+1 /\
    emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 st'
Proof
  simp_tac bool_ss [abi_encode_child_prefix_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op ADD [dst;Lit (n2w ho)] st = (head,c1)` >>
  rename1 `emit_op MLOAD [cursor] c1 = (offset,c2)` >>
  rename1 `emit_op ADD [dst;offset] c2 = (child_dst,ready)` >>
  imp_res_tac emitted_insts_emit_op >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND]
QED
