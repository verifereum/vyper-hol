Theory bodyPtrTypeBuiltinsExtract32Read
Ancestors
  bodyPtrTypeBuiltinsExtract32BoundsPtr rawCallBufferPtr
  immutableRegionLoadPtr storageCopyBodyRaisePtr assignBasePtrBytesPrefix
  instSeqComposePtr ghostPcTransportPtr bodyPtrDefs ptrDiscipline
  venomInst venomState venomExecSemantics instIdxIndep fragExec fragGasSeqPtr
  compileEnv loweringStateRelDefs words list finite_map pred_set exprLoweringProps emitHelperProps
  decoderGhostFramePtr bodyPtrTypeBuiltinsBounds builtinBytes emitHelper rich_list
  augAssignPtrScalarCertificate augAssignPtrScalarRun

(* An interior address retains the source provenance. Only the loaded word
   is provenance-free; clean_add_checked_uniform deliberately preserves it. *)
Theorem extract32_payload_read_certificate:
  lookup_var data s = SOME a /\ eval_operand offset s = SOME b /\
  ptr_covers G tn data s span /\ w2n b + 32 <= span /\
  w2n a + w2n b < dimword(:256) /\ op_taint tn offset = {} /\
  ~ctx_has_dalloca ctx /\
  (!i. w2n a + w2n b <= i /\ i < w2n a + w2n b + 32 ==> i NOTIN tn.t_mem) ==>
  ?H th t.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var data;offset] [addr];
       mk_inst (id+1) MLOAD [Var addr] [out]] (s with vs_inst_idx := k) H th) /\
    run_inst_seq [mk_inst id ADD [Var data;offset] [addr];
      mk_inst (id+1) MLOAD [Var addr] [out]] s = OK t /\
    t = update_var out (mload (w2n (a+b)) s) (update_var addr (a+b) s) /\
    op_prov H (Var out) = NONE /\ op_taint th (Var out) = {} /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!p. p <> addr /\ p <> out ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `op_taint tn (Var data) = {}` by gvs[ptr_covers_def] >>
  `eval_operand (Var data) s = SOME a` by simp[eval_operand_def] >>
  qabbrev_tac `s1 = update_var addr (a+b) s` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst id ADD [Var data;offset] [addr]) s1` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (addr,{})` >>
  `!k. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [Var data;offset] [addr]] (s with vs_inst_idx := k) G1 tn1` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `s1`] >>
     irule clean_add_checked_uniform >> simp[]) >>
  `ptr_covers G1 tn1 addr s1 32` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `s1`] >>
     irule (SRULE [ptr_covers_inst_idx] storage_copy_add_covers) >>
     simp[] >> qexists_tac `span` >> simp[]) >>
  `lookup_var addr s1 = SOME (a+b)` by simp[Abbr `s1`, lookup_var_update_var] >>
  `!i. w2n (a+b) <= i /\ i < w2n (a+b)+32 ==> i NOTIN tn1.t_mem` by
    simp[Abbr `tn1`, w2n_add_2] >>
  drule_all assign_base_bytes_mload_seq >>
  disch_then (qspecl_then [`D`,`fn`,`PG`,`id+1`,`out`] strip_assume_tac) >>
  qexistsl_tac [`G'`,`tn'`,`u`] >> simp[] >>
  conj_tac >- (irule (SRULE [] (Q.INST
      [`xs` |-> `[mk_inst id ADD [Var data;offset] [addr]]`,
       `ys` |-> `[mk_inst (id+1) MLOAD [Var addr] [out]]`]
      inst_seq_ptr_uniform_append)) >>
    simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, eval_operand_def, Abbr `s1`, is_terminator_def] >>
    simp[GSYM mk_inst_def] >> metis_tac[]) >>
  gvs[Abbr `tn1`] >>
  conj_tac >- (simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
    exec_pure2_def, eval_operand_def] >>
    simp[GSYM mk_inst_def] >> gvs[Abbr `s1`]) >>
  conj_tac >- simp[Abbr `s1`, update_var_def, mload_def] >>
  rpt strip_tac >>
  `FLOOKUP G' p = FLOOKUP G1 p /\
   op_taint tn' (Var p) = op_taint (tn with t_var := tn.t_var |+ (addr,{})) (Var p)` by
    metis_tac[] >>
  simp[Abbr `G1`, op_taint_def, FLOOKUP_UPDATE] >>
  irule step_prov_other_output >> simp[mk_inst_def]
QED

Theorem extract32_payload_window:
  ptr_mem_ok cx ty (BytesV bs) src G tn s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic m))) /\
  eval_operand src s = SOME (n2w p) /\ p+32+LENGTH bs < dimword(:256) /\
  off+32 <= LENGTH bs ==>
  off < dimword(:256) /\ p+32 < dimword(:256) /\
  p+32+off < dimword(:256) /\
  (!i. p+32+off <= i /\ i < p+32+off+32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all ptr_mem_ok_dynamic_bytes_clean >>
  `p < dimword(:256)` by decide_tac >>
  simp[w2n_n2w] >> strip_tac >>
  rpt conj_tac >> rpt strip_tac >> first_assum irule >> decide_tac
QED

Theorem extract32_load_compiler_cuts:
  compile_extract32_load len data offset sa = (raw,sb) ==>
  ?sm ptr sn.
    compile_assert_slice_bounds offset (Lit 32w) len sa = ((),sm) /\
    emit_op ADD [data;offset] sm = (ptr,sn) /\
    emit_op MLOAD [ptr] sn = (raw,sb)
Proof
  simp[builtinBytesTheory.compile_extract32_load_def, comp_ignore_bind_def,
       comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem extract32_load_code_shape:
  compile_extract32_load len data offset sa = (raw,sb) ==>
  ?sm addr out.
    compile_assert_slice_bounds offset (Lit 32w) len sa = ((),sm) /\
    raw = Var out /\ ~not_fresh_at sa addr /\ ~not_fresh_at sa out /\
    emitted_insts sa sb = emitted_insts sa sm ++
      [mk_inst sm.cs_next_id ADD [data;offset] [addr];
       mk_inst (sm.cs_next_id+1) MLOAD [Var addr] [out]]
Proof
  strip_tac >> drule extract32_load_compiler_cuts >> strip_tac >>
  drule compile_assert_slice_bounds_shape >> strip_tac >>
  gvs[emitHelperTheory.emit_op_def, fresh_id_def, fresh_var_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LE_ADD]
QED

Theorem extract32_load_normal_certificate:
  compile_extract32_load len (Var data) offset sa = (raw,sb) /\
  not_fresh_at sa data /\
  (!z. offset = Var z \/ len = Var z ==> not_fresh_at sa z) /\
  scalar_available A offset /\ scalar_available A len /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  lookup_var data s = SOME a /\ eval_operand offset s = SOME b /\
  eval_operand len s = SOME l /\ w2n b + 32 <= w2n l /\
  ptr_covers G tn data s span /\ w2n b + 32 <= span /\
  w2n a + w2n b < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  (!i. w2n a + w2n b <= i /\ i < w2n a + w2n b + 32 ==> i NOTIN tn.t_mem) ==>
  ?H th t.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H th) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    op_prov H raw = NONE /\ op_taint th raw = {} /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule extract32_load_code_shape >> strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sm) s = OK u /\
    u = s with vs_vars := u.vs_vars /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s)` by
    (irule (Q.INST [`a` |-> `offset`, `n` |-> `Lit 32w`, `limit` |-> `len`]
      slice_bounds_run_normal) >> simp[eval_operand_def, dimword_def] >> metis_tac[]) >>
  `?J un. (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sm)
      (s with vs_inst_idx := k) J un) /\
    (!p. not_fresh_at sa p ==> FLOOKUP J p = FLOOKUP G p /\
      op_taint un (Var p) = op_taint tn (Var p)) /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm` by
    (irule (Q.INST [`a` |-> `offset`, `n` |-> `Lit 32w`, `limit` |-> `len`]
      slice_bounds_fixed_certificate) >> simp[] >> qexistsl_tac [`A`,`len`,`offset`] >>
     simp[scalar_available_def] >> metis_tac[scalar_available_def]) >>
  `lookup_var data u = SOME a /\ eval_operand offset u = SOME b /\
   ptr_covers J un data u span /\ op_taint un offset = {}` by
    (`op_taint tn offset = {}` by metis_tac[scalar_available_clean] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (Cases_on `offset` >> gvs[eval_operand_def, scalar_available_def] >> metis_tac[]) >>
     conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
     Cases_on `offset` >> gvs[op_taint_def]) >>
  `!i. w2n a + w2n b <= i /\ i < w2n a + w2n b + 32 ==> i NOTIN un.t_mem` by simp[] >>
  `?H th t.
    (!k. inst_seq_ptr D 0 ctx fn PG J un
      [mk_inst sm.cs_next_id ADD [Var data;offset] [addr];
       mk_inst (sm.cs_next_id+1) MLOAD [Var addr] [out]] (u with vs_inst_idx := k) H th) /\
    run_inst_seq [mk_inst sm.cs_next_id ADD [Var data;offset] [addr];
      mk_inst (sm.cs_next_id+1) MLOAD [Var addr] [out]] u = OK t /\
    t = update_var out (mload (w2n (a+b)) u) (update_var addr (a+b) u) /\
    op_prov H (Var out) = NONE /\ op_taint th (Var out) = {} /\
    th.t_mem = un.t_mem /\ th.t_stor = un.t_stor /\
    th.t_trans = un.t_trans /\ th.t_imm = un.t_imm /\
    (!p. p <> addr /\ p <> out ==> FLOOKUP H p = FLOOKUP J p /\
      op_taint th (Var p) = op_taint un (Var p))` by
    (irule extract32_payload_read_certificate >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`H`,`th`,`t`] >> simp[] >>
  conj_tac >- (irule inst_seq_ptr_uniform_append >> simp[] >>
    conj_tac >- (qexistsl_tac [`J`,`un`] >> simp[]) >>
    drule compile_assert_slice_bounds_shape >> simp[mk_inst_def, is_terminator_def]) >>
  conj_tac >- metis_tac[run_inst_seq_append] >>
  metis_tac[]
QED

Theorem extract32_load_abort_certificate:
  compile_extract32_load len data offset sa = (raw,sb) /\
  (!z. offset = Var z \/ len = Var z ==> not_fresh_at sa z) /\
  scalar_available A offset /\ scalar_available A len /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  eval_operand offset s = SOME b /\ eval_operand len s = SOME l /\
  ~(w2n b + 32 <= w2n l) /\ ~ctx_has_dalloca ctx ==>
  ?H th t.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H th) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule extract32_load_code_shape >> strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sm) s =
     Abort Revert_abort (revert_state (set_returndata [] u)) /\
    u = s with vs_vars := u.vs_vars /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s)` by
    (irule (Q.INST [`a` |-> `offset`, `n` |-> `Lit 32w`, `limit` |-> `len`]
      slice_bounds_run_abort) >> simp[eval_operand_def, dimword_def] >> metis_tac[]) >>
  `?J un. (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sm)
      (s with vs_inst_idx := k) J un) /\
    (!p. not_fresh_at sa p ==> FLOOKUP J p = FLOOKUP G p /\
      op_taint un (Var p) = op_taint tn (Var p)) /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm` by
    (irule (Q.INST [`a` |-> `offset`, `n` |-> `Lit 32w`, `limit` |-> `len`]
      slice_bounds_fixed_certificate) >> simp[] >> qexistsl_tac [`A`,`len`,`offset`] >>
     simp[scalar_available_def] >> metis_tac[scalar_available_def]) >>
  qexistsl_tac [`J`,`un`,`revert_state (set_returndata [] u)`] >> simp[] >>
  conj_tac >- (irule inst_seq_ptr_uniform_abort_append >> simp[] >>
    drule compile_assert_slice_bounds_shape >> simp[mk_inst_def, is_terminator_def]) >>
  simp[run_inst_seq_append_err]
QED

Theorem extract32_load_normal_ptr_path:
  compile_extract32_load len data offset sa = (raw,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (OK (t with vs_inst_idx := s.vs_inst_idx + 8))
Proof
  strip_tac >> drule extract32_load_code_shape >> strip_tac >>
  drule compile_assert_slice_bounds_shape >> strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))) H th
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))` by
    (irule run_inst_seq_gas_path_ptr >> gvs[mk_inst_def, is_terminator_def]) >>
  gvs[mk_inst_def]
QED

Theorem extract32_load_abort_ptr_path:
  compile_extract32_load len data offset sa = (raw,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t ==>
  ?n j. gas_path_ptr D 0 ctx fn PG G tn s n H th
    (Abort err (t with vs_inst_idx := j))
Proof
  strip_tac >> irule run_inst_seq_abort_gas_path_ptr >> simp[] >>
  qexists_tac `emitted_insts sa sb` >> simp[] >>
  drule extract32_load_code_shape >> strip_tac >>
  drule compile_assert_slice_bounds_shape >> simp[mk_inst_def, is_terminator_def]
QED
