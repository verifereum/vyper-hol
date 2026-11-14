(* Shared instruction certificates for Extract32 bounds, payload and clamp. *)
Theory extract32Certificate
Ancestors
  augAssignPtrScalarRun augAssignPtrScalarClamp augAssignPtrScalarCertificate
  augAssignPtrScalarSafety
  bodyPtrTypeBuiltinsBounds assignBasePtrBytesPrefix
  rawCallBufferPtr storageCopyBodyRaisePtr instSeqComposePtr
  immutableRegionLoadPtr decoderGhostFramePtr
  exprSimExtract32Read exprLoweringProps exprLowering emitHelper emitHelperProps
  fragGasCopyLoop instSeqPtrLo fragGasSeqPtr ghostPcTransportPtr
  builtinBytes compileEnv ptrDiscipline bodyPtrDefs loweringStateRelDefs freshWrites
  venomInst venomState venomExecSemantics instIdxIndep
  words list pred_set finite_map

Theorem scalar_code_certificate_cursor:
  !code A G tn s H tm.
  scalar_code A code /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  ~ctx_has_dalloca ctx /\ inst_seq_ptr D 0 ctx fn PG G tn code s H tm ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn code (s with vs_inst_idx := k) H tm
Proof
  Induct >- simp[inst_seq_ptr_def] >>
  rpt gen_tac >> simp[scalar_code_def] >> strip_tac >>
  `EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) h.inst_operands` by
    (gvs[EVERY_MEM] >> metis_tac[scalar_available_clean]) >>
  `~is_terminator h.inst_opcode` by metis_tac[scalar_shape_control] >>
  `!k. ptr_inst_ok D 0 0 ctx fn G tn h (s with vs_inst_idx := k)` by
    (rpt strip_tac >> irule scalar_ptr_inst_ok >> simp[]) >>
  Cases_on `step_inst_base h s` >>
  gvs[Once inst_seq_ptr_def] >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `!v. v IN A UNION set h.inst_outputs ==>
    op_prov (step_prov PG G h u) (Var v) = NONE /\
    op_taint (step_taint h s u tn) (Var v) = {}` by
    (ho_match_mp_tac scalar_step_clean >> simp[]) >>
  first_x_assum drule >> disch_then drule >> simp[] >>
  disch_then drule >> simp[]
QED

Theorem slice_bounds_fixed_certificate:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  scalar_available A a /\ scalar_available A n /\ scalar_available A limit /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  ~ctx_has_dalloca ctx ==>
  ?H th. (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H th) /\
    (!z. not_fresh_at sa z ==> FLOOKUP H z = FLOOKUP G z /\
      op_taint th (Var z) = op_taint tn (Var z)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all slice_bounds_scalar_code >> strip_tac >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`, `s`] strip_assume_tac) >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  qexistsl_tac [`H`, `tm`] >>
  conj_tac >- (irule scalar_code_certificate_cursor >> simp[] >>
    qexists_tac `A` >> simp[]) >> simp[] >>
  `!z. not_fresh_at sa z ==>
    ~MEM z (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb)))` by
    (drule compile_assert_slice_bounds_shape >> strip_tac >>
     simp[mk_inst_def] >> rpt strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LE_ADD]) >>
  metis_tac[]
QED

Theorem clamp_basetype_returns_input:
  compile_clamp_basetype raw typ sa = (result,sb) ==> result = raw
Proof
  strip_tac >> Cases_on `typ` >> gvs[compile_clamp_basetype_def, comp_return_def] >>
  Cases_on `b`
  >~ [`compile_clamp_basetype raw (BaseT (UintT n)) sa = _`] >-
    (Cases_on `n < 256` >>
     gvs[compile_clamp_basetype_def, clamp_and_return_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >> pairarg_tac >> gvs[])
  >~ [`compile_clamp_basetype raw (BaseT (IntT n)) sa = _`] >-
    (Cases_on `n < 256` >>
     gvs[compile_clamp_basetype_def, clamp_and_return_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >> pairarg_tac >> gvs[])
  >~ [`compile_clamp_basetype raw (BaseT (BytesT bt)) sa = _`] >-
    (Cases_on `bt` >> gvs[compile_clamp_basetype_def, comp_return_def] >>
     Cases_on `n < 32` >>
     gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[])) >>
  gvs[compile_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem clamp_basetype_fixed_certificate:
  compile_clamp_basetype (Var x) typ sa = (result,sb) /\
  not_fresh_at sa x /\ op_prov G (Var x) = NONE /\ op_taint tn (Var x) = {} /\
  ~ctx_has_dalloca ctx ==>
  ?H th.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H th) /\
    result = Var x /\ op_prov H result = NONE /\ op_taint th result = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  `result = Var x` by metis_tac[clamp_basetype_returns_input] >>
  `scalar_code {x} (emitted_insts sa sb)` by
    (irule scalar_clamp_basetype_code >> simp[scalar_available_def] >> metis_tac[]) >>
  `!v. v IN {x} ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}` by simp[] >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`,`s`] strip_assume_tac) >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  `!p. not_fresh_at sa p ==>
    ~MEM p (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb)))` by
    (mp_tac (Q.SPECL [`Var x`,`typ`] extract32_read_clamp_basetype) >>
     simp[extract32_straight_read_frame_def] >> disch_then drule >>
     simp[EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  qexistsl_tac [`H`,`tm`] >> simp[] >>
  conj_tac >- (irule scalar_code_certificate_cursor >> simp[] >>
    qexists_tac `{x}` >> simp[]) >>
  gvs[op_prov_def] >> metis_tac[]
QED

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

Theorem extract32_load_result_available:
  compile_extract32_load len data offset sa = (raw,sb) ==>
  ?out. raw = Var out /\ not_fresh_at sb out
Proof
  strip_tac >> drule extract32_load_compiler_cuts >> strip_tac >>
  qpat_x_assum `emit_op MLOAD _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op_local) >>
  gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_SUC_REFL]
QED

Theorem extract32_tail_code_cuts:
  compile_extract32_load len data offset sa = (raw,sm) /\
  compile_clamp_basetype raw typ sm = (result,sb) ==>
  emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb /\
  sa.cs_next_var <= sm.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   sa.cs_next_var <= sm.cs_next_var` by
    (mp_tac (Q.SPECL [`len`,`data`,`offset`] extract32_read_load) >>
     simp[extract32_straight_read_frame_def] >> disch_then drule >> simp[]) >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (mp_tac (Q.SPECL [`raw`,`typ`] extract32_read_clamp_basetype) >>
     simp[extract32_straight_read_frame_def] >> disch_then drule >> simp[]) >>
  conj_tac >- (irule emitted_insts_append >> simp[]) >> simp[] >>
  drule_all extract32_tail_straight_noext >> simp[EVERY_MEM]
QED

Theorem extract32_tail_bounds_normal_certificate:
  compile_extract32_load len (Var data) offset sa = (raw,sm) /\
  compile_clamp_basetype raw typ sm = (result,sb) /\
  not_fresh_at sa data /\
  (!z. offset = Var z \/ len = Var z ==> not_fresh_at sa z) /\
  scalar_available A offset /\ scalar_available A len /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  lookup_var data s = SOME a /\ eval_operand offset s = SOME b /\
  eval_operand len s = SOME l /\ w2n b + 32 <= w2n l /\
  ptr_covers G tn data s span /\ w2n b + 32 <= span /\
  w2n a + w2n b < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  (!i. w2n a + w2n b <= i /\ i < w2n a + w2n b + 32 ==> i NOTIN tn.t_mem) ==>
  ?H th.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H th) /\
    op_prov H result = NONE /\ op_taint th result = {} /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all extract32_tail_code_cuts >> strip_tac >>
  drule_all extract32_load_normal_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule extract32_load_result_available >> strip_tac >>
  `?J un.
    (!k. inst_seq_ptr D 0 ctx fn PG H th (emitted_insts sm sb)
      (t with vs_inst_idx := k) J un) /\
    result = Var out /\ op_prov J result = NONE /\ op_taint un result = {} /\
    (!p. not_fresh_at sm p ==> FLOOKUP J p = FLOOKUP H p /\
      op_taint un (Var p) = op_taint th (Var p)) /\
    un.t_mem = th.t_mem /\ un.t_stor = th.t_stor /\
    un.t_trans = th.t_trans /\ un.t_imm = th.t_imm` by
    (irule clamp_basetype_fixed_certificate >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`J`,`un`] >> simp[] >>
  conj_tac >- (irule inst_seq_ptr_uniform_append >> simp[] >>
    conj_tac >- (qexistsl_tac [`H`,`th`] >> simp[]) >>
    gvs[EVERY_CONJ, EVERY_APPEND]) >>
  metis_tac[not_fresh_at_mono]
QED

Theorem extract32_tail_bounds_abort_certificate:
  compile_extract32_load len data offset sa = (raw,sm) /\
  compile_clamp_basetype raw typ sm = (result,sb) /\
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
  strip_tac >> drule_all extract32_tail_code_cuts >> strip_tac >>
  drule_all extract32_load_abort_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`,`t`] >> simp[run_inst_seq_append_err] >>
  irule inst_seq_ptr_uniform_abort_append >> simp[] >> gvs[EVERY_APPEND, EVERY_CONJ]
QED

Theorem extract32_tail_ready_certificate:
  compile_extract32_load (Var len) (Var data) offset sa = (raw,sm) /\
  compile_clamp_basetype raw typ sm = (result,sb) /\
  not_fresh_at sa len /\ not_fresh_at sa data /\
  (!z. offset = Var z ==> not_fresh_at sa z) /\ (!l. offset <> Label l) /\
  op_prov G offset = NONE /\ op_taint tn offset = {} /\
  op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
  ptr_mem_ok cx ty (BytesV bs) src G tn s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic m))) /\
  eval_operand src s = SOME (n2w p) /\
  eval_operand (Var data) s = SOME (n2w (p+32)) /\
  eval_operand (Var len) s = SOME (n2w (LENGTH bs)) /\
  eval_operand offset s = SOME (n2w n) /\
  n < dimword(:256) /\ p+32+LENGTH bs < dimword(:256) /\
  (!span. 0 < LENGTH bs /\ span <= LENGTH bs ==> ptr_covers G tn data s span) /\
  ~ctx_has_dalloca ctx ==>
  ?HG th.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) HG th) /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      op_prov HG result = NONE /\ op_taint th result = {}) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP HG x = FLOOKUP G x /\
      op_taint th (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `A = {x | op_prov G (Var x) = NONE /\ op_taint tn (Var x) = {}}` >>
  `scalar_available A offset /\ scalar_available A (Var len)` by
    (Cases_on `offset` >> gvs[scalar_available_def, Abbr `A`]) >>
  `!x. x IN A ==> op_prov G (Var x) = NONE /\ op_taint tn (Var x) = {}` by
    simp[Abbr `A`] >>
  `LENGTH bs < dimword(:256) /\ p+32 < dimword(:256)` by decide_tac >>
  `!z. offset = Var z \/ Var len = Var z ==> not_fresh_at sa z` by
    (simp[] >> metis_tac[]) >>
  Cases_on `n+32 <= LENGTH bs`
  >- suspend "inbounds" >>
  `~(w2n (n2w n:bytes32)+32 <= w2n (n2w (LENGTH bs):bytes32))` by
    simp[w2n_n2w, arithmeticTheory.LESS_MOD] >>
  drule_all extract32_tail_bounds_abort_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `HG` (qx_choose_then `th`
      (qx_choose_then `t` strip_assume_tac)))) >>
  qexistsl_tac [`HG`,`th`] >> simp[]
QED

Resume extract32_tail_ready_certificate[inbounds]:
  `n < dimword(:256) /\ p+32 < dimword(:256) /\
   p+32+n < dimword(:256) /\
   (!i. p+32+n <= i /\ i < p+32+n+32 ==> i NOTIN tn.t_mem)` by
    (irule extract32_payload_window >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `ptr_covers G tn data s (LENGTH bs)` by
    (first_assum irule >> simp[] >> decide_tac) >>
  `lookup_var data s = SOME (n2w (p+32))` by gvs[eval_operand_def] >>
  `w2n (n2w n:bytes32)+32 <= w2n (n2w (LENGTH bs):bytes32) /\
   w2n (n2w n:bytes32)+32 <= LENGTH bs /\
   w2n (n2w (p+32):bytes32)+w2n (n2w n:bytes32) < dimword(:256) /\
   (!i. w2n (n2w (p+32):bytes32)+w2n (n2w n:bytes32) <= i /\
     i < w2n (n2w (p+32):bytes32)+w2n (n2w n:bytes32)+32 ==> i NOTIN tn.t_mem)` by
    simp[w2n_n2w, arithmeticTheory.LESS_MOD] >>
  drule_all extract32_tail_bounds_normal_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `HG` (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl_tac [`HG`,`th`] >> simp[]
QED

Finalise extract32_tail_ready_certificate
