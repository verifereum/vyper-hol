(* Pointer boundary for the finite ABI encode setup. *)
Theory abiEncodePtrSetup
Ancestors
  exprSimAbiEncodeConcreteBuiltinWrappers exprSimPtrLiteralOps allocationPtr
  fragGasSeqPtr abiBuiltinAllocation abiBuiltinEncodeCode ptrDiscipline
  abiEncoderWindow bodyPtrDefs emitHelper emitHelperProps compileEnv context
  exprLoweringProps venomExecSemantics venomInstProofs venomInst venomState finite_map words
  list rich_list arithmetic revertReasonPrefixFramePtr loweringStateRelDefs
  abiEncodePtrInputTransport abiEncodeWindowBuiltin bodyPtrBopEntry
  exprSimAbiEncodeFramedBuiltin abiBuiltinEncodeCorrect abiBuiltinEncodeSetup
  abiDecoderReentry abiEncoderExtendSim

Theorem setup_add_continuation[local]:
  IS_SOME (lookup_var src s) /\ IS_SOME (FLOOKUP G src) /\
  op_taint tn (Var src) = {} /\ ~ctx_has_dalloca ctx ==>
  (inst_seq_ptr D 0 ctx func PG G tn
     (mk_inst id ADD [Var src; Lit off] [dst] :: code) s H tf <=>
   inst_seq_ptr D 0 ctx func PG (G |+ (dst,THE (FLOOKUP G src)))
     (tn with t_var := tn.t_var |+ (dst,{})) code
     ((update_var dst (THE (lookup_var src s)+off) s)
       with vs_inst_idx := SUC s.vs_inst_idx) H tf)
Proof
  Cases_on `lookup_var src s` >> simp[] >>
  Cases_on `FLOOKUP G src` >> simp[] >> strip_tac >>
  `step_inst_base (mk_inst id ADD [Var src; Lit off] [dst]) s =
    OK (update_var dst (x+off) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  drule literal_add_ghost >> disch_then assume_tac >>
  simp[inst_seq_ptr_def, literal_add_ptr_inst_ok]
QED

Theorem setup_mstore_continuation[local]:
  IS_SOME (lookup_var dst s) /\ ptr_covers G tn dst s 32 /\
  ~ctx_has_dalloca ctx ==>
  (inst_seq_ptr D 0 ctx func PG G tn
     (mk_inst id MSTORE [Var dst; Lit w] [] :: code) s H tf <=>
   inst_seq_ptr D 0 ctx func PG G
     (tn with t_mem := tn.t_mem DIFF
       {i | w2n (THE (lookup_var dst s)) <= i /\
            i < w2n (THE (lookup_var dst s)) + 32}) code
     ((mstore (w2n (THE (lookup_var dst s))) w s)
       with vs_inst_idx := SUC s.vs_inst_idx) H tf)
Proof
  Cases_on `lookup_var dst s` >> simp[] >> strip_tac >>
  `step_inst_base (mk_inst id MSTORE [Var dst; Lit w] []) s =
    OK (mstore (w2n x) w s)` by
    (irule step_MSTORE >> simp[eval_operand_def]) >>
  drule literal_mstore_ghost >> disch_then assume_tac >>
  simp[inst_seq_ptr_def, literal_mstore_ptr_inst_ok]
QED

Theorem setup_method_suffix[local]:
  lookup_var a s = SOME (n2w p) /\ FLOOKUP G a = SOME (p,sz) /\
  op_taint tn (Var a) = {} /\ a <> b /\ a <> c /\ b <> c /\
  p+sz < dimword (:256) /\ 64 <= sz /\ 36+n <= sz /\
  ~ctx_has_dalloca ctx /\ tm = tn.t_mem /\
  run_inst_seq [mk_inst i ADD [Var a; Lit 36w] [b];
    mk_inst j ADD [Var a; Lit 32w] [c];
    mk_inst k MSTORE [Var c; Lit w] []] s = OK raw ==>
  ?H tf.
    inst_seq_ptr D 0 ctx func PG G tn
      [mk_inst i ADD [Var a; Lit 36w] [b];
       mk_inst j ADD [Var a; Lit 32w] [c];
       mk_inst k MSTORE [Var c; Lit w] []] (s with vs_inst_idx := idx) H tf /\
    ptr_covers H tf a raw sz /\ op_taint tf (Var b) = {} /\
    ptr_covers H tf b raw n /\
    tf.t_mem = tm DIFF {i | p+32 <= i /\ i < p+64}
Proof
  strip_tac >>
  `step_inst_base (mk_inst i ADD [Var a; Lit 36w] [b]) s =
    OK (update_var b (n2w p + 36w) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst j ADD [Var a; Lit 32w] [c])
      (update_var b (n2w p + 36w) s) =
    OK (update_var c (n2w p + 32w) (update_var b (n2w p + 36w) s))` by
    (irule step_ADD >> fs[eval_operand_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst k MSTORE [Var c; Lit w] [])
      (update_var c (n2w p + 32w) (update_var b (n2w p + 36w) s)) =
    OK (mstore (w2n (n2w p + 32w : 256 word)) w
      (update_var c (n2w p + 32w) (update_var b (n2w p + 36w) s)))` by
    (irule step_MSTORE >> simp[eval_operand_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE]) >>
  gvs[run_inst_seq_def] >> fs[lookup_var_def, op_taint_def] >>
  simp[setup_add_continuation, lookup_var_def, op_taint_def] >>
  simp[setup_add_continuation, lookup_var_def, update_var_def,
    op_taint_def, FLOOKUP_UPDATE] >>
  `p < dimword (:256) /\ p+32 < dimword (:256) /\
    p+36 < dimword (:256)` by decide_tac >>
  simp[setup_mstore_continuation, ptr_covers_def, lookup_var_def,
    update_var_def, op_taint_def, FLOOKUP_UPDATE, word_add_n2w, w2n_n2w] >>
  simp[inst_seq_ptr_def] >>
  simp[FLOOKUP_UPDATE] >> decide_tac
QED

Theorem abi_encode_setup_ptr_sequence_mem:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  run_inst_seq (emitted_insts st ready) initial = OK raw /\
  outsz = 32 + 32 * word_size
    (maxlen + (case method_id of NONE => 0 | SOME mid => 4)) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p+outsz < dimword (:256) /\
  n <= maxlen /\ ~ctx_has_dalloca ctx ==>
  ?H tf x.
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st ready) initial H tf /\
    FST ops = Var x /\ ptr_covers H tf x raw outsz /\
    op_taint tf (SND ops) = {} /\
    (0 < n ==> ?y. SND ops = Var y /\ ptr_covers H tf y raw n) /\
    tf.t_mem =
      (if FLOOKUP initial.vs_allocas st.cs_next_id = NONE then
         tn.t_mem UNION {i | p <= i /\ i < p+outsz}
       else tn.t_mem) DIFF
      (case method_id of NONE => {} | SOME mid => {i | p+32 <= i /\ i < p+64})
Proof
  Cases_on `method_id` >>
  simp[abi_builtin_encode_setup_def, abi_builtin_encode_method_id_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[] >>
  fs[emitted_insts_def] >>
  RULE_ASSUM_TAC (REWRITE_RULE [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  fs[DROP_LENGTH_APPEND]
  >- suspend "none_fresh"
  >- suspend "none_reused"
  >- suspend "some_fresh"
  >> suspend "some_reused"
QED

Resume abi_encode_setup_ptr_sequence_mem[none_fresh]:
  qmatch_asmsub_abbrev_tac `Lit (n2w sz)` >>
  qmatch_goalsub_abbrev_tac `mk_inst _ ALLOCA [Lit (n2w sz)] [x]` >>
  qmatch_goalsub_abbrev_tac `mk_inst _ ADD [Var x; Lit 32w] [y]` >>
  `x <> y` by simp[Abbr `x`, Abbr `y`] >>
  `sz < dimword (:256)` by decide_tac >>
  qabbrev_tac `u = update_var x (n2w initial.vs_alloca_next)
    (initial with <|vs_allocas := initial.vs_allocas |+
      (st.cs_next_id,(initial.vs_alloca_next,sz));
      vs_alloca_next := initial.vs_alloca_next + sz|>)` >>
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [x]) initial = OK u` by
    simp[Abbr `u`, Once step_inst_base_def, exec_alloca_def, mk_inst_def,
      eval_operand_def, w2n_n2w] >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  `step_inst_base (mk_inst (st.cs_next_id+1) ADD [Var x; Lit 32w] [y]) u =
    OK (update_var y (n2w initial.vs_alloca_next + 32w) u)` by
    (irule step_ADD >> simp[Abbr `u`, eval_operand_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE]) >>
  gvs[run_inst_seq_def] >>
  simp[Once inst_seq_ptr_def, literal_alloca_ptr_inst_ok] >>
  simp[setup_add_continuation, op_taint_def, lookup_var_def,
    update_var_def, Abbr `u`, FLOOKUP_UPDATE] >>
  simp[inst_seq_ptr_def] >>
  simp[ptr_covers_def, op_taint_def, lookup_var_def, update_var_def,
    FLOOKUP_UPDATE, w2n_n2w] >>
  qspec_then `maxlen` assume_tac abi_builtin_word_size_capacity >>
  `initial.vs_alloca_next + 32 < dimword (:256)` by
    (fs[Abbr `sz`] >> decide_tac) >>
  simp[word_add_n2w, w2n_n2w] >> fs[Abbr `sz`] >> decide_tac
QED

Resume abi_encode_setup_ptr_sequence_mem[none_reused]:
  qmatch_asmsub_abbrev_tac `Lit (n2w sz)` >>
  qmatch_goalsub_abbrev_tac `mk_inst _ ALLOCA [Lit (n2w sz)] [x]` >>
  qmatch_goalsub_abbrev_tac `mk_inst _ ADD [Var x; Lit 32w] [y]` >>
  `x <> y` by simp[Abbr `x`, Abbr `y`] >>
  qabbrev_tac `u = update_var x (n2w p) initial` >>
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [x]) initial = OK u` by
    (simp[Abbr `u`] >> irule reused_alloca_step >> simp[]) >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`x`, `PG`, `G`, `tn`] strip_assume_tac) >>
  `step_inst_base (mk_inst (st.cs_next_id+1) ADD [Var x; Lit 32w] [y]) u =
    OK (update_var y (n2w p + 32w) u)` by
    (irule step_ADD >> simp[Abbr `u`, eval_operand_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE]) >>
  gvs[run_inst_seq_def, GSYM markerTheory.Abbrev_def] >>
  simp[Once inst_seq_ptr_def, literal_alloca_ptr_inst_ok] >>
  `lookup_var x (u with vs_inst_idx := SUC initial.vs_inst_idx) = SOME (n2w p)` by
    simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `FLOOKUP (G |+ (x,(p,sz))) x = SOME (p,sz)` by simp[FLOOKUP_UPDATE] >>
  `op_taint (tn with t_var := tn.t_var |+ (x,{})) (Var x) = {}` by
    simp[op_taint_def, FLOOKUP_UPDATE] >>
  simp[setup_add_continuation, FLOOKUP_UPDATE] >>
  simp[inst_seq_ptr_def] >>
  `p < dimword (:256)` by decide_tac >>
  `p + 32 < dimword (:256)` by (fs[Abbr `sz`] >> decide_tac) >>
  simp[ptr_covers_def, op_taint_def, lookup_var_def, update_var_def,
    FLOOKUP_UPDATE, Abbr `u`, word_add_n2w, w2n_n2w] >>
  qspec_then `maxlen` assume_tac abi_builtin_word_size_capacity >>
  fs[Abbr `sz`] >> decide_tac
QED

Resume abi_encode_setup_ptr_sequence_mem[some_fresh]:
  qmatch_asmsub_abbrev_tac `Lit (n2w sz)` >>
  qmatch_goalsub_abbrev_tac `mk_inst _ ALLOCA [Lit (n2w sz)] [a]` >>
  qmatch_goalsub_abbrev_tac `mk_inst _ ADD [Var a; Lit 36w] [b]` >>
  qmatch_goalsub_abbrev_tac `mk_inst _ ADD [Var a; Lit 32w] [c]` >>
  `a <> b /\ a <> c /\ b <> c` by simp[Abbr `a`, Abbr `b`, Abbr `c`] >>
  `sz < dimword (:256)` by decide_tac >>
  qabbrev_tac `u = update_var a (n2w initial.vs_alloca_next)
    (initial with <|vs_allocas := initial.vs_allocas |+
      (st.cs_next_id,(initial.vs_alloca_next,sz));
      vs_alloca_next := initial.vs_alloca_next + sz|>)` >>
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [a]) initial = OK u` by
    simp[Abbr `u`, Once step_inst_base_def, exec_alloca_def, mk_inst_def,
      eval_operand_def, w2n_n2w] >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  fs[run_inst_seq_def] >>
  simp[Once inst_seq_ptr_def, literal_alloca_ptr_inst_ok] >>
  `?H tf. inst_seq_ptr D 0 ctx func PG
      (G |+ (a,(initial.vs_alloca_next,sz)))
      (tn with <|t_mem := tn.t_mem UNION
        {i | initial.vs_alloca_next <= i /\ i < initial.vs_alloca_next+sz};
        t_var := tn.t_var |+ (a,{})|>)
      [mk_inst (st.cs_next_id+1) ADD [Var a; Lit 36w] [b];
       mk_inst (st.cs_next_id+2) ADD [Var a; Lit 32w] [c];
       mk_inst (st.cs_next_id+3) MSTORE [Var c; Lit (x << 224)] []]
      (u with vs_inst_idx := SUC initial.vs_inst_idx) H tf /\
      ptr_covers H tf a raw sz /\ op_taint tf (Var b) = {} /\
      ptr_covers H tf b raw n /\
      tf.t_mem = (tn.t_mem UNION
        {i | initial.vs_alloca_next <= i /\ i < initial.vs_alloca_next+sz}) DIFF
        {i | initial.vs_alloca_next+32 <= i /\ i < initial.vs_alloca_next+64}`
      suffices_by (simp[ADD_COMM] >> metis_tac[]) >>
  irule setup_method_suffix >>
  simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE, op_taint_def] >>
  conj_tac >- (fs[Abbr `sz`] >>
    qspec_then `maxlen+4` assume_tac abi_builtin_word_size_capacity >>
    Cases_on `word_size (maxlen+4)` >> fs[]) >>
  conj_tac >- (fs[Abbr `sz`] >>
    qspec_then `maxlen+4` assume_tac abi_builtin_word_size_capacity >> decide_tac) >>
  fs[run_inst_seq_def, update_var_def]
QED

Resume abi_encode_setup_ptr_sequence_mem[some_reused]:
  qmatch_asmsub_abbrev_tac `Lit (n2w sz)` >>
  qmatch_goalsub_abbrev_tac `mk_inst _ ALLOCA [Lit (n2w sz)] [a]` >>
  qmatch_goalsub_abbrev_tac `mk_inst _ ADD [Var a; Lit 36w] [b]` >>
  qmatch_goalsub_abbrev_tac `mk_inst _ ADD [Var a; Lit 32w] [c]` >>
  `a <> b /\ a <> c /\ b <> c` by simp[Abbr `a`, Abbr `b`, Abbr `c`] >>
  qabbrev_tac `u = update_var a (n2w p) initial` >>
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [a]) initial = OK u` by
    (simp[Abbr `u`] >> irule reused_alloca_step >> simp[]) >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`a`, `PG`, `G`, `tn`] strip_assume_tac) >>
  fs[run_inst_seq_def] >>
  simp[Once inst_seq_ptr_def, literal_alloca_ptr_inst_ok] >>
  `?H tf. inst_seq_ptr D 0 ctx func PG (G |+ (a,(p,sz)))
      (tn with t_var := tn.t_var |+ (a,{}))
      [mk_inst (st.cs_next_id+1) ADD [Var a; Lit 36w] [b];
       mk_inst (st.cs_next_id+2) ADD [Var a; Lit 32w] [c];
       mk_inst (st.cs_next_id+3) MSTORE [Var c; Lit (x << 224)] []]
      (u with vs_inst_idx := SUC initial.vs_inst_idx) H tf /\
      ptr_covers H tf a raw sz /\ op_taint tf (Var b) = {} /\
      ptr_covers H tf b raw n /\
      tf.t_mem = tn.t_mem DIFF {i | p+32 <= i /\ i < p+64}`
      suffices_by metis_tac[] >>
  irule setup_method_suffix >>
  simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE, op_taint_def] >>
  conj_tac >- (fs[Abbr `sz`] >>
    qspec_then `maxlen+4` assume_tac abi_builtin_word_size_capacity >>
    Cases_on `word_size (maxlen+4)` >> fs[]) >>
  conj_tac >- (fs[Abbr `sz`] >>
    qspec_then `maxlen+4` assume_tac abi_builtin_word_size_capacity >> decide_tac) >>
  fs[run_inst_seq_def, update_var_def]
QED
Finalise abi_encode_setup_ptr_sequence_mem

(* Original sequence interface, projected from the memory-effect certificate. *)
Theorem abi_encode_setup_ptr_sequence:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  run_inst_seq (emitted_insts st ready) initial = OK raw /\
  outsz = 32 + 32 * word_size
    (maxlen + (case method_id of NONE => 0 | SOME mid => 4)) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p+outsz < dimword (:256) /\
  n <= maxlen /\ ~ctx_has_dalloca ctx ==>
  ?H tf x.
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st ready) initial H tf /\
    FST ops = Var x /\ ptr_covers H tf x raw outsz /\
    op_taint tf (SND ops) = {} /\
    (0 < n ==> ?y. SND ops = Var y /\ ptr_covers H tf y raw n)
Proof
  metis_tac[abi_encode_setup_ptr_sequence_mem]
QED

Theorem abi_encode_setup_ptr_ghost_frame:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st ready) initial H tf ==>
  (!x. not_fresh_at st x ==>
    FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
Proof
  strip_tac >> conj_tac
  >- (gen_tac >> disch_tac >> irule inst_seq_ptr_other_output_frame >>
      goal_assum (drule_at Any) >>
      Cases_on `method_id` >>
      gvs[abi_builtin_encode_setup_def, abi_builtin_encode_method_id_def,
        compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
        fresh_id_def, emit_def] >>
      simp[emitted_insts_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[DROP_LENGTH_APPEND, mk_inst_def] >>
      fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]) >>
  irule inst_seq_ptr_nonmemory_taint_frame >>
  goal_assum (drule_at Any) >>
  Cases_on `method_id` >>
  gvs[abi_builtin_encode_setup_def, abi_builtin_encode_method_id_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  simp[emitted_insts_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encode_setup_ptr_entry_semantic:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  fn_has_code st ready func /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!mem. mem_agree_outside tn.t_mem initial.vs_memory mem ==>
     abi_encoder_window_input ei at av sb cap mem) /\
  eval_operand src initial = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var src /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  d+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  (sb+cap <= p+32 \/ p+32+w <= sb) /\
  LENGTH (enc at av) <= maxlen /\ ~ctx_has_dalloca ctx /\
  op_taint tn src = {} /\
  (0 < cap ==> ?x. src = Var x /\ ptr_covers G tn x initial cap) /\
  (0 < cap ==> sb+cap <= initial.vs_alloca_next) ==>
  ?prepared H tf x.
    eval_operand (FST ops) prepared = SOME (n2w p) /\
    eval_operand (SND ops) prepared = SOME (n2w d) /\
    eval_operand src prepared = SOME (n2w sb) /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 prepared.vs_memory = abi_builtin_encode_method_bytes mid) /\
    gas_path_ptr D 0 ctx func PG G tn initial 0 H tf (OK prepared) /\
    FST ops = Var x /\ ptr_covers H tf x prepared outsz /\
    op_taint tf src = {} /\ op_taint tf (SND ops) = {} /\
    (0 < cap ==> ?y. src = Var y /\ ptr_covers H tf y prepared cap) /\
    (0 < LENGTH (enc at av) ==> ?y. SND ops = Var y /\
      ptr_covers H tf y prepared (LENGTH (enc at av))) /\
    (!mem. mem_agree_outside tf.t_mem prepared.vs_memory mem ==>
      abi_encoder_window_input ei at av sb cap mem) /\
    alloca_inv prepared /\ alloca_room ctx func prepared /\
    sb+cap <= prepared.vs_alloca_next /\
    d+LENGTH (enc at av) <= prepared.vs_alloca_next /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\
    prepared.vs_labels = initial.vs_labels /\
    prepared.vs_accounts = initial.vs_accounts /\ prepared.vs_transient = initial.vs_transient /\
    prepared.vs_logs = initial.vs_logs /\ prepared.vs_requests = initial.vs_requests /\
    prepared.vs_pending_deletions = initial.vs_pending_deletions /\
    abi_decode_sim ctx func initial prepared /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint tf (Var y) = op_taint tn (Var y)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem =
      (if FLOOKUP initial.vs_allocas st.cs_next_id = NONE then
         tn.t_mem UNION {i | p <= i /\ i < p+outsz}
       else tn.t_mem) DIFF
      (case method_id of NONE => {} | SOME mid => {i | p+32 <= i /\ i < p+64}) /\
    abi_encode_exec_frame func initial prepared /\
    abi_encoder_extend_sim ctx func initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas
     st.cs_next_id = SOME (p,outsz)` by
    (irule abi_builtin_allocate_state_row >> simp[]) >>
  `p+outsz < dimword (:256)` by
    (drule alloca_room_next_lt >> strip_tac >>
     qpat_x_assum `alloca_inv _` (mp_tac o REWRITE_RULE
       [venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def]) >>
     disch_then (strip_assume_tac) >>
     qpat_x_assum `!aid base sz. _` (qspecl_then [`st.cs_next_id`, `p`, `outsz`] mp_tac) >>
     simp[] >> strip_tac >> gvs[] >> decide_tac) >>
  `abi_encoder_window_input ei at av sb cap initial.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all abi_encode_window_setup_concrete >>
  disch_then (qspec_then `ctx` mp_tac) >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `?H tf x.
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st ready) initial H tf /\
    FST ops = Var x /\ ptr_covers H tf x raw outsz /\
    op_taint tf (SND ops) = {} /\
    (0 < LENGTH (enc at av) ==> ?y. SND ops = Var y /\
      ptr_covers H tf y raw (LENGTH (enc at av))) /\
    tf.t_mem =
      (if FLOOKUP initial.vs_allocas st.cs_next_id = NONE then
        tn.t_mem UNION {i | p <= i /\ i < p+outsz} else tn.t_mem) DIFF
      (case method_id of NONE => {} | SOME mid => {i | p+32 <= i /\ i < p+64})` by
    (irule abi_encode_setup_ptr_sequence_mem >> metis_tac[]) >>
  drule_all abi_encode_setup_ptr_ghost_frame >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;MSTORE]) (emitted_insts st ready)` by
    (qpat_x_assum `abi_builtin_encode_setup _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `method_id` >>
     simp[abi_builtin_encode_setup_def, abi_builtin_encode_method_id_def,
       compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def]) >>
  `abi_encode_exec_frame func initial raw` by
    (drule_all abi_encode_setup_sequence_frame >> simp[]) >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  `abi_encoder_extend_sim ctx func initial
     (raw with vs_inst_idx := LENGTH ready.cs_current_insts)` by
    (irule abi_encoder_run_sequence_extend_sim >> metis_tac[]) >>
  qabbrev_tac `prepared = raw with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  `eval_operand src prepared = SOME (n2w sb)` by
    metis_tac[abi_builtin_encode_setup_frame_def] >>
  `(!y. src = Var y ==> not_fresh_at st y)` by
    (rpt strip_tac >> fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      not_fresh_at_def]) >>
  qexistsl [`prepared`, `H`, `tf`, `x`] >>
  simp[ptr_covers_def, lookup_var_def, Abbr `prepared`] >>
  rpt conj_tac
  >- suspend "entry_path"
  >- suspend "entry_source_taint"
  >- suspend "entry_source_cover"
  >- suspend "entry_dest_cover"
  >- suspend "entry_robust"
  >- suspend "entry_alloca_inv"
  >- suspend "entry_alloca_room"
  >> (drule abi_window_setup_frontier >> strip_tac >> gvs[])
QED

Resume abi_encode_setup_ptr_entry_semantic[entry_path]:
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  `?bb. lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st ready) (DROP initial.vs_inst_idx bb.bb_instructions)` by
    (irule bop_suffix_placement >> qexistsl [`st`, `ready`] >>
     simp[same_blocks_def, inst_extends_def] >> metis_tac[inst_extends_def]) >>
  `initial.vs_inst_idx + LENGTH (emitted_insts st ready) = LENGTH ready.cs_current_insts` by
    (fs[inst_extends_def] >> simp[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts st ready) = []` by
    (qpat_x_assum `abi_builtin_encode_setup _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `method_id` >>
     simp[abi_builtin_encode_setup_def, abi_builtin_encode_method_id_def,
       compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Resume abi_encode_setup_ptr_entry_semantic[entry_source_taint]:
  Cases_on `src` >> fs[op_taint_def] >> metis_tac[op_taint_def]
QED

Resume abi_encode_setup_ptr_entry_semantic[entry_source_cover]:
  rpt strip_tac >>
  qpat_x_assum `0 < cap ==> ?y. _` drule >> strip_tac >>
  gvs[ptr_covers_def, lookup_var_def, eval_operand_def] >> metis_tac[]
QED

Resume abi_encode_setup_ptr_entry_semantic[entry_dest_cover]:
  rpt strip_tac >>
  qpat_x_assum `0 < LENGTH (enc at av) ==> _` drule >> strip_tac >>
  fs[ptr_covers_def, lookup_var_def] >> metis_tac[]
QED

Resume abi_encode_setup_ptr_entry_semantic[entry_robust]:
  match_mp_tac (Q.INST [`old_t` |-> `tn.t_mem`,
    `old_mem` |-> `initial.vs_memory`] abi_encode_robust_window_transport) >>
  conj_tac >- metis_tac[] >>
  gen_tac >> disch_then strip_assume_tac >> conj_tac
  >- (Cases_on `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` >>
      fs[] >> simp[] >>
      `0 < cap` by decide_tac >>
      `sb+cap <= p` by decide_tac >>
      Cases_on `method_id` >> fs[] >> simp[] >> decide_tac) >>
  qpat_x_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` mp_tac >>
  simp[abi_builtin_encode_setup_frame_def, abiDecoderContractTheory.abi_decode_frame_def] >>
  strip_tac >> first_x_assum irule >> decide_tac
QED

Resume abi_encode_setup_ptr_entry_semantic[entry_alloca_inv]:
  drule abi_window_setup_alloca_inv >> simp[]
QED

Resume abi_encode_setup_ptr_entry_semantic[entry_alloca_room]:
  drule abi_window_setup_room >> strip_tac >> gvs[]
QED

Finalise abi_encode_setup_ptr_entry_semantic

(* Compatibility projection: the execution is shared with the enriched entry. *)
Theorem abi_encode_setup_ptr_entry:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  fn_has_code st ready func /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!mem. mem_agree_outside tn.t_mem initial.vs_memory mem ==>
     abi_encoder_window_input ei at av sb cap mem) /\
  eval_operand src initial = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var src /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  d+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  (sb+cap <= p+32 \/ p+32+w <= sb) /\
  LENGTH (enc at av) <= maxlen /\ ~ctx_has_dalloca ctx /\
  op_taint tn src = {} /\
  (0 < cap ==> ?x. src = Var x /\ ptr_covers G tn x initial cap) /\
  (0 < cap ==> sb+cap <= initial.vs_alloca_next) ==>
  ?prepared H tf x.
    eval_operand (FST ops) prepared = SOME (n2w p) /\
    eval_operand (SND ops) prepared = SOME (n2w d) /\
    eval_operand src prepared = SOME (n2w sb) /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 prepared.vs_memory = abi_builtin_encode_method_bytes mid) /\
    gas_path_ptr D 0 ctx func PG G tn initial 0 H tf (OK prepared) /\
    FST ops = Var x /\ ptr_covers H tf x prepared outsz /\
    op_taint tf src = {} /\ op_taint tf (SND ops) = {} /\
    (0 < cap ==> ?y. src = Var y /\ ptr_covers H tf y prepared cap) /\
    (0 < LENGTH (enc at av) ==> ?y. SND ops = Var y /\
      ptr_covers H tf y prepared (LENGTH (enc at av))) /\
    (!mem. mem_agree_outside tf.t_mem prepared.vs_memory mem ==>
      abi_encoder_window_input ei at av sb cap mem) /\
    alloca_inv prepared /\ alloca_room ctx func prepared /\
    sb+cap <= prepared.vs_alloca_next /\
    d+LENGTH (enc at av) <= prepared.vs_alloca_next /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\
    prepared.vs_labels = initial.vs_labels /\
    prepared.vs_accounts = initial.vs_accounts /\ prepared.vs_transient = initial.vs_transient /\
    prepared.vs_logs = initial.vs_logs /\ prepared.vs_requests = initial.vs_requests /\
    prepared.vs_pending_deletions = initial.vs_pending_deletions /\
    abi_decode_sim ctx func initial prepared /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint tf (Var y) = op_taint tn (Var y)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem =
      (if FLOOKUP initial.vs_allocas st.cs_next_id = NONE then
         tn.t_mem UNION {i | p <= i /\ i < p+outsz}
       else tn.t_mem) DIFF
      (case method_id of NONE => {} | SOME mid => {i | p+32 <= i /\ i < p+64})
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_setup_ptr_entry_semantic >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`prepared`, `H`, `tf`, `x`] >> simp[]
QED
