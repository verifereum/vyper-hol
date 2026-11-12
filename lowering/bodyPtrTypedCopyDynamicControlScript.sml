(* Scalar-bound counted control for runtime-length typed array copies. *)
Theory bodyPtrTypedCopyDynamicControl
Ancestors bodyPtrTypedCopyArrayControl typedCopyLoopHeaderPtr
  fragGasPathPtr exprSimPtrProps venomExecSemantics venomInst venomState words finite_map arithmetic
  bodyPtrBopScalarSeq fragExec exprLoweringProps ptrDiscipline list pred_set
  augAssignPtrFieldLoad typedCopyPtr bodyPtrDefs bodyPtrSignedConvertLoad
  forPtrScalarStore

Theorem typed_copy_scalar_lt_counted:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id LT [Var ctr;b] [out]) /\
  lookup_var ctr s = SOME (n2w i) /\ eval_operand b s = SOME (n2w n) /\
  op_taint tn (Var ctr) = {} /\ op_taint tn b = {} /\
  FLOOKUP G ctr = NONE /\ (!v. b = Var v ==> FLOOKUP G v = NONE) /\
  i < dimword(:256) /\ n < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out (bool_to_word (i < n)) s)
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  qabbrev_tac `u = update_var out (bool_to_word (i < n)) s` >>
  `step_inst_base (mk_inst id LT [Var ctr;b] [out]) s = OK u` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
      eval_operand_def, w2n_n2w, LESS_MOD, Abbr `u`] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id LT [Var ctr;b] [out]) s` by
    (simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
       ptrDisciplineTheory.taint_ok_def, ptrDisciplineTheory.allocas_from_def,
       mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, Abbr `u`, update_var_def] >>
     Cases_on `b` >> gvs[FLOOKUP_DEF] >> metis_tac[]) >>
  `(mk_inst id LT [Var ctr;b] [out]).inst_opcode <> INVOKE /\
   (mk_inst id LT [Var ctr;b] [out]).inst_opcode <> GAS /\
   ~is_terminator (mk_inst id LT [Var ctr;b] [out]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  `~u.vs_halted` by simp[Abbr `u`, update_var_def] >>
  drule_all gas_path_ptr_one_step >>
  disch_then (qspec_then `PG` mp_tac) >>
  `step_prov PG G (mk_inst id LT [Var ctr;b] [out]) u =
      DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id LT [Var ctr;b] [out]) s u tn =
      (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule typed_copy_loop_arith_ghost_clean >> simp[Abbr `u`, update_var_def]) >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem typed_copy_operand_test_counted:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id LT [Var ctr;b] [lt];
     mk_inst (id+1) ISZERO [Var lt] [done];
     mk_inst (id+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
  eval_operand b s = SOME (n2w n) /\ op_taint tn b = {} /\
  FLOOKUP G ctr = NONE /\ (!v. b = Var v ==> FLOOKUP G v = NONE) /\
  i <= n /\ n < dimword(:256) /\ ctr <> lt /\ ctr <> done /\
  (!v. b = Var v ==> v <> lt /\ v <> done) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done}))
    (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{}))
    (OK (jump_to (if i < n then body_lbl else exit)
      (update_var done (bool_to_word (~(i < n)))
        (update_var lt (bool_to_word (i < n)) s))))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `jump_to dest (update_var done w2 (update_var lt w1 s))` >>
  qabbrev_tac `s1 = (update_var lt w1 s) with vs_inst_idx := 1` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {lt})` >>
  qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (lt,{})` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` by
    (`get_instruction bb s.vs_inst_idx = SOME (mk_inst id LT [Var ctr;b] [lt])` by
       simp[get_instruction_def] >>
     `i < dimword(:256)` by decide_tac >>
     drule_all typed_copy_scalar_lt_counted >>
     disch_then (qspec_then `PG` mp_tac) >>
     simp[Abbr `s1`, Abbr `g1`, Abbr `t1`, Abbr `w1`]) >>
  qabbrev_tac `s2 = (update_var done w2 s1) with vs_inst_idx := 2` >>
  qabbrev_tac `g2 = DRESTRICT g1 (COMPL {done})` >>
  qabbrev_tac `t2 = t1 with t_var := t1.t_var |+ (done,{})` >>
  `gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 g2 t2 (OK s2)` by
    suspend "iszero" >>
  `gas_path_ptr D 0 ctx fn PG g2 t2 s2 0 g2 t2 (OK (jump_to dest s2))` by
    suspend "jump" >>
  qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  drule_all gas_path_ptr_then >>
  simp[Abbr `s2`, Abbr `s1`, Abbr `t2`, Abbr `t1`, jump_to_def,
       update_var_def]
QED

Resume typed_copy_operand_test_counted[iszero]:
  `gas_path_ptr D 0 ctx fn PG g1 t1 s1 0
     (DRESTRICT g1 (COMPL {done})) (t1 with t_var := t1.t_var |+ (done,{}))
     (OK ((update_var done w2 s1) with vs_inst_idx := SUC s1.vs_inst_idx))`
    suffices_by simp[Abbr `s2`, Abbr `g2`, Abbr `t2`, Abbr `s1`] >>
  irule typed_copy_arith_counted >>
  simp[Abbr `s1`, update_var_def] >>
  qexistsl_tac [`id+1`, `ISZERO`, `[Var lt]`] >>
  simp[get_instruction_def, Abbr `t1`, ptrDisciplineTheory.op_taint_def,
    FLOOKUP_UPDATE, step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
    eval_operand_def, lookup_var_def, update_var_def, Abbr `w1`, Abbr `w2`,
    bool_to_word_def] >> Cases_on `i<n` >> simp[]
QED

Resume typed_copy_operand_test_counted[jump]:
  irule typed_copy_counted_jump >> simp[Abbr `s2`, Abbr `s1`, update_var_def] >>
  qexists_tac `mk_inst (id+2) JNZ [Var done; Label exit; Label body_lbl] []` >>
  simp[get_instruction_def, update_var_def, mk_inst_def, is_terminator_def] >>
  conj_tac
  >- (simp[step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, Abbr `w2`, Abbr `dest`,
       bool_to_word_def, jump_to_def] >> Cases_on `i<n` >> simp[]) >>
  irule (SRULE [mk_inst_def] typed_copy_loop_test_check) >>
  simp[Abbr `t2`, Abbr `t1`] >> conj_tac
  >- (rpt strip_tac >> gvs[ptrDisciplineTheory.op_taint_def, FLOOKUP_UPDATE]) >>
  simp[step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def,
    FLOOKUP_UPDATE, Abbr `w2`, bool_to_word_def, jump_to_def] >>
  Cases_on `i<n` >> simp[]
QED

Finalise typed_copy_operand_test_counted

(* The capacity guard is wholly scalar; it neither reads nor clears padding. *)
Theorem typed_copy_capacity_guard_counted:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst id GT [Var len; Lit (n2w cap)] [too];
     mk_inst (id+1) ISZERO [Var too] [ok];
     mk_inst (id+2) ASSERT [Var ok] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_var len s = SOME (n2w n) /\ op_taint tn (Var len) = {} /\
  FLOOKUP G len = NONE /\ n <= cap /\ cap < dimword(:256) /\
  len <> too /\ len <> ok /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted ==>
  ?H tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf
      (OK ((update_var ok 1w (update_var too 0w s))
        with vs_inst_idx := s.vs_inst_idx+3)) /\
    FLOOKUP H len = NONE /\ op_taint tf (Var len) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. p <> too /\ p <> ok ==>
      FLOOKUP H p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qabbrev_tac `code =
    [mk_inst id GT [Var len; Lit (n2w cap)] [too];
     mk_inst (id+1) ISZERO [Var too] [ok];
     mk_inst (id+2) ASSERT [Var ok] []]` >>
  qabbrev_tac `A = {Var len; Lit (n2w cap)}` >>
  `bop_scalar_seq (COMPL {too;ok}) A code
     (Var ok INSERT Var too INSERT A)` by
    (qunabbrev_tac `code` >>
     simp[Once bop_scalar_seq_def] >> disj1_tac >>
     qexistsl_tac [`id`, `GT`, `[Var len;Lit (n2w cap)]`, `too`] >> simp[] >>
     conj_tac >- simp[Abbr `A`] >>
     simp[Once bop_scalar_seq_def] >> disj1_tac >>
     qexistsl_tac [`id+1`, `ISZERO`, `[Var too]`, `ok`] >> simp[] >>
     simp[Once bop_scalar_seq_def] >> disj2_tac >>
     qexistsl_tac [`id+2`, `ASSERT`, `Var ok`] >> simp[]) >>
  `!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[Abbr `A`] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `run_inst_seq code s = OK (update_var ok 1w (update_var too 0w s))` by
    (simp[Abbr `code`, run_inst_seq_def, step_inst_base_opcode_eqs,
       mk_inst_def, exec_pure2_def, exec_pure1_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, w2n_n2w,
       LESS_MOD, bool_to_word_def] >>
     `n < dimword(:256) /\ ~(cap < n)` by decide_tac >> simp[]) >>
  drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qpat_x_assum `!op. op IN Var ok INSERT _ ==> _`
    (qspec_then `Var len` mp_tac) >>
  simp[Abbr `A`, op_prov_def] >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`] >>
  gvs[Abbr `code`, op_taint_def]
QED

(* Lift endpoint coverage through an already proved counted ADD edge. *)
Theorem typed_copy_preamble_add_counted_conditional:
  (!PG G tn s root offset out id a off total n.
    lookup_var root s = SOME a /\
    eval_operand offset s = SOME (n2w off) /\
    ptr_covers G tn root s total /\ off+n <= total /\
    w2n a+off < dimword(:256) /\ root <> out ==>
    ptr_covers
      (step_prov PG G (mk_inst id ADD [Var root;offset] [out])
        (update_var out (a+n2w off) s))
      (step_taint (mk_inst id ADD [Var root;offset] [out]) s
        (update_var out (a+n2w off) s) tn)
      out (update_var out (a+n2w off) s) n) ==>
  !s ctx fn bb id root out off total n a G tn PG D.
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [Var root;Lit (n2w off)] [out]) /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s total /\
  off+n <= total /\ w2n a+off < dimword(:256) /\ root <> out ==>
  ?H tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
    u = ((update_var out (a+n2w off) s)
      with vs_inst_idx := SUC s.vs_inst_idx) /\
    lookup_var out u = SOME (a+n2w off) /\ ptr_covers H tf out u n /\
    op_taint tf (Var out) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. p <> out ==> lookup_var p u = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  `op_taint tn (Var root) = {}` by gvs[ptr_covers_def] >>
  drule_all add_literal_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  rename1 `ptr_covers G tn root s span` >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u)` >>
  qexistsl_tac [`H`, `tf`, `u`] >> simp[] >>
  `ptr_covers H tf out (update_var out (a+n2w off) s) n` by
    (map_every qunabbrev_tac [`H`, `tf`] >> first_x_assum irule >>
     simp[eval_operand_def] >> qexists_tac `span` >> simp[]) >>
  map_every qunabbrev_tac [`H`, `tf`, `u`] >>
  simp[copy_len_binop_ghost_frame, add_literal_imm_frame,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE, ptr_covers_def]
QED

Theorem typed_copy_dynamic_preamble_counted_conditional:
  (!PG G tn s root offset out id a off total n.
    lookup_var root s = SOME a /\
    eval_operand offset s = SOME (n2w off) /\
    ptr_covers G tn root s total /\ off+n <= total /\
    w2n a+off < dimword(:256) /\ root <> out ==>
    ptr_covers
      (step_prov PG G (mk_inst id ADD [Var root;offset] [out])
        (update_var out (a+n2w off) s))
      (step_taint (mk_inst id ADD [Var root;offset] [out]) s
        (update_var out (a+n2w off) s) tn)
      out (update_var out (a+n2w off) s) n) ==>
  !s ctx fn bb prefix suffix id src dst len too ok sp dp a b S T n cap G tn PG D.
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++
    [mk_inst id MLOAD [Var src] [len];
     mk_inst (id+1) GT [Var len;Lit (n2w cap)] [too];
     mk_inst (id+2) ISZERO [Var too] [ok];
     mk_inst (id+3) ASSERT [Var ok] [];
     mk_inst (id+4) MSTORE [Var dst;Var len] [];
     mk_inst (id+5) ADD [Var src;Lit 32w] [sp];
     mk_inst (id+6) ADD [Var dst;Lit 32w] [dp]] ++ suffix /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s (32+S) /\ ptr_covers G tn dst s (32+T) /\
  w2n a+32+S < dimword(:256) /\ w2n b+32+T < dimword(:256) /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n2w n /\ n <= cap /\ cap < dimword(:256) /\
  ALL_DISTINCT [len;too;ok;sp;dp] /\
  (!p. MEM p [len;too;ok;sp;dp] ==> src <> p /\ dst <> p) ==>
  ?H tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = LENGTH prefix+7 /\
    ~u.vs_halted /\ lookup_var len u = SOME (n2w n) /\
    FLOOKUP H len = NONE /\ op_taint tf (Var len) = {} /\
    lookup_var sp u = SOME (a+32w) /\ lookup_var dp u = SOME (b+32w) /\
    ptr_covers H tf sp u S /\ ptr_covers H tf dp u T /\
    u.vs_memory = (mstore (w2n b) (n2w n) s).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. ~MEM p [len;too;ok;sp;dp] ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p))
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  `ptr_covers G tn src s 32` by
    (gvs[ptr_covers_def] >> qexistsl_tac [`b'`, `n'`, `a`] >> simp[] >> decide_tac) >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [len])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  drule_all mload_counted_clean_ambient >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `isPREFIX
    [mk_inst (id+1) GT [Var len;Lit (n2w cap)] [too];
     mk_inst (id+2) ISZERO [Var too] [ok];
     mk_inst (id+3) ASSERT [Var ok] []]
    (DROP t.vs_inst_idx bb.bb_instructions)` by
    simp[DROP_APPEND, ADD1, DROP_LENGTH_TOO_LONG] >>
  `~t.vs_halted /\ lookup_var len t = SOME (n2w n) /\
   FLOOKUP G' len = NONE /\ len <> too /\ len <> ok /\
   lookup_block t.vs_current_bb fn.fn_blocks = SOME bb` by
    gvs[update_var_def, op_prov_def, ALL_DISTINCT] >>
  mp_tac (typed_copy_capacity_guard_counted |>
    Q.INST [`s` |-> `t`, `id` |-> `id+1`, `G` |-> `G'`, `tn` |-> `tn'`]) >>
  (impl_tac >- (simp[ADD_ASSOC] >> gvs[])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G' tn' t 0 g2 t2 (OK s2)` >>
  `lookup_var dst s2 = SOME b /\ lookup_var src s2 = SOME a /\
   lookup_var len s2 = SOME (n2w n) /\ ~s2.vs_halted /\
   lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s2.vs_inst_idx =
     SOME (mk_inst (id+4) MSTORE [Var dst;Var len] [])` by
    (`src <> len /\ src <> too /\ src <> ok /\
      dst <> len /\ dst <> too /\ dst <> ok` by
       (qpat_x_assum `!p. MEM p _ ==> _` mp_tac >> simp[]) >>
     `len <> too /\ len <> ok` by fs[ALL_DISTINCT] >>
     qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` kall_tac >>
     simp[Abbr `s2`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       NoAsms] >>
     qpat_x_assum `t = _` kall_tac >>
     qpat_x_assum `!PG G tn s root offset out id a off total n. _` kall_tac >>
     qpat_assum `!p. p <> len ==> _` (qspec_then `dst` assume_tac) >>
     qpat_x_assum `!p. p <> len ==> _` (qspec_then `src` assume_tac) >>
     qpat_x_assum `!p. MEM p _ ==> _` kall_tac >>
     simp[GSYM lookup_var_def] >>
     qpat_x_assum `bb.bb_instructions = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     strip_tac >> irule (cj 1 fragGasSeqAbortTheory.instruction_prefix_cursor) >>
     qexists_tac `[]` >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, ADD1]) >>
  `ptr_covers g2 t2 dst s2 32` by
    gvs[ptr_covers_def] >>
  `eval_operand (Var len) s2 = SOME (n2w n)` by simp[eval_operand_def] >>
  drule_all scalar_mstore_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG g2 t2 s2 0 g2 t3 (OK s3)` >>
  rename1 `ptr_covers G tn src s (32+sspan)` >>
  rename1 `ptr_covers G tn dst s (32+dspan)` >>
  `ptr_covers g2 t3 src s3 (32+sspan) /\ ptr_covers g2 t3 dst s3 (32+dspan)` by
    gvs[ptr_covers_def, Abbr `s3`, mstore_def, write_memory_with_expansion_def,
        write_memory_def, op_taint_def] >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG g2 t2 s2 0 g2 t3 (OK s3)` >>
  `~s3.vs_halted /\ lookup_var src s3 = SOME a /\
   lookup_block s3.vs_current_bb fn.fn_blocks = SOME bb` by
    (simp[Abbr `s3`, mstore_def, write_memory_with_expansion_def, write_memory_def,
         lookup_var_def] >> simp[GSYM lookup_var_def]) >>
  `get_instruction bb s3.vs_inst_idx =
     SOME (mk_inst (id+5) ADD [Var src;Lit 32w] [sp])` by
    (irule (cj 1 fragGasSeqAbortTheory.instruction_prefix_cursor) >>
     qexists_tac `[]` >>
     simp[Abbr `s3`, Abbr `s2`, mstore_def, write_memory_with_expansion_def,
          write_memory_def, update_var_def, DROP_APPEND, DROP_LENGTH_TOO_LONG, ADD1]) >>
  `src <> sp /\ dst <> dp /\ sp <> dp` by
    (fs[ALL_DISTINCT] >> qpat_x_assum `!p. MEM p _ ==> _` mp_tac >> simp[]) >>
  drule typed_copy_preamble_add_counted_conditional >>
  disch_then (qspecl_then [`s3`, `ctx`, `fn`, `bb`, `id+5`, `src`, `sp`,
    `32`, `32+sspan`, `sspan`, `a`, `g2`, `t3`, `PG`, `D`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG g2 t3 s3 0 g4 t4 (OK s4)` >>
  `dst <> sp` by (qpat_x_assum `!p. MEM p _ ==> _` mp_tac >> simp[]) >>
  `ptr_covers g4 t4 dst s4 (32+dspan)` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     metis_tac[]) >>
  `~s4.vs_halted /\ lookup_var dst s4 = SOME b /\
   lookup_block s4.vs_current_bb fn.fn_blocks = SOME bb` by
    (simp[Abbr `s4`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      Abbr `s3`, mstore_def, write_memory_with_expansion_def, write_memory_def] >>
     simp[GSYM lookup_var_def]) >>
  `get_instruction bb s4.vs_inst_idx =
     SOME (mk_inst (id+6) ADD [Var dst;Lit 32w] [dp])` by
    (irule (cj 1 fragGasSeqAbortTheory.instruction_prefix_cursor) >>
     qexists_tac `[]` >>
     simp[Abbr `s4`, Abbr `s3`, Abbr `s2`, mstore_def,
       write_memory_with_expansion_def, write_memory_def, update_var_def,
       DROP_APPEND, DROP_LENGTH_TOO_LONG, ADD1]) >>
  drule typed_copy_preamble_add_counted_conditional >>
  disch_then (qspecl_then [`s4`, `ctx`, `fn`, `bb`, `id+6`, `dst`, `dp`,
    `32`, `32+dspan`, `dspan`, `b`, `g4`, `t4`, `PG`, `D`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG g4 t4 s4 0 g5 t5 (OK s5)` >>
  qexistsl_tac [`g5`, `t5`, `s5`] >> conj_tac
  >- (qpat_x_assum `!PG G tn s root offset out id a off total n. _` kall_tac >>
      metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, ADD]) >>
  `ptr_covers g5 t5 sp s5 sspan` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> metis_tac[]) >>
  `len <> sp /\ len <> dp` by fs[ALL_DISTINCT] >>
  `FLOOKUP g5 len = NONE /\ op_taint t5 (Var len) = {}` by
    (qpat_assum `!p. p <> dp ==> _` (qspec_then `len` assume_tac) >>
     qpat_assum `!p. p <> sp ==> _` (qspec_then `len` assume_tac) >>
     fs[op_taint_def]) >>
  simp[] >>
  simp[Abbr `s3`, Abbr `s2`, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, mstore_def, write_memory_with_expansion_def,
    write_memory_def, ADD1] >>
  conj_tac
  >- (qpat_x_assum `s.vs_inst_idx = LENGTH prefix` (fn th => rewrite_tac[GSYM th]) >>
      simp[]) >>
  rpt strip_tac >>
  qpat_assum `!p. p <> too /\ p <> ok ==> _` (qspec_then `p` assume_tac) >>
  qpat_assum `!p. p <> len ==> _` (qspec_then `p` assume_tac) >>
  fs[op_taint_def]
QED

(* The endpoint-safe ADD boundary discharges the temporary helper contract. *)
Theorem typed_copy_dynamic_preamble_counted:
  !s ctx fn bb prefix suffix id src dst len too ok sp dp a b S T n cap G tn PG D.
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++
    [mk_inst id MLOAD [Var src] [len];
     mk_inst (id+1) GT [Var len;Lit (n2w cap)] [too];
     mk_inst (id+2) ISZERO [Var too] [ok];
     mk_inst (id+3) ASSERT [Var ok] [];
     mk_inst (id+4) MSTORE [Var dst;Var len] [];
     mk_inst (id+5) ADD [Var src;Lit 32w] [sp];
     mk_inst (id+6) ADD [Var dst;Lit 32w] [dp]] ++ suffix /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s (32+S) /\ ptr_covers G tn dst s (32+T) /\
  w2n a+32+S < dimword(:256) /\ w2n b+32+T < dimword(:256) /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n2w n /\ n <= cap /\ cap < dimword(:256) /\
  ALL_DISTINCT [len;too;ok;sp;dp] /\
  (!p. MEM p [len;too;ok;sp;dp] ==> src <> p /\ dst <> p) ==>
  ?H tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = LENGTH prefix+7 /\
    ~u.vs_halted /\ lookup_var len u = SOME (n2w n) /\
    FLOOKUP H len = NONE /\ op_taint tf (Var len) = {} /\
    lookup_var sp u = SOME (a+32w) /\ lookup_var dp u = SOME (b+32w) /\
    ptr_covers H tf sp u S /\ ptr_covers H tf dp u T /\
    u.vs_memory = (mstore (w2n b) (n2w n) s).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. ~MEM p [len;too;ok;sp;dp] ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p))
Proof
  match_mp_tac typed_copy_dynamic_preamble_counted_conditional >>
  ACCEPT_TAC typed_copy_loop_dynamic_offset_covers_endpoint
QED
