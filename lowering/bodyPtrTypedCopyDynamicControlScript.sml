(* Scalar-bound counted control for runtime-length typed array copies. *)
Theory bodyPtrTypedCopyDynamicControl
Ancestors bodyPtrTypedCopyArrayControl typedCopyLoopHeaderPtr
  fragGasPathPtr exprSimPtrProps venomExecSemantics venomInst venomState words finite_map arithmetic
  bodyPtrBopScalarSeq fragExec exprLoweringProps ptrDiscipline list pred_set

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
