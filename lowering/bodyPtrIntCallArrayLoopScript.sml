(* Pointer control for the non-fast typed-array copy loop.  These facts
   concern its concrete compiler header, not execution of a child copy. *)
Theory bodyPtrIntCallArrayLoop
Ancestors
  typedArrayLoopCode typedArrayLoopHeader typedArrayLoopAddress typedArrayLoopCounter
  bodyPtrBopScalarSeq bodyPtrBopInLoopSegments fragGasSeqPtr
  venomInst venomState venomExecSemantics fragGasPathPtr compileEnv finite_map pred_set list rich_list

Theorem intcall_typed_array_header_scalar[local]:
  compiler_var_name vb 1 NOTIN R /\ compiler_var_name vb 2 NOTIN R ==>
  bop_scalar_seq R {Var (compiler_var_name vb 0); len}
    (TAKE 2 (typed_array_loop_header id vb bl el len))
    {Var (compiler_var_name vb 2); Var (compiler_var_name vb 1);
     Var (compiler_var_name vb 0); len}
Proof
  strip_tac >> simp[typed_array_loop_header_def] >>
  pure_once_rewrite_tac[bop_scalar_seq_def] >> disj1_tac >>
  qexistsl_tac [`id + 2`, `LT`, `[Var (compiler_var_name vb 0); len]`,
    `compiler_var_name vb 1`] >> simp[] >>
  pure_once_rewrite_tac[bop_scalar_seq_def] >> disj1_tac >>
  qexistsl_tac [`id + 3`, `ISZERO`, `[Var (compiler_var_name vb 1)]`,
    `compiler_var_name vb 2`] >> simp[bop_scalar_seq_def]
QED

Theorem intcall_typed_array_header_prefix_counted:
  !D ctx fn PG G tn s id vb bl el len cw lw bb R.
  compiler_var_name vb 1 NOTIN R /\ compiler_var_name vb 2 NOTIN R /\
  op_prov G (Var (compiler_var_name vb 0)) = NONE /\
  op_taint tn (Var (compiler_var_name vb 0)) = {} /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  eval_operand (Var (compiler_var_name vb 0)) s = SOME cw /\
  eval_operand len s = SOME lw /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = typed_array_loop_header id vb bl el len ==>
  ?H tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf
      (OK ((typed_array_loop_header_state vb cw lw s) with vs_inst_idx := 2)) /\
    op_prov H (Var (compiler_var_name vb 2)) = NONE /\
    op_taint tf (Var (compiler_var_name vb 2)) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP tf.t_var x = FLOOKUP tn.t_var x)
Proof
  rpt gen_tac >> strip_tac >>
  `run_inst_seq (TAKE 2 (typed_array_loop_header id vb bl el len)) s =
    OK (typed_array_loop_header_state vb cw lw s)` by
    (irule typed_array_loop_header_execution >> simp[]) >>
  `bop_scalar_seq R {Var (compiler_var_name vb 0); len}
    (TAKE 2 (typed_array_loop_header id vb bl el len))
    {Var (compiler_var_name vb 2); Var (compiler_var_name vb 1);
     Var (compiler_var_name vb 0); len}` by
    (irule intcall_typed_array_header_scalar >> simp[]) >>
  `!op. op IN {Var (compiler_var_name vb 0); len} ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[]) >>
  `isPREFIX (TAKE 2 (typed_array_loop_header id vb bl el len))
    (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[typed_array_loop_header_def] >>
  drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> gvs[typed_array_loop_header_def]
QED

Theorem intcall_typed_array_header_counted:
  !D ctx fn PG G tn s id vb bl el len cw lw bb R.
  compiler_var_name vb 1 NOTIN R /\ compiler_var_name vb 2 NOTIN R /\
  op_prov G (Var (compiler_var_name vb 0)) = NONE /\
  op_taint tn (Var (compiler_var_name vb 0)) = {} /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  eval_operand (Var (compiler_var_name vb 0)) s = SOME cw /\
  eval_operand len s = SOME lw /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = typed_array_loop_header id vb bl el len ==>
  ?H tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf
      (OK (jump_to (if w2n cw < w2n lw then bl else el)
        (typed_array_loop_header_state vb cw lw s))) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP tf.t_var x = FLOOKUP tn.t_var x)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_typed_array_header_prefix_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = 2` by
    simp[Abbr `u`] >>
  `get_instruction bb u.vs_inst_idx =
    SOME (mk_inst (id+4) JNZ [Var (compiler_var_name vb 2); Label el; Label bl] [])` by
    simp[get_instruction_def, typed_array_loop_header_def] >>
  `eval_operand (Var (compiler_var_name vb 2)) u =
    SOME (bool_to_word (~(w2n cw < w2n lw)))` by
    simp[Abbr `u`, typed_array_loop_header_state_def,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `gas_path_ptr D 0 ctx fn PG H tf u 0 H tf
    (OK (jump_to (if w2n cw < w2n lw then bl else el) u))` by
    (`lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
     drule_all membership_jnz_path >>
     disch_then (qspecl_then [`PG`, `H`, `D`] mp_tac) >>
     Cases_on `w2n cw < w2n lw` >> simp[]) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`H`, `tf`] >> simp[] >>
  gvs[Abbr `u`, jump_to_def]
QED
