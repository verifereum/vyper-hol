(* Pointer control for the non-fast typed-array copy loop.  These facts
   concern its concrete compiler header, not execution of a child copy. *)
Theory bodyPtrIntCallArrayLoop
Ancestors
  typedArrayLoopCode typedArrayLoopHeader typedArrayLoopAddress typedArrayLoopCounter
  bodyPtrBopScalarSeq fragGasSeqPtr finite_map pred_set list rich_list

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
