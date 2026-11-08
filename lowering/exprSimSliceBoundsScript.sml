(* Overflow-aware arithmetic boundary for slice bounds checks. *)
Theory exprSimSliceBounds
Ancestors
  builtinBytes emitHelperProps freshWrites fragExec words arithmetic
  compileEnv emitHelper context venomInst venomState venomExecSemantics list
  exprLoweringProps

Theorem slice_bounds_mod:
  !modulus a n limit. a < modulus /\ n < modulus /\ limit < modulus ==>
  ((a + n) MOD modulus < a \/ limit < (a + n) MOD modulus <=>
   modulus <= a + n \/ limit < a + n)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `a + n < modulus`
  >- simp[LESS_MOD] >>
  `a + n < 2 * modulus` by decide_tac >>
  `(a + n) MOD modulus = a + n - modulus` by
    (irule MOD_UNIQUE >> qexists_tac `1` >> simp[] >> decide_tac) >>
  simp[] >> decide_tac
QED

Theorem slice_bounds_word:
  a < 2 ** 256 /\ n < 2 ** 256 /\ limit < 2 ** 256 ==>
  (((n2w a + n2w n):bytes32) <+ n2w a \/
    (n2w limit:bytes32) <+ n2w a + n2w n <=>
   2 ** 256 <= a + n \/ limit < a + n)
Proof
  strip_tac >>
  gvs[WORD_LO, word_add_n2w, w2n_n2w, dimword_def, LESS_MOD] >>
  irule slice_bounds_mod >> simp[]
QED

Theorem slice_bounds_shape:
  compile_assert_slice_bounds a n limit sa = ((), sb) ==>
  sb.cs_next_var = sa.cs_next_var + 5 /\
  sb.cs_next_id = sa.cs_next_id + 6 /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id ADD [a; n]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) LT
       [Var (STRING #"%" (toString sa.cs_next_var)); a]
       [STRING #"%" (toString (sa.cs_next_var + 1))];
     mk_inst (sa.cs_next_id + 2) GT
       [Var (STRING #"%" (toString sa.cs_next_var)); limit]
       [STRING #"%" (toString (sa.cs_next_var + 2))];
     mk_inst (sa.cs_next_id + 3) OR
       [Var (STRING #"%" (toString (sa.cs_next_var + 1)));
        Var (STRING #"%" (toString (sa.cs_next_var + 2)))]
       [STRING #"%" (toString (sa.cs_next_var + 3))];
     mk_inst (sa.cs_next_id + 4) ISZERO
       [Var (STRING #"%" (toString (sa.cs_next_var + 3)))]
       [STRING #"%" (toString (sa.cs_next_var + 4))];
     mk_inst (sa.cs_next_id + 5) ASSERT
       [Var (STRING #"%" (toString (sa.cs_next_var + 4)))] []]
Proof
  simp[compile_assert_slice_bounds_def, comp_bind_def, comp_ignore_bind_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

Theorem slice_bounds_writes_fresh:
  compile_assert_slice_bounds a n limit sa = ((), sb) ==>
  writes_fresh sa (emitted_insts sa sb)
Proof
  strip_tac >> drule slice_bounds_shape >> strip_tac >>
  simp[writes_fresh_def, fresh_write_op_def, mk_inst_def, not_fresh_at_def]
QED

Theorem slice_operand_update_not_fresh[local]:
  !sa a ss n w. (!z. a = Var z ==> not_fresh_at sa z) /\ sa.cs_next_var <= n ==>
    eval_operand a (update_var (STRING #"%" (toString n)) w ss) = eval_operand a ss
Proof
  gen_tac >> Cases >> simp[eval_operand_def, lookup_var_update_var] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[]
QED

Theorem slice_bounds_run:
  compile_assert_slice_bounds a n limit sa = ((), sb) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  (!z. a = Var z ==> not_fresh_at sa z) /\
  (!z. n = Var z ==> not_fresh_at sa z) /\
  (!z. limit = Var z ==> not_fresh_at sa z) ==>
  if wa + wn <+ wa \/ wl <+ wa + wn then
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
  else ?t. run_inst_seq (emitted_insts sa sb) s = OK t
Proof
  strip_tac >>
  `!j w ss. sa.cs_next_var <= j ==>
      eval_operand a (update_var (STRING #"%" (toString j)) w ss) = eval_operand a ss` by
    (rpt strip_tac >> irule slice_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `!j w ss. sa.cs_next_var <= j ==>
      eval_operand limit (update_var (STRING #"%" (toString j)) w ss) = eval_operand limit ss` by
    (rpt strip_tac >> irule slice_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  drule slice_bounds_shape >> strip_tac >>
  Cases_on `wa + wn <+ wa` >> Cases_on `wl <+ wa + wn` >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, exec_pure1_def, bool_to_word_def,
       eval_operand_def, lookup_var_update_var, WORD_OR_CLAUSES] >>
  gvs[WORD_LO, bool_to_word_def, WORD_OR_CLAUSES]
QED

Theorem slice_bounds_run_frame:
  compile_assert_slice_bounds a n limit sa = ((), sb) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  (!z. a = Var z ==> not_fresh_at sa z) /\
  (!z. n = Var z ==> not_fresh_at sa z) /\
  (!z. limit = Var z ==> not_fresh_at sa z) ==>
  if wa + wn <+ wa \/ wl <+ wa + wn then
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
  else ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
           t = s with vs_vars := t.vs_vars /\
           !x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  strip_tac >> drule_all slice_bounds_run >>
  Cases_on `wa + wn <+ wa \/ wl <+ wa + wn` >> simp[] >>
  strip_tac >> qexists_tac `t` >> simp[] >>
  irule run_inst_seq_writes_fresh >>
  qexists_tac `emitted_insts sa sb` >> simp[] >>
  irule slice_bounds_writes_fresh >> metis_tac[]
QED
