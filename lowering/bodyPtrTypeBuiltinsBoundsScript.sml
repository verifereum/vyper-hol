Theory bodyPtrTypeBuiltinsBounds
Ancestors
  builtinBytes exprLoweringProps emitHelperProps emitHelper compileEnv loweringStateRelDefs context
  venomInst venomState venomExecSemantics finite_map list words arithmetic
  fragGasSeqPtr ptrDiscipline ptrSafeRun codegenRel contextCodegenRel

Theorem compile_assert_slice_bounds_shape:
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

Theorem slice_bounds_overflow:
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

Theorem slice_bounds_word_ok:
  !(a:256 word) (n:256 word) (limit:256 word).
    (~(w2n (a + n) < w2n a) /\ ~(w2n limit < w2n (a + n))) <=>
    w2n a + w2n n <= w2n limit
Proof
  rpt gen_tac >>
  qspec_then `dimword (:256)` mp_tac slice_bounds_overflow >>
  disch_then (qspecl_then [`w2n a`, `w2n n`, `w2n limit`] mp_tac) >>
  simp[word_add_def, w2n_n2w, w2n_lt] >>
  `w2n limit < dimword (:256)` by simp[w2n_lt] >> decide_tac
QED

Theorem eval_operand_update_old:
  !sa a s n w.
    (!z. a = Var z ==> not_fresh_at sa z) /\ sa.cs_next_var <= n ==>
    eval_operand a (update_var (STRING #"%" (toString n)) w s) = eval_operand a s
Proof
  gen_tac >> Cases >> simp[eval_operand_def, lookup_var_update_var] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[]
QED

Theorem slice_bounds_run_normal:
  compile_assert_slice_bounds a n limit sa = ((), sb) /\
  (!z. a = Var z ==> not_fresh_at sa z) /\
  (!z. limit = Var z ==> not_fresh_at sa z) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\ w2n wa + w2n wn <= w2n wl ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t = s with vs_vars := t.vs_vars /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `!j w ss. sa.cs_next_var <= j ==>
    eval_operand a (update_var (STRING #"%" (toString j)) w ss) = eval_operand a ss` by
    (rpt strip_tac >> irule eval_operand_update_old >> qexists_tac `sa` >> simp[]) >>
  `!j w ss. sa.cs_next_var <= j ==>
    eval_operand limit (update_var (STRING #"%" (toString j)) w ss) = eval_operand limit ss` by
    (rpt strip_tac >> irule eval_operand_update_old >> qexists_tac `sa` >> simp[]) >>
  `~(w2n (wa + wn) < w2n wa) /\ ~(w2n wl < w2n (wa + wn))` by
    metis_tac[slice_bounds_word_ok] >>
  drule compile_assert_slice_bounds_shape >> strip_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, exec_pure1_def, bool_to_word_def,
       eval_operand_def, lookup_var_update_var, WORD_OR_CLAUSES] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[]
QED

Theorem slice_bounds_run_abort:
  compile_assert_slice_bounds a n limit sa = ((), sb) /\
  (!z. a = Var z ==> not_fresh_at sa z) /\
  (!z. limit = Var z ==> not_fresh_at sa z) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\ ~(w2n wa + w2n wn <= w2n wl) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s =
        Abort Revert_abort (revert_state (set_returndata [] t)) /\
      t = s with vs_vars := t.vs_vars /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `!j w ss. sa.cs_next_var <= j ==>
    eval_operand a (update_var (STRING #"%" (toString j)) w ss) = eval_operand a ss` by
    (rpt strip_tac >> irule eval_operand_update_old >> qexists_tac `sa` >> simp[]) >>
  `!j w ss. sa.cs_next_var <= j ==>
    eval_operand limit (update_var (STRING #"%" (toString j)) w ss) = eval_operand limit ss` by
    (rpt strip_tac >> irule eval_operand_update_old >> qexists_tac `sa` >> simp[]) >>
  `w2n (wa + wn) < w2n wa \/ w2n wl < w2n (wa + wn)` by
    metis_tac[slice_bounds_word_ok] >>
  drule compile_assert_slice_bounds_shape >> strip_tac >>
  Cases_on `w2n (wa + wn) < w2n wa` >>
  Cases_on `w2n wl < w2n (wa + wn)` >> gvs[] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, exec_pure1_def, bool_to_word_def,
       eval_operand_def, lookup_var_update_var, WORD_OR_CLAUSES] >>
  qmatch_goalsub_abbrev_tac `revert_state (set_returndata [] u)` >>
  qexists_tac `u` >> simp[Abbr `u`] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[]
QED

