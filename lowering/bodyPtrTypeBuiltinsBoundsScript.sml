Theory bodyPtrTypeBuiltinsBounds
Ancestors
  bodyPtrBytestringBuiltinsBounds[qualified,ignore_grammar] exprSimWordBuiltins[qualified,ignore_grammar]
  augAssignPtrScalarCertificate
  builtinBytes exprLoweringProps emitHelperProps emitHelper compileEnv loweringStateRelDefs context
  venomInst venomState venomExecSemantics finite_map list words arithmetic
  fragGasSeqPtr ptrDiscipline ptrSafeRun codegenRel contextCodegenRel



Theorem slice_bounds_word_ok:
  !(a:256 word) (n:256 word) (limit:256 word).
    (~(w2n (a + n) < w2n a) /\ ~(w2n limit < w2n (a + n))) <=>
    w2n a + w2n n <= w2n limit
Proof
  rpt gen_tac >>
  qspec_then `dimword (:256)` mp_tac bodyPtrBytestringBuiltinsBoundsTheory.slice_bounds_mod_overflow >>
  disch_then (qspecl_then [`w2n a`, `w2n n`, `w2n limit`] mp_tac) >>
  simp[word_add_def, w2n_n2w, w2n_lt] >>
  `w2n limit < dimword (:256)` by simp[w2n_lt] >> decide_tac
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
    (rpt strip_tac >> irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >> qexists_tac `sa` >> simp[]) >>
  `!j w ss. sa.cs_next_var <= j ==>
    eval_operand limit (update_var (STRING #"%" (toString j)) w ss) = eval_operand limit ss` by
    (rpt strip_tac >> irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >> qexists_tac `sa` >> simp[]) >>
  `~(w2n (wa + wn) < w2n wa) /\ ~(w2n wl < w2n (wa + wn))` by
    metis_tac[slice_bounds_word_ok] >>
  drule bodyPtrBytestringBuiltinsBoundsTheory.compile_assert_slice_bounds_layout >> strip_tac >>
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
    (rpt strip_tac >> irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >> qexists_tac `sa` >> simp[]) >>
  `!j w ss. sa.cs_next_var <= j ==>
    eval_operand limit (update_var (STRING #"%" (toString j)) w ss) = eval_operand limit ss` by
    (rpt strip_tac >> irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >> qexists_tac `sa` >> simp[]) >>
  `w2n (wa + wn) < w2n wa \/ w2n wl < w2n (wa + wn)` by
    metis_tac[slice_bounds_word_ok] >>
  drule bodyPtrBytestringBuiltinsBoundsTheory.compile_assert_slice_bounds_layout >> strip_tac >>
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

Theorem slice_bounds_scalar_code:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  scalar_available A a /\ scalar_available A n /\ scalar_available A limit ==>
  scalar_code A (emitted_insts sa sb)
Proof
  strip_tac >> drule bodyPtrBytestringBuiltinsBoundsTheory.compile_assert_slice_bounds_layout >> strip_tac >>
  simp[scalar_code_def, scalar_shape_def, scalar_binary_def,
       scalar_unary_def, mk_inst_def, scalar_available_def] >>
  gvs[scalar_available_def] >> simp[]
QED
