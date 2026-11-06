(* Semantic run existence for the unsigned clamp, including reversion. *)
Theory bodyPtrTypeBuiltinsUintClampSemantics
Ancestors bodyPtrTypeBuiltinsUnsignedSemantics builtinIntClamp
  exprLoweringProps exprLowering emitHelperProps compileEnv venomExecSemantics
  venomState venomInst venomInstProofs fragExec words vyperValue

Theorem uint_emit_gt_exact[local]:
  emit_op GT [a;b] sa = (v,sb) /\
  eval_operand a ss = SOME x /\ eval_operand b ss = SOME y /\
  fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand v sf = SOME (bool_to_word (w2n x > w2n y)) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  rpt strip_tac >> irule scalar_emit_update_exact >> simp[] >>
  goal_assum (drule_at (Pat `emit_op`)) >> simp[] >>
  simp[clamp_step_equations, exec_pure2_def, mk_inst_def]
QED

Theorem uint_emit_iszero_exact[local]:
  emit_op ISZERO [a] sa = (v,sb) /\
  eval_operand a ss = SOME x /\ fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand v sf = SOME (if x = 0w then 1w else 0w) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  rpt strip_tac >> irule scalar_emit_update_exact >> simp[] >>
  goal_assum (drule_at (Pat `emit_op`)) >> simp[] >>
  drule step_ISZERO >> Cases_on `x = 0w` >> simp[bool_to_word_def]
QED

Theorem uint_emit_assert_exact[local]:
  emit_void ASSERT [a] sa = (u,sb) /\
  eval_operand a ss = SOME x /\ fresh_vars_wrt sa ss ==>
  run_inst_seq (emitted_insts sa sb) ss =
    (if x = 0w then Abort Revert_abort (revert_state (set_returndata [] ss))
     else OK ss) /\ fresh_vars_wrt sb ss
Proof
  rpt gen_tac >> strip_tac >> Cases_on `u` >> conj_tac
  >- (drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
      Cases_on `x = 0w` >> simp[run_inst_seq_def, clamp_assert_step]) >>
  metis_tac[fresh_vars_wrt_emit_void]
QED

Theorem uint_clamp_raw_exact:
  compile_int_clamp F b v sa = (r,sb) /\
  eval_operand v ss = SOME x /\ fresh_vars_wrt sa ss ==>
  if w2n x <= w2n (n2w (2 ** b-1):bytes32) then
    ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME x /\ fresh_vars_wrt sb sf /\
      sf.vs_memory = ss.vs_memory /\ sf.vs_allocas = ss.vs_allocas /\
      (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  else ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_int_clamp _ _ _ _ = _` mp_tac >>
  simp_tac pure_ss [compile_int_clamp_def, COND_CLAUSES, comp_bind_def,
                   comp_ignore_bind_def, comp_return_def, LET_THM] >>
  qabbrev_tac `hi:bytes32 = n2w (2 ** b-1)` >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op GT [v;_] sa = (gt,s1)` >>
  rename1 `emit_op ISZERO [gt] s1 = (ok,s2)` >>
  rename1 `emit_void ASSERT [ok] s2 = ((),sb)` >>
  `eval_operand (Lit hi) ss = SOME hi` by simp[eval_operand_def] >>
  drule_all uint_emit_gt_exact >>
  disch_then (qx_choose_then `t1` strip_assume_tac) >>
  drule_all uint_emit_iszero_exact >>
  disch_then (qx_choose_then `t2` strip_assume_tac) >>
  drule_all uint_emit_assert_exact >> strip_tac >>
  `inst_extends sa s1 /\ inst_extends s1 s2 /\ inst_extends s2 sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `inst_extends sa s2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa s2) ss = OK t2` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`t1`,`s1`] >> simp[]) >>
  Cases_on `w2n x <= w2n hi` >> gvs[bool_to_word_def]
  >- (qexists_tac `t2` >> simp[] >>
      irule run_inst_seq_compose_ok >> qexistsl_tac [`t2`,`s2`] >> simp[]) >>
  drule_all run_inst_seq_emit_extend >> simp[]
QED

Theorem uint_clamp_test:
  b <= 256 ==>
  (w2n (x:bytes32) <= w2n (n2w (2 ** b-1):bytes32) <=>
   within_int_bound (Unsigned b) (&(w2n x)))
Proof
  strip_tac >>
  `2 ** b <= 2 ** 256` by simp[arithmeticTheory.EXP_BASE_LE_MONO] >>
  `0 < 2 ** b` by simp[] >>
  `2 ** b-1 < dimword(:256)` by simp[wordsTheory.dimword_def] >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD, within_int_bound_def] >>
  decide_tac
QED

Theorem uint_clamp_exact:
  compile_int_clamp F b v sa = (r,sb) /\
  eval_operand v ss = SOME x /\ fresh_vars_wrt sa ss /\
  0 < b /\ b <= 256 ==>
  if within_int_bound (Unsigned b) (&(w2n x)) then
    ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME x /\ fresh_vars_wrt sb sf /\
      sf.vs_memory = ss.vs_memory /\ sf.vs_allocas = ss.vs_allocas /\
      (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  else ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >> drule_all uint_clamp_raw_exact >> simp[uint_clamp_test]
QED
