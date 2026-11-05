(* The final two nonterminating instructions of the bounded copy body. *)
Theory exprPtrUnwrapIncrement
Ancestors
  exprPtrUnwrapScalarSegments exprPtrUnwrapSeq exprPtrUnwrapFrames
  ghostPcTransportPtr fragGasSeqPtr fragExec
  ptrDiscipline ptrSafeRun typedCopyPtr venomExecSemantics venomInst venomState
  finite_map exprLoweringProps slotCopyExecution

Theorem copy_increment_segment:
  counter <> next /\ eval_operand (Var counter) s = SOME x /\
  op_taint tn (Var counter) = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id ADD [Var counter;Lit 1w] [next];
      mk_inst aid ASSIGN [Var next] [counter]] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ADD [Var counter;Lit 1w] [next];
       mk_inst aid ASSIGN [Var next] [counter]] s Gf tnf /\
    t = update_var counter (x+1w) (update_var next (x+1w) s) /\
    op_taint tnf (Var counter) = {} /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!p. p <> counter /\ p <> next ==>
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. p <> counter /\ p <> next /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  `eval_operand (Lit 1w) s = SOME 1w /\ op_taint tn (Lit 1w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (Q.INST [`left` |-> `Var counter`, `tmp` |-> `next`,
    `id` |-> `id`] (SRULE [] (Q.INST [`opc` |-> `ADD`]
      (SPEC_ALL copy_arith_segment)))) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `inst_seq_ptr D lo ctx fn PG G tn _ s Gm tnm` >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK u` >>
  qabbrev_tac `v = u with vs_inst_idx := s.vs_inst_idx + 1` >>
  `eval_operand (Var next) v = SOME (x+1w) /\ allocas_from lo v /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
    (fs[Abbr `v`, Abbr `u`, eval_operand_def, lookup_var_def,
        update_var_def, FLOOKUP_UPDATE, allocas_from_def, allocas_below_fmp_def] >>
     metis_tac[]) >>
  drule_all (Q.INST [`arg` |-> `Var next`, `tmp` |-> `counter`,
    `id` |-> `aid`, `G` |-> `Gm`] (SPEC_ALL copy_assign_segment)) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `inst_seq_ptr D lo ctx fn PG Gm tnm _ v Gf tnf` >>
  qexistsl_tac [`Gf`, `tnf`,
    `update_var counter (x+1w) (update_var next (x+1w) s)`] >>
  conj_tac
  >- simp[Abbr `u`, run_inst_seq_def, step_inst_base_def, mk_inst_def,
          exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE] >>
  conj_tac
  >- (irule inst_seq_ptr_cons_compose >>
      conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl_tac [`Gm`, `u`, `tnm`] >>
      gvs[Abbr `v`, mk_inst_def, is_terminator_def, arithmeticTheory.ADD1]) >>
  gvs[Abbr `v`, Abbr `u`] >> metis_tac[]
QED
