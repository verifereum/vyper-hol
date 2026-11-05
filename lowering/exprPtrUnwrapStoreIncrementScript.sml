(* Taint-transferring store and the clean loop-counter increment. *)
Theory exprPtrUnwrapStoreIncrement
Ancestors
  exprPtrUnwrapStoreSegment exprPtrUnwrapIncrement exprPtrUnwrapSeq
  exprPtrUnwrapFrames ghostPcTransportPtr slotCopyExecution fragGasSeqPtr
  fragExec bodyPtrDefs ptrDiscipline ptrSafeRun venomExecSemantics venomInst
  venomState finite_map exprLoweringProps instIdxIndep list

Theorem copy_store_increment_segment:
  ptr_covers G tn root s 32 /\
  eval_operand (Var root) s = SOME addr /\ eval_operand v s = SOME value /\
  counter <> next /\ eval_operand (Var counter) s = SOME x /\
  op_taint tn (Var counter) = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id MSTORE [Var root;v] [];
      mk_inst iid ADD [Var counter;Lit 1w] [next];
      mk_inst aid ASSIGN [Var next] [counter]] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id MSTORE [Var root;v] [];
       mk_inst iid ADD [Var counter;Lit 1w] [next];
       mk_inst aid ASSIGN [Var next] [counter]] s Gf tnf /\
    t = update_var counter (x+1w) (update_var next (x+1w)
      (mstore (w2n addr) value s)) /\
    op_taint tnf (Var counter) = {} /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr + 32}) UNION
        {w2n addr + k | k IN op_taint tn v} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p. p <> counter /\ p <> next ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p c. p <> counter /\ p <> next /\ ptr_covers G tn p s c ==>
      ptr_covers Gf tnf p t c)
Proof
  strip_tac >>
  mp_tac (SPEC_ALL copy_store_segment) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  rename1 `inst_seq_ptr D lo ctx fn PG G tn _ s Gm tnm` >>
  qabbrev_tac `u = mstore (w2n addr) value s` >>
  qabbrev_tac `w = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `eval_operand (Var counter) w = SOME x /\ op_taint tnm (Var counter) = {} /\
   allocas_from lo w /\ (ctx_has_dalloca ctx ==> allocas_below_fmp w)` by
    (fs[Abbr `w`, Abbr `u`, mstore_def, eval_operand_def, lookup_var_def,
        allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `w`, `G` |-> `Gm`, `tn` |-> `tnm`,
    `id` |-> `iid`] (SPEC_ALL copy_increment_segment)) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  rename1 `inst_seq_ptr D lo ctx fn PG Gm tnm _ w Gf tnf` >>
  qexistsl_tac [`Gf`, `tnf`, `update_var counter (x+1w) (update_var next (x+1w) u)`] >>
  conj_tac
  >- (qpat_assum `eval_operand (Var counter) s = SOME x`
        (assume_tac o REWRITE_RULE [eval_operand_def, lookup_var_def]) >>
      simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
           exec_write2_def] >>
      simp[Abbr `u`, run_inst_seq_def, step_inst_base_def, mk_inst_def,
           exec_pure2_def, slot_copy_operand_update, slot_copy_operand_mstore,
           eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  conj_tac
  >- (irule inst_seq_ptr_cons_compose >>
      conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl_tac [`Gm`, `u`, `tnm`] >> gvs[Abbr `w`]) >>
  gvs[Abbr `w`, copy_update_inst_idx, ptr_covers_inst_idx,
      allocas_from_def, allocas_below_fmp_def] >> metis_tac[]
QED
