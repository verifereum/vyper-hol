(* Destination-offset MUL followed by a covered root-offset ADD. *)
Theory exprPtrUnwrapDestinationSegment
Ancestors
  exprPtrUnwrapScalarSegments exprPtrUnwrapOffsetSegment exprPtrUnwrapSeq
  exprPtrUnwrapFrames ghostPcTransportPtr slotCopyExecution fragGasSeqPtr
  fragExec bodyPtrDefs ptrDiscipline ptrSafeRun venomExecSemantics venomInst
  venomState finite_map exprLoweringProps

Theorem copy_destination_segment:
  eval_operand counter s = SOME k /\ op_taint tn counter = {} /\
  k * 32w = n2w off /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s capacity /\ root <> tmp /\ root <> out /\
  off < capacity /\ off + n <= capacity /\
  w2n a + off < dimword(:256) /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id MUL [counter;Lit 32w] [tmp];
      mk_inst aid ADD [Var root;Var tmp] [out]] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id MUL [counter;Lit 32w] [tmp];
       mk_inst aid ADD [Var root;Var tmp] [out]] s Gf tnf /\
    t = update_var out (a + n2w off) (update_var tmp (n2w off) s) /\
    ptr_covers Gf tnf out t n /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!p. p <> tmp /\ p <> out ==>
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p c. p <> tmp /\ p <> out /\ ptr_covers G tn p s c ==>
      ptr_covers Gf tnf p t c)
Proof
  strip_tac >>
  mp_tac (Q.INST [`opc` |-> `MUL`, `left` |-> `counter`,
    `right` |-> `Lit 32w`, `x` |-> `k`, `y` |-> `32w`]
    (SPEC_ALL copy_arith_segment)) >>
  (impl_tac >- simp[eval_operand_def, op_taint_def]) >>
  disch_then strip_assume_tac >>
  rename1 `inst_seq_ptr D lo ctx fn PG G tn _ s Gm tnm` >>
  qabbrev_tac `u = update_var tmp (n2w off) s` >>
  qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_var root v = SOME a /\ eval_operand (Var tmp) v = SOME (n2w off) /\
   ptr_covers Gm tnm root v capacity /\ allocas_from lo v /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
    (fs[Abbr `v`, Abbr `u`, lookup_var_def, eval_operand_def,
        update_var_def, FLOOKUP_UPDATE, ptr_covers_inst_idx,
        allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`offset` |-> `Var tmp`, `id` |-> `aid`,
    `s` |-> `v`, `G` |-> `Gm`, `tn` |-> `tnm`]
    (SPEC_ALL copy_offset_segment)) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  rename1 `inst_seq_ptr D lo ctx fn PG Gm tnm _ v Gf tnf` >>
  qexistsl_tac [`Gf`, `tnf`, `update_var out (a+n2w off) u`] >>
  conj_tac
  >- (qpat_assum `lookup_var root s = SOME a`
        (assume_tac o REWRITE_RULE [lookup_var_def]) >>
      simp[Abbr `u`, run_inst_seq_def, step_inst_base_def, mk_inst_def,
           exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def,
           FLOOKUP_UPDATE]) >>
  conj_tac
  >- (irule inst_seq_ptr_cons_compose >>
      conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl_tac [`Gm`, `u`, `tnm`] >>
      gvs[Abbr `v`, Abbr `u`, mk_inst_def, is_terminator_def]) >>
  gvs[Abbr `v`, Abbr `u`, copy_update_inst_idx, ptr_covers_inst_idx] >>
  metis_tac[]
QED
