(* Joint storage-copy control segments, retaining the list and jump at
   the very same successor as the invariant and ghost post. *)
Theory storageCopyControlRun
Ancestors
  fragGasCopyLoop fragCopyInitPhysical fragGasOrigin gasEvents
  exprLoweringProps venomExecSemantics venomExecProofs venomInst arithmetic list

Theorem storage_copy_init_origin_run:
  MEM cv ds /\ dst <> cv /\ (!x. src = Var x ==> x <> cv) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  n < 2**256 /\ b + 32*n < 2**256 /\ b + 32*n <= s.vs_alloca_next /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id ASSIGN [Lit 0w] [cv]; mk_inst (id+1) JMP [Label hdr] []] ==>
  !loc D explicit PG. ?t G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
    (toplevel_copy_inv cv ds dst src loc a b n s G tn 0 G1 tn1 t /\
     allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)) /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    ?raw mid.
      isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]] (DROP s.vs_inst_idx bb.bb_instructions) /\
      run_inst_seq [mk_inst id ASSIGN [Lit 0w] [cv]] s = OK raw /\
      mid = raw with vs_inst_idx := s.vs_inst_idx + 1 /\
      mid.vs_current_bb = s.vs_current_bb /\ ~mid.vs_halted /\
      get_instruction bb mid.vs_inst_idx = SOME (mk_inst (id+1) JMP [Label hdr] []) /\
      gas_origin_edge F explicit ctx func mid [] (OK t)
Proof
  rpt strip_tac >>
  drule_all storage_copy_init_physical >>
  disch_then (qspecl_then [`loc`,`D`,`explicit`,`PG`]
    (qx_choosel_then [`t`,`G1`,`tn1`] strip_assume_tac)) >>
  qexistsl_tac [`t`,`G1`,`tn1`] >>
  rpt (conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qexistsl_tac [`u`,`mid`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem storage_copy_header_origin_run:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  cv <> tv /\ dst <> tv /\ (!x. src = Var x ==> x <> tv) /\ MEM tv ds /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv];
    mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  !D explicit PG. ?r G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK r,G1,tn1) /\
    (toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G1 tn1 r /\
     allocas_from lo r /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r)) /\
    ~r.vs_halted /\ r.vs_inst_idx = 0 /\
    r.vs_current_bb = (if k=n then exit_lbl else body_lbl) /\
    ?raw mid.
      isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]] (DROP s.vs_inst_idx bb.bb_instructions) /\
      run_inst_seq [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]] s = OK raw /\
      mid = raw with vs_inst_idx := s.vs_inst_idx + 1 /\
      mid.vs_current_bb = s.vs_current_bb /\ ~mid.vs_halted /\
      get_instruction bb mid.vs_inst_idx = SOME
        (mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []) /\
      gas_origin_edge F explicit ctx func mid [] (OK r)
Proof
  rpt strip_tac >>
  drule_all storage_copy_header_origin_ptr_run >>
  disch_then (qspecl_then [`D`,`explicit`,`PG`]
    (qx_choosel_then [`r`,`G1`,`tn1`] strip_assume_tac)) >>
  `gas_origin_edge F explicit ctx func t [] (OK r)` by
    (qpat_x_assum `t = _ with vs_inst_idx := _` kall_tac >>
     simp[gas_origin_edge_def] >>
     qexistsl_tac [`0`,`mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []`] >>
     fs[step_inst_non_invoke, gas_events_step_def, mk_inst_def, is_terminator_def] >>
     metis_tac[]) >>
  `isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]]
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (_::_::_) _` mp_tac >>
     Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> simp[]) >>
  qexistsl_tac [`r`,`G1`,`tn1`] >>
  rpt (conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qexistsl_tac [`u`,`t`] >> rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE asm_rewrite_tac[GSYM ADD1])
QED
