(* A zero success bit on the reached EC arithmetic packet reverts at ASSERT. *)
Theory bodyECArithAssertExitMods
Ancestors
  bodyFullBuiltinPrecompileSuffixAbort exprSimECArith exprSimDefs
  gasOutcomeFullMods gasSummary fragGasOriginPtr fragExec
  venomInst venomState rich_list vyperStorageFootprint vyperInterpreter
  vyperContext vyperState vyperValue

Theorem ec_arith_assert_exit_mods:
  (bt = ECAdd \/ bt = ECMul) /\
  addr = (if bt = ECAdd then 6w else 7w) /\
  an = (if bt = ECAdd then 128w else 96w) /\
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit 64w] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  src <> gv /\ dst <> gv /\
  eval_operand (Var src) u = SOME wi /\ eval_operand (Var dst) u = SOME wo /\
  w2n wi + w2n an <= u.vs_alloca_next /\
  w2n wo + 64 <= u.vs_alloca_next /\
  step_inst_base gi u = OK sg /\ step_inst_base ci sg = OK sc /\
  eval_operand (Var cv) sc = SOME 0w /\
  ~u.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [gi;ci;ai] (DROP u.vs_inst_idx bb.bb_instructions) /\
  (func.fn_name,id) NOTIN explicit /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (t2,G2,tn2) [] (OK u,Gu,tnu) /\
    ptr_covers Gu tnu src u (w2n an) /\ ptr_covers Gu tnu dst u 64 /\
    allocas_from lo u /\
    (!i. w2n wi <= i /\ i < w2n wi + w2n an ==> i NOTIN tnu.t_mem) /\
    tnu.t_stor SUBSET (DF H).d_stor u.vs_call_ctx.cc_address
      (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
    tnu.t_trans SUBSET (DF H).d_trans u.vs_call_ctx.cc_address
      (u.vs_transient u.vs_call_ctx.cc_address)) /\
  ec_source_tail cx a bt tys [v1;v2] es2 =
    (INR (Error (RuntimeError msg)),source_end) /\
  storage_trace_domain cx st0 source_end.storage_trace /\
  (!H. valid_horizon cx st0 H source_end.storage_trace ==>
       valid_horizon cx st0 H es2.storage_trace) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (ec_source_tail cx a bt tys [v1;v2]) (es2,t2,G2,tn2) Q
    (\H rr ee gt r. expr_exit rr r /\ halt_exit H cx ee rr r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `?bad Ga tna.
     bad = (revert_state (set_returndata [] sc)
       with vs_inst_idx := u.vs_inst_idx + 2) /\
     Ga = step_prov PG (step_prov PG Gu gi sg) ci sc /\
     tna = step_taint ci sg sc (step_taint gi u sg tnu) /\
     (!H. valid_horizon cx st0 H es2.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (u,Gu,tnu) [F] (Abort Revert_abort bad,Ga,tna))` by
    (irule precompile_suffix_abort_full_family >>
     conj_tac >- simp[] >> conj_tac >- simp[] >>
     qexistsl_tac [`addr`,`ai`,`an`,`bb`,`ci`,`cv`,`dst`,`gi`,`gv`,`id`,
                  `64w`,`src`,`sg`,`wi`,`wo`] >>
     simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
     conj_tac >-
       (gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
          (drule_then strip_assume_tac) >> gvs[]) >>
     Cases_on `bt = ECAdd` >> simp[]) >>
  `gas_explicit [F] t2.vs_gas_readings = []` by
    (Cases_on `t2.vs_gas_readings` >> simp[gas_explicit_cons]) >>
  rewrite_tac[gas_outcome_full_mods_def] >>
  qexists_tac `[F]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`, `source_end`,
    `Abort Revert_abort bad`, `Ga`, `tna`] >>
  simp[exit_result_def, expr_exit_def, halt_exit_def] >>
  conj_tac >- (gen_tac >> irule ec_source_tail_gas_obs >> simp[]) >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es2.storage_trace` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [F] _`
    (drule_then assume_tac) >>
  qpat_assum `gas_origin_ptr_path _ (t2,G2,tn2) [] _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  simp[NoAsms] >> disch_then drule >> gvs[]
QED
