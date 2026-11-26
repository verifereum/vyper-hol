Theory bodyECArithHeadRunMods
Ancestors
  bodyPtrPrecompileBuiltinsSuffixPaths exprSimPrecompiles
  builtinIntClamp venomExecSemantics venomInst venomState
  compileEnv exprLoweringProps list rich_list venomCallOracleDefs extCallOracle

Theorem ec_head_assert_failure_bit[local]:
  step_inst_base gi u = OK sg /\ step_inst_base ci sg = OK sc /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  run_inst_seq [gi;ci;ai] u = Abort Revert_abort bad ==>
  eval_operand (Var cv) sc = SOME 0w
Proof
  strip_tac >>
  `step_inst_base ai sc = Abort Revert_abort bad` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  Cases_on `eval_operand (Var cv) sc` >>
  gvs[clamp_assert_step, AllCaseEqs()]
QED

Theorem ec_arith_head_run_mods:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit addr; Var src; Lit an; Var dst; Lit 64w];
      emit_void ASSERT [success]; return (Var dst) od) sm = (res,sb) /\
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit 64w] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\ emitted_insts sm sb = [gi;ci;ai] /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\ src <> gv /\ dst <> gv /\
  eval_operand (Var src) u = SOME wi /\ eval_operand (Var dst) u = SOME wo /\
  precompile_result (venom_call_request u addr 0w wi an T).cr_target
    (venom_call_request u addr 0w wi an T).cr_data =
    SOME (OPTION_MAP (\(rx,ry). word_to_bytes (n2w rx:bytes32) T ++
      word_to_bytes (n2w ry:bytes32) T) point_result) /\
  ptr_covers Gu tnu src u (w2n an) /\ ptr_covers Gu tnu dst u (w2n (64w:256 word)) /\
  (!i. w2n wi <= i /\ i < w2n wi + w2n an ==> i NOTIN tnu.t_mem) /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  tnu.t_stor SUBSET D.d_stor u.vs_call_ctx.cc_address
    (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
  tnu.t_trans SUBSET D.d_trans u.vs_call_ctx.cc_address
    (u.vs_transient u.vs_call_ctx.cc_address) /\
  ~u.vs_halted /\ lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [gi;ci;ai] (DROP u.vs_inst_idx bb.bb_instructions) /\
  u.vs_outcomes <> [] ==>
  ?sg sc. step_inst_base gi u = OK sg /\ step_inst_base ci sg = OK sc /\
    ((?rx ry co rest q. point_result = SOME (rx,ry) /\
        u.vs_outcomes = co::rest /\ co.co_success /\ run_inst_seq [gi;ci;ai] u = OK q) \/
     (eval_operand (Var cv) sc = SOME 0w /\
        ~(?rx ry co rest. point_result = SOME (rx,ry) /\
           u.vs_outcomes = co::rest /\ co.co_success)))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `computed_precompile (venom_call_request u addr 0w wi an T)` by
    (qpat_assum `precompile_result _ _ = SOME _` mp_tac >>
     simp[NoAsms, computed_precompile_def, venom_call_request_def]) >>
  `?sg sc. step_inst_base gi u = OK sg /\ step_inst_base ci sg = OK sc` by
    (`isPREFIX (emitted_insts sm sb) (DROP u.vs_inst_idx bb.bb_instructions)` by
       (qpat_assum `emitted_insts sm sb = _` (pure_rewrite_tac o single) >>
        first_assum ACCEPT_TAC) >>
     drule_all computed_emitted_suffix_paths >>
     disch_then (qspec_then `PG` (qx_choose_then `sg` (qx_choose_then `sc` strip_assume_tac))) >>
     qexistsl [`sg`, `sc`] >>
     gvs[]) >>
  rename [`step_inst_base gi u = OK sg`, `step_inst_base ci sg = OK sc`] >>
  qexistsl [`sg`, `sc`] >> simp[] >>
  Cases_on `?rx ry co rest. point_result = SOME (rx,ry) /\
    u.vs_outcomes = co::rest /\ co.co_success`
  >- (disj1_tac >> pop_assum strip_assume_tac >>
      qexistsl [`rx`,`ry`,`co`,`rest`] >> simp[] >>
      qpat_assum `_ sm = (_,sb)` (mp_then Any mp_tac computed_suffix_success) >>
      rename [`point_result = SOME (rx,ry)`, `u.vs_outcomes = co::rest`] >>
      disch_then (qspecl_then [`wo`,`wi`,`u`,
        `word_to_bytes (n2w rx:bytes32) T ++ word_to_bytes (n2w ry:bytes32) T`] mp_tac) >>
      simp[]) >>
  disj2_tac >> (reverse conj_tac >-
    (qpat_assum `~(?rx ry co rest. _)` mp_tac >> simp[NoAsms])) >>
  `?bad. run_inst_seq [gi;ci;ai] u = Abort Revert_abort bad` by
    (Cases_on `point_result = NONE`
     >- (qpat_assum `_ sm = (_,sb)` (mp_then Any mp_tac computed_suffix_failure) >>
         disch_then (qspecl_then [`wo`,`wi`,`u`] mp_tac o SRULE []) >> simp[]) >>
     `?co rest. u.vs_outcomes = co::rest /\ ~co.co_success` by
       (Cases_on `point_result` >> Cases_on `u.vs_outcomes` >> gvs[] >>
        rename1 `!rx ry. xy = (rx,ry) ==> _` >>
        qpat_x_assum `!rx ry. xy = (rx,ry) ==> _`
          (qspecl_then [`FST xy`, `SND xy`] mp_tac) >> simp[]) >>
     qpat_assum `_ sm = (_,sb)` (mp_then Any mp_tac computed_suffix_oracle_failure) >>
     disch_then (qspecl_then [`wo`,`wi`,`u`] mp_tac o SRULE []) >> simp[]) >>
  drule_all ec_head_assert_failure_bit >> simp[]
QED
