(* The nonempty, unsuccessful oracle case reaches ASSERT, not MLOAD. *)
Theory bodyECRecoverAssertExitMods
Ancestors
  bodyFullBuiltinPrecompileSuffixAbort bodyPtrPrecompileBuiltinsRuntime
  exprSimPrecompiles exprSimHash exprSimDefs
  fragGasOriginPtr fragExec ptrDiscipline instMemFrontier gasCount
  venomInstProofs venomExecSemantics venomInst venomState venomCallOracleDefs
  extCallOracle vyperCallOutcomeProps vyperStorageFootprint vyperState
  vyperInterpreter vyperValue words finite_map list rich_list
  exprLoweringProps gasSummary gasOutcomeFullMods
Libs
  monadsyntax

Theorem ecrecover_failed_prefix[local]:
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv;Lit 1w;Var src;Lit 128w;Var dst;Lit 32w] [cv] /\
  src <> gv /\ dst <> gv /\
  eval_operand (Var src) s = SOME wi /\
  eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s 1w 0w wi 128w T) /\
  s.vs_outcomes = co::rest /\ ~co.co_success ==>
  ?u v. step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
        eval_operand (Var cv) v = SOME 0w
Proof
  strip_tac >>
  `?v. run_inst_seq [gi;ci] s = OK v` by
    (simp[] >> irule computed_call_prefix >> simp[] >> metis_tac[]) >>
  qabbrev_tac `u = update_var gv (HD (s.vs_gas_readings ++ [0w]))
    (s with vs_gas_readings := DROP 1 s.vs_gas_readings)` >>
  `step_inst_base gi s = OK u` by simp[step_GAS, Abbr `u`] >>
  `step_inst_base ci u = OK v` by
    (qpat_x_assum `run_inst_seq [gi;ci] s = OK v` mp_tac >>
     qpat_x_assum `ci = _` kall_tac >>
     simp[run_inst_seq_def] >>
     Cases_on `step_inst_base ci u` >> simp[]) >>
  qexistsl_tac [`u`,`v`] >> simp[] >>
  `u.vs_outcomes = co::rest /\
   venom_call_request u 1w 0w wi 128w T =
     venom_call_request s 1w 0w wi 128w T` by
    simp[Abbr `u`, update_var_def, venom_call_request_def, read_memory_def] >>
  `eval_operand (Var src) u = SOME wi /\
   eval_operand (Var dst) u = SOME wo /\
   eval_operand (Var gv) u = SOME (HD (s.vs_gas_readings ++ [0w]))` by
    gvs[Abbr `u`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `~(FST (take_outcome (venom_call_request u 1w 0w wi 128w T)
                         u.vs_outcomes)).co_success` by
    simp[take_outcome_computed_success] >>
  qpat_x_assum `step_inst_base ci u = OK v` mp_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  simp[eval_operand_def] >>
  dep_rewrite.DEP_REWRITE_TAC[Q.INST [`out` |-> `cv`] computed_static_exec_eq] >>
  simp[] >>
  disch_then (SUBST1_TAC o SYM) >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ecrecover_assert_exit_mods:
  let source = \vs ee.
    case builtin_result cx ee.accounts ann ECRecover tys vs of
      INR exc => (INR exc,ee)
    | INL w => (do precompile_call_success ECRecover vs; return w od) ee
  in
  builtin_result cx mid.accounts ann ECRecover tys vals = INL w /\
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv;Lit 1w;Var src;Lit 128w;Var dst;Lit 32w] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  src <> gv /\ dst <> gv /\
  eval_operand (Var src) s = SOME wi /\
  eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s 1w 0w wi 128w T) /\
  s.vs_outcomes = co::rest /\ ~co.co_success /\
  mid.outcomes = SOME s.vs_outcomes /\
  w2n wi + 128 <= s.vs_alloca_next /\ w2n wo + 32 <= s.vs_alloca_next /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [gi;ci;ai] (DROP s.vs_inst_idx bb.bb_instructions) /\
  (func.fn_name,id) NOTIN explicit /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    ptr_covers G tn src s 128 /\ ptr_covers G tn dst s 32 /\
    (!i. w2n wi <= i /\ i < w2n wi + 128 ==> i NOTIN tn.t_mem) /\
    allocas_from lo s /\
    tn.t_stor SUBSET (DF H).d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
    tn.t_trans SUBSET (DF H).d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)) ==>
  ?u v t G' tn' after.
    step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
    eval_operand (Var cv) v = SOME 0w /\
    t = (revert_state (set_returndata [] v) with vs_inst_idx := s.vs_inst_idx + 2) /\
    G' = step_prov PG (step_prov PG G gi u) ci v /\
    tn' = step_taint ci u v (step_taint gi s u tn) /\
    after = SND (take_call_outcome NONE 1w (precompile_input ECRecover vals) NONE mid) /\
    storage_trace_domain cx st0 after.storage_trace /\
    (!tail. source vals (mid with gas_obs := gas_explicit [F] s.vs_gas_readings ++ tail) =
            (INR (Error (RuntimeError "precompile failed")), after with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H after.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [F] (Abort Revert_abort t,G',tn')) /\
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 (source vals)
      (mid,s,G,tn) Q
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  drule_all ecrecover_failed_prefix >> strip_tac >>
  qabbrev_tac `after = SND (take_call_outcome NONE 1w
    (precompile_input ECRecover vals) NONE mid)` >>
  qabbrev_tac `t = revert_state (set_returndata [] v)
    with vs_inst_idx := s.vs_inst_idx + 2` >>
  qabbrev_tac `G' = step_prov PG (step_prov PG G gi u) ci v` >>
  qabbrev_tac `tn' = step_taint ci u v (step_taint gi s u tn)` >>
  `!H. valid_horizon cx st0 H after.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
       (s,G,tn) [F] (Abort Revert_abort t,G',tn')` by
    (simp[Abbr `after`, Abbr `t`, Abbr `G'`, Abbr `tn'`] >>
     MATCH_MP_TAC (Q.INST [`trace` |-> `mid.storage_trace`,
       `addr` |-> `1w`, `an` |-> `128w`, `rn` |-> `32w`,
       `G2` |-> `step_prov PG (step_prov PG G gi u) ci v`,
       `tn2` |-> `step_taint ci u v (step_taint gi s u tn)`]
       (SIMP_RULE bool_ss [UNWIND_THM1] precompile_suffix_abort_full_family)) >>
     simp[wordsTheory.dimword_def] >>
     gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ptr_covers _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `storage_trace_domain cx st0 after.storage_trace` by
    fs[storage_trace_domain_def, Abbr `after`] >>
  `gas_explicit [F] s.vs_gas_readings = []` by
    (Cases_on `s.vs_gas_readings` >> simp[gas_explicit_cons]) >>
  qexistsl_tac [`u`,`v`,`t`,`G'`,`tn'`,`after`] >> simp[] >>
  conj_tac
  >- simp[ignore_bind_def, bind_def, ecrecover_source_outcome_step, Abbr `after`] >>
  rewrite_tac[gas_outcome_full_mods_def] >>
  qexists_tac `[F]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (Error (RuntimeError "precompile failed"))`, `after`,
    `Abort Revert_abort t`, `G'`, `tn'`] >>
  simp[ignore_bind_def, bind_def, ecrecover_source_outcome_step, Abbr `after`,
       exit_result_def, expr_exit_def, halt_exit_def]
QED
