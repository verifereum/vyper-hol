(* The generated GAS is observed internally; with no oracle entry the
   following STATICCALL aborts at its own cursor. *)
Theory bodyECRecoverEmptyExitMods
Ancestors
  bodyFullBuiltinPrecompileSuffixAbort exprSimPrecompiles exprSimDefs exprSimHash
  gasOutcomeFullMods gasSummary fragGasOriginPtr fragGasSeqAbort fragExec
  createSizeExit
  venomInstProofs venomExecSemantics venomInst venomState finite_map
  rich_list words vyperStorageFootprint vyperInterpreter vyperState
Libs
  monadsyntax

Theorem ecrecover_empty_exit_mods:
  let source = \vs' ee.
    case builtin_result cx ee.accounts ann ECRecover tys vs' of
      INR exc => (INR exc,ee)
    | INL w => (do precompile_call_success ECRecover vs'; return w od) ee
  in
  builtin_result cx mid.accounts ann ECRecover tys vs = INL w /\
  mid.outcomes = SOME sbuf.vs_outcomes /\ sbuf.vs_outcomes = [] /\
  storage_trace_domain cx st0 mid.storage_trace /\
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit 1w; Var src; Lit 128w; Var dst; Lit 32w] [cv] /\
  src <> gv /\ dst <> gv /\
  eval_operand (Var src) sbuf = SOME wi /\
  eval_operand (Var dst) sbuf = SOME wo /\
  w2n wi + 128 <= sbuf.vs_alloca_next /\
  w2n wo + 32 <= sbuf.vs_alloca_next /\
  ~sbuf.vs_halted /\
  lookup_block sbuf.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [gi;ci] (DROP sbuf.vs_inst_idx bb.bb_instructions) /\
  (func.fn_name,id) NOTIN explicit /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp sbuf) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    ptr_covers G tn src sbuf 128 /\ ptr_covers G tn dst sbuf 32 /\
    (!i. w2n wi <= i /\ i < w2n wi + 128 ==> i NOTIN tn.t_mem) /\
    allocas_from lo sbuf /\
    tn.t_stor SUBSET (DF H).d_stor sbuf.vs_call_ctx.cc_address
      (sbuf.vs_accounts sbuf.vs_call_ctx.cc_address).storage /\
    tn.t_trans SUBSET (DF H).d_trans sbuf.vs_call_ctx.cc_address
      (sbuf.vs_transient sbuf.vs_call_ctx.cc_address)) /\
  MEM func ctx.ctx_functions ==>
  ?u bad Ga tna.
    step_inst_base gi sbuf = OK u /\
    step_inst_base ci u = Abort ExHalt_abort (halt_state (set_returndata [] u)) /\
    bad = (halt_state (set_returndata [] u) with vs_inst_idx := SUC sbuf.vs_inst_idx) /\
    Ga = step_prov PG G gi u /\ tna = step_taint gi sbuf u tn /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (sbuf,G,tn) [F] (Abort ExHalt_abort bad,Ga,tna)) /\
    (!tail. source vs (mid with gas_obs :=
                         gas_explicit [F] sbuf.vs_gas_readings ++ tail) =
       (INR (Error (RuntimeError "precompile failed")),mid with gas_obs := tail)) /\
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 (source vs)
      (mid,sbuf,G,tn) Q
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `u = update_var gv (HD (sbuf.vs_gas_readings ++ [0w]))
    (sbuf with vs_gas_readings := DROP 1 sbuf.vs_gas_readings)` >>
  `step_inst_base gi sbuf = OK u` by simp[Abbr `u`,step_GAS] >>
  `step_inst_base ci u = Abort ExHalt_abort (halt_state (set_returndata [] u))` by
    (simp[Abbr `u`, mk_inst_def, step_inst_base_def, exec_ext_call_def,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     gvs[eval_operand_def, lookup_var_def]) >>
  qabbrev_tac `bad = halt_state (set_returndata [] u)
    with vs_inst_idx := SUC sbuf.vs_inst_idx` >>
  `lookup_block bad.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb bad.vs_inst_idx = SOME ci` by
    (simp[NoAsms, Abbr `bad`, Abbr `u`, halt_state_def, set_returndata_def,
          update_var_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     drule instruction_prefix_cursor >> strip_tac >>
     drule instruction_prefix_cursor >> simp[]) >>
  `ALL_DISTINCT (FLAT (MAP fn_labels ctx.ctx_functions)) ==>
   ~oversized_create_abort ctx (Abort ExHalt_abort bad)` by
    (strip_tac >> irule oversized_create_abort_non_create_cursor >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`bb`,`func`,`ci`] >> simp[mk_inst_def]) >>
  qabbrev_tac `Ga = step_prov PG G gi u` >>
  qabbrev_tac `tna = step_taint gi sbuf u tn` >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
       (sbuf,G,tn) [F] (Abort ExHalt_abort bad,Ga,tna)` by
    (simp[NoAsms, Abbr `bad`, Abbr `Ga`, Abbr `tna`] >>
     MATCH_MP_TAC (Q.INST [`trace` |-> `mid.storage_trace`,
       `addr` |-> `1w`, `an` |-> `128w`, `rn` |-> `32w`]
       precompile_suffix_call_abort_full_family) >>
     simp[wordsTheory.dimword_def] >>
     gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ptr_covers _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `gas_explicit [F] sbuf.vs_gas_readings = []` by
    (Cases_on `sbuf.vs_gas_readings` >> simp[gas_explicit_cons]) >>
  qexistsl_tac [`u`,`bad`,`Ga`,`tna`] >> simp[] >>
  conj_tac
  >- simp[ignore_bind_def, bind_def, ecrecover_source_outcome_step] >>
  rewrite_tac[gas_outcome_full_mods_def] >>
  qexists_tac `[F]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (Error (RuntimeError "precompile failed"))`, `mid`,
    `Abort ExHalt_abort bad`, `Ga`, `tna`] >>
  simp[ignore_bind_def, bind_def, ecrecover_source_outcome_step,
    exit_result_def, expr_exit_def, halt_exit_def] >>
  Cases_on `ALL_DISTINCT (FLAT (MAP fn_labels ctx.ctx_functions))` >> simp[]
QED
