Theory bodyPtrPrecompileBuiltinsRecoveryContinuation
Ancestors bodyPtrPrecompileBuiltinsSuffixPaths
          bodyPtrPrecompileBuiltinsSuffixGhost bodyPtrPrecompileBuiltinsLoad
          bodyPtrPrecompileBuiltinsCompilerStages exprSimPrecompiles
          exprLoweringProps context emitHelper compileEnv venomInst list

Theorem computed_load_suffix_parts:
  comp_bind
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
        emit_void ASSERT [success]; return op od)
    (\out. emit_op MLOAD [out]) sm = (res,sb) ==>
  ?sl.
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
        emit_void ASSERT [success]; return op od) sm = (op,sl) /\
    emit_op MLOAD [op] sl = (res,sb) /\
    sl.cs_next_var = sm.cs_next_var + 2 /\ sl.cs_next_id = sm.cs_next_id + 3 /\
    res = Var (STRING #"%" (toString sl.cs_next_var)) /\
    emitted_insts sl sb =
      [mk_inst sl.cs_next_id MLOAD [op] [STRING #"%" (toString sl.cs_next_var)]] /\
    emitted_insts sm sb = emitted_insts sm sl ++ emitted_insts sl sb
Proof
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op MLOAD [_] sl = (res,sb)` >>
  drule computed_suffix_shape >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op_local >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  simp[] >> mp_tac (Q.SPECL [`sm`,`sl`,`sb`] emitted_insts_append) >> simp[]
QED

Theorem computed_load_suffix_oracle_failure_path:
  comp_bind
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit target; Var src; Lit insz; Var dst; Lit outsz];
        emit_void ASSERT [success]; return (Var dst) od)
    (\out. emit_op MLOAD [out]) sm = (res,sb) /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s target 0w wi insz T) /\
  ptr_covers G tn src s (w2n insz) /\ ptr_covers G tn dst s (w2n outsz) /\
  (!i. w2n wi <= i /\ i < w2n wi + w2n insz ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  (s.vs_outcomes = [] \/ ?co rest. s.vs_outcomes = co::rest /\ ~co.co_success) ==>
  ?t n j G' tn'.
    run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort t /\
    gas_path_ptr D lo ctx fn PG G tn s n G' tn'
      (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  strip_tac >> drule computed_load_suffix_parts >> strip_tac >>
  `isPREFIX (emitted_insts sm sl) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  drule_all computed_emitted_suffix_paths >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `?t. run_inst_seq (emitted_insts sm sl) s = Abort Revert_abort t` by
    (qpat_assum `_ sm = (Var dst,sl)`
       (mp_then Any mp_tac computed_suffix_oracle_failure) >>
     disch_then (qspecl_then [`wo`,`wi`,`s`] mp_tac) >> simp[]) >>
  `?n j. gas_path_ptr D lo ctx fn PG G tn s n G' tn'
    (Abort Revert_abort (t with vs_inst_idx := j))` by metis_tac[] >>
  qexistsl [`t`,`n`,`j`,`G'`,`tn'`] >> simp[] >>
  `!u. run_inst_seq (emitted_insts sm sl) s <> OK u` by simp[] >>
  drule run_inst_seq_append_err >> simp[]
QED
