Theory bodyPtrPrecompileBuiltinsRecoveryContinuation
Ancestors bodyPtrPrecompileBuiltinsSuffixPaths
          bodyPtrPrecompileBuiltinsSuffixGhost bodyPtrPrecompileBuiltinsLoad
          bodyPtrPrecompileBuiltinsCompilerStages exprSimPrecompiles
          exprLoweringProps exprSimHash context emitHelper compileEnv venomInst list
          bodyPtrPrecompileBuiltinsSuffixReady bodyPtrPrecompileBuiltinsAppendLoad

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

Theorem computed_load_suffix_clean_path:
  comp_bind
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit target; Var src; Lit insz; Var dst; Lit 32w];
        emit_void ASSERT [success]; return (Var dst) od)
    (\out. emit_op MLOAD [out]) sm = (res,sb) /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s target 0w wi insz T) /\
  ptr_covers G tn src s (w2n insz) /\ ptr_covers G tn dst s 32 /\
  (!i. w2n wi <= i /\ i < w2n wi + w2n insz ==> i NOTIN tn.t_mem) /\
  (!i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME (SOME data) /\
  (?co rest. s.vs_outcomes = co::rest /\ co.co_success) ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sm sb) s = OK t /\
    gas_path_ptr D lo ctx fn PG G tn s 1 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 4)) /\
    op_prov G' res = NONE /\ op_taint tn' res = {} /\
    eval_operand res t = SOME (mem_word_at (w2n wo)
      (write_memory_with_expansion (w2n wo) (TAKE 32 data) s).vs_memory) /\
    ?sl q u v G1 tn1 y.
      (do gas <- emit_op GAS [];
          success <- emit_op STATICCALL
            [gas; Lit target; Var src; Lit insz; Var dst; Lit 32w];
          emit_void ASSERT [success]; return (Var dst) od) sm = (Var dst,sl) /\
      emit_op MLOAD [Var dst] sl = (res,sb) /\ res = Var y /\
      run_inst_seq (emitted_insts sm sl) s = OK q /\
      step_inst_base (EL 0 (emitted_insts sm sl)) s = OK u /\
      step_inst_base (EL 1 (emitted_insts sm sl)) u = OK v /\
      G1 = step_prov PG (step_prov PG G (EL 0 (emitted_insts sm sl)) u)
        (EL 1 (emitted_insts sm sl)) v /\
      tn1 = step_taint (EL 1 (emitted_insts sm sl)) u v
        (step_taint (EL 0 (emitted_insts sm sl)) s u tn) /\
      t = update_var y (mload (w2n wo) q) q /\
      G' = step_prov PG G1 (mk_inst sl.cs_next_id MLOAD [Var dst] [y])
        (t with vs_inst_idx := s.vs_inst_idx + 3) /\
      tn' = step_taint (mk_inst sl.cs_next_id MLOAD [Var dst] [y])
        (q with vs_inst_idx := s.vs_inst_idx + 3)
        (t with vs_inst_idx := s.vs_inst_idx + 3) tn1
Proof
  strip_tac >> drule computed_load_suffix_parts >> strip_tac >>
  `isPREFIX (emitted_insts sm sl) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `ptr_covers G tn dst s (w2n (32w:256 word))` by simp[wordsTheory.dimword_def] >>
  drule_all computed_emitted_suffix_paths >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `?q. run_inst_seq (emitted_insts sm sl) s = OK q` by
    (qpat_assum `_ sm = (Var dst,sl)`
       (mp_then Any mp_tac computed_suffix_success) >>
     disch_then (qspecl_then [`wo`,`wi`,`s`,`data`] mp_tac) >> simp[]) >>
  `eval_operand (Var dst) q = SOME wo /\
   q.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE 32 data) s).vs_memory /\
   q.vs_allocas = s.vs_allocas /\
   (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s)` by
    (qpat_assum `_ sm = (Var dst,sl)`
       (mp_then Any mp_tac computed_suffix_output) >>
     disch_then (drule_all o SRULE []) >>
     simp[wordsTheory.dimword_def]) >>
  `ptr_covers G' tn' dst q 32 /\ allocas_from lo q /\
   (!i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn'.t_mem) /\
   q.vs_halted = s.vs_halted /\ q.vs_current_bb = s.vs_current_bb /\
   q.vs_inst_idx = s.vs_inst_idx` by
    (irule computed_suffix_load_ready >> metis_tac[]) >>
  `LENGTH (emitted_insts sm sl) = 3` by
    (drule computed_suffix_shape >> simp[]) >>
  `gas_path_ptr D lo ctx fn PG G tn s 1 G' tn'
    (OK (q with vs_inst_idx := s.vs_inst_idx+3))` by metis_tac[] >>
  `~q.vs_halted` by simp[] >>
  `isPREFIX (emitted_insts sm sl ++
     [mk_inst sl.cs_next_id MLOAD [Var dst] [STRING #"%" (toString sl.cs_next_var)]])
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule_all appended_clean_mload_path >> strip_tac >>
  suspend "endpoints"
QED

Resume computed_load_suffix_clean_path[endpoints]:
  qexistsl [`t`,`G2`,`tn2`] >> conj_tac
  >- (qpat_x_assum `run_inst_seq (_ ++ _) s = OK t` mp_tac >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ G2 tn2 _` mp_tac >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `op_prov G2 _ = NONE` mp_tac >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `op_taint tn2 _ = {}` mp_tac >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `eval_operand _ t = _` mp_tac >> simp[]) >>
  qexists `sl` >> qexistsl [`q`,`u`,`v`] >>
  qexistsl [`G'`,`tn'`,`STRING #"%" (toString sl.cs_next_var)`] >> simp[]
QED

Finalise computed_load_suffix_clean_path

