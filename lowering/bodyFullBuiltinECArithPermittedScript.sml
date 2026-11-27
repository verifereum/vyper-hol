Theory bodyFullBuiltinECArithPermitted
Ancestors
  bodyFullBuiltinPrecompileSuffixSuccess bodyFullBuiltinPrecompileSuffixAbort
  bodyPtrPrecompileBuiltinsSuffixPaths bodyPtrPrecompileBuiltinsRuntime
  bodyPtrPrecompileBuiltinsArithmeticValue bodyPtrPrecompileBuiltinsSuffixGhost
  exprSimECArith exprSimAggregates exprSimPrecompiles exprSimProps exprLoweringProps exprSimWordArgs
  allocaHistoryFragment valueEncodingProofs venomCallOracleDefs venomExecSemantics
  venomInst venomState finite_map rich_list compileEnv vyperValue vyperState
  vyperInterpreter vyperContext fragGasOriginPtr gasOutcomeFull fragExec
  extCallOracle loweringStateRelDefs exprSimDefs byte valueEncoding
  valueEncodingDefs bodyFullGhostFrame bodySimFull loweringPosts
  vyperAST list vyperStorageFootprint exprSimOperands context
  gasOutcomeFullCompose gasSummary wordArgsPtr exprSimMemDefs vyperStorageTrace
  vyperCallOutcome vyperCallOutcomeProps
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

(* An aborting run with two normal prefix steps is an ASSERT failure. *)
Theorem ec_assert_failure_bit[local]:
  step_inst_base gi u = OK sg /\ step_inst_base ci sg = OK sc /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  run_inst_seq [gi;ci;ai] u = Abort Revert_abort bad ==>
  eval_operand (Var cv) sc = SOME 0w
Proof
  strip_tac >>
  `step_inst_base ai sc = Abort Revert_abort bad` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  Cases_on `eval_operand (Var cv) sc` >>
  gvs[builtinIntClampTheory.clamp_assert_step, AllCaseEqs()]
QED

(* The source result distinguishes an invalid point (before the oracle) from
   a valid point followed by an unsuccessful oracle head. *)
Theorem ec_permitted_source_result[local]:
  (bt = ECAdd \/ bt = ECMul) /\
  (if bt = ECAdd then evaluate_ecadd [v1;v2] else evaluate_ecmul [v1;v2]) =
    (case point_result of NONE => INR (RuntimeError
       (if bt = ECAdd then "ECAdd invalid point" else "ECMul invalid point"))
     | SOME xy => INL (mk_ec_result xy)) /\
  precompile_result (precompile_address bt) (precompile_input bt [v1;v2]) =
    SOME (OPTION_MAP (\(rx,ry). word_to_bytes (n2w rx:bytes32) T ++
      word_to_bytes (n2w ry:bytes32) T) point_result) /\
  es.outcomes = SOME u.vs_outcomes /\
  u.vs_outcomes <> [] ==>
  case point_result of NONE =>
    ec_source_tail cx a bt tys [v1;v2] es =
      (INR (Error (RuntimeError
         (if bt = ECAdd then "ECAdd invalid point" else "ECMul invalid point"))),es)
  | SOME xy =>
    ec_source_tail cx a bt tys [v1;v2] es =
      (if (HD u.vs_outcomes).co_success then INL (Value (mk_ec_result xy))
       else INR (Error (RuntimeError "precompile failed")),
       SND (take_call_outcome NONE (precompile_address bt) (precompile_input bt [v1;v2]) NONE es))
Proof
  strip_tac >> Cases_on `point_result` >> Cases_on `u.vs_outcomes` >>
  gvs[ec_source_tail_cases, builtin_result_def, evaluate_builtin_def]
QED

Theorem ec_permitted_suffix_run[local]:
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
        ~( ?rx ry co rest. point_result = SOME (rx,ry) /\
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
     disch_then (qspec_then `PG` (strip_assume_tac o SRULE [])) >>
     gvs[] >> metis_tac[]) >>
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
  disj2_tac >> (reverse conj_tac >- metis_tac[]) >>
  `?bad. run_inst_seq [gi;ci;ai] u = Abort Revert_abort bad` by
    (Cases_on `point_result = NONE`
     >- (qpat_assum `_ sm = (_,sb)` (mp_then Any mp_tac computed_suffix_failure) >>
         disch_then (qspecl_then [`wo`,`wi`,`u`] mp_tac o SRULE []) >> simp[]) >>
     `?co rest. u.vs_outcomes = co::rest /\ ~co.co_success` by
       (Cases_on `point_result` >> Cases_on `u.vs_outcomes` >> gvs[] >>
        metis_tac[pairTheory.PAIR]) >>
     qpat_assum `_ sm = (_,sb)` (mp_then Any mp_tac exprSimPrecompilesTheory.computed_suffix_oracle_failure) >>
     disch_then (qspecl_then [`wo`,`wi`,`u`] mp_tac o SRULE []) >> simp[]) >>
  drule_all ec_assert_failure_bit >> simp[]
QED

Theorem ec_arith_permitted_tail_full:
  (bt = ECAdd \/ bt = ECMul) /\
  a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  vv = StackValue a (Var dst) /\
  addr = (if bt = ECAdd then 6w else 7w) /\
  an = (if bt = ECAdd then 128w else 96w) /\
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit addr; Var src; Lit an; Var dst; Lit 64w];
      emit_void ASSERT [success]; return (Var dst) od) sm = (res,sb) /\
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit 64w] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\ emitted_insts sm sb = [gi;ci;ai] /\
  src <> gv /\ dst <> gv /\ dst <> cv /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
  s2.cs_next_var <= sm.cs_next_var /\ s2.cs_next_id <= sm.cs_next_id /\
  local_ptrs_reserved cenv sm /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (lo <> 0 ==> !z. cenv.ce_imm_alloca = SOME (Var z) ==> not_fresh_at sm z) /\
  ~u.vs_halted /\
  lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [gi;ci;ai] (DROP u.vs_inst_idx bb.bb_instructions) /\
  (func.fn_name,id) NOTIN gas_explicit_sites ctx shadow_ctx /\
  eval_operand (Var src) u = SOME wi /\ eval_operand (Var dst) u = SOME wo /\
  w2n wi + w2n an <= u.vs_alloca_next /\
  w2n wo + w2n (64w:256 word) <= u.vs_alloca_next /\ lo <= w2n wo /\
  u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func u /\ t2.vs_alloca_next <= u.vs_alloca_next /\
  pure_frame cenv func es2 s2 t2 u /\
  context$compile_alloc_buffer 64 out_alloc = (ob,sm) /\
  FLOOKUP u.vs_allocas out_alloc.cs_next_id = SOME (w2n wo,64) /\
  s2.cs_next_id <= out_alloc.cs_next_id /\
  MEM (mk_inst out_alloc.cs_next_id ALLOCA [Lit 64w] [dst]) (fn_insts func) /\
  precompile_input bt [v1;v2] = read_memory (w2n wi) (w2n an) u /\
  precompile_result (venom_call_request u addr 0w wi an T).cr_target
    (venom_call_request u addr 0w wi an T).cr_data =
    SOME (OPTION_MAP (\(rx,ry). word_to_bytes (n2w rx:bytes32) T ++
      word_to_bytes (n2w ry:bytes32) T) point_result) /\
  (if bt = ECAdd then evaluate_ecadd [v1;v2] else evaluate_ecmul [v1;v2]) =
    (case point_result of NONE => INR (RuntimeError
       (if bt = ECAdd then "ECAdd invalid point" else "ECMul invalid point"))
     | SOME xy => INL (mk_ec_result xy)) /\
  es2.outcomes = SOME u.vs_outcomes /\ es2.gas_obs = [] /\
  u.vs_outcomes <> [] /\
  storage_trace_domain cx st0 es2.storage_trace /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= s2.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es1.scopes = MAP FDOM es2.scopes /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t2,G2,tn2) [] (OK u,Gu,tnu) /\
    ghost_kept_at lo cenv es2 s2 G2 tn2 t2 Gu tnu /\
    wb_frame cenv es2 es2 s2 t2 u /\
    ghost_inv_at (DF H) lo d cenv cx es2 Gu tnu u /\
    stmt_state_rel H ctx func cenv cx es2 u /\ local_ptrs_rel func cenv es2.scopes u /\
    ptr_covers Gu tnu src u (w2n an) /\ ptr_covers Gu tnu dst u (w2n (64w:256 word)) /\
    allocas_from lo u /\
    tnu.t_stor SUBSET (DF H).d_stor u.vs_call_ctx.cc_address
      (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
    tnu.t_trans SUBSET (DF H).d_trans u.vs_call_ctx.cc_address
      (u.vs_transient u.vs_call_ctx.cc_address) /\
    (!i. w2n wi <= i /\ i < w2n wi + w2n an ==> i NOTIN tnu.t_mem) /\
    (!name b sz. local_region cenv es2.scopes u name b sz ==>
      regions_disjoint (w2n wo) (w2n (64w:256 word)) b sz) /\
    (!aid b sz. aid < s2.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint (w2n wo) (w2n (64w:256 word)) b sz) /\
    (cenv.ce_is_ctor ==> !name tv iv off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es2.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
      regions_disjoint (w2n wo) (w2n (64w:256 word)) off (type_memory_size tv))) /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
    valid_horizon cx st0 H es1.storage_trace /\ valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    expr_post H ctx func cenv cx e1 es sa s1 s0 es1 v1 x t1 /\
    s0.vs_alloca_next <= t1.vs_alloca_next /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
    expr_post H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2 /\
    t1.vs_alloca_next <= t2.vs_alloca_next /\
    ghost_kept_at lo cenv es1 s1 G1 tn1 t1 G2 tn2) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (ec_source_tail cx a bt [expr_type e1;expr_type e2] [v1;v2])
    (es2,t2,G2,tn2)
    (\H rr ee G tn t. ?tv. rr = INL tv /\
      vv_post H ctx func cenv cx (Builtin a bt [e1;e2]) es sa sb s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv (Builtin a bt [e1;e2]))
        (lowered_value_type cenv (Builtin a bt [e1;e2])) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv (Builtin a bt [e1;e2])) tv vv ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Builtin a bt [e1;e2])) /\
        ~is_bytestring_type (post_value_type cenv (Builtin a bt [e1;e2])) ==>
        vv_own cenv cx (post_value_type cenv (Builtin a bt [e1;e2])) sa sb ee tv vv t /\
        (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Builtin a bt [e1;e2])) = SOME rt /\
            eval_operand (vv_operand vv) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
      (!ty' op. vv = StackValue ty' op /\
        ~is_word_type (post_value_type cenv (Builtin a bt [e1;e2])) ==>
        ptr_buf_ok cenv (Builtin a bt [e1;e2]) op G t) /\
      (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (Builtin a bt [e1;e2]) p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H rr ee gt r. expr_exit rr r /\ halt_exit H cx ee rr r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_assum `storage_trace_domain _ _ _`
    (assume_tac o REWRITE_RULE [storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
    (drule_then strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx es2 u`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  mp_tac (Q.INST [`D` |-> `DF (storage_trace_horizon es2.storage_trace)`]
    ec_permitted_suffix_run) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `sg` (qx_choose_then `sc` strip_assume_tac)) >>
  `precompile_address bt = w2w addr` by
    (qpat_assum `bt = ECAdd \/ bt = ECMul` DISJ_CASES_TAC >>
     fs[precompile_address_def, wordsTheory.w2w_n2w, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:160)``]) >>
  `precompile_result (precompile_address bt) (precompile_input bt [v1;v2]) =
     SOME (OPTION_MAP (\(rx,ry). word_to_bytes (n2w rx:bytes32) T ++
       word_to_bytes (n2w ry:bytes32) T) point_result)` by
    (qpat_assum `precompile_address bt = w2w addr` (fn target =>
       qpat_assum `precompile_input bt [v1;v2] = _` (fn payload =>
         PURE_REWRITE_TAC [target,payload])) >>
     qpat_assum `precompile_result (_ : call_request).cr_target _ = _`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [venom_call_request_def])) >>
  qabbrev_tac `ee = SND (take_call_outcome NONE (w2w addr)
    (read_memory (w2n wi) (w2n an) u) NONE es2)` >>
  `storage_trace_domain cx st0 ee.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 es2.storage_trace` mp_tac >>
     simp[storage_trace_domain_def, Abbr `ee`]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace <=>
       valid_horizon cx st0 H es2.storage_trace` by simp[Abbr `ee`] >>
  `gas_explicit [F] t2.vs_gas_readings = []` by
    (Cases_on `t2.vs_gas_readings` >> simp[gas_explicit_cons]) >>~
    [`run_inst_seq [gi;ci;ai] u = OK _`] >- suspend "success" >>
  suspend "abort"
QED

Resume ec_arith_permitted_tail_full[abort]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.INST [`s` |-> `u`, `u` |-> `sg`, `v` |-> `sc`,
    `G` |-> `Gu`, `tn` |-> `tnu`,
    `G2` |-> `step_prov PG (step_prov PG Gu gi sg) ci sc`,
    `tn2` |-> `step_taint ci sg sc (step_taint gi u sg tnu)`,
    `rn` |-> `64w`, `trace` |-> `es2.storage_trace`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    precompile_suffix_abort_full_family) >>
  (impl_tac >- (conj_tac >- (Cases_on `bt = ECAdd` >>
     simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
    rpt conj_tac >> TRY (REFL_TAC ORELSE first_assum ACCEPT_TAC) >>
    gen_tac >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
      (drule_then strip_assume_tac) >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `bad` (qx_choose_then `Gout`
    (qx_choose_then `tnout` strip_assume_tac))) >>
  `?msg source_end. ec_source_tail cx a bt [expr_type e1;expr_type e2] [v1;v2] es2 =
      (INR (Error (RuntimeError msg)),source_end) /\
      storage_trace_domain cx st0 source_end.storage_trace /\
      (!H. valid_horizon cx st0 H source_end.storage_trace <=>
           valid_horizon cx st0 H es2.storage_trace)` by
    (mp_tac (Q.INST [`tys` |-> `[expr_type e1;expr_type e2]`, `es` |-> `es2`]
       ec_permitted_source_result) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     Cases_on `point_result` >- (simp[] >> metis_tac[]) >>
     namedCases_on `u.vs_outcomes` ["", "co rest"] >- gvs[] >>
     `~co.co_success` by
       (qpat_assum `~?rx ry co rest. _` mp_tac >>
        qpat_assum `u.vs_outcomes = co::rest` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[pairTheory.PAIR]) >>
     simp[storage_trace_domain_def]) >>
  W (fn (_,goal) => mp_tac (Q.INST [`G'` |-> `Gout`, `tn'` |-> `tnout`,
    `marks` |-> `[F]`, `r` |-> `Abort Revert_abort bad`,
    `res` |-> `INR (Error (RuntimeError msg))`, `ee` |-> `source_end`]
    (PART_MATCH (snd o dest_imp) gas_outcome_full_intro goal))) >>
  (impl_tac >- (conj_tac
    >- (qpat_assum `gas_explicit [F] t2.vs_gas_readings = []`
          (pure_rewrite_tac o single) >> simp[NoAsms] >> gen_tac >>
        drule_all ec_source_tail_gas_obs >> simp[NoAsms]) >>
    conj_tac >- simp[] >>
    simp[NoAsms, exit_result_def, expr_exit_def, halt_exit_def] >>
    gen_tac >> strip_tac >>
    `valid_horizon cx st0 H es2.storage_trace` by
      (qpat_assum `!H. valid_horizon cx st0 H source_end.storage_trace <=> _`
        (qspec_then `H` (fn eq =>
          qpat_assum `valid_horizon cx st0 H source_end.storage_trace`
            (ACCEPT_TAC o EQ_MP eq)))) >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
      (drule_then strip_assume_tac) >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [F] _`
      (drule_then assume_tac) >>
    qpat_assum `gas_origin_ptr_path _ (t2,G2,tn2) [] _`
      (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
    simp[NoAsms] >> disch_then drule >> simp[NoAsms])) >>
  disch_then ACCEPT_TAC
QED

Resume ec_arith_permitted_tail_full[success]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `data = word_to_bytes (n2w rx:bytes32) T ++ word_to_bytes (n2w ry:bytes32) T` >>
  `precompile_result (venom_call_request u addr 0w wi an T).cr_target
      (venom_call_request u addr 0w wi an T).cr_data = SOME (SOME data)` by
    simp[Abbr `data`] >>
  `computed_precompile (venom_call_request u addr 0w wi an T)` by
    (qpat_assum `precompile_result _ _ = SOME (SOME data)` mp_tac >>
     simp[NoAsms, computed_precompile_def, venom_call_request_def]) >>
  `addr <> 1w /\ 64 <= LENGTH data` by
    (Cases_on `bt = ECAdd` >>
     simp[Abbr `data`, LENGTH_word_to_bytes, wordsTheory.n2w_11,
       wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
  mp_tac (Q.INST [`s` |-> `u`, `u` |-> `sg`, `v` |-> `sc`,
    `G` |-> `Gu`, `tn` |-> `tnu`,
    `G2` |-> `step_prov PG (step_prov PG Gu gi sg) ci sc`,
    `tn2` |-> `step_taint ci sg sc (step_taint gi u sg tnu)`,
    `rn` |-> `64w`, `trace` |-> `es2.storage_trace`, `sf` |-> `s2`, `es` |-> `es2`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    precompile_suffix_success_full_family) >>
  (impl_tac >- (conj_tac >- (Cases_on `bt = ECAdd` >> simp[]) >>
    rpt conj_tac >> TRY (REFL_TAC ORELSE first_assum ACCEPT_TAC) >>~
    [`addr <> 1w ==> _`] >- simp[] >>
    gen_tac >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
      (drule_then strip_assume_tac) >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC ORELSE (simp[] >> NO_TAC)) >>
    disch_tac >> rpt gen_tac >>
    disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
    `regions_disjoint off (type_memory_size tv) (w2n wo) 64` by
      (qpat_assum `stmt_state_rel H ctx func cenv cx es2 u`
         (fn rel => let
            val horizon = hd (snd (strip_comb (concl rel)))
            val frame = aggregate_alloca_immutable_sep_source
            val premises = fst (dest_imp (concl frame))
            val frame_horizon = hd (snd (strip_comb (fst (dest_conj premises))))
          in irule (INST_TYPE (match_type (type_of frame_horizon) (type_of horizon)) frame) end) >>
       qpat_assum `stmt_state_rel H ctx func cenv cx es2 u` (irule_at Any) >>
       qexistsl [`src_id`, `name`, `iv`,
         `mk_inst out_alloc.cs_next_id ALLOCA [Lit 64w] [dst]`] >>
       simp[mk_inst_def]) >>
    pop_assum mp_tac >>
    pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
    simp[wordsTheory.dimword_def] >> decide_tac)) >>
  disch_then (qx_choose_then `ec_tail_end` (qx_choose_then `Gout`
    (qx_choose_then `tnout` strip_assume_tac))) >>
  qpat_assum `Abbrev (ee = _)`
    (fn abb =>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] abb)]) >>
      assume_tac abb) >>
  `ec_source_tail cx a bt [expr_type e1;expr_type e2] [v1;v2] es2 =
    (INL (Value (mk_ec_result (rx,ry))),ee)` by
    (mp_tac (Q.INST [`tys` |-> `[expr_type e1;expr_type e2]`, `es` |-> `es2`]
       ec_permitted_source_result) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[Abbr `ee`]) >>
  suspend "success_path"
QED

Resume ec_arith_permitted_tail_full[success_path]:
  markerLib.RESUME_TAC >>
  `(ee with gas_obs := []) = ee` by
    simp[Abbr `ee`, evaluation_state_component_equality] >>
  W (fn (_,goal) => mp_tac (Q.INST [`G'` |-> `Gout`, `tn'` |-> `tnout`,
    `marks` |-> `[F]`, `r` |-> `OK ec_tail_end`,
    `res` |-> `INL (Value (mk_ec_result (rx,ry)))`, `ee` |-> `ee`]
    (PART_MATCH (snd o dest_imp) gas_outcome_full_intro goal))) >>
  (impl_tac >- (conj_tac
    >- (qpat_assum `gas_explicit [F] t2.vs_gas_readings = []`
          (pure_rewrite_tac o single) >> simp[NoAsms] >> gen_tac >>
        drule_all ec_source_tail_gas_obs >> simp[NoAsms]) >>
    conj_tac >- simp[] >>
    gen_tac >> strip_tac >>
    `valid_horizon cx st0 H es2.storage_trace` by
      (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace <=> _`
        (qspec_then `H` (fn eq =>
          qpat_assum `valid_horizon cx st0 H ee.storage_trace`
            (ACCEPT_TAC o EQ_MP eq)))) >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
      (drule_then strip_assume_tac) >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [F] _ /\ _`
      (drule_then strip_assume_tac) >>
    `ctx_has_dalloca ctx ==> allocas_below_fmp ec_tail_end` by
      (qpat_assum `stmt_state_rel H ctx func cenv cx _ ec_tail_end`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
    conj_tac >- (qpat_assum `gas_origin_ptr_path _ (t2,G2,tn2) [] _`
      (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
      simp[NoAsms] >> disch_then drule >> simp[NoAsms]) >>
    qpat_assum `(ee with gas_obs := []) = ee`
      (fn source_end => PURE_REWRITE_TAC [source_end]) >>
    disj1_tac >> qexists_tac `ec_tail_end` >> simp[NoAsms] >>
    suspend "success_post")) >>
  disch_then ACCEPT_TAC
QED

Resume ec_arith_permitted_tail_full[success_post]:
  markerLib.RESUME_TAC >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> valid_horizon _ _ H _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `expr_post H ctx func cenv cx e1 es sa s1 s0 es1 v1 x t1`
    (fn post => assume_tac (MATCH_MP (SPEC_ALL expr_post_frame) post) >>
      strip_assume_tac (PURE_REWRITE_RULE [expr_post_def] post)) >>
  qpat_assum `expr_post H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2`
    (fn post => assume_tac (MATCH_MP (SPEC_ALL expr_post_frame) post) >>
      strip_assume_tac (PURE_REWRITE_RULE [expr_post_def] post)) >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    (conj_tac >> irule local_ptrs_reserved_next_var
     >- (qexists_tac `sa` >> simp[]) >> qexists_tac `sa` >> simp[]) >>
  drule_then strip_assume_tac loweringHaltTheory.compile_alloc_buffer_parts >>
  qpat_assum `_ sm = (_,sb)` (mp_then Any strip_assume_tac computed_suffix_shape) >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (qpat_assum `_ sm = (_,sb)`
       (mp_tac o AP_TERM ``\r:operand # compile_state. (SND r).cs_current_bb``) >>
     simp[NoAsms, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def]) >>
  `q.vs_current_bb = u.vs_current_bb` by
    (qspecl_then [`[gi;ci;ai]`,`u`,`q`] mp_tac entrySinkExtractionTheory.run_inst_seq_preserves_entry_control >>
     simp[mk_inst_def, is_terminator_def]) >>
  `q.vs_allocas = u.vs_allocas` by
    (qpat_assum `ec_tail_end = _` (fn finish_eq =>
       qpat_assum `ec_tail_end.vs_allocas = u.vs_allocas`
         (mp_tac o PURE_REWRITE_RULE [finish_eq])) >> simp[NoAsms]) >>
  qpat_assum `isPREFIX [gi;ci;ai] _`
    (qx_choose_then `suffix` assume_tac o PURE_REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `alloca_history func ec_tail_end` by
    (qpat_assum `ec_tail_end = _` (pure_rewrite_tac o single) >>
     qspecl_then [`func`,`u`,`q`,`bb`,`[gi;ci;ai]`,`suffix`] mp_tac
       bodyBinopFragMemoryTheory.alloca_history_no_alloca_slice >>
     simp[mk_inst_def]) >>
  `ec_tail_end.vs_current_bb = sb.cs_current_bb /\
   ec_tail_end.vs_inst_idx = LENGTH sb.cs_current_insts /\
   s0.vs_alloca_next <= ec_tail_end.vs_alloca_next` by simp[] >>
  suspend "success_buffer"
QED

Resume ec_arith_permitted_tail_full[success_buffer]:
  markerLib.RESUME_TAC >>
  `ee.scopes = es2.scopes` by simp[Abbr `ee`] >>
  `wb_frame cenv es2 ee s2 t2 ec_tail_end` by
    (qspecl_then [`func`,`cenv`,`cx`,`es2`,`t2`,`s2`,`es2`,`ee`,
       `s2`,`u`,`ec_tail_end`,`ctx`] mp_tac (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >>
     simp[]) >>
  `!n b sz. local_region cenv es2.scopes t2 n b sz <=>
             local_region cenv es2.scopes u n b sz` by
    (mp_tac (Q.INST [`es` |-> `es2`, `s0` |-> `t2`, `sa` |-> `s2`,
       `es1` |-> `es2`, `s1` |-> `u`, `es'` |-> `es2`]
       (INST_TYPE [alpha |-> ``:256``] wb_frame_local_regions)) >> simp[]) >>
  `!n b sz. local_region cenv es2.scopes u n b sz <=>
             local_region cenv ee.scopes ec_tail_end n b sz` by
    (mp_tac (Q.INST [`es` |-> `es2`, `s0` |-> `u`, `sa` |-> `s2`,
       `es1` |-> `ee`, `s1` |-> `ec_tail_end`, `es'` |-> `ee`]
       (INST_TYPE [alpha |-> ``:256``] wb_frame_local_regions)) >> simp[]) >>
  `w2n (64w:256 word) = 64` by
    simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  `!n b sz. local_region cenv es2.scopes u n b sz ==>
     regions_disjoint (w2n wo) 64 b sz` by
    (qpat_assum `!n b sz. local_region cenv es2.scopes u n b sz ==> _` mp_tac >>
     qpat_assum `w2n (64w:256 word) = 64` (pure_rewrite_tac o single) >>
     simp[NoAsms]) >>
  `!n b sz. local_region cenv es2.scopes t2 n b sz ==>
     regions_disjoint (w2n wo) 64 b sz` by
    (qpat_assum `!n b sz. local_region cenv es2.scopes t2 n b sz <=> _`
       (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `!n b sz. local_region cenv ee.scopes ec_tail_end n b sz ==>
     regions_disjoint (w2n wo) 64 b sz` by
    (qpat_assum `!n b sz. local_region cenv es2.scopes u n b sz <=> _`
       (pure_rewrite_tac o single o GSYM) >> first_assum ACCEPT_TAC) >>
  `!off len. regions_disjoint off len (w2n wo) 64 ==>
     mem_bytes_at off len ec_tail_end.vs_memory = mem_bytes_at off len u.vs_memory` by
    (rpt strip_tac >> qpat_assum `ec_tail_end.vs_memory = _`
       (pure_rewrite_tac o single) >> simp[write_memory_take_exterior]) >>
  `pure_frame cenv func es2 s2 t2 ec_tail_end` by
    (qspecl_then [`cenv`,`func`,`es2`,`s2`,`t2`,`u`,`ec_tail_end`,
       `mk_inst out_alloc.cs_next_id ALLOCA [Lit 64w] [dst]`,`w2n wo`,`64`]
       mp_tac pure_frame_buffer_tail >>
     (impl_tac >-
       (qpat_assum `MEM (mk_inst out_alloc.cs_next_id ALLOCA [Lit 64w] [dst]) _`
          (assume_tac o SRULE [mk_inst_def]) >>
        qpat_assum `ec_tail_end.vs_allocas = u.vs_allocas`
          (fn allocas => simp[NoAsms, allocas, mk_inst_def]) >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `mem_bytes_at (w2n wo) 64 ec_tail_end.vs_memory =
     word_to_bytes (n2w rx:bytes32) T ++ word_to_bytes (n2w ry:bytes32) T` by
    (qpat_assum `ec_tail_end.vs_memory = _` (pure_rewrite_tac o single) >>
     qspecl_then [`w2n wo`,`data`,`u`] mp_tac write_memory_mem_bytes_at_same >>
     simp[NoAsms, Abbr `data`, wordsTheory.dimword_def, LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, TAKE_LENGTH_TOO_LONG]) >>
  `storage_well_formed_on cx ee (FST H)` by
    (mp_tac (Q.INST [`st'` |-> `ee`, `st` |-> `es2`,
       `regions` |-> `FST (H : (bool # bytes32 # type_value) list # num list)`]
       (INST_TYPE [alpha |-> ``:256``] storage_well_formed_on_backends)) >>
     simp[Abbr `ee`]) >>
  `!c. bt <> Concat c` by
    (qpat_assum `bt = ECAdd \/ bt = ECMul` DISJ_CASES_TAC >> simp[]) >>
  `FLOOKUP ec_tail_end.vs_allocas out_alloc.cs_next_id = SOME (w2n wo,64) /\
   out_alloc.cs_next_id < sb.cs_next_id /\ sa.cs_next_id <= out_alloc.cs_next_id` by simp[] >>
  suspend "success_vv"
QED

Resume ec_arith_permitted_tail_full[success_vv]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.INST [`fn` |-> `func`, `es` |-> `es2`, `es'` |-> `ee`,
    `sa` |-> `s2`, `s0` |-> `t2`, `t` |-> `ec_tail_end`, `G` |-> `Gout`,
    `tn` |-> `tnout`, `w` |-> `wo`, `x` |-> `rx`, `y` |-> `ry`,
    `aid` |-> `out_alloc.cs_next_id`, `args` |-> `[e1;e2]`]
    (INST_TYPE [alpha |-> ``:256``] ec_builtin_result_posts)) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (qpat_assum `w2n (64w:256 word) = 64` (fn bytes =>
       first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [bytes])))))) >> strip_tac >>
  `post_value_type cenv (Builtin a bt [e1;e2]) = a /\
   lowered_value_type cenv (Builtin a bt [e1;e2]) = a` by
    (qpat_assum `bt = ECAdd \/ bt = ECMul` DISJ_CASES_TAC >>
     simp[post_value_type_def, exprLoweringTheory.lowered_value_type_def, expr_type_def]) >>
  `(~expr_has_effect (Builtin a bt [e1;e2]) ==>
      pure_frame cenv func es sa s0 t1) /\
   (~expr_has_effect (Builtin a bt [e1;e2]) ==>
      pure_frame cenv func es1 s1 t1 t2)` by
    (conj_tac >> simp[] >> strip_tac >> first_assum irule >>
     first_assum ACCEPT_TAC) >>
  `vv_post H ctx func cenv cx (Builtin a bt [e1;e2])
     es2 s2 sb t2 ee (Value (mk_ec_result (rx,ry))) vv ec_tail_end` by
    (qpat_assum `vv_post H _ _ _ _ _ es2 s2 sb t2 ee _ _ ec_tail_end` mp_tac >>
     qpat_assum `a = ArrayT (BaseT (UintT 256)) (Fixed 2)` (fn annotation =>
       qpat_assum `vv = StackValue a (Var dst)`
         (fn value => simp[NoAsms, annotation, value, exprLoweringTheory.as_stack_val_def]))) >>
  `vv_post H ctx func cenv cx (Builtin a bt [e1;e2])
     es1 s1 sb t1 ee (Value (mk_ec_result (rx,ry))) vv ec_tail_end` by
    (mp_tac (Q.INST [`es` |-> `es1`, `sa` |-> `s1`, `s0` |-> `t1`,
       `es1` |-> `es2`, `sm` |-> `s2`, `t` |-> `t2`, `es2` |-> `ee`,
       `tv` |-> `Value (mk_ec_result (rx,ry))`, `vv` |-> `vv`, `u` |-> `ec_tail_end`,
       `e` |-> `Builtin a bt [e1;e2]`]
       (INST_TYPE [alpha |-> ``:256``] exprSimCalldataSliceTheory.vv_post_prefix_frame)) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `vv_post H ctx func cenv cx (Builtin a bt [e1;e2])
     es sa sb s0 ee (Value (mk_ec_result (rx,ry))) vv ec_tail_end` by
    (mp_tac (Q.INST [`es1` |-> `es1`, `sm` |-> `s1`, `t` |-> `t1`,
       `es2` |-> `ee`, `tv` |-> `Value (mk_ec_result (rx,ry))`,
       `u` |-> `ec_tail_end`, `e` |-> `Builtin a bt [e1;e2]`]
       (INST_TYPE [alpha |-> ``:256``] exprSimCalldataSliceTheory.vv_post_prefix_frame)) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  suspend "success_ghost"
QED

Resume ec_arith_permitted_tail_full[success_ghost]:
  markerLib.RESUME_TAC >>
  `ghost_kept_at lo cenv es2 s2 G2 tn2 t2 Gout tnout` by
    (qspecl_then [`lo`,`cenv`,`es2`,`s2`,`G2`,`tn2`,`t2`,`Gu`,`tnu`,
       `es2`,`s2`,`Gout`,`tnout`,`u`,`H`,`ctx`,`func`,`cx`,`es2`]
       mp_tac (INST_TYPE [alpha |-> ``:num # num``, beta |-> ``:256``]
         ghost_kept_at_wb_trans) >>
     (impl_tac >- (simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es1 s1 G1 tn1 t1 Gout tnout` by
    (qspecl_then [`lo`,`cenv`,`es1`,`s1`,`G1`,`tn1`,`t1`,`G2`,`tn2`,
       `es2`,`s2`,`Gout`,`tnout`,`t2`,`H`,`ctx`,`func`,`cx`,`es2`]
       mp_tac (INST_TYPE [alpha |-> ``:num # num``, beta |-> ``:256``]
         ghost_kept_at_wb_trans) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gout tnout` by
    (qspecl_then [`lo`,`cenv`,`es`,`sa`,`G0`,`tn0`,`s0`,`G1`,`tn1`,
       `es1`,`s1`,`Gout`,`tnout`,`t1`,`H`,`ctx`,`func`,`cx`,`es1`]
       mp_tac (INST_TYPE [alpha |-> ``:num # num``, beta |-> ``:256``]
         ghost_kept_at_wb_trans) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  suspend "success_owned"
QED

Resume ec_arith_permitted_tail_full[success_owned]:
  markerLib.RESUME_TAC >>
  `evaluate_type (get_tenv cx) a =
     SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 2))` by
    (qpat_assum `a = ArrayT (BaseT (UintT 256)) (Fixed 2)` (fn annotation =>
       simp[NoAsms, annotation, evaluate_type_def, type_slot_size_def,
         wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``])) >>
  `w2n wo + 64 <= ec_tail_end.vs_alloca_next` by simp[] >>
  `vv_store_bound cx a a ee (Value (mk_ec_result (rx,ry))) vv ec_tail_end` by
    (qpat_assum `vv = StackValue a _` (pure_rewrite_tac o single) >>
     qpat_assum `a = ArrayT _ _` (fn annotation =>
       qpat_assum `evaluate_type (get_tenv cx) a = SOME _` (fn ty_eq =>
         simp[NoAsms, annotation, PURE_REWRITE_RULE [annotation] ty_eq,
              vv_store_bound_def, is_word_type_def, read_result_def, return_def,
              mk_ec_result_def, val_store_size_def, type_memory_size_def])) >>
     qpat_assum `eval_operand (Var dst) ec_tail_end = SOME wo`
       (fn eval => simp[NoAsms, eval]) >> first_assum ACCEPT_TAC) >>
  `vv_own cenv cx a sa sb ee (Value (mk_ec_result (rx,ry))) vv ec_tail_end` by
    (qpat_assum `vv = StackValue a _` (pure_rewrite_tac o single) >>
     qpat_assum `a = ArrayT _ _` (fn annotation =>
       qpat_assum `evaluate_type (get_tenv cx) a = SOME _` (fn ty_eq =>
         simp[NoAsms, annotation, PURE_REWRITE_RULE [annotation] ty_eq,
              vv_own_def, expr_val_own_def, is_word_type_def, read_result_def, return_def])) >>
     qexists_tac `wo` >> conj_tac >- first_assum ACCEPT_TAC >>
     disj1_tac >> qexistsl [`out_alloc.cs_next_id`,`w2n wo`,`64`] >>
     simp[NoAsms, mk_ec_result_def, val_footprint_def, type_memory_size_def] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       qpat_assum `!n b sz. local_region cenv ee.scopes ec_tail_end n b sz ==> _`
         (ACCEPT_TAC o PURE_REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]))) >>
  qpat_assum `lowered_value_type cenv (Builtin a bt [e1;e2]) = a`
    (fn ty_eq => pure_rewrite_tac [expr_type_def,ty_eq]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `vv = StackValue a _` (fn value =>
    qpat_assum `a = ArrayT _ _` (fn annotation =>
      simp[NoAsms, value, annotation, contextTheory.vv_location_def,
           is_word_type_def, is_bytestring_type_def] >>
      first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss())
        [value, annotation, exprLoweringTheory.as_stack_val_def])))
QED

Finalise ec_arith_permitted_tail_full
