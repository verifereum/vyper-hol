Theory bodyFullBuiltinECArithEmpty
Ancestors
  bodyFullBuiltinPrecompileSuffixAbort exprSimECArith exprSimWordArgs
  gasOutcomeFullCompose fragGasOriginPtr fragExec exprSimDefs exprSimHash
  venomInstProofs venomExecSemantics venomInst venomState finite_map
  rich_list vyperStorageFootprint vyperInterpreter vyperContext vyperState
  vyperValue extCallOracle

Theorem ec_arith_empty_tail_full:
  (bt = ECAdd \/ bt = ECMul) /\
  (if bt = ECAdd then evaluate_ecadd [v1;v2] else evaluate_ecmul [v1;v2]) =
    (case point_result of NONE => INR (RuntimeError
       (if bt = ECAdd then "ECAdd invalid point" else "ECMul invalid point"))
     | SOME xy => INL (mk_ec_result xy)) /\
  es2.outcomes = SOME [] /\ gas_explicit [F] t2.vs_gas_readings = [] /\
  storage_trace_domain cx st0 es2.storage_trace /\
  u.vs_outcomes = [] /\
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit 64w] [cv] /\
  src <> gv /\ dst <> gv /\
  eval_operand (Var src) u = SOME wi /\ eval_operand (Var dst) u = SOME wo /\
  w2n wi + w2n an <= u.vs_alloca_next /\
  w2n wo + 64 <= u.vs_alloca_next /\
  ~u.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  MEM func ctx.ctx_functions /\
  lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (gi::ci::rest) (DROP u.vs_inst_idx bb.bb_instructions) /\
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
      (u.vs_transient u.vs_call_ctx.cc_address)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (ec_source_tail cx a bt tys [v1;v2]) (es2,t2,G2,tn2) Q
    (\H rr ee gt r. expr_exit rr r /\ halt_exit H cx ee rr r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `?msg. ec_source_tail cx a bt tys [v1;v2] es2 =
     (INR (Error (RuntimeError msg)),es2)` by
    (Cases_on `point_result` >> Cases_on `bt = ECAdd` >>
     gvs[ec_source_tail_cases, builtin_result_def, evaluate_builtin_def]) >>
  qabbrev_tac `sg = update_var gv (HD (u.vs_gas_readings ++ [0w]))
    (u with vs_gas_readings := DROP 1 u.vs_gas_readings)` >>
  `step_inst_base gi u = OK sg` by simp[Abbr `sg`,step_GAS] >>
  `step_inst_base ci sg = Abort ExHalt_abort (halt_state (set_returndata [] sg))` by
    (simp[Abbr `sg`, mk_inst_def, step_inst_base_def, exec_ext_call_def,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     gvs[eval_operand_def, lookup_var_def]) >>
  `isPREFIX [gi;ci] (DROP u.vs_inst_idx bb.bb_instructions)` by
    metis_tac[IS_PREFIX_APPEND, APPEND] >>
  qabbrev_tac `bad = halt_state (set_returndata [] sg)
    with vs_inst_idx := SUC u.vs_inst_idx` >>
  `lookup_block bad.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb bad.vs_inst_idx = SOME ci` by
    (simp[Abbr `bad`, Abbr `sg`, halt_state_def, set_returndata_def, update_var_def] >>
     qpat_assum `isPREFIX (gi::ci::rest) _`
       (strip_assume_tac o MATCH_MP fragGasSeqAbortTheory.instruction_prefix_cursor) >>
     drule fragGasSeqAbortTheory.instruction_prefix_cursor >> simp[]) >>
  `ALL_DISTINCT (FLAT (MAP fn_labels ctx.ctx_functions)) ==>
   ~oversized_create_abort ctx (Abort ExHalt_abort bad)` by
    (strip_tac >> irule createSizeExitTheory.oversized_create_abort_non_create_cursor >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`bb`, `func`, `ci`] >> simp[mk_inst_def]) >>
  qabbrev_tac `Ga = step_prov PG Gu gi sg` >>
  qabbrev_tac `tna = step_taint gi u sg tnu` >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (u,Gu,tnu) [F] (Abort ExHalt_abort bad,Ga,tna)` by
    (simp[NoAsms, Abbr `bad`, Abbr `Ga`, Abbr `tna`] >>
     MATCH_MP_TAC (Q.INST [`trace` |-> `es2.storage_trace`, `rn` |-> `64w`]
       precompile_suffix_call_abort_full_family) >>
     rpt conj_tac >>
     TRY (REFL_TAC ORELSE first_assum ACCEPT_TAC) >>
     simp[NoAsms, wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
     TRY (first_assum ACCEPT_TAC) >>
     gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  W (fn (_,goal) => mp_tac (Q.INST [`G'` |-> `Ga`, `tn'` |-> `tna`,
    `marks` |-> `[F]`, `r` |-> `Abort ExHalt_abort bad`,
    `res` |-> `INR (Error (RuntimeError msg))`, `ee` |-> `es2`]
    (PART_MATCH (snd o dest_imp) gas_outcome_full_intro goal))) >>
  (impl_tac >- (conj_tac
    >- (qpat_assum `gas_explicit [F] t2.vs_gas_readings = []`
          (pure_rewrite_tac o single) >> simp[NoAsms] >> gen_tac >>
        drule_all ec_source_tail_gas_obs >> simp[NoAsms]) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    simp[NoAsms, exit_result_def, expr_exit_def, halt_exit_def] >>
    gen_tac >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
      (drule_then strip_assume_tac) >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [F] _`
      (drule_then assume_tac) >>
    qpat_assum `gas_origin_ptr_path _ (t2,G2,tn2) [] _`
      (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
    simp[NoAsms] >> disch_then drule >> simp[NoAsms] >>
    qpat_assum `ALL_DISTINCT _ ==> ~oversized_create_abort _ _` mp_tac >>
    tautLib.TAUT_TAC)) >>
  disch_then ACCEPT_TAC
QED
