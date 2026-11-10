Theory bodyMemBiECRecoverPaths
Ancestors
  bodyMemBiECRecoverMemory bodyMemBiECRecoverRun exprSimPrecompiles exprSimDefs
  exprSimProps exprLowering exprLoweringProps exprSimWordArgs exprSimHypsDefs
  vyperTyping vyperAST vyperTypeSystem compileEnv loweringStateRelDefs list rich_list builtinMisc
  loweringPosts exprBopLowering vyperInterpreter vyperState vyperContext
  vyperValue vyperTypeInvariants valueEncoding integer_word words byte context
  emitHelper emitHelperProps venomExecSemantics venomInst venomState
  venomMemDefs venomCallOracleDefs extCallOracle fragExec fragGasSeqAbort
  fragGasSeqMem allocaHistoryFragment exprSimHash exprSimHashBoundary venomMemProps venomInstProofs
  fragGasMode bodyMemBiSha256Compose

Theorem ecrecover_seq_path_mem:
  !code s t ctx func bb.
    ~s.vs_halted /\ fn_inst_ids_distinct func /\
    alloca_history func s /\ alloca_inv s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK t ==>
    gas_path_mem ctx func s (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
    alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH code) /\
    s.vs_alloca_next <= (t with vs_inst_idx := s.vs_inst_idx + LENGTH code).vs_alloca_next
Proof
  rpt strip_tac
  >- (irule run_inst_seq_gas_path_mem >> goal_assum drule >> simp[])
  >- (qpat_x_assum `isPREFIX _ _` mp_tac >>
      pure_rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
      irule alloca_history_run_inst_seq >>
      goal_assum (drule_at Any) >> simp[] >>
      fs[EVERY_MEM]) >>
  simp[] >> irule sha256_run_inst_seq_alloca_next_mono >>
  goal_assum drule >> simp[]
QED

Theorem ecrecover_failure_path_mem:
  compile_ecrecover h v r sig sm = (op,sb) /\
  eval_operand h t = SOME wh /\ eval_operand v t = SOME wv /\
  eval_operand r t = SOME wr /\ eval_operand sig t = SOME ws /\
  stmt_state_rel ctx func cenv cx es t /\ fn_inst_ids_distinct func /\
  fn_has_code sm sb func /\
  ~(?co rest. t.vs_outcomes = co::rest /\ co.co_success) /\
  local_ptrs_reserved cenv sm /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sm x) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?n a u. gas_marked_path T ctx func t n (Abort a u)
Proof
  strip_tac >>
  `!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts func)` by
    metis_tac[hash_emitted_inst_mem] >>
  drule_all compile_ecrecover_mem_ok >> strip_tac >>
  drule_all compile_ecrecover_oracle_failure >> strip_tac >>
  drule ecrecover_code_shape >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by gvs[same_blocks_def] >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sm sb)
          (DROP t.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexists_tac `l` >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_gas_path >>
  disch_then (qspecl_then [`T`, `ctx`, `func`, `bb`] mp_tac) >>
  simp[] >> metis_tac[]
QED

(* Memory analogue of local ecrecover_success_path in exprSimPrecompiles. *)
Theorem ecrecover_success_path_mem:
  compile_ecrecover h v r sig sm = (op,sb) /\ fn_has_code sm sb func /\
  t.vs_outcomes = co::rest /\ co.co_success /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sm x) /\
  wb_frame cenv es sa s0 t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel ctx func cenv cx es' t /\ alloca_history func t /\
  eval_operand h t = SOME wh /\ eval_operand v t = SOME wv /\
  eval_operand r t = SOME wr /\ eval_operand sig t = SOME ws /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?n u. gas_marked_path T ctx func t n (OK u) /\
    expr_post ctx func cenv cx (Builtin (BaseT AddressT) ECRecover args)
      es sa sb s0 (es' with outcomes := SOME rest)
      (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws) of
        NONE => 0w | SOME a => a)) op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  `!i. MEM i (emitted_insts sm sb) ==> MEM i (fn_insts func)` by
    metis_tac[hash_emitted_inst_mem] >>
  drule_all compile_ecrecover_mem_ok >> strip_tac >>
  drule_all compile_ecrecover_run >> strip_tac >>
  rename1 `run_inst_seq _ t = OK output` >>
  drule ecrecover_code_shape >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by gvs[same_blocks_def] >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sm sb)
          (DROP t.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexists_tac `l` >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `alloca_inv t` by gvs[stmt_state_rel_def, state_rel_def] >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) ecrecover_seq_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `output.vs_current_bb = sb.cs_current_bb` by
    (drule_all hash_run_path >> strip_tac >> simp[]) >>
  qexistsl_tac [`LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb))`,
    `output with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sm sb)`] >>
  simp[gas_marked_path_def] >>
  irule expr_post_typed_stack_intro >>
  simp[stmt_state_rel_inst_idx, expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def] >>
  irule wb_frame_trans >> conj_tac >- simp[] >>
  conj_tac
  >- (qexistsl_tac [`es'`, `sm`, `t`] >>
      gvs[wb_frame_def, lookup_var_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]
QED
