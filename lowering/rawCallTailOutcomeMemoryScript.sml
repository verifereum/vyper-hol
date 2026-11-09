(* Source and counted target outcomes for the raw-call suffix. *)
Theory rawCallTailOutcomeMemory
Ancestors
  rawCallTailMemory exprSimRawCall exprSimRawCallCalldata rawCallPrefixMemory valueEncodingDefs
  exprSimMemDefs gasOutcome gasSummary fragGasMode
  vyperInterpreter vyperState exprLowering compileEnv exprSimDefs exprSimProps
  loweringPosts valueEncoding words finite_map list exprLoweringProps exprSimSource
  allocLimits localPtrsProps vyperValue exprSimHypsDefs
  vyperEvalExprPreservesScopesDom vyperCallOutcome vyperTypeSystem venomState
  vyperAST vyperTypeExtCallSoundness bodyMemBopRestWordPath
Libs
  monadsyntax

Theorem raw_call_tail_outcome_mem:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) = (INL av,esA) /\
  bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
    (INL (BytesV bs),esD) /\
  eval_exprs cx kws (esD with gas_obs := gsK) = (INL kvs,esK) /\
  esK.gas_obs = [] /\ expr_sim_inv cenv cx env esK /\
  typed_args_post ctx func cenv cx esD s4 tm esK kws xs kvs tk /\
  expr_val_rel cx (BaseT AddressT) av addr t /\
  (!x w. MEM x xs /\ eval_operand x tk = SOME w ==> eval_operand x t = SOME w) /\
  eval_operand len t = SOME (n2w (LENGTH bs)) /\
  eval_operand dp t = SOME (n2w (b+32)) /\ eval_operand gas t = SOME gw /\
  mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
  b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  alloca_history func t /\ b+32+LENGTH bs <= t.vs_alloca_next /\
  lowered_value_type cenv (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE) =
    raw_call_return_type flags /\
  stmt_state_rel ctx func cenv cx esK t /\ wb_frame cenv es sa s0 t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  ci_mono sa s6 /\ fn_has_code s6 sb func /\ fn_inst_ids_distinct func /\
  ~t.vs_halted /\ t.vs_current_bb = s6.cs_current_bb /\
  t.vs_inst_idx = LENGTH s6.cs_current_insts /\
  safe_operand s6 addr /\ safe_operand s6 len /\ safe_operand s6 dp /\
  safe_operand s6 gas /\ safe_operand s6
    (case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v) /\
  compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
  compile_raw_call_finish addr dp len gas
    (case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v)
    (if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (do
      type_check (LENGTH (av::BytesV bs::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
      target <- lift_option_type (dest_AddressV av) "raw_call target";
      data <- lift_option_type (dest_BytesV (BytesV bs)) "raw_call data";
      amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
      eval_raw_call cx flags target data amount
        (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs))
    od) (esK,t)
    (\res ee u. (?tv. res = INL tv /\
      vv_post ctx func cenv cx
        (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE)
        es sa sb s0 ee tv
        (if flags.rcf_max_outsize = 0 then StackValue ann result
         else LocatedValue (raw_call_return_type flags) (mk_ptr result LocMemory)) u /\
      vv_store_bound cx (raw_call_return_type flags) (raw_call_return_type flags) ee tv
        (if flags.rcf_max_outsize = 0 then StackValue ann result
         else LocatedValue (raw_call_return_type flags) (mk_ptr result LocMemory)) u) /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all raw_call_prefix_source_ready >> strip_tac >>
  drule raw_call_pre_flags >> strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `IS_SOME esK.outcomes /\ outcomes_accounts_typed esK.outcomes /\
   accounts_runtime_well_typed esK.accounts` by
    fs[expr_sim_inv_def,
      vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
  drule_all raw_call_source_tail >>
  disch_then (qspecl_then [`target`,
    `forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs)`,`bs`]
    strip_assume_tac) >>
  suspend "ready"
QED

Resume raw_call_tail_outcome_mem[ready]:
  `MAP FDOM es.scopes = MAP FDOM esA.scopes` by
    (qpat_assum `bind (eval_expr cx a) _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM esA.scopes = MAP FDOM esD.scopes` by
    (qpat_assum `bind (eval_expr cx d) _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM esD.scopes = MAP FDOM esK.scopes` by
    (drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM esK.scopes` by metis_tac[] >>
  `MAP FDOM esK.scopes = MAP FDOM es2.scopes` by
    (`es1.scopes = esK.scopes` by
       (drule take_call_outcome_frame >>
        disch_then (mp_tac o Q.AP_TERM `\s. s.scopes`) >> simp[]) >>
     drule adopt_call_outcome_frame >> simp[] >> strip_tac >>
     pop_assum (mp_tac o Q.AP_TERM `\s. s.scopes`) >> simp[]) >>
  drule_all raw_call_source_continuation >>
  disch_then (qspecl_then [`cx`,`bs`] SUBST1_TAC) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`bind (eval_expr cx a) _ _ = _`, `bind (eval_expr cx d) _ _ = _`,
     `eval_exprs cx kws _ = _`, `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _`,
     `expr_val_rel _ _ _ _ _`, `!x w. MEM x xs /\ _ ==> _`,
     `MAP FDOM es.scopes = MAP FDOM esA.scopes`,
     `MAP FDOM esA.scopes = MAP FDOM esD.scopes`,
     `MAP FDOM esD.scopes = MAP FDOM esK.scopes`] >>
  suspend "capacity"
QED

Resume raw_call_tail_outcome_mem[capacity]:
  `0 < flags.rcf_max_outsize ==>
    64 + ((flags.rcf_max_outsize + 31) DIV 32)*32 < dimword (:256)` by
    (strip_tac >>
     `type_alloc_ok cenv ann` by fs[expr_body_pre_def, alloc_limits_expr_def] >>
     Cases_on `flags.rcf_revert_on_failure` >>
     gvs[raw_call_return_type_def, type_alloc_ok_def, is_word_type_def,
       type_memory_bytes_def] >>
     `2 ** 64 + 64 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
     fs[] >> decide_tac) >>
  `local_ptrs_reserved cenv s6` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `LENGTH outcome.co_returnData < dimword (:256)` by
    (drule_all exprSimRawCallCalldataTheory.calldata_take_call_outcome_bound >> simp[]) >>
  `read_memory (w2n (n2w (b+32):bytes32)) (w2n (n2w (LENGTH bs):bytes32)) t = bs` by
    simp[read_memory_def, GSYM mem_bytes_at_def] >>
  suspend "path"
QED

Resume raw_call_tail_outcome_mem[path]:
  `w2w (w2w target : bytes32) = target` by wordsLib.WORD_DECIDE_TAC >>
  `w2n (if flags.rcf_is_static then 0w else (n2w amount : bytes32)) =
    (case (if flags.rcf_is_static then NONE else SOME amount) of NONE => 0 | SOME n => n)` by
    (Cases_on `flags.rcf_is_static` >> simp[]) >>
  `flags.rcf_is_static = IS_NONE (if flags.rcf_is_static then NONE else SOME amount)` by
    (Cases_on `flags.rcf_is_static` >> simp[]) >>
  `take_call_outcome target
    (read_memory (w2n (n2w (b+32):bytes32)) (w2n (n2w (LENGTH bs):bytes32)) t)
    (if flags.rcf_is_static then NONE else SOME amount) esK = (INL (rq,outcome),es1)` by simp[] >>
  `MAP FDOM esK.scopes = MAP FDOM (SND (adopt_call_outcome rq outcome es1)).scopes` by simp[] >>
  `0 < flags.rcf_max_outsize ==> evaluate_type (get_tenv cx)
    (expr_type (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE)) =
    SOME (if flags.rcf_revert_on_failure then BaseTV (BytesT (Dynamic flags.rcf_max_outsize))
      else TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))])` by
    (qpat_assum `flags.rcf_max_outsize < dimword (:256)`
       (mp_then Any strip_assume_tac raw_call_bytes_slot_size_bound) >>
     Cases_on `flags.rcf_revert_on_failure` >>
     fs[expr_type_def, raw_call_return_type_def, evaluate_type_def]) >>
  `expr_type (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE) =
    raw_call_return_type flags` by simp[expr_type_def] >>
  suspend "execute"
QED

Resume raw_call_tail_outcome_mem[execute]:
  drule_at (Pat `compile_raw_call_outbuf _ _ = _`) raw_call_outbuf_tail_mem >>
  disch_then (drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_type _ = _`)) >>
  simp[expr_type_def] >>
  disch_then (drule_at (Pat `lowered_value_type _ _ = _`)) >>
  disch_then (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ esK t`)) >>
  disch_then (drule_at (Pat `eval_operand addr t = _`)) >>
  disch_then (drule_at (Pat `eval_operand dp t = _`)) >>
  disch_then (drule_at (Pat `eval_operand len t = _`)) >>
  disch_then (drule_at (Pat `eval_operand gas t = _`)) >>
  disch_then (drule_at (Pat `eval_operand (case ext_call_kwarg _ _ _ of _ => _ | _ => _) t = _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `take_call_outcome _ _ _ esK = _`)) >>
  disch_then (qspec_then `ann` mp_tac) >>
  impl_tac >- fs[expr_type_def, wordsTheory.dimword_def] >>
  disch_then (qx_choose_then `r` assume_tac) >> suspend "outcome"
QED

Resume raw_call_tail_outcome_mem[outcome]:
  markerLib.RESUME_TAC >> simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexists_tac `FST (eval_raw_call cx flags target bs amount
    (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs)) esK)` >>
  qexists_tac `es2` >> qexists_tac `r` >>
  conj_tac >- simp[gas_marked_exec_def, gas_marked_path_def] >>
  qpat_x_assum `gas_path_mem _ _ _ _ _ /\ _` strip_assume_tac >>
  gvs[expr_exit_def, fragExecTheory.exit_result_def] >>
  `es2 with gas_obs := [] = es2` by
    (qpat_x_assum `es2.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `t.vs_alloca_next <= u.vs_alloca_next` by
    (drule fragGasPathMemTheory.gas_path_mem_exec >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (mp_then Any mp_tac rest_word_path_frontier) >> simp[]) >>
  simp[] >> metis_tac[]
QED

Finalise raw_call_tail_outcome_mem
