(* Source and counted target outcomes for the raw-call suffix. *)
Theory rawCallTailOutcomeMemory
Ancestors
  vyperStorageFootprint vyperStorageTrace gasStorage vyperFiniteStoragePreservation
  rawCallTailMemory rawCallOracleMemory fragExec exprSimRawCall exprSimRawCallCalldata valueEncodingDefs
  exprSimMemDefs gasOutcome gasSummary fragGasMode
  vyperInterpreter vyperState exprLowering compileEnv exprSimDefs exprSimProps
  loweringPosts valueEncoding words finite_map list exprLoweringProps exprSimSource
  allocLimits localPtrsProps vyperValue exprSimHypsDefs venomMemDefs
  vyperEvalExprPreservesScopesDom vyperCallOutcome vyperTypeSystem venomState
  vyperAST vyperTypeExtCallSoundness bodyMemBopRestWordPath loweringStateRelDefs
Libs
  monadsyntax

Theorem raw_call_tail_outcome_mem:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) = (INL av,esA) /\
  bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
    (INL (BytesV bs),esD) /\
  eval_exprs cx kws (esD with gas_obs := gsK) = (INL kvs,esK) /\
  esK.gas_obs = [] /\ expr_sim_inv cenv cx env esK /\
  (?H. valid_horizon cx st0 H esK.storage_trace) /\
  (!H. valid_horizon cx st0 H esK.storage_trace ==>
    expr_post H ctx func cenv cx a es sa s1 s0 esA av addr tA /\
    expr_post H ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
    typed_args_post H ctx func cenv cx esD s4 tm esK kws xs kvs tk /\
    expr_val_rel cx (BaseT AddressT) av addr t /\
    (!x w. MEM x xs /\ eval_operand x tk = SOME w ==> eval_operand x t = SOME w) /\
    eval_operand len t = SOME (n2w (LENGTH bs)) /\
    eval_operand dp t = SOME (n2w (b+32)) /\ eval_operand gas t = SOME gw /\
    mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
    b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    stmt_state_rel H ctx func cenv cx esK t /\
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx esK (FST H) /\ wb_frame cenv es esK sa s0 t /\
    ~t.vs_halted /\ t.vs_current_bb = s6.cs_current_bb /\
    t.vs_inst_idx = LENGTH s6.cs_current_insts /\
    (!x. addr = Var x \/ len = Var x \/ dp = Var x \/ gas = Var x \/
         MEM (Var x) xs ==> not_fresh_at s6 x) /\
    safe_operand s6 addr /\ safe_operand s6 len /\ safe_operand s6 dp /\
    safe_operand s6 gas /\ safe_operand s6
      (case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v) /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    b+32+LENGTH bs <= t.vs_alloca_next) /\
  lowered_value_type cenv (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE) =
    raw_call_return_type flags /\
  local_ptrs_reserved cenv sa /\
  ci_mono sa s6 /\ fn_has_code s6 sb func /\ fn_inst_ids_distinct func /\
  compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
  compile_raw_call_finish addr dp len gas
    (case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v)
    (if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (do
      type_check (LENGTH (av::BytesV bs::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
      target <- lift_option_type (dest_AddressV av) "raw_call target";
      data <- lift_option_type (dest_BytesV (BytesV bs)) "raw_call data";
      amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
      eval_raw_call cx flags target data amount
        (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs))
    od) (esK,t)
    (\H res ee u. (?tv. res = INL tv /\
      vv_post H ctx func cenv cx
        (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE)
        es sa sb s0 ee tv
        (if flags.rcf_max_outsize = 0 then StackValue ann result
         else LocatedValue (raw_call_return_type flags) (mk_ptr result LocMemory)) u /\
      vv_store_bound cx (raw_call_return_type flags) (raw_call_return_type flags) ee tv
        (if flags.rcf_max_outsize = 0 then StackValue ann result
         else LocatedValue (raw_call_return_type flags) (mk_ptr result LocMemory)) u) /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next)
    (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >>
  rename1 `valid_horizon cx st0 H0 esK.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_all raw_call_prefix_source_ready >> strip_tac >>
  drule raw_call_pre_flags >> strip_tac >>
  `IS_SOME esK.outcomes /\ outcomes_accounts_typed esK.outcomes /\
   accounts_runtime_well_typed esK.accounts` by
    fs[expr_sim_inv_def,
      vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
  `0 < flags.rcf_max_outsize ==>
    64 + ((flags.rcf_max_outsize + 31) DIV 32)*32 < dimword (:256)` by
    (strip_tac >>
     `type_alloc_ok cenv ann` by fs[expr_body_pre_def, alloc_limits_expr_def] >>
     Cases_on `flags.rcf_revert_on_failure` >>
     gvs[raw_call_return_type_def, type_alloc_ok_def, is_word_type_def,
       type_memory_bytes_def] >>
     `2 ** 64 + 64 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
     fs[] >> decide_tac) >>
  Cases_on `cx.txn.is_static /\ amount <> 0`
  >- suspend "static_value_abort" >>
  `cx.txn.is_static ==> amount = 0` by fs[] >>
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
     `eval_exprs cx kws _ = _`, `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _`,
     `expr_val_rel _ _ _ _ _`, `!x w. MEM x xs /\ _ ==> _`,
     `MAP FDOM es.scopes = MAP FDOM esA.scopes`,
     `MAP FDOM esA.scopes = MAP FDOM esD.scopes`,
     `MAP FDOM esD.scopes = MAP FDOM esK.scopes`] >>
  suspend "capacity"
QED

Resume raw_call_tail_outcome_mem[capacity]:
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
    (case (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount) of NONE => 0 | SOME n => n)` by
    (Cases_on `flags.rcf_is_static` >> Cases_on `cx.txn.is_static` >> gvs[]) >>
  `(flags.rcf_is_static \/ cx.txn.is_static) =
    IS_NONE (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount)` by simp[] >>
  `take_call_outcome target
    (read_memory (w2n (n2w (b+32):bytes32)) (w2n (n2w (LENGTH bs):bytes32)) t)
    (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount) esK = (INL (rq,outcome),es1)` by
    (qpat_x_assum `take_call_outcome _ _ _ esK = _` mp_tac >> simp[]) >>
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
  (* A horizon valid after the call was valid before it, and the call keeps
     storage well formed on it. *)
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
       stmt_state_rel H ctx func cenv cx esK t /\
       storage_well_formed_on cx es2 (FST H)` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H esK.storage_trace` by
       (qpat_assum `eval_raw_call _ _ _ _ _ _ esK = _`
          (mp_then (Pat `_ _ = (_,_)`) mp_tac
             vyperStorageFootprintTheory.valid_horizon_frame) >>
        simp[storage_trace_frame_raw_call]) >>
     qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _` drule >>
     strip_tac >> simp[] >>
     qpat_assum `eval_raw_call _ _ _ _ _ _ esK = _`
       (mp_then (Pat `eval_raw_call _ _ _ _ _ _ _ = _`) mp_tac
          vyperFiniteStoragePreservationTheory.eval_raw_call_preserves_storage_well_formed_on) >>
     disch_then irule >> fs[valid_horizon_def]) >>
  suspend "execute"
QED

Resume raw_call_tail_outcome_mem[execute]:
  drule_at (Pat `compile_raw_call_outbuf _ _ = _`) raw_call_outbuf_tail_mem >>
  disch_then (drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_type _ = _`)) >>
  simp[expr_type_def] >>
  disch_then (drule_at (Pat `lowered_value_type _ _ = _`)) >>
  disch_then (drule_at (Pat `wb_frame _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ esK t`)) >>
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
  markerLib.RESUME_TAC >> simp[gas_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexists_tac `FST (eval_raw_call cx flags target bs amount
    (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs)) esK)` >>
  qexists_tac `es2` >> qexists_tac `r` >>
  conj_tac >- simp[gas_marked_exec_def, gas_marked_path_def] >>
  qpat_x_assum `gas_path_mem _ _ _ _ _ /\ _` strip_assume_tac >>
  simp[expr_exit_def, halt_exit_def, fragExecTheory.exit_result_def] >>
  `es2.gas_obs = []` by asm_rewrite_tac[] >>
  `es2 with gas_obs := [] = es2` by
    (qpat_x_assum `es2.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `t.vs_alloca_next <= u.vs_alloca_next` by
    (drule fragGasPathMemTheory.gas_path_mem_exec >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (mp_then Any mp_tac rest_word_path_frontier) >> simp[]) >>
  qpat_assum `adopt_call_outcome rq outcome es1 = _`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th, pairTheory.SND])) >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Resume raw_call_tail_outcome_mem[static_value_abort]:
  `~flags.rcf_is_static` by fs[] >> fs[] >>
  drule_all raw_call_source_continuation >>
  disch_then (qspecl_then [`cx`,`bs`] SUBST1_TAC) >>
  `!st. eval_raw_call cx flags target bs amount
    (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs)) st =
    (INR (Error (RuntimeError "write in static context")), st)` by
    (gen_tac >> irule raw_call_static_value_abort >> simp[]) >>
  `local_ptrs_reserved cenv s6` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `0 < flags.rcf_max_outsize ==>
     ((flags.rcf_max_outsize + 31) DIV 32) * 32 + 32 < dimword (:256)` by
    (strip_tac >> fs[wordsTheory.dimword_def] >> decide_tac) >>
  `ci_mono s6 s7 /\ ci_mono s7 sb` by
    metis_tac[ci_mono_compile_raw_call_outbuf,
              ci_mono_compile_raw_call_finish, pairTheory.SND] >>
  `cs_extends s6 s7 /\ cs_extends s7 sb` by fs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all raw_call_outbuf_run_mem >>
  disch_then (qx_choose_then `u` (qx_choose_then `w` strip_assume_tac)) >>
  `!p v. safe_operand s6 p /\ eval_operand p t = SOME v ==> eval_operand p u = SOME v` by
    (rpt strip_tac >> Cases_on `p` >> gvs[exprSafeOperandTheory.safe_operand_def, eval_operand_def] >>
     irule exprSimWordArgsTheory.wb_frame_vars >>
     qexistsl_tac [`cenv`,`esK`,`esK`,`t`,`s6`] >> simp[]) >>
  `~u.vs_halted` by
    (`EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
       (emitted_insts s6 s7)` by
       (drule raw_call_outbuf_no_gas >> simp[EVERY_MEM] >> metis_tac[]) >>
     drule_all entrySinkExtractionTheory.run_inst_seq_preserves_entry_control >> simp[]) >>
  qabbrev_tac `z = u with vs_inst_idx := LENGTH s7.cs_current_insts` >>
  `~z.vs_halted /\ z.vs_current_bb = s7.cs_current_bb /\
   z.vs_inst_idx = LENGTH s7.cs_current_insts /\
   z.vs_call_ctx.cc_static` by
    (simp[Abbr `z`] >>
     qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ u` mp_tac >>
     qpat_assum `cx.txn.is_static` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[stmt_state_rel_def, state_rel_def, call_ctx_rel_def]) >>
  `eval_operand gas z = SOME gw /\ eval_operand addr z = SOME (w2w target) /\
   eval_operand dp z = SOME (n2w (b+32)) /\
   eval_operand len z = SOME (n2w (LENGTH bs)) /\
   eval_operand (case ext_call_kwarg EKValue flags.rcf_kws xs of
     NONE => Lit 0w | SOME v => v) z = SOME (n2w amount) /\
   eval_operand op z = SOME (if flags.rcf_max_outsize = 0 then w else w+32w)` by
    (simp[Abbr `z`, instIdxIndepTheory.eval_op_inst_idx] >> metis_tac[]) >>
  drule raw_call_finish_prefix >> strip_tac >>
  `ci_mono s7 sc` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends s7 sc` by fs[ci_mono_def] >>
  `fn_has_code s7 sc func` by metis_tac[fn_has_code_split] >>
  suspend "static_edge"
QED

Resume raw_call_tail_outcome_mem[static_edge]:
  qmatch_asmsub_abbrev_tac `emit_op CALL ops s7 = _` >>
  qabbrev_tac `inst = mk_inst s7.cs_next_id CALL ops
    [STRING #"%" (toString s7.cs_next_var)]` >>
  `step_inst_base inst z = Abort ExHalt_abort (halt_state (set_returndata [] z))` by
    (simp[Abbr `inst`, Abbr `ops`,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomInstTheory.mk_inst_def, eval_operand_def, wordsTheory.n2w_11]) >>
  `flags.rcf_max_outsize <= ((flags.rcf_max_outsize+31) DIV 32)*32` by
    (rpt (pop_assum kall_tac) >>
     qspec_then `flags.rcf_max_outsize` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     pure_rewrite_tac[vfmConstantsTheory.word_size_def, Once arithmeticTheory.MULT_COMM] >>
     simp[]) >>
  `flags.rcf_max_outsize = 0 \/
   w2n (if flags.rcf_max_outsize = 0 then w else w+32w) + flags.rcf_max_outsize <= z.vs_alloca_next` by
    (Cases_on `flags.rcf_max_outsize = 0` >- simp[] >>
     `0 < flags.rcf_max_outsize` by decide_tac >>
     `w2n w + (((flags.rcf_max_outsize+31) DIV 32)*32+32) <= u.vs_alloca_next` by
       (`alloca_next_valid u` by
          (qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ u` mp_tac >>
           rpt (pop_assum kall_tac) >> simp[stmt_state_rel_def, alloca_inv_def]) >>
        qpat_x_assum `FLOOKUP u.vs_allocas _ = _` mp_tac >>
        qpat_x_assum `alloca_next_valid u` mp_tac >>
        qpat_assum `flags.rcf_max_outsize <> 0` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[alloca_next_valid_def] >> metis_tac[]) >>
     fs[Abbr `z`] >> decide_tac) >>
  `inst_mem_below_frontier inst z` by
    (simp[Abbr `inst`, Abbr `ops`] >>
     irule (bodyMemRawCallBoundsTheory.raw_call_input_output_frontier |> Q.INST [`stat` |-> `F`] |> SIMP_RULE (srw_ss()) []) >>
     conj_tac
     >- (qexistsl_tac [`n2w (b+32)`,`n2w (LENGTH bs)`] >>
         fs[Abbr `z`, wordsTheory.dimword_def] >> decide_tac) >>
     qexistsl_tac [`if flags.rcf_max_outsize = 0 then w else w+32w`, `n2w flags.rcf_max_outsize`] >>
     fs[eval_operand_def, wordsTheory.dimword_def]) >>
  suspend "static_fetch"
QED

Resume raw_call_tail_outcome_mem[static_fetch]:
  markerLib.RESUME_TAC >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op_local >> strip_tac >>
  `sc.cs_current_bb = s7.cs_current_bb` by fs[same_blocks_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH s7.cs_current_insts) = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `inst`]) >>
  suspend "static_counted"
QED

Resume raw_call_tail_outcome_mem[static_counted]:
  markerLib.RESUME_TAC >>
  `gas_path_mem_edge ctx func z 0
     (Abort ExHalt_abort (halt_state (set_returndata [] z)))` by
    (rewrite_tac[fragGasPathMemTheory.gas_path_mem_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     `mem_safe_step 0 ctx inst z` by
       simp[memSafeRunTheory.mem_safe_step_non_invoke,
         memSafeRunTheory.inst_dload_in_section_def,
         Abbr `inst`, venomInstTheory.mk_inst_def] >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke,
       gasCountTheory.gas_count_step_def, fragExecTheory.exit_result_def,
       Abbr `inst`, venomInstTheory.mk_inst_def] >> metis_tac[]) >>
  `gas_path_mem ctx func z 0
     (Abort ExHalt_abort (halt_state (set_returndata [] z)))` by
    metis_tac[fragGasPathMemTheory.gas_path_mem_rules, fragExecTheory.exit_result_def] >>
  `gas_path_mem ctx func t 0
     (Abort ExHalt_abort (halt_state (set_returndata [] z)))` by
    metis_tac[fragGasPathMemTheory.gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  suspend "static_outcome"
QED

Resume raw_call_tail_outcome_mem[static_outcome]:
  markerLib.RESUME_TAC >>
  simp[gas_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "write in static context"))`,
    `esK`, `Abort ExHalt_abort (halt_state (set_returndata [] z))`] >>
  simp[gas_marked_exec_def, gas_marked_path_def,
    type_check_def, lift_option_type_def, dest_BytesV_def,
    vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.return_def, vyperStateTheory.assert_def,
    expr_exit_def, halt_exit_def, fragExecTheory.exit_result_def]
QED

Finalise raw_call_tail_outcome_mem
