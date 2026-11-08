(* Composition of raw-call argument and memory-counted suffix boundaries. *)
Theory rawCallExpressionMemory
Ancestors
  rawCallTailOutcomeMemory rawCallPrefixMemory exprSimRawCall exprSimMemDefs
  bodyMemoryPreds exprSimDefs exprSimProps exprLoweringProps exprLowering
  compileEnv loweringPosts vyperInterpreter vyperState venomState
  exprSimHypsDefs exprSimWordArgs exprSimHyps exprSimSource list fragExec
Libs
  monadsyntax

Theorem raw_call_expr_vv_sim_mem:
  body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es ==>
  expr_vv_sim_mem ctx func cenv cx ty
    (Call ann (RawCallTarget flags) (a::d::kws) dflt) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule compile_expr_raw_call >> strip_tac >>
  drule raw_call_pre_flags >> strip_tac >>
  `ci_mono s6 s7 /\ ci_mono s7 sb` by
    metis_tac[ci_mono_compile_raw_call_outbuf,
              ci_mono_compile_raw_call_finish, pairTheory.SND] >>
  `cs_extends s6 sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  suspend "placement"
QED

Resume raw_call_expr_vv_sim_mem[placement]:
  drule raw_call_kwargs_types >> simp[] >> strip_tac >>
  `LENGTH kws = LENGTH flags.rcf_kws` by fs[] >>
  drule_all raw_call_kwargs_word_args >> strip_tac >>
  qspecl_then [`kws`, `cenv`, `K (BaseT (UintT 256))`] mp_tac lower_word_args_shape >>
  (impl_tac
   >- (rpt strip_tac >>
       `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
       `MEM e (a::d::kws)` by simp[] >>
       `expr_body_pre cenv cx env e es` by
         (drule_all expr_body_pre_raw_call_arg >> simp[]) >>
       `is_word_type (expr_type e)` by fs[EVERY_MEM, is_word_type_def] >>
       drule_all expr_body_pre_lower_value_word_shape >> simp[])) >>
  disch_then drule >> strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    metis_tac[ci_mono_lower_value_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono s2 s3 /\ ci_mono s3 s4` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono s5 s6` by
    (Cases_on `go` >> gvs[]
     >- metis_tac[ci_mono_emit_op, pairTheory.SND] >> simp[ci_mono_refl]) >>
  `ci_mono sa s6` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code sa s6 func /\ fn_has_code s6 sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  gvs[] >> suspend "prefix"
QED

Resume raw_call_expr_vv_sim_mem[prefix]:
  rewrite_tac[raw_call_eval_action] >>
  irule (BETA_RULE (Q.ISPEC `\av dv kvs.
    do
      type_check (LENGTH (av::dv::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
      target <- lift_option_type (dest_AddressV av) "raw_call target";
      data <- lift_option_type (dest_BytesV dv) "raw_call data";
      amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
      eval_raw_call cx flags target data amount
        (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs))
    od` (Q.GEN `k` (SPEC_ALL raw_call_prefix_sim_mem)))) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `body_inv _ _ _ _`)) >>
  qpat_assum `lower_value _ _ _ a sa = _` (irule_at Any) >>
  simp[] >> conj_tac >-
    (rpt gen_tac >> Cases_on `r` >> Cases_on `exc` >>
     simp[expr_exit_def] >> rename1 `Error err` >>
     Cases_on `err` >> simp[expr_exit_def]) >>
  rpt strip_tac >> suspend "tail"
QED

Resume raw_call_expr_vv_sim_mem[tail]:
  qpat_x_assum `ext_call_kwarg EKValue _ xs = _`
    (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  `lowered_value_type cenv
     (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE) =
     raw_call_return_type flags` by
    simp[lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  irule gas_outcome_post_mono >>
  irule_at Any (SRULE [CONJ_ASSOC, arithmeticTheory.ADD_COMM]
    (BETA_RULE raw_call_tail_outcome_mem)) >>
  first_assum (irule_at (Pat `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_raw_call_outbuf _ _ = _`)) >>
  simp[] >> rpt (goal_assum (drule_at Any)) >> simp[] >>
  rpt strip_tac >> gvs[vyperASTTheory.expr_type_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Finalise raw_call_expr_vv_sim_mem
