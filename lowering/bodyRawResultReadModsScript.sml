(* Force a raw-call result from the linked value judgment. *)
Theory bodyRawResultReadMods
Ancestors
  bodyAggregateReadMods bodyAggregateReadPostMods bodyFullPredsMods
  bodyRawRequestInputsMods bodyFullShared bodyFullPostsMods
  exprSimSend vyperCallFrame vyperTypeSystem
  gasShadowCompile gasShadowState exprLowering compileEnv vyperInterpreter
  vyperState vyperAST context
Libs monadsyntax

Theorem raw_request_nonword[local]:
  flags.rcf_max_outsize <> 0 ==> ~is_word_type (raw_call_return_type flags)
Proof
  Cases_on `flags.rcf_revert_on_failure` >> simp[raw_call_return_type_def,is_word_type_def]
QED

Theorem raw_request_compile_shape[local]:
  ((tgt = RawCallTarget flags /\ (?a d kws. args = a::d::kws)) \/
   (tgt = RawCallCalldataTarget flags /\ (?a kws. args = a::kws))) /\
  compile_expr cenv ty (Call ann tgt args dflt) sa = (vv,sm) ==>
  ?op. vv = if flags.rcf_max_outsize = 0 then StackValue ann op
            else LocatedValue ann (mk_ptr op LocMemory)
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_call, compile_call_def] >>
  rpt (pairarg_tac >> simp[]) >>
  Cases_on `flags.rcf_max_outsize = 0` >> simp[] >> metis_tac[]
QED

Theorem raw_call_paired_lower_value[local]:
  ((tgt = RawCallTarget flags /\ (?a d kws. args = a::d::kws)) \/
   (tgt = RawCallCalldataTarget flags /\ (?a kws. args = a::kws))) /\
  ann = raw_call_return_type flags /\
  lower_value compile_expr cenv ty (Call ann tgt args dflt) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann tgt args dflt)) sha = (op,shb) /\
  gas_shadow_state sa sha ==>
  let vv = if flags.rcf_max_outsize = 0 then StackValue ann op
           else LocatedValue ann (mk_ptr op LocMemory) in
  compile_expr cenv ty (Call ann tgt args dflt) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann tgt args dflt)) sha = (vv,shb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `compile_expr cenv ty (Call ann tgt args dflt) sa` >>
  drule_all_then strip_assume_tac raw_request_compile_shape >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann tgt args dflt)) sha` >>
  `gas_shadow_compiles (compile_expr cenv ty (Call ann tgt args dflt))
    (compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr (Call ann tgt args dflt)))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  gvs[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def,
      mk_ptr_def, raw_request_nonword]
QED

Theorem raw_request_eval_value[local]:
  (tgt = RawCallTarget flags \/ tgt = RawCallCalldataTarget flags) /\
  eval_expr cx (Call ann tgt args dflt) es = (INL raw,ee) ==>
  ?v. raw = Value v
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac bool_ss [evaluate_def, ignore_bind_def] >>
  simp[bind_def, return_def, raise_def, AllCaseEqs()] >> strip_tac >>
  drule eval_raw_call_success_value >> simp[]
QED

Theorem raw_request_value_of_vv_mods:
  !DF lo d mods ctx shadow_ctx PG func shadow_func cenv env cx ty
   ann tgt flags args dflt es.
    (tgt = RawCallTarget flags \/ tgt = RawCallCalldataTarget flags) /\
    expr_body_pre_mods mods cenv cx env (Call ann tgt args dflt) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann tgt args dflt) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann tgt args dflt) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule materialized_value_from_vv_mods >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (rpt gen_tac >> disch_tac >> metis_tac[raw_request_eval_value]) >>
  Q.SUBGOAL_THEN
    `ann = raw_call_return_type flags /\
     ((tgt = RawCallTarget flags /\ (?a d kws. args = a::d::kws)) \/
      (tgt = RawCallCalldataTarget flags /\ (?a kws. args = a::kws)))`
    (CONJUNCTS_THEN2 assume_tac assume_tac)
  >- (qpat_x_assum `tgt = _ \/ tgt = _` strip_assume_tac >> gvs[]
      >- (drule_then strip_assume_tac raw_call_pre_operands_flags_mods >> simp[]) >>
      drule_then strip_assume_tac raw_calldata_pre_operands_flags_mods >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then mp_tac raw_call_paired_lower_value >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  asm_simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (qexists_tac `StackValue (raw_call_return_type flags) op` >> asm_rewrite_tac[] >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      irule stack_value_read_post_mods >> simp[] >>
      qexists_tac `raw_call_return_type flags` >> simp[]) >>
  qexists_tac `LocatedValue (raw_call_return_type flags) (mk_ptr op LocMemory)` >>
  asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac raw_request_nonword >>
  `(mk_ptr op LocMemory).ptr_location = LocMemory` by simp[mk_ptr_def] >>
  `ptr_buf_ok cenv (Call (raw_call_return_type flags) tgt args dflt)
    (mk_ptr op LocMemory).ptr_operand G t` by
    (qpat_assum `!b p. LocatedValue _ _ = LocatedValue b p /\ _ ==> ptr_buf_ok _ _ _ _ _`
       (qspecl_then [`raw_call_return_type flags`,`mk_ptr op LocMemory`] mp_tac) >> simp[]) >>
  drule_all memory_buffer_read_post_mods >> fs[mk_ptr_def]
QED
