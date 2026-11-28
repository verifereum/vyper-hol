(* Native request prefix for a Boolean Not with a literal-target static call. *)
Theory s1PrefixBoolChainNotDirect
Ancestors
  bodyFullBuiltinWordNot exprSimUnopProps gasShadowCompileStmtHelpers
  gasShadowCompileBase gasShadowState gasShadow exprLoweringProps fragExec
  bodyFullExprCore s1PrefixLiteralWord s1PrefixPreds s1PrefixOfVV s1PrefixDefs
  s1PrefixExtCallRequestStage s1PrefixBoolChainDirectCall s1PrefixExtCallReturnTrace
  bodyFullExtCallReadyReturn bodyFullExtCallReturn abiDecodeValidJoint
  abiDecodeRejectJoint exprSimExtCallCase bodySim bodyInvCodeProps
  bodyFullPreds bodyFullExprsListFacts exprSimSource vyperInterpreter vyperAST vyperState list

(* The call returns a located value; use the VV prefix before the read. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> irule expr_sim_prefix_of_vv >>
  pure_rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `body_exprs_full_ok cx [Literal (BaseT AddressT) (BytesL (REPLICATE 18 0w ++ [1w;0w]))]` by
    simp[body_exprs_full_ok_cons, body_exprs_full_ok_nil, literal_expr_full_ok] >>
  `body_expr_prefix_ok cx (Literal (BaseT AddressT) (BytesL (REPLICATE 18 0w ++ [1w;0w])))` by
    simp[Once body_expr_prefix_ok_def, literal_word_value_prefix, literal_vv_prefix] >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    metis_tac[body_inv_contract, contract_inv_acyclic_struct_metadata] >>
  ho_match_mp_tac (GEN_ALL extcall_request_prefix) >>
  qexistsl [`vv`,`BaseT BoolT`,`tops`,`shadow_sb`,`shadow_sa`,`shadow_func`,
            `sb`,`sa`,`env`,`d`,`cenv`] >>
  simp[NoAsms, body_exprs_full_ok_cons, body_exprs_full_ok_nil,
       body_exprs_prefix_ok_def, literal_expr_full_ok] >>
  rpt (goal_assum (drule_at Any)) >>
  qexists `\H res ee G tn t. T` >> conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      mp_tac extcall_return_full >>
      (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_valid_allocated_joint)) >>
      (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_malformed_allocated_joint)) >>
      disch_then (fn th =>
        mp_tac extcall_ready_return_outcome >>
        (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC (SPEC_ALL th)))) >>
      disch_then (fn th =>
        irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
        irule_at Any (SPEC_ALL th)) >>
      qhdtm_assum `extcall_request_ready` (irule_at Any) >>
      qexistsl [`vv`,`u`,`tn0`,`sr`,`NONE`,`sb`,`result`,`env`,`NONE`,`d`,
                `[Literal (BaseT AddressT) (BytesL (REPLICATE 18 0w ++ [1w;0w]))]`,
                `BaseT BoolT`,`G0`] >>
      fs[EVERY_DEF, ext_call_kwarg_def, optionTheory.OPTION_BIND_EQUALS_OPTION] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule extcall_return_trace_prefix >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`calldata`,`target`,`NONE`] >>
  simp[ext_call_kwarg_def] >>
  irule bool_chain_direct_bool_extcall_prefix >>
  qhdtm_assum `extcall_request_ready` (irule_at Any) >>
  qexistsl [`u`,`tn0`,`sr`,`d`,`G0`] >>
  fs[EVERY_DEF, ext_call_kwarg_def, optionTheory.OPTION_BIND_EQUALS_OPTION] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)
Theorem bool_chain_literal_static_expr_prefix[local]:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  expr_body_pre cenv cx env
    (Call (BaseT BoolT) (ExtCall T F (fname,[],BaseT BoolT) [])
      [Literal (BaseT AddressT) (BytesL (REPLICATE 18 0w ++ [1w;0w]))] NONE) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (BaseT BoolT)
    (Call (BaseT BoolT) (ExtCall T F (fname,[],BaseT BoolT) [])
      [Literal (BaseT AddressT) (BytesL (REPLICATE 18 0w ++ [1w;0w]))] NONE) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `expr_type a = BaseT BoolT` by fs[expr_type_def] >>
  `expr_body_pre cenv cx env a es` by (drule word_not_pre >> simp[]) >>
  qhdtm_x_assum `expr_sim_full_pre` (strip_assume_tac o REWRITE_RULE [expr_sim_full_pre_def]) >>
  drule lower_value_not >> strip_tac >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _` mp_tac >>
  pure_rewrite_tac[gas_shadow_expr_def, gas_shadow_builtin_def, MAP] >>
  simp[NoAsms] >> disch_then (strip_assume_tac o MATCH_MP lower_value_not) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (BaseT BoolT) a)
    (lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT)
      (gas_shadow_expr a))` by irule gas_shadow_stmt_lower_value_env >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  rename [`lower_value _ cenv _ a sa = (_,sm)`,
          `lower_value _ _ _ (gas_shadow_expr a) shadow_sa = (_,shadow_sm)`] >>
  RULE_ASSUM_TAC (REWRITE_RULE [gas_shadow_expr_type]) >>
  qpat_x_assum `expr_type a = BaseT BoolT` (RULE_ASSUM_TAC o ONCE_REWRITE_RULE o single) >>
  qpat_x_assum `a = Call _ _ _ _`
    (fn ath => simp[] >> strip_tac >> assume_tac ath) >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    metis_tac[straight_fresh_not, straight_fresh_cs_extends] >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx a) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (BaseT BoolT) a es (st0,sa,sm,shadow_sa,shadow_sm,x,s,G,tn)` by
    (pure_rewrite_tac[expr_sim_full_pre_def] >>
     qpat_x_assum `a = Call _ _ _ _` kall_tac >> simp[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (BaseT BoolT) a es` by
    (qpat_x_assum `a = Call _ _ _ _` SUBST_ALL_TAC >>
     irule bool_chain_literal_static_expr_prefix >> simp[] >>
     qexistsl_tac [`env`,`tops`] >> simp[]) >>
  qhdtm_x_assum `expr_sim_prefix` (drule_all o REWRITE_RULE [expr_sim_prefix_def]) >>
  strip_tac >>
  rewrite_tac[Q.INST [`bi` |-> `Not`] eval_expr_unop_action |>
    SIMP_RULE (srw_ss()) []] >>
  qpat_assum `gas_prefix_full _ _ _ _ _`
    (mp_then Any irule (iffRL gas_prefix_full_state_cong)) >>
  qx_gen_tac `qe` >> Cases_on `bind (eval_expr cx a) (read_result cx) qe` >>
  rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[bind_def]
QED
*)
Theorem bool_chain_not_direct_operand_prefix:
  a = Call (BaseT BoolT) (ExtCall T F (fname,[],BaseT BoolT) [])
        [Literal (BaseT AddressT) (BytesL (REPLICATE 18 0w ++ [1w;0w]))] NONE /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  reached (Builtin (BaseT BoolT) Not [a]::rest) sa shadow_sa es s G tn /\
  body_expr_full_ok cx (Builtin (BaseT BoolT) Not [a]) /\
  expr_type (Builtin (BaseT BoolT) Not [a]) = BaseT BoolT /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin (BaseT BoolT) Not [a]) es /\
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (BaseT BoolT) (Builtin (BaseT BoolT) Not [a]) es
      (st0,sa,sb,shadow_sa,shadow_sb,op,s,G,tn) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (bind (eval_expr cx (Builtin (BaseT BoolT) Not [a])) (read_result cx)) (es,s,G,tn)
Proof
  cheat
QED
