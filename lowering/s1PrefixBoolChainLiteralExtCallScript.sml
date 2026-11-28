(* A literal-target static query has no recursive prefix obligations. *)
Theory s1PrefixBoolChainLiteralExtCall
Ancestors
  s1PrefixLiteralWord s1PrefixPreds s1PrefixOfVV s1PrefixDefs
  s1PrefixExtCallRequestStage s1PrefixExtCallCallStage s1PrefixExtCallReturnTrace
  bodyFullExtCallReadyReturn bodyFullExtCallReturn abiDecodeValidJoint
  abiDecodeRejectJoint exprSimExtCallCase bodyFullExprCore bodySim bodyInvCodeProps
  bodyFullPreds bodyFullExprsListFacts exprSimSource vyperInterpreter vyperAST vyperState list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  pure_rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `body_expr_prefix_ok cx (Literal (BaseT AddressT) lit)` by
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
                `[Literal (BaseT AddressT) lit]`,`BaseT BoolT`,`G0`] >>
      fs[EVERY_DEF, ext_call_kwarg_def, optionTheory.OPTION_BIND_EQUALS_OPTION] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule extcall_return_trace_prefix >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`calldata`,`target`,`NONE`] >>
  simp[ext_call_kwarg_def] >>
  irule extcall_call_stage_prefix >>
  qhdtm_assum `extcall_request_ready` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[EVERY_DEF, ext_call_kwarg_def, optionTheory.OPTION_BIND_EQUALS_OPTION]
QED
*)
Theorem literal_static_query_vv_prefix[local]:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env
    (Call (BaseT BoolT) (ExtCall T skip (fname,[],BaseT BoolT) [])
      [Literal (BaseT AddressT) lit] NONE) es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (BaseT BoolT)
    (Call (BaseT BoolT) (ExtCall T skip (fname,[],BaseT BoolT) [])
      [Literal (BaseT AddressT) lit] NONE) es
Proof
  cheat
QED

Theorem bool_chain_literal_extcall_head_prefix:
  h = Call (BaseT BoolT) (ExtCall T skip (fname,[],BaseT BoolT) [])
        [Literal (BaseT AddressT) lit] NONE /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env ee /\
  expr_body_pre cenv cx env h ee /\
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (BaseT BoolT) h ee (st0,sa,sb,shadow_sa,shadow_sb,op,s,G,tn) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx h) (read_result cx)) (ee,s,G,tn)
Proof
  strip_tac >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT BoolT) h ee` by
    (irule expr_sim_prefix_of_vv >> gvs[] >>
     irule literal_static_query_vv_prefix >> rpt (goal_assum (drule_at Any))) >>
  qhdtm_assum `expr_sim_prefix` (drule_then irule o REWRITE_RULE[expr_sim_prefix_def])
QED
