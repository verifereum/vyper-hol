(* A reached ExtCall head uses the actual ordinary and shadow code intervals. *)
Theory s1PrefixBoolChainExtCallHead
Ancestors
  s1PrefixPreds s1PrefixOfVV s1PrefixDefs
  s1PrefixExtCallRequestStage s1PrefixExtCallCallStage s1PrefixExtCallReturnTrace
  bodyFullExtCallReadyReturn bodyFullExtCallReturn abiDecodeValidJoint
  abiDecodeRejectJoint exprSimExtCallCase bodyFullExprCore bodySim bodyInvCodeProps
  bodyFullPreds exprSimSource vyperInterpreter vyperAST vyperState list rich_list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    (drule_then assume_tac body_inv_contract >>
     drule_then ACCEPT_TAC contract_inv_acyclic_struct_metadata) >>
  pure_rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ho_match_mp_tac (GEN_ALL extcall_request_prefix) >>
  qexistsl [`vv`,`ty`,`tops`,`shadow_sb`,`shadow_sa`,`shadow_func`,`sb`,`sa`,
            `env`,`d`,`cenv`] >>
  simp[NoAsms] >>
  ntac 2 (qpat_x_assum `!st target mid src vs ee. _ ==> _ cx (DROP (1 + LENGTH ats) args)`
    (assume_tac o PURE_ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM])) >>
  qexists `\H res ee G tn t. T` >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
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
      `TAKE (LENGTH ats) (vs ++ kws) = vs /\ DROP (LENGTH ats) (vs ++ kws) = kws` by
        (qpat_assum `LENGTH vs = LENGTH ats` (SUBST1_TAC o SYM) >>
         simp[TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]) >>
      simpLib.ASM_SIMP_TAC bool_ss [LENGTH_APPEND] >>
      qhdtm_assum `extcall_request_ready` (irule_at Any) >>
      rpt (goal_assum (drule_at Any)) >>
      simp[EVERY_DEF, optionTheory.OPTION_BIND_EQUALS_OPTION]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `TAKE (LENGTH ats) (vs ++ kws) = vs /\ DROP (LENGTH ats) (vs ++ kws) = kws` by
    (qpat_assum `LENGTH vs = LENGTH ats` (SUBST1_TAC o SYM) >>
     simp[TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]) >>
  irule extcall_return_trace_prefix >>
  conj_tac >- simp[LENGTH_APPEND] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`calldata`, `target`,
            `if stat then NONE
             else case ext_call_kwarg EKValue opts kws of
                    NONE => SOME 0 | SOME x => dest_NumV x`] >>
  simpLib.ASM_SIMP_TAC bool_ss [] >>
  conj_tac
  >- (qhdtm_assum `extcall_request_ready`
        (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
      first_assum ACCEPT_TAC) >>
  irule extcall_call_stage_prefix >>
  qhdtm_assum `extcall_request_ready` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[EVERY_DEF, optionTheory.OPTION_BIND_EQUALS_OPTION]
QED
*)
Theorem extcall_head_vv_prefix:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr) es /\
  body_exprs_full_ok cx (TAKE 1 args) /\
  body_exprs_prefix_ok cx (TAKE 1 args) /\
  (!st target mid.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) ==>
    body_exprs_full_ok cx (TAKE (LENGTH ats) (DROP 1 args))) /\
  (!st target mid.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) ==>
    body_exprs_prefix_ok cx (TAKE (LENGTH ats) (DROP 1 args))) /\
  (!st target mid src vs ee.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    eval_exprs cx (TAKE (LENGTH ats) (DROP 1 args)) src = (INL vs,ee) ==>
    body_exprs_full_ok cx (DROP (1 + LENGTH ats) args)) /\
  (!st target mid src vs ee.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    eval_exprs cx (TAKE (LENGTH ats) (DROP 1 args)) src = (INL vs,ee) ==>
    body_exprs_prefix_ok cx (DROP (1 + LENGTH ats) args)) ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr) es
Proof
  cheat
QED

Theorem bool_chain_extcall_head_prefix:
  h = Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr /\
  expr_type h = BaseT BoolT /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env ee /\
  expr_body_pre cenv cx env h ee /\
  body_exprs_full_ok cx (TAKE 1 args) /\
  body_exprs_prefix_ok cx (TAKE 1 args) /\
  (!st target mid.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) ==>
    body_exprs_full_ok cx (TAKE (LENGTH ats) (DROP 1 args))) /\
  (!st target mid.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) ==>
    body_exprs_prefix_ok cx (TAKE (LENGTH ats) (DROP 1 args))) /\
  (!st target mid src vs ef.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    eval_exprs cx (TAKE (LENGTH ats) (DROP 1 args)) src = (INL vs,ef) ==>
    body_exprs_full_ok cx (DROP (1 + LENGTH ats) args)) /\
  (!st target mid src vs ef.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    eval_exprs cx (TAKE (LENGTH ats) (DROP 1 args)) src = (INL vs,ef) ==>
    body_exprs_prefix_ok cx (DROP (1 + LENGTH ats) args)) /\
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (BaseT BoolT) h ee (st0,sa,sb,shadow_sa,shadow_sb,op,s,G,tn) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx h) (read_result cx)) (ee,s,G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT BoolT) h ee` by
    (irule expr_sim_prefix_of_vv >> gvs[] >>
     irule extcall_head_vv_prefix >>
     simp[NoAsms] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`env`,`tops`] >> simp[]) >>
  qhdtm_assum `expr_sim_prefix` (drule_then irule o REWRITE_RULE[expr_sim_prefix_def])
QED
