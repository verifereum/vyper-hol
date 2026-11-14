(* The source replay advances the conditional induction hypothesis only
   after the current tuple target has actually been assigned. *)
Theory tupleAssignImmutableDeploySourceSuffix
Ancestors
  tupleAssignImmutableDeploySuffix tuplePlaceHeadGas tuplePlaceHead
  tuplePlaceSuffixCode tuplePlaceSource bodySim
  gasOutcome gasSummary gasSummaryCompose gasExemptCert
  stmtSimDefs stmtSimProps exprSimHypsDefs
  stmtLowering compileEnv loweringStateRelDefs
  vyperInterpreter vyperState vyperTypeDefaults list rich_list

Theorem tuple_mixed_suffix_from_steps:
  !ctx func cenv cx env gs tys ltys ltvs vs elems w lo.
  LIST_REL (\g t. well_typed_atarget env g t) gs tys /\
  EVERY (\g. ?bt. g = BaseTarget bt) gs /\
  LENGTH ltys = LENGTH tys /\
  (!i es sp sa sb s0 bt r.
    i < LENGTH tys /\ EL i gs = BaseTarget bt /\
    expr_sim_inv cenv cx env es /\ ~block_is_terminated sp /\
    tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
    body_tuple_target_ok cx (BaseTarget bt) (EL i vs) /\
    compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
    (if is_word_type (EL i ltys) then
       if is_word_type (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys) then
         compile_store_at_loc cenv.ce_imm_alloca (FST r) (EL i elems) (FST (SND r))
       else emit_void INVALID []
     else compile_assign_value cenv (FST r)
       (case FST (SND r) of SOME l => l | NONE => LocMemory) (EL i elems)
       (is_word_type (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys))
       NONE (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys) (EL i ltys)
       (type_memory_bytes cenv
         (case SND (SND r) of SOME (ValPT t) => t | _ => EL i ltys))) sa = ((),sb) /\
    fn_has_code sp sa func /\ fn_has_code sa sb func /\
    sp.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (assign_tuple_targets cx (BaseTarget bt) (EL i vs)) (es,s0)
      (\res ff t. res = INL () /\ ~block_is_terminated sb /\
        expr_sim_inv cenv cx env ff /\
        tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
        (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
        (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
          FLOOKUP t.vs_allocas id = SOME entry) /\
        alloca_frame cenv es sp s0 cenv ff t)
      (\res ff r. expr_exit res r)) ==>
  !i es sp sf s0.
    i <= LENGTH tys /\ expr_sim_inv cenv cx env es /\ ~block_is_terminated sp /\
    tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
    body_tuple_targets_ok cx (DROP i gs) (DROP i vs) /\
    compile_tuple_store_all cenv (DROP i ltys) (DROP i gs) (DROP i elems) sp = ((),sf) /\
    fn_has_code sp sf func ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (assign_tuple_target_list cx (DROP i gs) (DROP i vs)) (es,s0)
      (\res ff t. res = INL () /\ expr_sim_inv cenv cx env ff /\ ~block_is_terminated sf /\
        tuple_place_head ctx func cenv cx ff lo sf tys ltys ltvs vs elems w (LENGTH tys) t /\
        body_tuple_targets_ok cx (DROP (LENGTH tys) gs) (DROP (LENGTH tys) vs) /\
        (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
        (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
          FLOOKUP t.vs_allocas id = SOME entry) /\
        alloca_frame cenv es sp s0 cenv ff t)
      (\res ff r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`,`func`,`cenv`,`cx`,`env`,`gs`,`tys`,`ltys`,`ltvs`,
    `vs`,`elems`,`w`,`lo`,`\j ee cs s.
      body_tuple_targets_ok cx (DROP j gs) (DROP j vs)`]
    tuple_mixed_suffix_from_heads) >>
  impl_tac >- (simp[LET_THM] >>
  map_every qx_gen_tac [`j`,`ee`,`cs`,`ca`,`cb`,`s`,`bt`,`r`,`next`,`Q`] >>
  strip_tac >>
  `LENGTH gs = LENGTH tys /\ LENGTH vs = LENGTH tys` by
    fs[LIST_REL_EL_EQN, tuple_place_head_def, values_have_types_LIST_REL] >>
  `DROP j gs = BaseTarget bt :: DROP (SUC j) gs /\
   DROP j vs = EL j vs :: DROP (SUC j) vs` by simp[DROP_CONS_EL] >>
  `body_tuple_target_ok cx (BaseTarget bt) (EL j vs)` by
    (qpat_x_assum `body_tuple_targets_ok _ (DROP _ _) _` mp_tac >>
     asm_simp_tac (srw_ss()) [body_tuple_target_ok_def]) >>
  qabbrev_tac `a = assign_tuple_targets cx (BaseTarget bt) (EL j vs)` >>
  `(?source_state out final_state. a source_state = (INL out,final_state)) ==>
    body_tuple_targets_ok cx (DROP (SUC j) gs) (DROP (SUC j) vs)` by
    (qunabbrev_tac `a` >>
     qpat_x_assum `body_tuple_targets_ok _ (DROP _ _) _` mp_tac >>
     asm_simp_tac (srw_ss()) [body_tuple_target_ok_def]) >>
  `gas_outcome F (cx_tops cx) (ctx,func) a (ee,s)
    (\res ff t. res = INL () /\ ~block_is_terminated cb /\
      expr_sim_inv cenv cx env ff /\
      tuple_place_head ctx func cenv cx ff lo cb tys ltys ltvs vs elems w (SUC j) t /\
      (!x v. not_fresh_at cs x /\ lookup_var x s = SOME v ==> lookup_var x t = SOME v) /\
      (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
        FLOOKUP t.vs_allocas id = SOME entry) /\
      alloca_frame cenv ee cs s cenv ff t)
    (\res ff r. expr_exit res r)` by
    (qunabbrev_tac `a` >>
     qpat_x_assum `!i es sp ca cb s0 bt r. _`
       (qspecl_then [`j`,`ee`,`cs`,`ca`,`cb`,`s`,`bt`,`r`] mp_tac) >>
     simp[LET_THM]) >>
  qpat_x_assum `!i es sp ca cb s0 bt r. _` kall_tac >>
  qpat_x_assum `(if _ then _ else _) _ = ((),_)` kall_tac >>
  `bind (eval_target_place cx bt)
    (\p. ignore_bind (write_place cx p (EL j vs)) next) = ignore_bind a next` by
    (simp[Abbr `a`, ignore_bind_def] >>
     CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >>
     simp[bind_assoc]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `gas_outcome _ _ _ a _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `left` (DISJ_CASES_THEN mp_tac))
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `rr` (qx_choose_then `mid`
        (qx_choose_then `result` (CONJUNCTS_THEN2 assume_tac
          (DISJ_CASES_THEN mp_tac)))))
      >- (disch_then (qx_choose_then `t` strip_assume_tac) >> gvs[] >>
          `a (ee with gas_obs := gas_explicit left s.vs_gas_readings) =
            (INL (),mid with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ a _ _ _ _ _` mp_tac >>
             simp[gas_marked_exec_def] >> strip_tac >>
             first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          `body_tuple_targets_ok cx (DROP (SUC j) gs) (DROP (SUC j) vs)` by
            (qpat_x_assum `_ ==> body_tuple_targets_ok cx
               (DROP (SUC j) gs) (DROP (SUC j) vs)` irule >>
             qexists `ee with gas_obs := gas_explicit left s.vs_gas_readings` >> simp[]) >>
          `gas_outcome F (cx_tops cx) (ctx,func) next
             (mid with gas_obs := [],t) Q (\res ee r. expr_exit res r)` by
            (qpat_x_assum `!ff t'. _ ==> gas_outcome _ _ _ next _ _ _`
               (qspecl_then [`mid`,`t`] mp_tac) >>
             simp[gas_outcome_def, gas_summary_at_def]) >>
          qpat_x_assum `gas_outcome _ _ _ next _ _ _` mp_tac >>
          rewrite_tac[gas_outcome_def] >>
          disch_then (qx_choose_then `right` (DISJ_CASES_THEN mp_tac))
          >- (rewrite_tac[gas_summary_at_def] >>
              disch_then (qx_choose_then `out` (qx_choose_then `fin`
                (qx_choose_then `result` (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
              qexists `left ++ right` >> disj1_tac >>
              rewrite_tac[gas_summary_at_def] >>
              qexistsl [`out`,`fin`,`result`] >> conj_tac
              >- (rewrite_tac[ignore_bind_def] >>
                  irule gas_marked_exec_bind_normal >>
                  qexistsl [`mid`,`t`,`()`] >> simp[]) >> fs[]) >>
          disch_then (qx_choose_then `err` (qx_choose_then `fin_src`
            (qx_choose_then `leaf` (qx_choose_then `fin_t` assume_tac)))) >>
          qexists `left ++ right` >> disj2_tac >>
          qexistsl [`err`,`fin_src`,`leaf`,`fin_t`] >>
          rewrite_tac[ignore_bind_def,bind_assoc] >>
          irule gas_exempt_cert_bind_unit >>
          qexistsl [`mid`,`t`,`()`] >> simp[GSYM ignore_bind_def]) >>
      strip_tac >>
      `?exc. rr = INR exc` by
        (Cases_on `rr` >> fs[exprSimDefsTheory.expr_exit_def]) >> gvs[] >>
      qexists `left` >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
      qexistsl [`INR exc`,`mid`,`result`] >> simp[] >>
      rewrite_tac[ignore_bind_def] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  disch_then (qx_choose_then `err` (qx_choose_then `fin_src`
    (qx_choose_then `leaf` (qx_choose_then `fin_t` assume_tac)))) >>
  qexists `left` >> disj2_tac >>
  qexistsl [`err`,`fin_src`,`leaf`,`fin_t`] >>
  rewrite_tac[ignore_bind_def,bind_assoc] >>
  irule gas_exempt_cert_error_unit >> simp[GSYM ignore_bind_def]) >>
  disch_then (qspecl_then [`i`,`es`,`sp`,`sf`,`s0`] mp_tac) >> simp[]
QED
