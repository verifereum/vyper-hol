(* The source replay advances the conditional induction hypothesis only
   after the current tuple target has actually been assigned. *)
Theory tupleAssignImmutableDeploySourceSuffix
Ancestors
  tupleAssignImmutableDeploySuffix tuplePlaceHead
  tuplePlaceSuffixCode tuplePlaceSource bodySim
  aggregateCountedOutcome gasStorage vyperStorageTrace vyperStorageFootprint
  gasOutcome gasSummary gasSummaryCompose gasExemptCert
  stmtSimDefs stmtSimProps exprSimHypsDefs
  stmtLowering compileEnv loweringStateRelDefs
  vyperInterpreter vyperState vyperTypeDefaults list rich_list

Theorem tuple_mixed_suffix_from_steps:
  !ctx func cenv cx st0 env gs tys ltys ltvs vs elems w lo.
  LIST_REL (\g t. well_typed_atarget env g t) gs tys /\
  EVERY (\g. ?bt. g = BaseTarget bt) gs /\
  LENGTH ltys = LENGTH tys /\
  (!i es sp sa sb s0 bt r.
    i < LENGTH tys /\ EL i gs = BaseTarget bt /\
    expr_sim_inv cenv cx env es /\ ~block_is_terminated sp /\
    tuple_place_head ctx func cenv cx st0 es lo sp tys ltys ltvs vs elems w i s0 /\
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
    gas_outcome F (cx_tops cx) (ctx,func) cx st0
      (assign_tuple_targets cx (BaseTarget bt) (EL i vs)) (es,s0)
      (\H res ff t. res = INL () /\ ~block_is_terminated sb /\
        expr_sim_inv cenv cx env ff /\
        tuple_place_head ctx func cenv cx st0 ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
        stmt_state_rel H ctx func cenv cx ff t /\
        storage_well_formed_on cx ff (FST H) /\
        (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
        (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
          FLOOKUP t.vs_allocas id = SOME entry) /\
        alloca_frame cenv es sp s0 cenv ff t)
      (\H res ff r. expr_exit res r)) ==>
  !i es sp sf s0.
    i <= LENGTH tys /\ expr_sim_inv cenv cx env es /\ ~block_is_terminated sp /\
    tuple_place_head ctx func cenv cx st0 es lo sp tys ltys ltvs vs elems w i s0 /\
    body_tuple_targets_ok cx (DROP i gs) (DROP i vs) /\
    compile_tuple_store_all cenv (DROP i ltys) (DROP i gs) (DROP i elems) sp = ((),sf) /\
    fn_has_code sp sf func ==>
    gas_outcome F (cx_tops cx) (ctx,func) cx st0
      (assign_tuple_target_list cx (DROP i gs) (DROP i vs)) (es,s0)
      (\H res ff t. res = INL () /\ expr_sim_inv cenv cx env ff /\ ~block_is_terminated sf /\
        tuple_place_head ctx func cenv cx st0 ff lo sf tys ltys ltvs vs elems w (LENGTH tys) t /\
        stmt_state_rel H ctx func cenv cx ff t /\
        storage_well_formed_on cx ff (FST H) /\
        body_tuple_targets_ok cx (DROP (LENGTH tys) gs) (DROP (LENGTH tys) vs) /\
        (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
        (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
          FLOOKUP t.vs_allocas id = SOME entry) /\
        alloca_frame cenv es sp s0 cenv ff t)
      (\H res ff r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`,`func`,`cenv`,`cx`,`st0`,`env`,`gs`,`tys`,`ltys`,`ltvs`,
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
  `gas_outcome F (cx_tops cx) (ctx,func) cx st0 a (ee,s)
    (\H res ff t. res = INL () /\ ~block_is_terminated cb /\
      expr_sim_inv cenv cx env ff /\
      tuple_place_head ctx func cenv cx st0 ff lo cb tys ltys ltvs vs elems w (SUC j) t /\
        stmt_state_rel H ctx func cenv cx ff t /\
        storage_well_formed_on cx ff (FST H) /\
      (!x v. not_fresh_at cs x /\ lookup_var x s = SOME v ==> lookup_var x t = SOME v) /\
      (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
        FLOOKUP t.vs_allocas id = SOME entry) /\
      alloca_frame cenv ee cs s cenv ff t)
    (\H res ff r. expr_exit res r)` by
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
  rewrite_tac[ignore_bind_def] >>
  irule counted_outcome_bind_exec >>
  conj_tac >- simp[] >>
  conj_tac
  >- (BETA_TAC >> rpt strip_tac >> rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_unit >>
      qexistsl_tac [`mid`, `t`, `v`] >> simp[GSYM ignore_bind_def]) >>
  conj_tac
  >- (rpt strip_tac >> rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_unit >> simp[GSYM ignore_bind_def]) >>
  qpat_assum `gas_outcome _ _ _ _ _ a _ _ _` (irule_at Any) >>
  simp[] >> rpt conj_tac
  >~ [`expr_exit _ _`]
  >- (rpt strip_tac >> Cases_on `res` >>
      gvs[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 mid.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `a (ee with gas_obs := gas_explicit marks s.vs_gas_readings) =
    (INL (),mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ a _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `body_tuple_targets_ok cx (DROP (SUC j) gs) (DROP (SUC j) vs)` by
    (qpat_x_assum `_ ==> body_tuple_targets_ok cx
       (DROP (SUC j) gs) (DROP (SUC j) vs)` irule >>
     qexists `ee with gas_obs := gas_explicit marks s.vs_gas_readings` >> simp[]) >>
  qpat_x_assum `!ff t'. _ ==> gas_outcome _ _ _ _ _ next _ _ _`
    (qspecl_then [`mid`, `t`] mp_tac) >> simp[SF ETA_ss]) >>
  disch_then (qspecl_then [`i`,`es`,`sp`,`sf`,`s0`] mp_tac) >> simp[]
QED
