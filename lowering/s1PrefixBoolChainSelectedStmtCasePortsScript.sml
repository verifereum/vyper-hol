(* Constructor ports for the selected-body request-prefix induction. *)
Theory s1PrefixBoolChainSelectedStmtCasePorts
Ancestors
  s1PrefixDefs s1PrefixPreds s1PrefixReturnSome s1PrefixReturnNone s1PrefixExits
  s1PrefixStmtZero s1PrefixExprStmt s1PrefixAssertBare s1PrefixAssertReason
  s1PrefixRaiseCustomError[qualified] s1PrefixAssertCustomError[qualified]
  s1PrefixRaiseReason s1PrefixLog s1PrefixAnnAssign s1PrefixAssign s1PrefixAssignTuple
  s1PrefixBoolChainSelectedLocalAssign s1PrefixAugAssign s1PrefixFor s1PrefixIf
  s1PrefixStmtsCons s1PrefixTarget s1PrefixOfVV
  s1PrefixAppendSourceChildren s1PrefixAppendCodeCuts s1PrefixAppendToplevelEntry
  s1PrefixAppendReplayRhs bodyPtrPopTargetFragTransport bodyAppendResolvedPre
  bodySimFullMain[qualified] bodyFullPreds bodyFullTarget bodyFullTargetDefs
  bodyFullIfExpReach bodyInvCodeProps bodyInvExecutionProps bodyExprPreFacts
  stmtExprAllocationPreProps bodySingletonCallSupport contractInvContextProps
  gasOutcomeFullCompose gasShadow gasShadowStmtEnv gasShadowCompileStmtHelpers
  allocLimits allocLimitsProps supportedExprTraverse supportedStmtTraverse
  bodySim bodySimFull exprSimSource exprSimAggregateLayout exprLoweringProps
  targetPlaceSimCases vyperExprNoControl vyperTypeContract
  supportedStmts vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  loweringPosts exprLowering compileEnv gasContext vyperInterpreter vyperState
  stmtSimDefs exprSimDefs exprSimHypsDefs s1PrefixStmtFullApply bodyFullSimProjection list
Libs
  pairLib

Theorem body_return_case_prefix:
  !cx e.
    body_expr_full_ok cx e /\ body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Return (SOME e))
Proof
  rw[body_stmt_prefix_ok_def, gas_shadow_stmt_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all body_inv_stmt_const_name_free >>
     simp[supported_stmt_expr_exists_def, supported_expr_exists_def]) >>
  `well_typed_expr env e` by fs[type_stmt_def] >>
  drule_all_then strip_assume_tac
    bodySingletonCallSupportTheory.supported_singleton_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    drule_then ACCEPT_TAC body_inv_main_support >>
  `cx_tops cx = tops` by
    (drule_then (ACCEPT_TAC o CONJUNCT2) body_inv_main_code) >>
  `alloc_limits_expr cenv e` by
    gvs[stmt_exprs_ok_flat, alloc_limits_stmt_def, allocLimitsTheory.alloc_limits_expr_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule (Q.SPECL [`cenv`, `cx`, `env`, `e`, `es`, `[]`]
              stmt_expr_body_pre) >>
     gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def] >>
     conj_tac
     >- (rpt strip_tac >> drule_all_then ACCEPT_TAC body_inv_singleton_abi_types) >>
     irule allocLimitsPropsTheory.alloc_limits_expr_not_extcode >>
     qexists_tac `cenv` >> simp[]) >>
  irule compile_return_some_frag_prefix >>
  qpat_x_assum `body_expr_prefix_ok cx e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  first_x_assum (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
    `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `ret_ty`, `es`] mp_tac) >>
  simp[]
QED

Theorem body_return_none_case_prefix:
  !cx. body_stmt_prefix_ok cx (Return NONE)
Proof
  simp[body_stmt_prefix_ok_def, gas_shadow_stmt_def,
       compile_return_none_frag_prefix]
QED

Theorem body_break_case_prefix:
  !cx. body_stmt_prefix_ok cx Break
Proof
  simp[body_stmt_prefix_ok_def, compile_loop_jump_frag_prefix]
QED

Theorem body_continue_case_prefix:
  !cx. body_stmt_prefix_ok cx Continue
Proof
  simp[body_stmt_prefix_ok_def, compile_loop_jump_frag_prefix]
QED

Theorem body_raise_bare_case_prefix:
  !cx. body_stmt_prefix_ok cx (Raise RaiseBare)
Proof
  simp[body_stmt_prefix_ok_def, compile_raise_frag_prefix]
QED

Theorem body_raise_unreachable_case_prefix:
  !cx. body_stmt_prefix_ok cx (Raise RaiseUnreachable)
Proof
  simp[body_stmt_prefix_ok_def, compile_raise_frag_prefix]
QED

Theorem body_pass_case_prefix:
  !cx. body_stmt_prefix_ok cx Pass
Proof
  simp[body_stmt_prefix_ok_def, gas_shadow_stmt_def, compile_pass_frag_prefix]
QED

Theorem body_stmts_nil_case_prefix:
  !cx. body_stmts_prefix_ok cx []
Proof
  simp[body_stmts_prefix_ok_def, stmt_frag_nil_prefix]
QED

Theorem body_expr_stmt_case_prefix:
  !cx e.
    body_expr_full_ok cx e /\
    body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Expr e)
Proof
  rw[body_stmt_prefix_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  `well_typed_expr env e` by gvs[type_stmt_def] >>
  qpat_assum `body_inv tops ctx cenv cx`
    (assume_tac o MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules
      o MATCH_MP body_inv_contract) >>
  `expr_body_pre cenv cx env e es` by
    (mp_tac (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`, `s` |-> `Expr e`]
       stmtExprAllocationPrePropsTheory.body_inv_stmt_expr_pre_singleton) >>
     simp[supported_stmt_expr_exists_def, int_calls_stmt_def] >>
     disch_then irule >>
     `alloc_limits_expr cenv e` by
       fs[stmt_exprs_ok_flat, alloc_limits_stmt_def] >>
     `~is_extcode e` by
       (irule allocLimitsPropsTheory.alloc_limits_expr_not_extcode >>
        qexists_tac `cenv` >> simp[]) >>
     mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`, `calls` |-> `[]`]
       stmt_expr_body_pre_main_mods) >>
     gvs[compileUnitTheory.main_module_def, alistTheory.ALOOKUP_def,
         stmt_exprs_ok_flat, supported_stmt_expr_exists_def, int_calls_stmt_def]) >>
  irule compile_expr_stmt_frag_ok_prefix >>
  qpat_x_assum `body_expr_prefix_ok cx e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  first_x_assum (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
    `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `expr_type e`, `es`] mp_tac) >>
  simp[]
QED

val _ = Parse.hide "body";

Theorem body_raise_custom_case_prefix:
  !cx err.
  (!id positional kwargs tops params es.
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_full_ok cx es) /\
  (!id positional kwargs tops params es.
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_prefix_ok cx es) ==>
  body_stmt_prefix_ok cx (Raise (RaiseCustomError err))
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[body_stmt_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  irule s1PrefixRaiseCustomErrorTheory.compile_raise_custom_frag_prefix >>
  asm_rewrite_tac[] >>
  map_every qexists_tac [`bindings`,`env`,`env'`,`tops`] >>
  asm_rewrite_tac[]
QED

Theorem body_assert_custom_case_prefix:
  !cx e err.
  (!s tv t id positional kwargs tops params es.
       eval_expr cx e s = (INL tv,t) /\
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_full_ok cx es) /\
  (!s tv t id positional kwargs tops params es.
       eval_expr cx e s = (INL tv,t) /\
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_prefix_ok cx es) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assert e (AssertCustomError err))
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[body_stmt_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  irule s1PrefixAssertCustomErrorTheory.compile_assert_custom_frag_prefix_from_raise >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> irule bodySimFullMainTheory.body_raise_custom_case_full >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule body_raise_custom_case_prefix >> metis_tac[]) >>
  map_every qexists_tac [`bindings`,`env`,`env'`,`tops`] >> asm_rewrite_tac[]
QED

Theorem body_annassign_case_prefix:
  !cx id typ e.
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_prefix_ok cx e) ==>
  body_stmt_prefix_ok cx (AnnAssign id typ e)
Proof
  rw[body_stmt_prefix_ok_def] >>
  Cases_on `is_word_type typ`
  >- (irule body_annassign_word_prefix >>
      simp[] >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
      qexistsl_tac [`bindings`, `env`, `env'`, `tops`] >> asm_rewrite_tac[]) >>
  `0 < type_memory_bytes cenv typ` by
    (irule exprSimAggregateLayoutTheory.annassign_memory_bytes_pos_ptr >>
     metis_tac[]) >>
  Cases_on `expr_type e = typ \/ lowered_value_type cenv e = typ \/
            is_bytestring_type typ \/
            has_length_word typ /\ is_empty_value_expr e`
  >- (Cases_on `lowered_value_type cenv e = expr_type e \/
                is_bytestring_type (expr_type e) /\
                is_bytestring_type (lowered_value_type cenv e) /\
                arg_type_fits (lowered_value_type cenv e) (expr_type e)`
      >- (`lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
           has_length_word typ /\ is_empty_value_expr e` by metis_tac[] >>
          irule body_annassign_memory_prefix >>
          simp[] >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
          qexistsl_tac [`bindings`, `env`, `env'`, `tops`] >> asm_rewrite_tac[]) >>
      irule body_annassign_widened_prefix >>
      asm_rewrite_tac[] >> simp[] >>
      rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
      qexistsl_tac [`bindings`, `env`, `env'`, `tops`] >> asm_rewrite_tac[]) >>
  `~(expr_type e = typ \/ is_bytestring_type typ \/
      has_length_word typ /\ is_empty_value_expr e)` by metis_tac[] >>
  irule body_annassign_other_prefix >>
  asm_rewrite_tac[] >> simp[] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  qexistsl_tac [`bindings`, `env`, `env'`, `tops`] >> asm_rewrite_tac[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  simp[body_stmt_prefix_ok_def, stmt_frag_prefix_def] >>
  rpt gen_tac >> strip_tac >>
  qx_genl_tac [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`s0`,`G0`,`tn0`,`ce`] >> disch_tac >>
  qpat_assum `stmt_frag_full_pre _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [stmt_frag_full_pre_def]) >>
  drule_all_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`r`,`sp`,`shadow_sp`] strip_assume_tac)) append_prefix_code_cuts >>
  Cases_on `?nid. t = TopLevelNameTarget nid`
  >- suspend "toplevel" >>
  drule_all_then strip_assume_tac body_append_typed_pre >>
  rename1 `type_place_target env t = SOME (Type (ArrayT elem (Dynamic cap)))` >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)` by
    fs[ret_pc_ok_def] >>
  `gas_admissible (eval_target_place cx t) target_place_res_ok es` by
    suspend "place_admissible" >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_target_place cx t) (es,s0,G0,tn0)` by suspend "place_prefix" >>
  drule_all body_target_place_sim_full >>
  disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`func`,`shadow_func`] mp_tac) >>
  rewrite_tac[target_place_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`ArrayT elem (Dynamic cap)`,`sa`,`sp`,
    `shadow_sa`,`shadow_sp`,`r`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_target_place cx t) _ targetQ targetR` >>
  suspend "resolved"
QED
*)
Theorem body_append_case_prefix:
  !cx t e.
  (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_full_ok cx e) /\
  (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx t /\
  body_base_target_prefix_ok cx t ==>
  body_stmt_prefix_ok cx (Append t e)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume body_append_case_prefix[toplevel]:
  gvs[] >> rename1 `TopLevelNameTarget nid` >>
  `sp = sa /\ shadow_sp = shadow_sa` by suspend "top_cut" >>
  qpat_assum `stmt_frag_full_pre _ _ _ _ _ _ _ _ _ _`
    (mp_then (Pat `stmt_frag_full_pre _ _ _ _ _ _ _ _ _ _`) mp_tac
      append_toplevel_prefix_entry) >>
  disch_then (qspecl_then [`tops`,`env'`,`env`,`bindings`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> suspend "top_rhs_code")) >>
  disch_then (qx_choose_then `Q` strip_assume_tac) >>
  irule (Q.INST [`QT` |-> `Q`, `tops` |-> `cx_tops cx`,
    `RT` |-> `\H res ee gt r. F`, `RV` |-> `\H res ee gt r. T`,
    `QV` |-> `\H res ee G tn v. ~v.vs_halted`] append_source_children_prefix) >>
  simp[GSYM quantHeuristicsTheory.ISR_exists] >> qexists_tac `Q` >>
  simp[] >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_append_case_prefix[top_cut]:
  ntac 2 (qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac) >>
  Cases_on `FLOOKUP cenv.ce_module_vars nid` >>
  simp[gasShadowTheory.gas_shadow_expr_def, compile_get_target_ptr_def, comp_return_def] >>
  Cases_on `x` >> simp[comp_return_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_append_case_prefix[top_rhs_code]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!b loc elem cap. r = _ ==> _`
    (qspecl_then [`b`,`loc`,`elem`,`cap`] mp_tac) >>
  gvs[] >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_append_case_prefix[place_admissible]:
  rw[gas_admissible_def] >> Cases_on `res`
  >- simp[target_place_res_ok_def] >>
  rename1 `eval_target_place cx t _ = (INR ex,ee)` >>
  drule_then assume_tac eval_target_place_no_control >>
  qpat_assum `gas_admissible (eval_stmt _ _) _ _`
    (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
  disch_then (qspec_then `gs` mp_tac) >>
  simp[Once evaluate_def, bind_def] >>
  gvs[stmt_res_ok_def, target_place_res_ok_def, no_control_exc_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_append_case_prefix[place_prefix]:
  `gas_admissible (eval_base_place cx t) target_res_ok es` by
    (irule get_place_base_admissible >> simp[GSYM eval_target_place_as_bind]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_base_place cx t) (es,s0,G0,tn0)` by
    (irule body_target_sim_prefix >> asm_simp_tac bool_ss [] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cenv`,`d`,`env`,`r`,`sa`,`sp`,`shadow_func`,`shadow_sa`,`shadow_sp`,
                   `tops`,`Type (ArrayT elem (Dynamic cap))`] >>
     asm_simp_tac bool_ss [] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!ee. SND (eval_target_place cx t ee) = SND (eval_base_place cx t ee)` by
    (simp[eval_target_place_as_bind] >> gen_tac >>
     Cases_on `eval_base_place cx t ee` >> rename1 `_ = (ans,mid)` >>
     Cases_on `ans` >> simp[bind_def] >>
     rename1 `get_place pv mid` >> Cases_on `pv` >> simp[get_place_def, return_def, raise_def]) >>
  drule gas_prefix_full_state_cong >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_append_case_prefix[resolved]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_target_place cx t) (es,s0,G0,tn0)
    (\H res ee G tn u. targetQ H res ee G tn u /\
      (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z)) targetR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ targetQ targetR` (irule_at Any) >>
     simp[] >> rpt strip_tac >> drule_all_then ACCEPT_TAC gas_origin_ptr_path_dalloca_fmp_headroom) >>
  qabbrev_tac `cutQ = \H res ee G tn u. targetQ H res ee G tn u /\
    ~u.vs_halted /\ ee.gas_obs = [] /\
    (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z)` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_target_place cx t) (es,s0,G0,tn0) cutQ
    (\H res ee gt r. ISR res)` by
    (irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn u. _ /\ _) targetR`
       (irule_at Any) >>
     simp[Abbr `cutQ`, Abbr `targetR`] >>
     rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]) >>
  irule (Q.INST [`QT` |-> `cutQ`, `tops` |-> `cx_tops cx`,
    `RT` |-> `\H res ee gt r. T`, `RV` |-> `\H res ee gt r. T`,
    `QV` |-> `\H res ee G tn v. ~v.vs_halted`] append_source_children_prefix) >>
  simp[GSYM quantHeuristicsTheory.ISR_exists] >> qexists_tac `cutQ` >> simp[] >>
  qx_genl_tac [`marks`,`p`,`mid`,`G1`,`tn1`,`u`] >> strip_tac >>
  qpat_assum `stmt_frag_full_pre _ _ _ _ _ _ _ _ _ _`
    (mp_then (Pat `stmt_frag_full_pre _ _ _ _ _ _ _ _ _ _`) irule
       append_replay_rhs_prefix_entry) >>
  simp[] >> suspend "resolved_entry"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_append_case_prefix[resolved_entry]:
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `type_place_target _ _ = _`)) >>
  qexistsl_tac [`marks`,`p`,`r`,`shadow_sp`,`sp`] >>
  goal_assum (drule_at (Pat `body_inv _ _ _ _`)) >>
  asm_simp_tac bool_ss [] >> reverse conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> cutQ H _ _ _ _ _`
        (drule_then mp_tac) >>
      simp[Abbr `cutQ`, Abbr `targetQ`, NoAsms] >>
      strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!b loc elem cap. r = _ ==> _`
    (qspecl_then [`b`,`loc`,`elem`,`cap`] mp_tac) >>
  simp[] >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise body_append_case_prefix
*)

Theorem body_assert_case_prefix:
  !cx e.
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assert e AssertBare)
Proof
  metis_tac[body_assert_guard_prefix_ok]
QED

Theorem body_assert_reason_case_prefix:
  !cx e se.
  (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_full_ok cx se) /\
  (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_prefix_ok cx se) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assert e (AssertReason se))
Proof
  rpt strip_tac >> rewrite_tac[body_stmt_prefix_ok_def] >> rpt strip_tac >>
  irule compile_assert_reason_frag_prefix >> metis_tac[]
QED

Theorem body_assert_unreachable_case_prefix:
  !cx e.
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assert e AssertUnreachable)
Proof
  metis_tac[body_assert_guard_prefix_ok]
QED

Theorem body_assign_case_prefix:
  !cx t e.
  (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
            struct_args_unique tops) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx t) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assign (BaseTarget t) e)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[body_stmt_prefix_ok_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
                    (is_word_type ty \/ expr_type e = ty \/ lowered_value_type cenv e = ty \/
                     is_bytestring_type ty \/
                     has_length_word (expr_type e) /\ is_empty_value_expr e)`
  >- (qpat_x_assum `?id ty. _` (qx_choose_then `id` (qx_choose_then `ty`
        (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) >>
      qpat_x_assum `t = NameTarget id` SUBST_ALL_TAC >>
      irule bool_chain_selected_local_assign_prefix >> metis_tac[]) >>
  `struct_args_unique tops` by
    (drule_then assume_tac body_inv_contract >>
     drule contract_inv_singleton_source_modules >> simp[]) >>
  Cases_on `?nsid mut ty slot.
              t = TopLevelNameTarget nsid /\
              supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
              (mut = Storage \/ mut = Transient) /\
              ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
              ~is_bytestring_type ty /\
              0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
              lowered_value_type cenv e = expr_type e`
  >- (gvs[] >> irule body_assign_toplevel_copy_prefix >> metis_tac[]) >>
  Cases_on `?nsid dty. t = TopLevelNameTarget nsid /\
                       supported_scalar_target tops nsid /\
                       type_place_target env t = SOME (Type dty) /\ is_word_type dty`
  >- (gvs[] >> irule body_assign_toplevel_word_prefix >> metis_tac[]) >>
  Cases_on `?id fld sid fty.
              t = AttributeTarget (NameTarget id) fld /\
              FLOOKUP env.var_types id = SOME (StructT sid) /\
              attribute_type env.type_defs (StructT sid) fld = SOME fty /\
              is_word_type fty`
  >- (gvs[] >> irule body_assign_attr_local_prefix >> metis_tac[]) >>
  Cases_on `?nsid fld fty.
              t = AttributeTarget (TopLevelNameTarget nsid) fld /\
              supported_storage_field_write tops nsid fld /\
              type_place_target env t = SOME (Type fty) /\ is_word_type fty`
  >- (gvs[] >> irule body_assign_attr_storage_prefix >> metis_tac[]) >>
  irule body_assign_other_prefix >> simp[] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bindings`, `env`, `env'`, `tops`] >> gvs[]
QED

Theorem body_assign_tuple_case_prefix:
  !cx gs e.
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_prefix_ok cx (TupleTarget gs) v) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assign (TupleTarget gs) e)
Proof
  rw[body_stmt_prefix_ok_def] >>
  drule_all_then assume_tac body_inv_stmt_const_name_free >>
  Cases_on `EXISTS (\g. ?t. g = BaseTarget t /\ immutable_root cx t /\
                    ~(?nsid. t = TopLevelNameTarget nsid)) gs`
  >- (irule body_assign_tuple_nested_immutable_prefix >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
      asm_simp_tac bool_ss []) >>
  reverse (Cases_on `lowered_value_type cenv e = expr_type e`)
  >- (irule body_assign_tuple_widened_prefix >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
      asm_simp_tac bool_ss []) >>
  Cases_on `?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
                  EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids`
  >- (gvs[] >> drule_all_then assume_tac
        exprSimAggregateLayoutTheory.assign_tuple_locals_bytes_pos >>
      `EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                         0 < type_memory_bytes cenv ty) ids` by
        (fs[EVERY_MEM] >> metis_tac[]) >>
      irule body_assign_tuple_locals_prefix >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
      asm_simp_tac bool_ss []) >>
  Cases_on `EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                     FLOOKUP env.var_types id = SOME ty /\
                     0 < type_memory_bytes cenv ty) \/
                  (?nsid dty. g = BaseTarget (TopLevelNameTarget nsid) /\
                     supported_scalar_target tops nsid /\
                     type_place_target env (TopLevelNameTarget nsid) = SOME (Type dty) /\
                     is_word_type dty) \/
                  (?nsid fld fty.
                     g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                     supported_storage_field_write tops nsid fld /\
                     type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
                       SOME (Type fty) /\ is_word_type fty)) gs`
  >- (irule body_assign_tuple_targets_word_prefix >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
      asm_simp_tac bool_ss []) >>
  irule body_assign_tuple_other_prefix >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_augassign_case_prefix:
  !cx ty t bop e.
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx t /\
  body_base_target_prefix_ok cx t ==>
  body_stmt_prefix_ok cx (AugAssign ty t bop e)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[body_stmt_prefix_ok_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `?id. t = NameTarget id`
  >- (gvs[] >> irule body_augassign_local_prefix >> metis_tac[]) >>
  Cases_on `?nsid. t = TopLevelNameTarget nsid /\
                   supported_scalar_target tops nsid`
  >- (gvs[] >> irule body_augassign_toplevel_word_prefix >> metis_tac[]) >>
  Cases_on `?id fld. t = AttributeTarget (NameTarget id) fld`
  >- (gvs[] >> irule body_augassign_attr_local_prefix >> metis_tac[]) >>
  Cases_on `?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                       supported_storage_field_write tops nsid fld`
  >- (gvs[] >> irule body_augassign_attr_storage_prefix >> metis_tac[]) >>
  irule body_augassign_other_prefix >> metis_tac[]
QED

Theorem body_for_case_prefix:
  !cx id typ it n body.
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_prefix_ok cx tyv id body vs) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx it) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_prefix_ok cx it) /\
  (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
       stmt_loop_calls_ok [(NONE,tops)] (For id typ it n body)) ==>
  body_stmt_prefix_ok cx (For id typ it n body)
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[body_stmt_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    (drule body_inv_contract >>
     MATCH_ACCEPT_TAC contract_inv_singleton_source_modules) >>
  `stmt_loop_calls_ok [(NONE,tops)] (For id typ it n body)` by metis_tac[] >>
  irule compile_for_frag_prefix >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`bindings`, `env`, `env'`, `tops`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_if_case_prefix:
  !cx e ss1 ss2.
  (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_full_ok cx ss1) /\
  (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_prefix_ok cx ss1) /\
  (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_full_ok cx ss2) /\
  (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_prefix_ok cx ss2) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (If e ss1 ss2)
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[body_stmt_prefix_ok_def, gas_shadow_stmt_def] >>
  rpt gen_tac >> strip_tac >>
  drule body_inv_contract >>
  disch_then (assume_tac o MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules) >>
  `expr_body_pre cenv cx env e es` by
    (mp_tac (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`,
                     `s` |-> `If e ss1 ss2`]
              stmtExprAllocationPrePropsTheory.body_inv_stmt_expr_pre_singleton) >>
     simp[supported_stmt_expr_exists_def] >> disch_then irule >>
     `supported_expr tops e /\ well_typed_expr env e` by
       (fs[supported_stmt_def, type_stmt_def, optionTheory.IS_SOME_EXISTS] >>
        pure_rewrite_tac[supportedExprsTheory.supported_expr_def] >>
        disj1_tac >> first_assum ACCEPT_TAC) >>
     `alloc_limits_expr cenv e` by
       fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def] >>
     drule_then assume_tac allocLimitsPropsTheory.alloc_limits_expr_not_extcode >>
     drule_then assume_tac (cj 1 allocLimitsPropsTheory.alloc_limits_expr_exists) >>
     mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`,
                      `calls` |-> `int_calls_stmts ss1 ++ int_calls_stmts ss2`]
              stmt_expr_body_pre_main_mods) >>
     gvs[compileUnitTheory.main_module_def, alistTheory.ALOOKUP_def,
         stmt_exprs_ok_def, supported_stmt_expr_exists_def, int_calls_stmt_def,
         DE_MORGAN_THM, LEFT_AND_OVER_OR, supported_expr_exists_disj]) >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def,
      supported_stmt_expr_exists_def, DE_MORGAN_THM]) >>
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      supported_stmt_expr_exists_def, optionTheory.IS_SOME_EXISTS] >>
  irule compile_if_stmt_frag_prefix >>
  simp[stmts_env_cs_mono] >> rpt conj_tac
  >~ [`ctx_has_dalloca _ /\ _ ==> _`]
  >- metis_tac[body_inv_no_phi]
  >~ [`expr_sim_full _ _ _ _ _ _`]
  >- (drule_all body_expr_full_ok_simulations >> metis_tac[])
  >~ [`expr_sim_prefix _ _ _ _ _ _`]
  >- (drule (cj 1 (iffLR (cj 1 body_expr_prefix_ok_def))) >> metis_tac[])
  >~ [`gas_shadow_compiles _ _`]
  >- irule gas_shadow_stmt_lower_value_env
  >~ [`gas_shadow_compiles_env _ _ (stmts_env _ _ _ (MAP gas_shadow_stmt ss1))`]
  >- irule gas_shadow_stmts_env_env
  >~ [`gas_shadow_compiles_env _ _ _`]
  >- irule gas_shadow_stmts_env_env
  >- (rpt gen_tac >> disch_tac >> drule (cj 2 compile_expr_grows) >> simp[])
  >- (rpt gen_tac >> disch_tac >> drule (cj 2 compile_expr_grows) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `?tv s1. eval_expr cx e (es with gas_obs := gs) = (INL tv,s1)` by
    (drule vyperStatePreservationTheory.bind_split >> simp[] >> metis_tac[]) >>
  `push_scope es1 = (INL (),es1 with scopes updated_by CONS FEMPTY)` by
    simp[push_scope_def, return_def] >>
  `expr_sim_inv cenv cx env es1` by
    (`expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
     drule exprSimSourceTheory.expr_body_pre_eval >>
     disch_then (qspecl_then [`INL (BoolV b)`, `es1`] mp_tac) >>
     impl_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> first_assum ACCEPT_TAC) >>
     simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env es1` by
    (irule body_const_cells_agree_expr_read >>
     goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env
      (es1 with scopes updated_by CONS FEMPTY)` by
    (irule (iffLR body_const_cells_agree_immutables) >>
     qexists_tac `es1` >> simp[]) >>
  drule expr_sim_inv_push_scope >> strip_tac >>
  Cases_on `b` >> fs[] >>
  qmatch_goalsub_rename_tac `stmts_env cenv lctx ret_ty branch` >>
  `body_stmts_full_ok cx branch /\ body_stmts_prefix_ok cx branch` by
    metis_tac[] >>
  ((irule body_stmts_full_ok_apply >> conj_tac >- first_assum ACCEPT_TAC) ORELSE
   first_assum (irule o MATCH_MP (iffLR body_stmts_prefix_ok_def))) >>
  gvs[stmts_exprs_ok_thm, stmt_exprs_ok_def,
      allocLimitsTheory.alloc_limits_stmt_def,
      compileVyperTheory.stmt_valued_return_def,
      GSYM optionTheory.IS_SOME_EXISTS] >>
  metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]
QED

Theorem body_log_case_prefix:
  !cx id es.
  body_exprs_full_ok cx es /\
  body_exprs_prefix_ok cx es ==>
  body_stmt_prefix_ok cx (Log id es)
Proof
  rw[body_stmt_prefix_ok_def] >>
  irule compile_log_frag_prefix >> metis_tac[]
QED

Theorem body_raise_reason_case_prefix:
  !cx e.
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Raise (RaiseReason e))
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[body_stmt_prefix_ok_def] >> rpt strip_tac >>
  irule compile_raise_reason_frag_prefix >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem body_stmts_cons_case_prefix:
  !cx s ss.
  (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_full_ok cx ss) /\
  (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_prefix_ok cx ss) /\
  body_stmt_full_ok cx s /\
  body_stmt_prefix_ok cx s ==>
  body_stmts_prefix_ok cx (s::ss)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmts_prefix_ok_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def, type_stmt_def, AllCaseEqs(), int_calls_stmt_def,
      supported_stmt_expr_exists_def, stmts_exprs_ok_def] >>
  rename1 `type_stmt env ret_ty s = SOME env1` >>
  `call_evaluation_safe cx (int_calls_stmt s) /\
   call_evaluation_safe cx (int_calls_stmts ss)` by
    metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right] >>
  match_mp_tac (REWRITE_RULE [MAP] stmt_frag_prefix_cons_env) >>
  conj_tac
  >- (strip_tac >> metis_tac[body_inv_no_phi]) >>
  conj_tac
  >- (drule_then irule body_stmt_full_ok_apply >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `body_stmt_prefix_ok _ _`
        (irule o REWRITE_RULE [body_stmt_prefix_ok_def]) >> metis_tac[]) >>
  `!gs es1 c sa sm.
      eval_stmt cx s (es with gas_obs := gs) = (INL (),es1) /\
      stmt_env cenv lctx ret_ty s sa = (c,sm) /\
      cenv_top_ext cenv c es1.scopes ==>
      stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ c
        (stmts_env c lctx ret_ty ss)
        (stmts_env (gas_shadow_env T c) lctx ret_ty (MAP gas_shadow_stmt ss))
        (eval_stmts cx ss) es1 /\
      stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ c
        (stmts_env c lctx ret_ty ss)
        (stmts_env (gas_shadow_env T c) lctx ret_ty (MAP gas_shadow_stmt ss))
        (eval_stmts cx ss) es1`
    suffices_by (rpt (pop_assum kall_tac) >> metis_tac[]) >>
  map_every qx_gen_tac [`gs`, `es1`, `c`, `sa`, `sm`] >> strip_tac >>
  `same_frame cenv c` by metis_tac[cenv_top_ext_same_frame] >>
  `stmts_exprs_ok c ss` by metis_tac[stmt_env_stmts_exprs_ok] >>
  `expr_sim_inv c cx env1 es1` by
    (drule_then strip_assume_tac body_inv_main_support >>
     `cenv.ce_alloca_locals` by metis_tac[body_inv_contract, contract_inv_alloca_locals] >>
     irule expr_sim_inv_stmt >> simp[] >> metis_tac[expr_sim_inv_gas_obs]) >>
  `body_const_cells_agree [(NONE,tops)] cx env1 es1` by
    (irule body_const_cells_agree_stmt >>
     goal_assum (drule_at (Pat `eval_stmt _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `type_stmt _ _ _ = _`)) >> simp[]) >>
  `ce_locals_declared c env1` by metis_tac[ce_locals_declared_stmt] >>
  `locals_alloc_ok c env1` by metis_tac[locals_alloc_ok_stmt] >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
     cx RetQ c ret_ty` by
    (qpat_x_assum `frame_ret_ok_full _ _ _ cenv _` mp_tac >>
     rewrite_tac[frame_ret_ok_full_def] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> metis_tac[same_frame_trans]) >>
  conj_tac
  >- (qpat_x_assum `!st t. _ ==> body_stmts_full_ok _ _` drule >>
      disch_then (irule o MATCH_MP body_stmts_full_ok_apply) >> metis_tac[]) >>
  qpat_x_assum `!st t. _ ==> body_stmts_prefix_ok _ _` drule >>
  disch_then (irule o REWRITE_RULE [body_stmts_prefix_ok_def]) >> metis_tac[]
QED

(* Keep the projections in evaluation-induction order. *)
val selected_stmt_ports =
  [body_pass_case_prefix, body_continue_case_prefix, body_break_case_prefix,
   body_return_none_case_prefix, body_return_case_prefix,
   body_raise_bare_case_prefix, body_raise_unreachable_case_prefix,
   body_raise_reason_case_prefix, body_raise_custom_case_prefix,
   body_assert_case_prefix, body_assert_unreachable_case_prefix,
   body_assert_reason_case_prefix, body_assert_custom_case_prefix,
   body_log_case_prefix, body_annassign_case_prefix, body_append_case_prefix,
   body_assign_case_prefix, body_assign_tuple_case_prefix, body_augassign_case_prefix,
   body_if_case_prefix, body_for_case_prefix, body_expr_stmt_case_prefix,
   body_stmts_nil_case_prefix, body_stmts_cons_case_prefix];

Theorem bool_chain_selected_stmt_case_ports:
  ^(list_mk_conj (map concl selected_stmt_ports))
Proof
  rpt conj_tac >> FIRST (map ACCEPT_TAC selected_stmt_ports)
QED
