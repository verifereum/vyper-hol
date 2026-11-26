(* Shared setup for the full and request-prefix Range drivers. *)
structure rangeForDriverLib =
struct
open HolKernel boolLib bossLib
open bodyFullPredsTheory bodyFullForFactsTheory bodyFullGhostFrameTheory
     stmtSimDefsTheory loweringStateRelDefsTheory loweringPostsTheory
     compileEnvTheory vyperInterpreterTheory vyperStateTheory vyperASTTheory
     integerTheory listTheory finite_mapTheory pred_setTheory wordsTheory
     venomStateTheory venomInstTheory ptrDisciplineTheory fragExecTheory
     fragGasOriginPtrTheory vyperStorageFootprintTheory
     bodyInvSplitTheory bodyInvExecutionPropsTheory bodyInvCodePropsTheory
     vyperTypeSystemTheory stmtSimForRangeTheory supportedStmtsTheory
     supportedStmtTraverseTheory supportedExprTraverseTheory
     bodyExprPreFactsTheory exprLoweringPropsTheory gasShadowTheory
     stmtLoweringTheory bodySimTheory gasShadowStateTheory gasOutcomeFullTheory
     localPtrsPropsTheory exprSimHypsDefsTheory bodyFullShadowBodyInvTheory
     stmtSimPropsTheory bodyMemoryDefsTheory stmtSimForPartsTheory
     bodyPtrDefsTheory vyperStorageTraceTheory loweringSliceTheory valueEncodingTheory

(* Called after opening the client's fragment predicate. Neither this
   setup nor layout selection consumes the client's additional IHs. *)
fun range_driver_static_tac outer_env static_pre =
  `cenv' = cenv` by (metis_tac[outer_env]) >>
  pop_assum SUBST_ALL_TAC >>
  drule_all static_pre >> strip_tac >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    (drule_then assume_tac exprSimAbiDecodeEntryTypingTheory.abi_decode_inv_type_env >>
     drule assignable_type_well_formed >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x` by
    (rpt strip_tac >>
     qpat_assum `ret_pc_ok cenv sa s0`
       (drule_then (ACCEPT_TAC o CONJUNCT1) o REWRITE_RULE [ret_pc_ok_def]));

fun range_driver_layout_tac prepare =
  prepare >>
  disch_then (qspecl_then
    [`cx`, `id`, `typ`, `e1`, `e2`, `n`, `body`, `DF`, `lo`, `d`, `PG`, `tops`,
     `bindings`, `ctx`, `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `env'`,
     `ret_ty`, `lctx`, `RetQ`, `tyv`, `sa`, `sb`, `shadow_sa`, `shadow_sb`]
    (mp_tac o BETA_RULE o PURE_ONCE_REWRITE_RULE [LET_THM])) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then
      [`st`, `bc`, `body_cenv`, `body_env'`, `sb0`, `sb1`, `shadow_sb0`, `shadow_sb1`,
       `p`, `sz`, `ainst`, `cv`, `ev`, `dv`, `nv`, `entry_lbl`, `cond_lbl`, `exit_lbl`,
       `body_lbl`, `incr_lbl`, `j1`, `j2`, `j3`, `bbb`, `i1`, `i2`, `i3`, `sj`,
       `op1`, `s1`, `op2`, `rv`, `g1`, `z1`, `g2`, `z2`]
      (fn pkg =>
        let val clauses = CONJUNCTS pkg in
          EVERY (map assume_tac (Lib.butlast clauses)) >>
          mk_asm "round_cons" (List.last clauses)
        end) o BETA_RULE o PURE_REWRITE_RULE [LET_THM]);

fun range_driver_cases_tac literal computed =
  Q_TAC ASM_CASES_TAC `?a1 m1 a2 m2. e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2)`
  >- literal >>
  qpat_x_assum `~(?a1 m1 a2 m2. e1 = _ /\ e2 = _) ==> _`
    (fn th => drule_then strip_assume_tac th) >> computed;

(* Reconcile the paired compiler runs before either endpoint simulation. *)
val range_checked_shadow_edges_tac =
  let
    fun shadow_edge expr start shadowStart related leftEq shadowRun rightEq out mid =
      namedCases_on shadowRun [out ^ " " ^ mid] >>
      qpat_assum related (fn rel =>
        qpat_assum leftEq (fn left =>
          qpat_assum rightEq (fn right =>
            qspecl_then [start,shadowStart]
              (strip_assume_tac o SRULE [rel,left,right])
              (REWRITE_RULE [gas_shadow_compiles_def]
                (Q.INST [`ty` |-> `typ`, `e` |-> expr, `sd` |-> `T`]
                  gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env)))))
  in
    shadow_edge `e1` `sa` `shadow_sa` `gas_shadow_state sa shadow_sa`
      `lower_value compile_expr cenv typ e1 sa = _`
      `lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e1) shadow_sa`
      `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _`
      "shadow_op1" "shadow_s1" >>
    qpat_x_assum `op1 = shadow_op1` (SUBST_ALL_TAC o SYM) >>
    shadow_edge `e2` `s1` `shadow_s1` `gas_shadow_state s1 shadow_s1`
      `lower_value compile_expr cenv typ e2 s1 = _`
      `lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e2) shadow_s1`
      `lower_value _ _ _ (gas_shadow_expr e2) shadow_s1 = _`
      "shadow_op2" "shadow_st" >>
    qpat_x_assum `op2 = shadow_op2` (SUBST_ALL_TAC o SYM)
  end;

val range_checked_code_tac =
  let
    fun grows eq = qpat_assum eq
      (mp_then Any strip_assume_tac (cj 2 compile_expr_grows))
  in
    grows `lower_value _ _ _ e1 sa = (op1,s1)` >>
    grows `lower_value _ _ _ e2 s1 = (op2,st)` >>
    grows `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = (op1,shadow_s1)` >>
    grows `lower_value _ _ _ (gas_shadow_expr e2) shadow_s1 = (op2,shadow_st)`
  end >>
  `cs_extends shadow_sa shadow_st` by
    (irule cs_extends_trans >> qexists_tac `shadow_s1` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!e a m. gas_shadow_expr e = Literal a (IntL m) ==> e = Literal a (IntL m)` by
    (Cases >> simp[NoAsms, gas_shadow_expr_def]) >>
  `~(?a1 m1 a2 m2. gas_shadow_expr e1 = Literal a1 (IntL m1) /\
                     gas_shadow_expr e2 = Literal a2 (IntL m2))` by
    (strip_tac >> qpat_x_assum `~(?a1 m1 a2 m2. e1 = _ /\ e2 = _)` mp_tac >>
     simp[NoAsms] >> qexistsl_tac [`a1`,`m1`,`a2`,`m2`] >>
     conj_tac >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `for_range_checked_code (gas_shadow_env T cenv) lctx ret_ty id typ n (MAP gas_shadow_stmt body)
      op1 op2 shadow_st = ((),shadow_sb)` by
    (qpat_assum `compile_stmt _ _ _ _ shadow_sa = ((),shadow_sb)` (SUBST1_TAC o SYM) >>
     sym_tac >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _`
       (mp_then Any irule compile_stmt_for_range_checked) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `cenv.ce_alloca_locals` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (ACCEPT_TAC o MATCH_MP contract_inv_alloca_locals o MATCH_MP body_inv_contract)) >>
  `!c lc s t. compile_stmts c lc ret_ty (MAP gas_shadow_stmt body) s = ((),t) ==>
               cs_extends s t` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (cj 2 stmtLoweringMonoTheory.compile_stmt_cs_mono) >>
     simp[NoAsms, cs_mono_def] >> disch_then drule >> simp[]) >>
  `cs_extends shadow_st shadow_sb` by
    (qpat_assum `for_range_checked_code _ _ _ _ _ _ _ _ _ shadow_st = _`
       (mp_then Any (qspecl_then [`shadow_sa`,`shadow_func`] mp_tac)
          for_range_checked_parts) >>
     impl_tac
     >- (conj_tac >- simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  let
    fun split a b c fnm = qspecl_then [a,b,c,fnm] mp_tac fn_has_code_split >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac
  in
    split `sa` `st` `sb` `func` >>
    split `sa` `s1` `st` `func` >>
    split `shadow_sa` `shadow_st` `shadow_sb` `shadow_func` >>
    split `shadow_sa` `shadow_s1` `shadow_st` `shadow_func`
  end;

val range_checked_source_tac =
  `supported_pure_expr tops e1 /\ supported_pure_expr tops e2` by
    (qpat_assum `supported_iterator _ _ _ _` mp_tac >>
     qpat_assum `~(?a1 m1 a2 m2. e1 = _ /\ e2 = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[supported_iterator_def, AllCaseEqs()] >>
     Cases_on `e1` >> simp[] >> Cases_on `e2` >> simp[] >>
     simp[supportedExprsTheory.supported_pure_expr_def]) >>
  `cx_tops cx = tops` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (ACCEPT_TAC o cj 2 o MATCH_MP body_inv_main_code)) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
            is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)` by
    (qpat_assum `cx_tops cx = tops` (rewrite_tac o single) >>
     gen_tac >> disch_tac >>
     qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `is_dynamic (vyper_to_abi_type (get_tenv cx) target)`
         (fn abi => ACCEPT_TAC
           (MATCH_MP body_inv_singleton_abi_types (CONJ inv abi))))) >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (ACCEPT_TAC o MATCH_MP body_inv_main_support)) >>
  let
    fun ready e =
      sg ([QUOTE "!ee. expr_sim_inv cenv cx env ee ==> expr_body_pre cenv cx env "] @
          e @ [QUOTE " ee"]) >-
      (qx_gen_tac `ee` >> strip_tac >>
       sg ([QUOTE "supported_expr tops "] @ e) >-
         simp[supportedExprsTheory.supported_expr_def] >>
       drule_all_then strip_assume_tac
         bodySingletonCallSupportTheory.supported_singleton_expr_body_calls >>
       sg ([QUOTE "~supported_expr_exists (const_name_root cx) "] @ e) >-
         (drule_all body_inv_stmt_const_name_free >>
          simp[supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
               supportedStmtTraverseTheory.supported_iterator_exists_def]) >>
       sg ([QUOTE "~is_extcode "] @ e) >-
         (qpat_assum ([QUOTE "alloc_limits_expr cenv "] @ e)
           (mp_then Any ACCEPT_TAC allocLimitsPropsTheory.alloc_limits_expr_not_extcode)) >>
       qspecl_then [`cenv`,`cx`,`env`,e,`ee`,`[]`] mp_tac stmt_expr_body_pre_alloc >>
       impl_tac >- (simp[] >> strip_tac >> qexists_tac `tops` >> simp[]) >>
       disch_then ACCEPT_TAC)
  in
    ready `e1` >> ready `e2`
  end;

(* Keep the full endpoint outcome available even in the prefix driver:
   the succeeding endpoint can only start after its normal replay. *)
fun range_endpoint_full_tac endpoint source entry_args ready =
  sg (`expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx typ ` @
      endpoint @ ` ` @ source) >-
    (irule (cj 1 bodyFullSimProjectionTheory.body_expr_full_ok_simulations) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`env`,`tops`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum mp_tac >>
  pure_once_rewrite_tac [bodySimFullTheory.expr_sim_full_def] >>
  disch_then (qspecl_then (`st0` :: entry_args) mp_tac) >>
  impl_tac >- ready >> disch_tac;

fun range_endpoint_headroom_tac outcome strengthened =
  qmatch_asmsub_abbrev_tac outcome >>
  sg strengthened >-
    (unabbrev_all_tac >> irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[NoAsms] >> rpt strip_tac >>
     drule_all bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >>
     simp[]) >>
  qpat_x_assum outcome kall_tac >> unabbrev_all_tac;

val range_first_endpoint_tac =
  qpat_assum `!tenv s'' tyv t. _ ==> body_iterator_full_ok _ _`
    (qspecl_then [`get_tenv cx`,`es`,`tyv`,`es`] mp_tac) >>
  impl_tac >- simp[lift_option_type_def, return_def] >>
  disch_then (mp_then Any strip_assume_tac
    bodyFullRangeProjectionTheory.body_iterator_full_ok_range) >>
  `expr_body_pre cenv cx env e1 es` by
    (qpat_assum `!ee. _ ==> expr_body_pre _ _ _ e1 ee`
      (qspec_then `es` mp_tac) >> simp[]) >>
  range_endpoint_full_tac `e1` `es`
    [`sa`,`s1`,`shadow_sa`,`shadow_s1`,`op1`,`s0`,`G0`,`tn0`]
    (rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
            irule exprSimSourceTheory.expr_body_pre_gas_admissible >>
            goal_assum (drule_at Any)]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (fn inv => qpat_assum `MEM func ctx.ctx_functions`
         (fn member => ACCEPT_TAC
           (MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi (CONJ inv member))))) >>
  range_endpoint_headroom_tac
    `gas_outcome_full cfg tops' cx st0 (bind (eval_expr cx e1) _) (es,s0,G0,tn0) Q0 R0`
    `gas_outcome_full cfg tops' cx st0 (bind (eval_expr cx e1) (read_result cx))
      (es,s0,G0,tn0) (\H res ee G tn t. Q0 H res ee G tn t /\
        (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z)) R0`;

fun range_second_endpoint_tac ready =
  range_endpoint_full_tac `e2` `mid1`
    [`s1`,`st`,`shadow_s1`,`shadow_st`,`op2`,`t1`,`G1`,`tn1`] ready >>
  range_endpoint_headroom_tac
    `gas_outcome_full cfg tops' cx st0 (bind (eval_expr cx e2) _) (mid1,t1,G1,tn1) Q0 R0`
    `gas_outcome_full cfg tops' cx st0 (bind (eval_expr cx e2) (read_result cx))
      (mid1,t1,G1,tn1) (\H res ee G tn t. Q0 H res ee G tn t /\
        (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z)) R0`;

(* Facts at the normal first-endpoint midpoint. The selected bind rule
   supplies this midpoint and its domain; neither tactic chooses a new one. *)
val range_first_replay_tac =
  `!fn inst z. frag_reachable ctx func t1 fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid1.storage_trace` mp_tac) >>
     impl_tac >- (qpat_assum `storage_trace_domain cx st0 mid1.storage_trace`
       (ACCEPT_TAC o PURE_ONCE_REWRITE_RULE [storage_trace_domain_def])) >>
     disch_then strip_assume_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!tail. bind (eval_expr cx e1) (read_result cx) _ = (INL v1,mid1 with gas_obs := tail)`
    (qspec_then `[]` (mk_asm "read1")) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid1` by
    (`well_typed_expr env e1` by
       qpat_assum `expr_body_pre cenv cx env e1 es`
         (ACCEPT_TAC o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
     `body_const_cells_agree [(NONE,tops)] cx env (mid1 with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     asm "read1" (irule_at Any) >> simp[]) >>
  `expr_sim_inv cenv cx env mid1 /\ expr_result_typed env e1 (Value v1)` by
    (asm "read1" (mp_then Any mp_tac
       (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval)) >>
     disch_then (qspecl_then [`cenv`,`env`] mp_tac) >>
     impl_tac >- simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
     simp[NoAsms, exprSimHypsDefsTheory.expr_sim_inv_gas_obs]);

(* Select the full or prefix guard, using the same successful e1 read. *)
fun range_second_guard_tac guard =
  qpat_assum guard irule >>
  asm "read1" (mp_then Any mp_tac vyperStatePreservationTheory.bind_split) >>
  simp[NoAsms] >> disch_then (qx_choosel_then [`tv`,`src1`] strip_assume_tac) >>
  qexistsl_tac [`es with gas_obs := gas_explicit marks1 s0.vs_gas_readings`,
    `tv`,`src1`,`src1`,`v1`,`mid1 with gas_obs := []`] >>
  conj_tac >> first_assum ACCEPT_TAC;

val range_second_pre_tac =
  `expr_body_pre cenv cx env e2 mid1` by
    (qpat_assum `!ee. _ ==> expr_body_pre _ _ _ e2 ee`
       (qspec_then `mid1` mp_tac) >> simp[]) >>
  `return_buf_frame d cenv s1 t1 /\
   (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) t1)` by
    (qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid1.storage_trace` mp_tac) >>
     impl_tac >- simp[GSYM storage_trace_domain_def] >>
     disch_then (strip_assume_tac o PURE_ONCE_REWRITE_RULE [expr_post_def]) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC]);

val range_second_entry_tac =
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid1.storage_trace` mp_tac) >>
  impl_tac >- (qpat_assum `storage_trace_domain cx st0 mid1.storage_trace`
      (ACCEPT_TAC o PURE_ONCE_REWRITE_RULE [storage_trace_domain_def])) >> strip_tac >>
  qpat_assum `expr_post _ _ _ _ _ e1 es sa s1 s0 mid1 v1 op1 t1`
    (assume_tac o cj 6 o PURE_ONCE_REWRITE_RULE [expr_post_def]) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[],
    gen_tac >> gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[],
    irule exprSimSourceTheory.expr_body_pre_gas_admissible >>
      goal_assum (drule_at Any),
    qx_gen_tac `H` >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
    disch_then (strip_assume_tac o PURE_ONCE_REWRITE_RULE [expr_post_def]) >>
    rpt conj_tac >> first_assum ACCEPT_TAC];

(* Two successful reads yield the integer endpoints and the snapshots used
   for the checked initializer. These are the endpoints' actual bind states. *)
val range_checked_read_tac =
  qpat_assum `!tail. bind (eval_expr cx e2) (read_result cx) _ = (INL v2,mid2 with gas_obs := tail)`
    (qspec_then `[]` (mk_asm "read2")) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid2` by
    (`well_typed_expr env e2` by
       qpat_assum `expr_body_pre cenv cx env e2 mid1`
         (ACCEPT_TAC o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
     `body_const_cells_agree [(NONE,tops)] cx env (mid2 with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     asm "read2" (irule_at Any) >> simp[]) >>
  `expr_sim_inv cenv cx env mid2 /\ expr_result_typed env e2 (Value v2)` by
    (asm "read2" (mp_then Any mp_tac
       (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval)) >>
     disch_then (qspecl_then [`cenv`,`env`] mp_tac) >>
     impl_tac >- simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
     simp[NoAsms, exprSimHypsDefsTheory.expr_sim_inv_gas_obs]) >>
  let
    val endpoint = SRULE [SF ETA_ss] (SIMP_RULE std_ss [pairTheory.FORALL_PROD]
      (CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX))) bodySimDeclCasesTheory.body_range_endpoint_read))
    fun read pre value finish label num =
      sg pre >- simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
      qpat_x_assum pre (mp_then Any mp_tac endpoint) >>
      disch_then (qspecl_then [`tyv`,value,finish] mp_tac) >>
      impl_tac >- asm label (fn th => simp[SRULE [SF ETA_ss] th]) >>
      disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then num strip_assume_tac))
  in
    read `expr_body_pre cenv cx env e1 (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings)`
      `v1` `mid1 with gas_obs := []` "read1" `n1` >>
    read `expr_body_pre cenv cx env e2 (mid1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings)`
      `v2` `mid2 with gas_obs := []` "read2" `n2`
  end;

(* Compose the endpoint frames at the normal midpoint horizons. *)
val range_checked_frame_tac =
  let
    fun project post domain horizon =
      qpat_assum post (qspec_then horizon mp_tac) >>
      impl_tac >- (qpat_assum domain
        (ACCEPT_TAC o PURE_ONCE_REWRITE_RULE [storage_trace_domain_def])) >>
      disch_then (strip_assume_tac o
        PURE_ONCE_REWRITE_RULE [expr_post_def,ghost_kept_at_def])
  in
    project `!H. valid_horizon _ _ H mid1.storage_trace ==> expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
      `storage_trace_domain cx st0 mid1.storage_trace` `storage_trace_horizon mid1.storage_trace` >>
    project `!H. valid_horizon _ _ H mid2.storage_trace ==> expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _ /\ _`
      `storage_trace_domain cx st0 mid2.storage_trace` `storage_trace_horizon mid2.storage_trace`
  end >>
  `storage_trace_domain cx st0 es.storage_trace` by
    (asm "read1" (mp_then Any mp_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
       storage_trace_frame_prefix)) >>
     impl_tac >- simp[storage_trace_frame_bind_all,storage_trace_frame_read_result,
                      cj 5 evaluate_storage_trace_frame] >>
     simp[NoAsms] >> disch_then (qx_choose_then `obs` assume_tac) >>
     irule storage_trace_domain_prefix >> qexists_tac `obs` >>
     qpat_assum `mid1.storage_trace = _` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ es s0 /\ _`
    (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
  impl_tac >- (qpat_assum `storage_trace_domain cx st0 es.storage_trace`
    (ACCEPT_TAC o PURE_ONCE_REWRITE_RULE [storage_trace_domain_def])) >> strip_tac >>
  asm "read1" (mp_then Any mp_tac eval_read_preserves_scopes_dom) >>
  asm "read2" (mp_then Any mp_tac eval_read_preserves_scopes_dom) >>
  simp[NoAsms] >> rpt (disch_then assume_tac) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv mid1 t1` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qexistsl_tac [`storage_trace_horizon es.storage_trace`,`ctx`,`cx`,`func`] >>
       first_assum ACCEPT_TAC]) >>
  `alloca_frame cenv mid1 s1 t1 cenv mid2 t2` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qexistsl_tac [`storage_trace_horizon mid1.storage_trace`,`ctx`,`cx`,`func`] >>
       first_assum ACCEPT_TAC]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s1 x` by
    (gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  asm "frame_comp" (fn comp =>
    qpat_assum `alloca_frame cenv es sa s0 cenv mid1 t1`
      (mp_then (Pat `alloca_frame _ _ _ _ _ _ _`) (mk_asm "frame_comp_1") comp)) >>
  asm "frame_comp_1" (fn comp =>
    qpat_assum `alloca_frame cenv mid1 s1 t1 cenv mid2 t2`
      (mp_then (Pat `alloca_frame _ _ _ _ _ _ _`) mp_tac comp)) >>
  (* The abstract map range of the conditional frame is fixed by its
     hypothesis. Compose the real provenance equalities separately. *)
  disch_then (mp_tac o Q.SPECL
    [`func`,`ctx`,`FEMPTY`,`tn0`,`FEMPTY`,`tn1`,`FEMPTY`,`tn2`]) >>
  (impl_tac >- (asm_rewrite_tac [] >>
    rpt conj_tac >> qx_gen_tac `x` >> disch_tac >>
    first_assum (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
  strip_tac >>
  `!x. not_fresh_at sa x ==>
    FLOOKUP G2 x = FLOOKUP G0 x /\ op_taint tn2 (Var x) = op_taint tn0 (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at s1 x`
       (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP G1 x = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at s1 x ==> FLOOKUP G2 x = _ /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac []);

val range_checked_operands_tac =
  `is_word_type typ` by
    (qpat_assum `is_int_type typ` mp_tac >> Cases_on `typ` >> simp[NoAsms] >>
     rename1 `is_int_type (BaseT bt) ==> _` >> Cases_on `bt` >>
     simp[NoAsms,is_word_type_def]) >>
  let
    fun word goal rel = sg goal >-
      (qpat_assum rel
         (qx_choose_then `we` (CONJUNCTS_THEN2 assume_tac (qspec_then `tyv` mp_tac)) o
          PURE_ONCE_REWRITE_RULE [expr_val_rel_def]) >>
       simp[post_value_type_word, exprSimPropsTheory.typed_val_to_w256_word_value,
            word_value_def, val_to_w256_def])
  in
    word `eval_operand op1 t1 = SOME (i2w n1)` `expr_val_rel _ _ _ op1 t1` >>
    word `eval_operand op2 t2 = SOME (i2w n2)` `expr_val_rel _ _ _ op2 t2`
  end >>
  qpat_assum `lower_value _ _ _ e1 sa = (op1,s1)`
    (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
  disch_then (qspecl_then [`cx`,`env`,`es`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_assum `lower_value _ _ _ e2 s1 = (op2,st)`
    (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
  disch_then (qspecl_then [`cx`,`env`,`mid1`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `eval_operand op1 t2 = SOME (i2w n1)` by
    (MATCH_MP_TAC (Q.SPECL [`op1`,`s1`,`t1`,`t2`,`i2w n1`]
       exprBopSimPropsTheory.eval_operand_frame) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `is_word_type (post_value_type cenv e1)` by simp[post_value_type_word] >>
  qpat_assum `is_word_type (post_value_type cenv e1)` (fn wt =>
    qpat_assum `ptr_val_ok _ _ _ op1 G1 tn1 t1`
      (strip_assume_tac o REWRITE_RULE [ptr_val_ok_def,wt])) >>
  `is_word_type (post_value_type cenv e2)` by simp[post_value_type_word] >>
  qpat_assum `is_word_type (post_value_type cenv e2)` (fn wt =>
    qpat_assum `ptr_val_ok _ _ _ op2 G2 tn2 t2`
      (strip_assume_tac o REWRITE_RULE [ptr_val_ok_def,wt])) >>
  `!x. op1 = Var x \/ op2 = Var x ==>
       not_fresh_at st x /\ op_prov G2 (Var x) = NONE /\ op_taint tn2 (Var x) = {}` by
    (qx_gen_tac `x` >> strip_tac
     >- (`not_fresh_at s1 x` by (first_assum irule >> first_assum ACCEPT_TAC) >>
         qpat_assum `!x. not_fresh_at s1 x ==> FLOOKUP G2 x = _ /\ _`
           (drule_then strip_assume_tac) >>
         `not_fresh_at st x` by
           (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `s1` >> simp[]) >>
         qpat_assum `op1 = Var x` (fn eq =>
           qpat_assum `op_prov G1 op1 = NONE`
             (assume_tac o SRULE [eq,op_prov_def]) >>
           qpat_assum `op_taint tn1 op1 = {}` (assume_tac o REWRITE_RULE [eq])) >>
         simp[op_prov_def]) >>
     qpat_assum `!z. op2 = Var z ==> not_fresh_at st z`
       (drule_then assume_tac) >>
     qpat_assum `op2 = Var x` (SUBST1_TAC o SYM) >>
     rpt conj_tac >> first_assum ACCEPT_TAC);

(* Prepares a single invariant and its full round continuations for either driver. *)

val range_join_rounds_invariants_tac =
  qabbrev_tac `Inv = \H rs ee G tn s. ?k.
    k + LENGTH rs = Num (n2 - n1) /\
    rs = GENLIST (\j. Value (IntV (n1 + &(k+j)))) (LENGTH rs) /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    expr_sim_inv cenv cx env ee /\ lookup_scopes id ee.scopes = NONE /\
    s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ret_pc_ok cenv sa s /\ return_buf_frame d cenv sb0 s /\ return_buf_sep d cenv ee s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    lookup_var cv s = SOME (i2w (n1 + &k)) /\ lookup_var ev s = SOME (i2w n2) /\
    lookup_var p s = SOME w /\ FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n w,sz) /\
    ptr_covers G tn p s sz /\ op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
    op_taint tn (Var ev) = {} /\ op_prov G (Var ev) = NONE /\
    alloca_history func s /\
    (!fn inst v. frag_reachable ctx func s fn inst v ==> dalloca_fmp_headroom inst v) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 cenv ee s /\
    (!aid off z i. FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
      (!nm b z'. local_region cenv es.scopes s0 nm b z' ==> off+z <= b \/ b+z' <= off) /\
      off <= i /\ i < off+z /\ i IN tn.t_mem ==> i IN tn0.t_mem)` >>
  qabbrev_tac `Done = \H ee G tn s.
    stmt_lands lctx sb (INL ()) s /\ ~s.vs_halted /\ ~block_is_terminated sb /\
    cenv_top_ext cenv cenv ee.scopes /\ stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ return_buf_frame d cenv sb s /\
    return_buf_sep d cenv ee s /\ ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 cenv ee s /\
    (!aid off z i. FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
      (!nm b z'. local_region cenv es.scopes s0 nm b z' ==> off+z <= b \/ b+z' <= off) /\
      off <= i /\ i < off+z /\ i IN tn.t_mem ==> i IN tn0.t_mem)` >>
  qabbrev_tac `R = \H ex ee gt r.
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex : unit + exception) gt r) /\
    halt_exit H cx ee (INR ex : unit + exception) r /\
    (ctx_has_dalloca ctx ==> !s.
      (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)`;

fun range_fresh_scope_tac source =
  let
    val inv = [`expr_sim_inv cenv cx env `,source] |> List.concat
    val scope = [`lookup_scopes id (`,source,`).scopes`] |> List.concat
  in
    sg (scope @ ` = NONE`) >-
      (qpat_assum inv (mp_then Any irule
         exprSimInvScopeAbsenceTheory.expr_sim_inv_scope_lookup_none) >>
       first_assum ACCEPT_TAC)
  end;

val range_init_size_tac =
  `type_memory_bytes cenv typ < dimword (:256)` by
    (irule arithmeticTheory.LESS_TRANS >> qexists `2 ** 64` >>
     simp[wordsTheory.dimword_def,venomMemPropsTheory.dimindex_256,
          bitTheory.TWOEXP_MONO]);

fun range_init_outcome_tac initializer states select_code =
  qspecl_then
    ([`DF`,`lo`,`gas_explicit_sites ctx shadow_ctx`,`d`,`ctx`,`func`,`PG`,
      `cx_tops cx`,`cx`,`st0`,`RetQ`,`cenv`,`env`,`es`,`sa`,`s0`,`G0`,`tn0`] @
      states @ [`st`,`sb0`,`entry_lbl`,`cond_lbl`,`p`,`cv`,`ev`,
                `n`,`typ`,`tyv`,`n1`,`n2`,`sz`,`id`]) mp_tac initializer >>
  simp[NoAsms,LET_THM] >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[] >>
     conj_tac >- select_code >> asm_rewrite_tac [] >> simp[])) >>
  disch_then (qx_choose_then `w` assume_tac) >>
  qabbrev_tac
    `init = bind (lift_sum (get_range_limits (IntV n1) (IntV n2)))
       (\rl. ignore_bind (check (compatible_bound (Dynamic n) (SND rl)) "For too long")
         (return (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl))))`;

fun range_computed_init_tac computed_bound initializer =
  `local_ptrs_reserved cenv st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `ret_pc_ok cenv sa t2` by
    (irule ret_pc_ok_frame >>
     qpat_assum `ret_pc_ok cenv sa s0` (irule_at Any) >>
     asm_rewrite_tac [arithmeticTheory.LESS_EQ_REFL]) >>
  `return_buf_frame d cenv st t2` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC]) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid2 t2 /\
       storage_well_formed_on cx mid2 (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid2 G2 tn2 t2` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ e2 _ _ _ _ _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o PURE_ONCE_REWRITE_RULE [expr_post_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `n < dimword (:256)` by
    (qpat_assum `type_stmt env ret_ty (For id typ (Range e1 e2) n body) = SOME env'`
       (mp_then Any mp_tac computed_bound) >> asm_rewrite_tac []) >>
  range_init_size_tac >>
  `st.cs_next_var <= st.cs_next_var + 9` by decide_tac >>
  range_init_outcome_tac initializer [`mid2`,`t2`,`G2`,`tn2`]
    (disj2_tac >> qexistsl_tac [`op1`,`op2`,`rv`,`g1`,`z1`,`g2`,`z2`] >>
     asm_rewrite_tac [] >>
     simp[NoAsms,ASCIInumbersTheory.toString_inj,not_fresh_at_def,
          DISJ_IMP_THM,FORALL_AND_THM]) >>
  `bind (lift_sum (get_range_limits v1 v2))
     (\rl. ignore_bind (check (compatible_bound (Dynamic n) (SND rl)) "For too long")
       (eval_for cx tyv id body (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)))) =
   bind init (eval_for cx tyv id body)` by
    (simp[Abbr `init`, ignore_bind_def, bind_assoc, bind_return]) >>
  pop_assum (fn th => mk_asm "init_bind" th >> SUBST1_TAC th);

val range_literal_code_tac =
  qpat_x_assum `?a1 m1 a2 m2. e1 = _ /\ e2 = _`
    (qx_choosel_then [`a1`,`n1`,`a2`,`n2`] strip_assume_tac) >>
  qpat_x_assum `!a1 m1 a2 m2. e1 = _ /\ e2 = _ ==> _`
    (qspecl_then [`a1`,`n1`,`a2`,`n2`] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac;

fun range_literal_bounds_tac end_words =
  `n1 <= n2 /\ n = Num (n2 - n1)` by
    (qpat_assum `supported_iterator _ _ _ _` mp_tac >>
     qpat_assum `e1 = Literal a1 (IntL n1)` SUBST1_TAC >>
     qpat_assum `e2 = Literal a2 (IntL n2)` SUBST1_TAC >>
     simp[supported_iterator_def]) >>
  let
    fun typed_literal e a bound =
      sg ([QUOTE "value_has_type tyv (IntV "] @ bound @ [QUOTE ")"]) >-
       (sg ([QUOTE "well_typed_literal typ (IntL "] @ bound @ [QUOTE ")"]) >-
          (qpat_assum ([QUOTE "well_typed_expr env "] @ e) mp_tac >>
           qpat_assum ([QUOTE "expr_type "] @ e @ [QUOTE " = typ"]) mp_tac >>
           qpat_assum (e @ [QUOTE " = Literal "] @ a @ [QUOTE " (IntL "] @ bound @ [QUOTE ")"]) SUBST1_TAC >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp[well_typed_expr_def, expr_type_def]) >>
        irule (REWRITE_RULE [vyperValueOperationTheory.evaluate_literal_def]
          (Q.INST [`lit` |-> ([QUOTE "IntL "] @ bound)] vyperTypeValuesTheory.well_typed_literal_sound)) >>
        qexistsl [`get_tenv cx`,`typ`] >> rpt conj_tac >> first_assum ACCEPT_TAC)
  in
    typed_literal `e1` `a1` `n1` >> typed_literal `e2` `a2` `n2`
  end >>
  `n < dimword (:256)` by
    (qspecl_then [`get_tenv cx`,`typ`,`tyv`,`n1`,`n2`] mp_tac end_words >> simp[]) >>
  range_init_size_tac >> range_fresh_scope_tac `es`;

fun range_literal_init_tac initializer =
  `alloca_frame cenv es sa s0 cenv es s0` by (irule alloca_frame_same >> simp[]) >>
  `st.cs_next_var <= sb0.cs_next_var` by simp[] >>
  range_init_outcome_tac initializer [`es`,`s0`,`G0`,`tn0`]
    (disj1_tac >> simp[ASCIInumbersTheory.toString_inj,not_fresh_at_def]) >>
  `eval_iterator cx (Range e1 e2) =
     return (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)))` by
    (qpat_assum `e1 = Literal a1 (IntL n1)` SUBST1_TAC >>
     qpat_assum `e2 = Literal a2 (IntL n2)` SUBST1_TAC >>
     simp[FUN_EQ_THM, eval_iterator_range_lit, return_def]) >>
  `eval_stmt cx (For id typ (Range e1 e2) n body) =
     bind init (eval_for cx tyv id body)` by
    (pure_once_rewrite_tac[Once evaluate_def] >>
     simp[LET_THM, lift_option_type_def, bind_return, ignore_bind_def,
          Abbr `init`, get_range_limits_def, lift_sum_def, LENGTH_GENLIST, bind_assoc]) >>
  pop_assum (fn eq =>
    qpat_assum `gas_admissible (eval_stmt cx (For _ _ _ _ _)) _ es`
      (assume_tac o PURE_REWRITE_RULE [eq]) >> SUBST1_TAC eq);

(* Replay the silent source initializer at the machine midpoint returned by
   the selected bind rule. The rule, rather than this tactic, chooses mid. *)
fun range_join_init_replay_tac replay scopes immutables =
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    (rewrite_tac[GSYM storage_trace_domain_def] >> first_assum ACCEPT_TAC) >>
  `?rs. res = INL rs /\ n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\ Num (n2 - n1) <= n` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                  (?rs. res = INL rs /\ _) /\ _`
       (drule_then strip_assume_tac) >> qexists `rs` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!st. init st = (INL (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))),st)` by
    (simp[Abbr `init`, get_range_limits_def, lift_sum_def, bind_def,
          ignore_bind_def, check_def, assert_def,
          vyperValueTheory.compatible_bound_def, return_def]) >>
  qpat_assum replay
    (qspec_then `[]` (fn step =>
      qpat_assum `!st. init st = _` (fn init =>
        qpat_assum `res = INL rs` (fn res =>
          strip_assume_tac
            (PURE_REWRITE_RULE [init, res, pairTheory.PAIR_EQ, sumTheory.INL_11]
               step))))) >>
  sg `rs = GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))` >-
    (FIRST [first_assum ACCEPT_TAC, irule EQ_SYM >> first_assum ACCEPT_TAC]) >>
  sg scopes >-
    (qpat_assum `_ with gas_obs := _ = mid with gas_obs := []`
       (mp_tac o Q.AP_TERM `(\s:evaluation_state. s.scopes)`) >> simp[NoAsms]) >>
  sg immutables >-
    (qpat_assum `_ with gas_obs := _ = mid with gas_obs := []`
       (mp_tac o Q.AP_TERM `(\s:evaluation_state. s.immutables)`) >> simp[NoAsms]);

val range_init_admissible_tac =
  qpat_assum `gas_admissible (bind init _) _ _`
    (mp_then Any mp_tac (SRULE [gasContextTheory.gas_admissible_gas_obs]
      stmtSimForRoundsTheory.gas_admissible_bind_tail)) >>
  disch_then (fn th => qpat_assum `res = INL rs` (fn eq =>
    qpat_assum `!tail. init _ = (res,mid with gas_obs := tail)`
    (mp_then Any ACCEPT_TAC th o PURE_REWRITE_RULE [eq])));

val range_computed_eval_tac =
  `eval_stmt cx (For id typ (Range e1 e2) n body) =
       do a <- bind (eval_expr cx e1) (read_result cx);
          b <- bind (eval_expr cx e2) (read_result cx);
          rl <- lift_sum (get_range_limits a b);
          check (compatible_bound (Dynamic n) (SND rl)) "For too long";
          eval_for cx tyv id body (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl))
       od` by
    (pure_once_rewrite_tac[Once evaluate_def] >>
     simp[LET_THM, lift_option_type_def] >>
     pure_once_rewrite_tac[Once evaluate_def] >>
     simp[LET_THM, bind_assoc, bind_return, LENGTH_GENLIST]);

val range_computed_admissible_tac =
  `gas_admissible (eval_for cx tyv id body rs) (stmt_res_ok lctx) mid` by
    (range_computed_eval_tac >>
     pop_assum (fn eq =>
       qpat_assum `gas_admissible (eval_stmt cx (For _ _ _ _ _)) _ es`
         (assume_tac o PURE_REWRITE_RULE [eq])) >>
     let
       val tail = SRULE [gasContextTheory.gas_admissible_gas_obs]
         stmtSimForRoundsTheory.gas_admissible_bind_tail
       fun advance adm replay = qpat_assum adm (mp_then Any mp_tac tail) >>
         disch_then (fn th => qpat_assum replay
           (mp_then Any (assume_tac o BETA_RULE) th))
     in
       advance `gas_admissible (bind (bind (eval_expr cx e1) (read_result cx)) _) _ es`
         `!tail. bind (eval_expr cx e1) (read_result cx) _ = (INL v1,mid1 with gas_obs := tail)` >>
       advance `gas_admissible (bind (bind (eval_expr cx e2) (read_result cx)) _) _ mid1`
         `!tail. bind (eval_expr cx e2) (read_result cx) _ = (INL v2,mid2 with gas_obs := tail)`
     end >>
     asm "init_bind" (fn eq =>
       qpat_x_assum `gas_admissible (bind (lift_sum (get_range_limits v1 v2)) _) _ mid2`
         (assume_tac o PURE_REWRITE_RULE [eq])) >>
     range_init_admissible_tac);

val range_literal_admissible_tac =
  `gas_admissible (eval_for cx tyv id body rs) (stmt_res_ok lctx) mid` by
    range_init_admissible_tac;

val range_computed_iterator_replay_tac =
  `?start finish. eval_iterator cx (Range e1 e2) start = (INL rs,finish)` by
    ((`eval_iterator cx (Range e1 e2) =
        do a <- bind (eval_expr cx e1) (read_result cx);
           b <- bind (eval_expr cx e2) (read_result cx);
           rl <- lift_sum (get_range_limits a b);
           return (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od` by
       simp[Once evaluate_def, LET_THM, bind_assoc] >>
     pop_assum SUBST1_TAC >>
     qexistsl [`es with gas_obs := gas_explicit marks1 s0.vs_gas_readings ++ gas_explicit marks2 t1.vs_gas_readings`,
               `mid2 with gas_obs := []`] >>
     qpat_assum `!tail. bind (eval_expr cx e1) (read_result cx) _ = _`
       (qspec_then `gas_explicit marks2 t1.vs_gas_readings` (mk_asm "range_read1")) >>
     asm "range_read1" (fn th => simp[NoAsms, Once bind_def, th]) >>
     asm "read2" (fn th => simp[NoAsms, Once bind_def, REWRITE_RULE [APPEND_NIL] th]) >>
     qpat_assum `v1 = IntV n1` (fn v1 =>
       qpat_assum `v2 = IntV n2` (fn v2 =>
         qpat_assum `n1 <= n2` (fn bounds =>
           qpat_assum `rs = GENLIST _ _` (fn rs =>
             simp[NoAsms, v1, v2, bounds, rs, bind_def, get_range_limits_def,
                  lift_sum_def, return_def]))))));

val range_literal_iterator_replay_tac =
  `?start finish. eval_iterator cx (Range e1 e2) start = (INL rs,finish)` by
    (qexistsl [`es`,`es`] >>
     qpat_assum `eval_iterator cx (Range e1 e2) = _` (fn iter =>
       qpat_assum `rs = GENLIST _ _` (fn rs =>
         simp[NoAsms, iter, rs, return_def])));

(* The client supplies the appropriate guarded full or prefix body IH. *)
fun range_join_rounds_source_tac body_ok guard =
  `lift_option_type (evaluate_type (get_tenv cx) typ) "For evaluate_type" es = (INL tyv,es)` by
    (qpat_assum `evaluate_type (get_tenv cx) typ = SOME tyv`
       (fn ty => simp[NoAsms, ty, lift_option_type_def, return_def])) >>
  `check (compatible_bound (Dynamic n) (LENGTH rs)) "For too long" es = (INL (),es)` by
    (qpat_assum `rs = GENLIST _ _` (fn rs =>
      qpat_assum `Num (n2 - n1) <= n` (fn length =>
        simp[NoAsms, rs, length, LENGTH_GENLIST, vyperValueTheory.compatible_bound_def,
             check_def, assert_def, return_def]))) >>
  sg body_ok >-
    (qpat_assum guard irule >>
     conj_tac >- (qpat_assum `eval_iterator cx (Range e1 e2) _ = (INL rs,_)`
       (irule_at Any) >> simp[]) >>
     conj_tac >- (qexistsl [`es`,`es`,`()`] >> first_assum ACCEPT_TAC) >>
     qexistsl [`es`,`es`,`get_tenv cx`] >> simp[]);

val range_join_rounds_entry_tac =
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                (?rs. _) /\ (!bw capacity. _ ==> allocas_from _ t)`
    (drule_then strip_assume_tac) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions`
         (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi o CONJ inv))) >>
  `!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                  gas_origin_ptr_path _ _ _ (OK t,_,_)`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_then (Pos hd) mp_tac
       bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac []);

val range_join_rounds_sep_tac =
  `return_buf_sep d cenv mid t` by
    (irule (INST_TYPE [alpha |-> ``:256``]
       bodyFullSharedTheory.return_buf_sep_locals_kept) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`storage_trace_horizon es.storage_trace`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC);

val range_join_rounds_pack_tac =
  qpat_x_assum `res = INL rs'` mp_tac >>
  qpat_assum `res = INL rs` (fn th => rewrite_tac[th,sumTheory.INL_11]) >>
  disch_then SUBST_ALL_TAC >>
  simp[NoAsms,Abbr `Inv`,arithmeticTheory.ADD_COMM] >>
  qexists `k` >>
  `ainst.inst_id = st.cs_next_id` by
    (qpat_assum `ainst = mk_inst _ _ _ _`
      (fn th => simp[NoAsms,th,venomInstTheory.mk_inst_def])) >>
  qpat_assum `p = STRING _ _` SUBST1_TAC >>
  qpat_assum `ainst.inst_id = st.cs_next_id` SUBST1_TAC >>
  rpt conj_tac >> first_assum ACCEPT_TAC;

end
