(* Continuation of a storage-array For after evaluating its iterator place. *)
Theory forCapturedStorageContinue
Ancestors
  bodyInvExecutionProps
  bodyFullForExprCut bodyFullForArrayRound bodyFullForRounds bodyFullForFacts
  forCapturedStorageCode forCapturedStorageEntry forCapturedStorageHead forCapturedStorageRound
  bodyFullForStorage bodyFullForStorageCapture bodyFullForRange bodyFullIfExpReach
  bodyFullShared bodySim bodySimFull bodyFullPreds bodyFullShadowBodyInv
  exprSimSource exprSimHyps exprSimProps exprSimHypsDefs exprSimCopy loweringPosts
  loweringStateRelDefs stmtSimDefs stmtSimProps bodyPtrDefs bodyMemoryDefs
  bodyExprPreFacts reasonEndpointResourcesPtr typedMemoryCopy slotCopyExecution
  gasOutcomeFullCompose gasOutcomeFullGuarded gasOutcomeFull gasContext gasExemptCert gasExplicitSites
  vyperStorageFootprint vyperStorageTrace vyperTypeInvariants vyperInterpreter vyperState
  vyperStorageBackend vyperTypeValues vyperTyping vyperAST vyperValue
  supportedStmts compileEnv stmtLowering context freshWrites exprLoweringProps
  emitHelper emitHelperProps fragExec fragGasOriginPtr ptrDiscipline
  venomState venomInst venomExecSemantics words finite_map list arithmetic
  vyperTypeContract[qualified,ignore_grammar]
Libs monadsyntax

(* The full round and Extra use the same live suffix, target entry and
   guarded read/push replay. The callback does not depend on the backedge. *)
Theorem for_captured_storage_continue_rounds_cut:
  compile_stmt c lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb) /\
  compile_stmt (gas_shadow_env T c) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n loop_body))
    sha = ((),shb) /\
  compile_expr c (expr_type e) e sa = (vv,se) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  body_inv tops ctx c cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Array e) n loop_body) /\
  type_stmt env ret_ty (For id typ (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id typ (Array e) n loop_body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n loop_body) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n loop_body)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ c ret_ty /\
  c.ce_alloca_locals /\ local_ptrs_reserved c sa /\
  ret_pc_ok c sa s0 /\ return_buf_frame d c sa s0 /\ return_buf_sep d c em u /\
  (!H. dead_lo_ok H (DF H) lo c cx) /\
  (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\ expr_body_pre c cx env e es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_type e = ArrayT typ bd /\ bound_length bd <= n /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!tail. eval_expr cx e (es with gas_obs := obs ++ tail) =
     (INL (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))),em with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
     for_array_expr_endpoint (DF,lo,d,ctx,func) c cx e (es,sa,s0,G0,tn0)
       (vv,se) H (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) em Gu tu u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     storage_well_formed_on cx es (FST H)) /\
  alloca_frame c es sa s0 c em u /\
  ((?w. vv_operand vv = Lit w) \/
   (?tgt nid. loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid /\
             ~(?ty i. e = TopLevelName ty i))) /\
  (!vs. (!tail. array_iterator_results cx (expr_type e)
                  (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) (em with gas_obs := tail) =
                  (INL vs,em with gas_obs := tail)) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
    body_for_full_ok cx tyv id loop_body vs /\
    gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em) /\
  (!a rs ei s G tn bc bc1 env_b exit incr sb0 sb1 shadow_sb0 shadow_sb1
     idx p dst lvo len inst nb bop vs.
    body_inv tops ctx bc cx /\ shadow_body_inv tops ctx shadow_ctx /\
    supported_stmts tops bindings loop_body /\
    (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) loop_body ==>
       occurs_abi_decode_target target tops) /\
    type_stmts (extend_local env id typ F) ret_ty loop_body = SOME env_b /\
    stmts_exprs_ok bc loop_body /\ call_evaluation_safe cx (int_calls_stmts loop_body) /\
    frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc ret_ty /\
    stmts_env bc (InLoop exit incr) ret_ty loop_body sb0 = (bc1,sb1) /\
    stmts_env (gas_shadow_env T bc) (InLoop exit incr) ret_ty (MAP gas_shadow_stmt loop_body)
      shadow_sb0 = (gas_shadow_env T bc1,shadow_sb1) /\
    gas_shadow_state sb0 shadow_sb0 /\ gas_shadow_state sb1 shadow_sb1 /\
    fn_has_code sb0 sb1 func /\ fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
    (!H. dead_lo_ok H (DF H) lo bc cx) /\ local_ptrs_reserved bc sb0 /\
    (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb0 x) /\
    ~block_is_terminated sb0 /\ not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
    (!x. lvo = Var x ==> not_fresh_at sb0 x) /\ (!lbl. lvo <> Label lbl) /\
    ~s.vs_halted /\ (!f i t. frag_reachable ctx func s f i t ==> dalloca_fmp_headroom i t) /\
    body_const_cells_agree [(NONE,tops)] cx env ei /\
    gas_admissible (eval_for cx tyv id loop_body (a::rs)) (stmt_res_ok lctx) ei /\
    storage_trace_domain cx st0 ei.storage_trace /\
    lookup_scopes id ei.scopes = NONE /\
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) tops cx st0
      (bind (read_result cx a) (push_scope_with_var id tyv)) (ei,s,G,tn)
      (\H res eb GG tt z. res = INL () /\ eb.gas_obs = [] /\
        ?v j. eb = for_captured_storage_round_scope id tyv (ei with gas_obs := []) v /\
          read_result cx a ei = (INL v,ei) /\
          for_captured_storage_round_entry (DF,lo,d,ctx,func)
            (cx,c,bc,extend_local env id typ F,sb0,loop_body)
            (es with gas_obs := obs,sa,s0,G0,tn0) (idx,p,dst,lvo,len,inst,nb) (H,eb,j,z,GG,tt) /\
          eval_operand bop z = SOME slot /\ op_taint tt bop = {} /\ a::rs = DROP j vs)
      (\H res ee gt r. ?ex. res = INR ex /\ for_array_loop_exit ctx cx RetQ H (INR ex) ee gt r) ==>
    Extra a rs ei s G tn) ==>
  ?vs z G tn Inv Done.
    (!tail. array_iterator_results cx (expr_type e)
        (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) (em with gas_obs := tail) =
        (INL vs,em with gas_obs := tail)) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" = return () /\
    em.gas_obs = [] /\ ~u.vs_halted /\ ~z.vs_halted /\
    gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (u,Gu,tu) [] (OK z,G,tn) /\ Inv H vs em G tn z) /\
    (!H ee GG tt t. Done H ee GG tt t ==>
      for_array_loop_post (DF,lo,d,ctx,func) c cx lctx (es,sa,s0,G0,tn0) sb H (INL ()) ee GG tt t) /\
    (!a rs ei s G tn.
      ~s.vs_halted /\ storage_trace_domain cx st0 ei.storage_trace /\
      (!H. valid_horizon cx st0 H ei.storage_trace ==> Inv H (a::rs) ei G tn s) /\
      gas_admissible (eval_for cx tyv id loop_body (a::rs)) (stmt_res_ok lctx) ei ==>
      gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
        (do v <- read_result cx a; push_scope_with_var id tyv v;
            finally (try (do eval_stmts cx loop_body; return F od) handle_loop_exception) pop_scope od)
        (ei,s,G,tn)
        (\H res ee GG tt t. ee.gas_obs = [] /\ ~t.vs_halted /\
          ?b. res = INL b /\ (b ==> Done H ee GG tt t) /\ (~b ==> Inv H rs ee GG tt t))
        (\H res ee gt r. ?ex. res = INR ex /\ for_array_loop_exit ctx cx RetQ H (INR ex) ee gt r) /\
      Extra a rs ei s G tn) /\
    (!ei s G tn.
      ~s.vs_halted /\ storage_trace_domain cx st0 ei.storage_trace /\
      (!H. valid_horizon cx st0 H ei.storage_trace ==> Inv H [] ei G tn s) /\
      gas_admissible (eval_for cx tyv id loop_body []) (stmt_res_ok lctx) ei ==>
      ?t G1 tn1. !H. valid_horizon cx st0 H ei.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s,G,tn) [] (OK t,G1,tn1) /\ Done H (ei with gas_obs := []) G1 tn1 t)
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  drule_all (Q.INST [`sty` |-> `typ`, `fty` |-> `typ`] for_nonslot_array_layout_full_with_increment) >>
  disch_then (qx_choosel_then [`vv0`,`se0`,`she`,`loc`,`lvo`,`sd`,`bc`,`saD`,`saA`,`p`,`nb`,`aidItem`,
     `entry`,`cond`,`bod`,`incr`,`exit`,`idx`,`invalid`,`valid`,`dv`,`next_var`,`shead`,
     `stride`,`off_op`,`sMul`,`sum_op`,`sAdd`,`addr`,`saCopy`,`sbCopy`,
     `sbBody`,`sj`,`shadow_sbCopy`,`shadow_sbBody`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_layout_def]) >>
  `vv0 = vv /\ se0 = se` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `vv0 = vv` SUBST_ALL_TAC >> qpat_x_assum `se0 = se` SUBST_ALL_TAC >>
  qabbrev_tac `H0 = storage_trace_horizon em.storage_trace` >>
  `valid_horizon cx st0 H0 em.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> for_array_expr_endpoint _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS o
       REWRITE_RULE [for_array_expr_endpoint_def]))) >>
  qabbrev_tac `start = es with gas_obs := obs` >>
  `em with gas_obs := [] = em` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e start = (INL (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))),em)` by
    (qpat_assum `em with gas_obs := [] = em` (fn eq =>
       qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` mp_tac) >>
       simp[NoAsms,Abbr `start`,eq])) >>
  `expr_body_pre c cx env e start` by simp[Abbr `start`] >>
  `body_const_cells_agree [(NONE,tops)] cx env em` by
    (irule body_const_cells_agree_expr >>
     qpat_assum `eval_expr cx e start = _`
       (irule_at (Pat `eval_expr _ _ _ = _`)) >>
     drule_then strip_assume_tac exprBodyPrePropsTheory.expr_body_pre_static_facts >>
     simp[Abbr `start`]) >>
  suspend "capture"
QED

Resume for_captured_storage_continue_rounds_cut[capture]:
  `!H. valid_horizon cx st0 H em.storage_trace ==>
    vv_post H ctx func c cx e start sa se s0 em (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) vv u /\
    storage_well_formed_on cx start (FST H) /\ storage_well_formed_on cx em (FST H) /\
    stmt_state_rel H ctx func c cx em u /\ ghost_inv_at (DF H) lo d c cx em Gu tu u` by
    suspend "horizon" >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> vv_post _ _ _ _ _ _ start _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  drule_at_then (Pat `vv_post _ _ _ _ _ _ start _ _ _ _ _ _ _`) drule_all for_storage_iterator_operand >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?p. vv = LocatedValue _ _ /\ _` strip_assume_tac >>
  `loc = slot_loc tr` by fs[vv_location_def] >>
  drule_all_then (map_every assume_tac o CONJUNCTS) for_captured_storage_code >>
  qpat_x_assum `?ov tot ep cb bb. _` strip_assume_tac >>
  qabbrev_tac `bop = vv_operand vv` >>
  `!x. bop = Var x ==> not_fresh_at se x` by
    (simp[NoAsms, Abbr `bop`] >> drule_all_then (ACCEPT_TAC o REWRITE_RULE [copy_old_operand_def])
       reasonEndpointResourcesPtrTheory.compile_expr_old_operand) >>
  suspend "initial"
QED

Resume for_captured_storage_continue_rounds_cut[horizon]:
  gen_tac >> disch_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`valid_horizon cx st0 H start.storage_trace` suffices_by simp[Abbr `start`] >>
     irule (Q.ISPEC `eval_expr cx e` (Q.GEN `f` valid_horizon_frame)) >>
     qexistsl [`e`,`INL (PlaceR (StoragePlace tr slot (ArrayTV tyv bd)))`,`em`] >>
     simp[cj 5 evaluate_storage_trace_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> for_array_expr_endpoint _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS o
       REWRITE_RULE [for_array_expr_endpoint_def]))) >>
  qpat_assum `vv_post H _ _ _ _ _ es _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [vv_post_def]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- simp[Abbr `start`,vv_post_initial_gas] >>
  conj_tac >-
    (`storage_well_formed_on cx es (FST H)` by simp[] >>
     `storage_well_formed_on cx (es with gas_obs := obs) (FST H) =
      storage_well_formed_on cx es (FST H)` by
       (irule storage_well_formed_on_backends >> simp[]) >>
     simp[Abbr `start`]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_captured_storage_continue_rounds_cut[initial]:
  drule_then strip_assume_tac type_stmt_for_projection >>
  drule_all_then assume_tac bodySimStmtFactsTheory.expr_body_pre_eval_result >>
  `lookup_scopes id em.scopes = NONE` by
    (irule exprSimInvScopeAbsenceTheory.expr_sim_inv_scope_lookup_none >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  `stride = type_slot_size tyv /\ type_memory_bytes c typ = 32 * type_slot_size tyv` by
    (qpat_assum `stride = elem_size_in_location c (slot_loc tr) typ` SUBST1_TAC >>
     simp[slot_loc_def,NoAsms] >>
     conj_tac >- (irule (cj 1 for_storage_element_layout) >> qexistsl [`cx`,`env`,`em`] >>
                   rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule (cj 2 for_storage_element_layout) >> qexistsl [`cx`,`env`,`em`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `bound_length bd < dimword (:256)` by
    (qpat_assum `evaluate_type _ (expr_type e) = SOME _` mp_tac >>
     qpat_assum `expr_type e = ArrayT typ bd` (rewrite_tac o single) >>
     MATCH_ACCEPT_TAC typed_copy_array_count_bound) >>
  `type_memory_bytes c typ < 2 ** 64` by
    (qhdtm_assum `stmt_exprs_ok` mp_tac >> simp[NoAsms,stmt_exprs_ok_def,Once allocLimitsTheory.alloc_limits_stmt_def]) >>
  `nb < dimword (:256) /\ 32 * type_slot_size tyv <= nb` by
    (reverse conj_tac >- simp[] >> irule LESS_TRANS >> qexists `2 ** 64` >>
     conj_tac >- (qpat_assum `nb = type_memory_bytes c typ` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     simp[dimword_def,NoAsms]) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    (qpat_assum `return_buf_frame d c sa s0` (fn th => POP_ASSUM_LIST (K (mp_tac th))) >>
     Cases_on `d` >> simp[return_buf_frame_def,pairTheory.FORALL_PROD,pairTheory.EXISTS_PROD] >>
     PairCases_on `x` >> rw[return_buf_frame_def] >> gvs[]) >>
  `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  qpat_assum `vv_post H0 _ _ _ _ _ start _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [vv_post_def]) >>
  `alloca_frame c start sa s0 c em u /\ ghost_kept_at lo c start sa G0 tn0 s0 Gu tu` by
    (conj_tac >- simp[Abbr `start`] >>
     qpat_assum `ghost_kept_at lo c es sa G0 tn0 s0 Gu tu` (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     simp[NoAsms,Abbr `start`,ghost_kept_at_def] >>
     strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  `bop = vv_operand vv` by simp[Abbr `bop`] >>
  drule_all for_captured_storage_initial_full >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`vs`,`len`,`dst`,`z`,`G`,`tn`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "source"
QED

Resume for_captured_storage_continue_rounds_cut[source]:
  qabbrev_tac `items = array_iterator_results cx (expr_type e)
    (PlaceR (StoragePlace tr slot (ArrayTV tyv bd)))` >>
  `items em = (INL vs,em)` by
    (qpat_assum `eval_iterator cx (Array e) start = _` mp_tac >>
     simp[NoAsms,Once evaluate_def,bind_def] >>
     qpat_assum `eval_expr cx e start = _` (fn th => simp[NoAsms,th,Abbr `items`])) >>
  `!tail. items (em with gas_obs := tail) = (INL vs,em with gas_obs := tail)` by
    (qpat_assum `items em = _` mp_tac >>
     Cases_on `bd` >> Cases_on `tr` >>
     simp[NoAsms,Abbr `items`,array_iterator_results_storage,result_array_length_def,
          get_storage_backend_eq,get_storage_def,bind_def,ignore_bind_def,
          check_def,assert_def,return_def,AllCaseEqs()]) >>
  `check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" = return ()` by
    (qpat_assum `len = LENGTH vs` (rewrite_tac o single o SYM) >>
     `len <= n` by decide_tac >> simp[FUN_EQ_THM,compatible_bound_def,check_def,assert_def,return_def]) >>
  `body_for_full_ok cx tyv id loop_body vs /\
   gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em` by
    (qpat_assum `!vs. _ ==> body_for_full_ok _ _ _ _ vs /\ _` irule >>
     simp[return_def] >> qpat_assum `!tail. items _ = _` (mp_tac o REWRITE_RULE [Abbr `items`]) >> simp[]) >>
  suspend "rounds"
QED

Resume for_captured_storage_continue_rounds_cut[rounds]:
  drule_all for_nonslot_increment_slice >>
  disch_then (qx_choosel_then [`si`,`sk`,`sl`,`sm`] (map_every assume_tac o CONJUNCTS)) >>
  drule_all range_body_compiler_pair >>
  disch_then (qx_choosel_then [`bc1`,`shadow_body_end`] (map_every assume_tac o CONJUNCTS)) >>
  `shadow_body_end = shadow_sbBody` by metis_tac[pairTheory.PAIR_EQ] >>
  pop_assum SUBST_ALL_TAC >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`body_inv tops ctx c cx`,`MEM func ctx.ctx_functions`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[body_inv_no_phi]) >>
  qabbrev_tac `Live = \H k rs ee GG tt s.
    for_captured_storage_live (DF,lo,d,ctx,func,cx,c,id,env,typ,loop_body)
      (start,sa,s0,G0,tn0) (em,se,bop,tr,slot,tyv,bd,vs,len)
      (lvo,idx,cond) (p,dst,nb,sd) (H,k,rs,ee,GG,tt,s)` >>
  qabbrev_tac `Inv = \H rs ee GG tt s.
    body_const_cells_agree [(NONE,tops)] cx env ee /\ (?k. Live H k rs ee GG tt s) /\
    (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u)` >>
  qabbrev_tac `Done = \H ee GG tt t.
    for_array_loop_post (DF,lo,d,ctx,func) c cx lctx
      (start,sa,s0,G0,tn0) sb H (INL ()) ee GG tt t` >>
  suspend "static"
QED

Resume for_captured_storage_continue_rounds_cut[static]:
  `~z.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> _ /\ for_captured_storage_live _ _ _ _ _ _`
       (qspec_then `H0` (drule_then (strip_assume_tac o
         REWRITE_RULE [forCapturedStorageLiveTheory.for_captured_storage_live_def] o CONJUNCT2))) >>
     first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= saCopy.cs_next_var /\
    shead.cs_next_var <= saCopy.cs_next_var /\ saCopy.cs_next_var <= sbCopy.cs_next_var /\
    saCopy.cs_next_var <= si.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
    se.cs_next_var <= saCopy.cs_next_var /\ sa.cs_next_id <= sbCopy.cs_next_id /\
    sa.cs_next_var <= sbCopy.cs_next_var /\ se.cs_next_var <= sbCopy.cs_next_var` by suspend "ages" >>
  `!x. not_fresh_at sa x ==> not_fresh_at saCopy x /\ not_fresh_at sbCopy x /\ not_fresh_at sb x` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`sa.cs_next_var <= sd.cs_next_var`,`sd.cs_next_var <= saCopy.cs_next_var`,
        `saCopy.cs_next_var <= sbCopy.cs_next_var`,`sa.cs_next_var <= sb.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `~not_fresh_at sa p /\ ~not_fresh_at sd p` by suspend "item_age" >>
  `~not_fresh_at sa idx /\ ~not_fresh_at sa dv /\ ~not_fresh_at sa next_var /\
    p <> idx /\ p <> next_var /\
    (!x. lvo = Var x ==> x <> idx /\ x <> next_var) /\
    (!x. bop = Var x ==> x <> idx /\ x <> next_var)` by suspend "fresh" >>
  `shead.cs_next_id - 1 = (shead.cs_next_id - 2) + 1` by suspend "cond_ids" >>
  `~block_is_terminated sb` by
    (qpat_assum `sb.cs_current_insts = []` (fn th => simp[NoAsms,th,block_is_terminated_def])) >>
  suspend "prepare_body"
QED

Resume for_captured_storage_continue_rounds_cut[ages]:
  `ci_mono se sd` by
    (qpat_assum `(case bd of Fixed _ => comp_return _ | Dynamic _ => _) se = (lvo,sd)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bd` >> simp[comp_return_def]
     >- simp[ci_mono_def,cs_extends_def] >>
     metis_tac[ci_mono_compile_ptr_load,pairTheory.SND]) >>
  map_every (fn q => qpat_assum q (mp_tac o CONJUNCT2 o REWRITE_RULE [ci_mono_def]))
    [`ci_mono sa sd`,`ci_mono se sd`,`ci_mono sd saA`,`ci_mono saA shead`,
     `ci_mono shead saCopy`,`ci_mono saCopy sbCopy`,`ci_mono sbCopy sbBody`,
     `ci_mono sbBody sj`,`ci_mono sj sb`] >>
  qpat_assum `si.cs_next_var = sj.cs_next_var` SUBST1_TAC >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac
QED

Resume for_captured_storage_continue_rounds_cut[item_age]:
  `p = STRING #"%" (toString sd.cs_next_var)` by
    (qpat_assum `compile_alloc_buffer nb sd = _`
       (mp_tac o cj 1 o MATCH_MP loweringHaltTheory.compile_alloc_buffer_insts) >> simp[NoAsms]) >>
  map_every (fn q => qpat_assum q mp_tac)
    [`p = STRING _ _`,`sa.cs_next_var <= sd.cs_next_var`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Resume for_captured_storage_continue_rounds_cut[fresh]:
  map_every (fn q => qpat_assum q mp_tac)
    [`EVERY (\p. ~not_fresh_at sd p) [idx;dv;next_var]`,
     `ALL_DISTINCT [p;idx;dv;next_var]`, `sa.cs_next_var <= sd.cs_next_var`,
     `!x. bop = Var x \/ lvo = Var x ==> not_fresh_at sd x`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[DISJ_IMP_THM,FORALL_AND_THM] >>
  metis_tac[not_fresh_at_mono]
QED

Resume for_captured_storage_continue_rounds_cut[cond_ids]:
  `MEM cb func.fn_blocks` by
    (qpat_assum `lookup_block cond func.fn_blocks = SOME cb`
       (ACCEPT_TAC o MATCH_MP venomExecPropsTheory.lookup_block_MEM)) >>
  drule_all mmWfProofsTheory.fn_inst_ids_distinct_block >>
  qpat_assum `cb.bb_instructions = _` (fn th => simp[NoAsms,th,mk_inst_def]) >> decide_tac
QED

Resume for_captured_storage_continue_rounds_cut[prepare_body]:
  `FLOOKUP c.ce_vars id = NONE` by
    (irule bodySimDeclCasesTheory.declared_name_unbound >>
     goal_assum (drule_at (Pat `type_stmt _ _ _ = _`)) >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  `!l. FLOOKUP c.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz` by
    (qpat_assum `FLOOKUP c.ce_vars id = NONE` (fn th => simp[NoAsms,th])) >>
  drule_all_then assume_tac bodySimDeclCasesTheory.declare_local_same_frame >>
  drule_all_then (map_every assume_tac o CONJUNCTS) declare_local_ptr >>
  `bc.ce_return_buf = c.ce_return_buf /\ bc.ce_imm_alloca = c.ce_imm_alloca` by
    (qpat_assum `bc with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = c`
       (fn th => conj_tac
         >- (mp_tac (AP_TERM ``\c. c.ce_return_buf`` th) >> simp[NoAsms]) >>
         mp_tac (AP_TERM ``\c. c.ce_imm_alloca`` th) >> simp[NoAsms])) >>
  `!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sbCopy x` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `bc.ce_return_buf = c.ce_return_buf` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
       (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then (ACCEPT_TAC o cj 2))) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x` by
    (rpt strip_tac >>
     qpat_assum `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
       (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then (ACCEPT_TAC o cj 3))) >>
  `bc.ce_modules = c.ce_modules` by
    (qpat_assum `bc with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = c`
       (mp_tac o AP_TERM ``\env. env.ce_modules``) >> simp[NoAsms]) >>
  `!H. dead_lo_ok H (DF H) lo bc cx` by
    (gen_tac >> qpat_assum `same_frame c bc`
       (fn th => rewrite_tac[dead_lo_ok_def,MATCH_MP bodyPtrDefsTheory.same_frame_is_ctor th]) >>
     qpat_assum `bc.ce_modules = c.ce_modules` (rewrite_tac o single) >>
     qpat_assum `!H. dead_lo_ok H (DF H) lo c cx`
       (qspec_then `H` (ACCEPT_TAC o REWRITE_RULE [dead_lo_ok_def]))) >>
  `frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc ret_ty` by suspend "ret_frame" >>
  suspend "source_body"
QED

Resume for_captured_storage_continue_rounds_cut[ret_frame]:
  qpat_assum `frame_ret_ok_full _ _ _ c _`
    (mk_asm "original_ret" o REWRITE_RULE [frame_ret_ok_full_def]) >>
  rewrite_tac[frame_ret_ok_full_def] >> rpt gen_tac >> strip_tac >> asm "original_ret" irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (irule same_frame_trans >> goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at Any) >> first_assum ACCEPT_TAC
QED

Resume for_captured_storage_continue_rounds_cut[source_body]:
  drule_then strip_assume_tac body_inv_main_support >>
  `cx_tops cx = tops` by
    (qpat_assum `get_module_code cx NONE = SOME tops`
       (fn th => simp[NoAsms,gasContextTheory.cx_tops_def,th])) >>
  `body_inv tops ctx bc cx` by
    (irule body_inv_same_frame >> qexists `c` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_then assume_tac supportedStmtsTheory.supported_loop_body_contract >>
  drule_then assume_tac bodySimDeclCasesTheory.body_for_exprs_ok >>
  drule_all_then assume_tac bodyExprPreFactsTheory.for_declare_stmts_exprs_ok >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) loop_body ==>
     occurs_abi_decode_target target tops` by
    (gen_tac >> disch_tac >>
     qpat_assum `!target. supported_stmt_expr_exists _ (For _ _ _ _ _) ==> _` irule >>
     simp[NoAsms,supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >>
     disj2_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `IS_SOME (type_stmts _ _ _)`
    (qx_choose_then `env_b` assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qpat_assum `call_evaluation_safe cx (int_calls_stmt (For _ _ _ _ _))`
    (assume_tac o MATCH_MP vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right o
     REWRITE_RULE [vyperTypeCallGraphTheory.int_calls_stmt_def]) >>
  suspend "prepare_head"
QED

Resume for_captured_storage_continue_rounds_cut[prepare_head]:
  `0 < type_slot_size tyv` by
    (irule vyperTypeSystemTheory.assignable_type_slot_size_pos >>
     qexistsl [`get_tenv cx`,`typ`] >> conj_tac >- first_assum ACCEPT_TAC >>
     drule_then (SUBST1_TAC o SYM) exprBodyPrePropsTheory.expr_body_pre_env_type_defs >>
     first_assum ACCEPT_TAC) >>
  `!l. lvo <> Label l` by
    (qpat_assum `(case bd of Fixed _ => _ | Dynamic _ => _) se = (lvo,sd)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bd` >> simp[comp_return_def]
     >- (disch_then (SUBST1_TAC o SYM o CONJUNCT1) >> simp[]) >>
     disch_then (ACCEPT_TAC o MATCH_MP fragFuelExprHelpersTheory.compile_ptr_load_not_label)) >>
  `!x. lvo = Var x ==> not_fresh_at saCopy x /\ not_fresh_at sbCopy x` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`!p. bop = Var p \/ lvo = Var p ==> not_fresh_at sd p`,
        `sd.cs_next_var <= saCopy.cs_next_var`,`saCopy.cs_next_var <= sbCopy.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[not_fresh_at_mono,LESS_EQ_TRANS]) >>
  `not_fresh_at saCopy idx /\ not_fresh_at saCopy p /\
   not_fresh_at sbCopy idx /\ not_fresh_at sbCopy p /\ not_fresh_at si idx` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`not_fresh_at shead idx`,`not_fresh_at shead p`,`shead.cs_next_var <= saCopy.cs_next_var`,
        `saCopy.cs_next_var <= sbCopy.cs_next_var`,`saCopy.cs_next_var <= si.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[not_fresh_at_mono,LESS_EQ_TRANS]) >>
  `local_ptrs_reserved c sbCopy /\ local_ptrs_reserved bc saCopy` by
    (conj_tac >- (irule local_ptrs_reserved_next_var >> qexists `saCopy` >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >> suspend "bc_reserved") >>
  `!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY::scs) p` by
    (rpt strip_tac >> irule localPtrsPropsTheory.not_local_ptr_name_update >>
     qexistsl [`c`,`id`] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     irule exprSimOperandsTheory.fresh_not_local_ptr >> qexists `sd` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "head_code"
QED

Resume for_captured_storage_continue_rounds_cut[bc_reserved]:
  `local_ptrs_reserved bc saD` by drule_all_then ACCEPT_TAC declare_local_reserved >>
  irule local_ptrs_reserved_next_var >> qexists `saD` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  map_every (fn q => qpat_assum q mp_tac)
    [`saD = sd with cs_next_var := sd.cs_next_var + 1`,
     `compile_alloc_buffer nb sd = _`, `ci_mono saA shead`, `ci_mono shead saCopy`] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[compile_alloc_buffer_def,emit_op_def,fresh_var_def,comp_bind_def,comp_return_def,
       emit_inst_def,fresh_id_def,comp_ignore_bind_def,emit_def,ci_mono_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Resume for_captured_storage_continue_rounds_cut[head_code]:
  qabbrev_tac `ai = mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]` >>
  `MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\
    ai.inst_id = sd.cs_next_id /\ sa.cs_next_id <= ai.inst_id` by
    (conj_tac >-
       (irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
        qexistsl [`sd`,`saA`] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
        qpat_assum `compile_alloc_buffer nb sd = _`
          (strip_assume_tac o SIMP_RULE (srw_ss()) [] o MATCH_MP loweringHaltTheory.compile_alloc_buffer_insts) >>
        qpat_assum `saA.cs_current_insts = _` SUBST1_TAC >> simp[Abbr `ai`]) >>
     simp[NoAsms,Abbr `ai`,mk_inst_def] >>
     qpat_assum `aidItem = sd.cs_next_id` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `compile_iter_elem_copy bc (Var ep) (Var p) (type_slot_size tyv) (slot_loc tr) T typ typ saCopy = ((),sbCopy)` by
    (simp[NoAsms,compile_iter_elem_copy_def,comp_ignore_bind_def,comp_bind_def,comp_return_def] >>
     qpat_assum `stride = type_slot_size tyv` (SUBST1_TAC o SYM) >>
     qpat_assum `compile_slot_to_memory (Var ep) _ _ _ _ = _` (fn th => simp[NoAsms,th])) >>
  qpat_assum `fn_has_code saCopy sbCopy func` mp_tac >>
  qpat_assum `sbCopy = slot_copy_final _ _ _ _ _` (fn th => rewrite_tac[th]) >>
  disch_then (strip_assume_tac o MATCH_MP copyExecutionTheory.slot_copy_lookup) >>
  `~block_is_terminated sbCopy` by
    (qpat_assum `sbCopy = slot_copy_final _ _ _ _ _` SUBST1_TAC >>
     simp[NoAsms,copyExecutionTheory.slot_copy_final_def,block_is_terminated_def]) >>
  suspend "package"
QED

Resume for_captured_storage_continue_rounds_cut[package]:
  qexistsl [`vs`,`z`,`G`,`tn`,`Inv`,`Done`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> _ /\ for_captured_storage_live _ _ _ _ _ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     conj_tac >- first_assum ACCEPT_TAC >> simp[NoAsms,Abbr `Inv`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists `0` >> simp[NoAsms,Abbr `Live`] >> first_assum ACCEPT_TAC) >>
     qpat_assum `gas_origin_ptr_path _ (u,Gu,tu) [] (OK z,G,tn)`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac[]) >>
  conj_tac >-
    (rpt gen_tac >> simp[NoAsms,Abbr `Done`,for_array_loop_post_def,Abbr `start`] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "cons" >>
  suspend "nil"
QED

Resume for_captured_storage_continue_rounds_cut[cons]:
  rpt gen_tac >> strip_tac >>
  rename1 `!H. valid_horizon cx st0 H ei.storage_trace ==> Inv H (a::rs) ei g tt s` >>
  `!H. valid_horizon cx st0 H ei.storage_trace ==> ?k. Live H k (a::rs) ei g tt s` by
    (qx_gen_tac `H` >> disch_tac >> qpat_assum `!H. valid_horizon _ _ H ei.storage_trace ==> Inv _ _ _ _ _ _`
       (qspec_then `H` (drule_then mp_tac)) >> simp[NoAsms,Abbr `Inv`] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `body_const_cells_agree [(NONE,tops)] cx env ei` by
    (qpat_assum `!H. valid_horizon _ _ H ei.storage_trace ==> Inv _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon ei.storage_trace` mp_tac) >>
     qpat_assum `storage_trace_domain cx st0 ei.storage_trace`
       (fn th => simp[NoAsms,Abbr `Inv`,REWRITE_RULE [storage_trace_domain_def] th]) >>
     disch_then (ACCEPT_TAC o cj 1)) >>
  `!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u` by
    (qpat_assum `!H. valid_horizon _ _ H ei.storage_trace ==> Inv _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon ei.storage_trace` mp_tac) >>
     qpat_assum `storage_trace_domain cx st0 ei.storage_trace`
       (fn th => simp[NoAsms,Abbr `Inv`,REWRITE_RULE [storage_trace_domain_def] th]) >>
     disch_then (ACCEPT_TAC o cj 3)) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (do v <- read_result cx a; push_scope_with_var id tyv v;
        finally (try (do eval_stmts cx loop_body; return F od) handle_loop_exception) pop_scope od)
    (ei,s,g,tt)
    (\H res ee GG tn t. ee.gas_obs = [] /\ ~t.vs_halted /\
      ?b. res = INL b /\ (b ==> Done H ee GG tn t) /\
        (~b ==> body_const_cells_agree [(NONE,tops)] cx env ee /\ ?j. Live H j rs ee GG tn t))
    (\H res ee gt r. ?ex. res = INR ex /\ for_array_loop_exit ctx cx RetQ H (INR ex) ee gt r) /\
    Extra a rs ei s g tt`
  suffices_by
    (strip_tac >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `gas_outcome_full _ _ _ _ _ (ei,s,g,tt) _ _`
       (mp_then Any irule gas_outcome_full_post_path) >>
     rpt gen_tac >> BETA_TAC >> strip_tac >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> rename1 `_ = INL b` >> qexists `b` >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     disch_tac >> simp[NoAsms,Abbr `Inv`] >>
     qpat_assum `~b ==> body_const_cells_agree _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `Live H _ rs ee _ _ _` (irule_at Any)) >>
     qpat_assum `gas_origin_ptr_path _ (s,g,tt) _ (OK _,_,_)`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >> asm_rewrite_tac[]) >>
  suspend "cons_stages"
QED

Resume for_captured_storage_continue_rounds_cut[cons_stages]:
  `!H. valid_horizon cx st0 H ei.storage_trace ==> Live H (len - LENGTH (a::rs)) (a::rs) ei g tt s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ei.storage_trace ==> ?k. Live _ _ _ _ _ _ _`
       (drule_then (qx_choose_then `k` assume_tac)) >>
     `len - LENGTH (a::rs) = k` by
       (qpat_assum `Abbrev (Live = _)` (fn def =>
          qpat_assum `Live H k _ _ _ _ _`
            (mp_tac o BETA_RULE o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] def])) >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        rewrite_tac[forCapturedStorageLiveTheory.for_captured_storage_live_def] >> strip_tac >>
        `LENGTH (a::rs) = LENGTH vs - k` by
          (qpat_assum `a::rs = DROP k vs` (fn th => rewrite_tac[th,LENGTH_DROP])) >>
        qpat_assum `k <= len` mp_tac >> qpat_assum `len = LENGTH vs` mp_tac >>
        qpat_assum `LENGTH (a::rs) = LENGTH vs - k` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!H. valid_horizon _ _ H ei.storage_trace ==> Live _ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms,Abbr `Live`,Abbr `Done`] >> disch_tac >>
  qpat_assum `cx_tops cx = tops` (fn th =>
    qpat_assum `body_const_cells_agree [(NONE,tops)] cx env ei`
      (assume_tac o PURE_REWRITE_RULE [GSYM th])) >>
  qpat_assum `cx_tops cx = tops` (fn th =>
    pure_rewrite_tac [GSYM th]) >>
  `storage_trace_domain cx st0 ei.storage_trace ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
      (bind (read_result cx a) (push_scope_with_var id tyv)) (ei,s,g,tt)
      (\H res eb GG tt z. res = INL () /\ eb.gas_obs = [] /\
        ?v j. eb = for_captured_storage_round_scope id tyv (ei with gas_obs := []) v /\
          read_result cx a ei = (INL v,ei) /\
          for_captured_storage_round_entry (DF,lo,d,ctx,func)
            (cx,c,bc,extend_local env id typ F,sbCopy,loop_body)
            (start,sa,s0,G0,tn0) (idx,p,dst,lvo,len,ai,nb) (H,eb,j,z,GG,tt) /\
          eval_operand bop z = SOME slot /\ op_taint tt bop = {} /\ a::rs = DROP j vs)
      (\H res ee gt r. ?ex. res = INR ex /\ for_array_loop_exit ctx cx RetQ H (INR ex) ee gt r)` by
    suspend "head_cut" >>
  reverse conj_tac >- suspend "extra" >>
  irule for_captured_storage_round_from_head >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists `len - SUC (LENGTH rs)` >> first_assum ACCEPT_TAC) >>
  qpat_assum `cx_tops cx = tops` (rewrite_tac o single) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists `bindings` >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`bc`,`bc1`,`env_b`,`exit`,`incr`,`ai`,`next_var`,`ret_ty`,
    `sbCopy`,`sbBody`,`shadow_func`,`shadow_sbCopy`,`shadow_sbBody`,`si`,`sj`,`sk`,`sl`,`sm`] >>
  qpat_assum `!x. lvo = Var x ==> not_fresh_at saCopy x /\ not_fresh_at sbCopy x`
    (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM,FORALL_AND_THM]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `cx_tops cx = tops` (rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_captured_storage_continue_rounds_cut[extra]:
  qpat_assum `storage_trace_domain _ _ _ ==> gas_outcome_full _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `cx_tops cx = tops` (fn eq =>
    qpat_assum `gas_outcome_full _ _ _ _ _ (ei,s,g,tt) _ _`
      (assume_tac o PURE_REWRITE_RULE[eq])) >>
  qpat_assum `!a rs ei ss gg tt bc bc1 env_b exit incr sb0 sb1 sh0 sh1 idx p dst lvo len inst nb bop vs. _ ==> _`
    irule >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (`valid_horizon cx st0 (storage_trace_horizon ei.storage_trace) ei.storage_trace` by
       (qpat_assum `storage_trace_domain cx st0 ei.storage_trace`
          (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
     qpat_assum `!H. valid_horizon _ _ H ei.storage_trace ==> for_captured_storage_live _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon ei.storage_trace`
          (drule_then (strip_assume_tac o
            REWRITE_RULE [forCapturedStorageLiveTheory.for_captured_storage_live_def]))) >>
     first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists `env_b` >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`bc`,`bc1`,`bop`,`dst`,`exit`,`idx`,`incr`,`ai`,`len`,`lvo`,`nb`,`p`,
            `sbCopy`,`sbBody`,`shadow_sbCopy`,`shadow_sbBody`,`vs`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     qpat_assum `!x. lvo = Var x ==> not_fresh_at saCopy x /\ not_fresh_at sbCopy x`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_captured_storage_continue_rounds_cut[head_cut]:
  disch_tac >>
  qpat_assum `!x. lvo = Var x ==> not_fresh_at saCopy x /\ not_fresh_at sbCopy x`
    (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM,FORALL_AND_THM]) >>
  irule gas_outcome_full_post_mono >>
  mp_tac (Q.INST [`c0` |-> `c`,`sa0` |-> `sa`,`e0` |-> `start`,`sbExpr` |-> `se`,
    `sa` |-> `saCopy`,`sb0` |-> `sbCopy`,`h` |-> `shead.cs_next_id`,`st` |-> `saD`,
    `inst` |-> `ai`,`G` |-> `g`,`tn` |-> `tt`,`explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (CONV_RULE (REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM,BETA_CONV]))
      (Q.SPEC `loop_body` for_captured_storage_head_full))) >>
  impl_keep_tac >- suspend "head_static" >>
  disch_then (irule_at Any o REWRITE_RULE [ETA_AX] o CONJUNCT2) >> BETA_TAC >>
  reverse conj_tac >-
    (POP_ASSUM_LIST (K ALL_TAC) >> pure_rewrite_tac[for_array_loop_exit_def] >>
     metis_tac[haltExitProjTheory.halt_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rename [`read_result cx a ei = (INL v,ei)`,`a::rs = DROP k vs`] >> qexistsl [`v`,`k`] >>
  pure_rewrite_tac[for_captured_storage_round_scope_def,for_captured_storage_round_entry_def] >>
  qpat_x_assum `ee = (ei with <|scopes := _; gas_obs := []|>)` SUBST_ALL_TAC >>
  conj_tac >- REFL_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_captured_storage_continue_rounds_cut[head_static]:
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `stride = type_slot_size tyv` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `stride = type_slot_size tyv` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `stride = type_slot_size tyv` (SUBST1_TAC o SYM) >>
     qpat_assum `saCopy.cs_current_insts = _` (fn th => simp[NoAsms,th])) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (gen_tac >> disch_tac >> qpat_assum `!x. lvo = Var x \/ bop = Var x ==> _` irule >>
     disj1_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (gen_tac >> disch_tac >> qpat_assum `!x. lvo = Var x \/ bop = Var x ==> _` irule >>
     disj2_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (gen_tac >> disch_tac >> qexists `len - SUC (LENGTH rs)` >>
     qpat_assum `!H. valid_horizon _ _ H ei.storage_trace ==> for_captured_storage_live _ _ _ _ _ _`
       (drule_then ACCEPT_TAC)) >>
  first_assum ACCEPT_TAC
QED

Resume for_captured_storage_continue_rounds_cut[nil]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon cx st0 H _ ==> Inv H [] _ _ _ _` mp_tac >>
  simp[NoAsms,Abbr `Inv`,Abbr `Live`,Abbr `Done`] >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM,FORALL_AND_THM]) >>
  irule for_captured_storage_nil_full >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`cb`,`bd`,`bod`,`bop`,`cond`,`dst`,`dv`,`shead.cs_next_id - 2`,
    `em`,`env`,`exit`,`id`,`idx`,`len`,`lvo`,`nb`,`p`,`se`,`sd`,`slot`,`loop_body`,`tr`,`typ`,`tyv`,`vs`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `cb.bb_instructions = _` (fn th => simp[NoAsms,th,get_instruction_def]) >>
  AP_THM_TAC >> AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  first_assum ACCEPT_TAC
QED

Finalise for_captured_storage_continue_rounds_cut

Theorem for_captured_storage_continue_full:
  compile_stmt c lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb) /\
  compile_stmt (gas_shadow_env T c) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n loop_body))
    sha = ((),shb) /\
  compile_expr c (expr_type e) e sa = (vv,se) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  body_inv tops ctx c cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Array e) n loop_body) /\
  type_stmt env ret_ty (For id typ (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id typ (Array e) n loop_body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n loop_body) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n loop_body)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ c ret_ty /\
  c.ce_alloca_locals /\ local_ptrs_reserved c sa /\
  ret_pc_ok c sa s0 /\ return_buf_frame d c sa s0 /\ return_buf_sep d c em u /\
  (!H. dead_lo_ok H (DF H) lo c cx) /\
  (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\ expr_body_pre c cx env e es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_type e = ArrayT typ bd /\ bound_length bd <= n /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!tail. eval_expr cx e (es with gas_obs := obs ++ tail) =
     (INL (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))),em with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
     for_array_expr_endpoint (DF,lo,d,ctx,func) c cx e (es,sa,s0,G0,tn0)
       (vv,se) H (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) em Gu tu u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     storage_well_formed_on cx es (FST H)) /\
  alloca_frame c es sa s0 c em u /\
  ((?w. vv_operand vv = Lit w) \/
   (?tgt nid. loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid /\
             ~(?ty i. e = TopLevelName ty i))) /\
  (!vs. (!tail. array_iterator_results cx (expr_type e)
                  (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) (em with gas_obs := tail) =
                  (INL vs,em with gas_obs := tail)) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
    body_for_full_ok cx tyv id loop_body vs /\
    gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (array_iterator_results cx (expr_type e) (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))))
      (\items. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH items)) "For too long")
                         (eval_for cx tyv id loop_body items)))
    (em,u,Gu,tu) (for_array_loop_post (DF,lo,d,ctx,func) c cx lctx (es,sa,s0,G0,tn0) sb)
    (for_array_loop_exit ctx cx RetQ)
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  mp_tac (BETA_RULE (Q.INST [`Extra` |-> `\a rs ei s G tn. T`]
    for_captured_storage_continue_rounds_cut)) >>
  pure_rewrite_tac[boolTheory.FORALL_SIMP, boolTheory.IMP_CLAUSES, boolTheory.AND_CLAUSES] >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`vs`,`z`,`G`,`tn`,`Inv`,`Done`]
    (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `items = array_iterator_results cx (expr_type e)
    (PlaceR (StoragePlace tr slot (ArrayTV tyv bd)))` >>
  `em with gas_obs := [] = em` by simp[evaluation_state_component_equality] >>
  qabbrev_tac `Round = \a. do v <- read_result cx a; push_scope_with_var id tyv v;
    finally (try (do eval_stmts cx loop_body; return F od) handle_loop_exception) pop_scope od` >>
  qabbrev_tac `Next = \rs b. if b then return () else eval_for cx tyv id loop_body rs` >>
  qabbrev_tac `Exit = \H ex ee gt r. for_array_loop_exit ctx cx RetQ H (INR ex) ee gt r` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_for cx tyv id loop_body vs) (em,z,G,tn)
    (\H res ee GG tt t. res = INL () /\ Done H ee GG tt t)
    (\H res ee gt r. ?ex. res = INR ex /\ Exit H ex ee gt r)` by
    suspend "rounds" >>
  suspend "finish"
QED

Resume for_captured_storage_continue_full[rounds]:
  irule eval_for_rounds_full >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Inv`,`Next`,`stmt_res_ok lctx`,`Round`] >>
  conj_tac >- suspend "cons" >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >> irule gas_exempt_cert_bind_bool >>
     goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >> BETA_TAC >> first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> irule gas_exempt_cert_error_bool >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[Abbr `Round`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[Abbr `Next`] >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> _ /\ Inv _ _ _ _ _ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  first_assum ACCEPT_TAC
QED

Resume for_captured_storage_continue_full[cons]:
  rpt gen_tac >> strip_tac >> irule gas_outcome_full_initial_domain >>
  conj_tac >-
    (simp[NoAsms,Abbr `Round`] >> irule storage_trace_frame_bind_all >>
     simp[NoAsms,storage_trace_frame_read_result,storage_trace_frame_ignore_bind,
       storage_trace_frame_state_updates,storage_trace_frame_finally,
       storage_trace_frame_try,storage_trace_frame_return,storage_trace_frame_loop_handler,
       storage_trace_frame_pop_scope,evaluate_storage_trace_frame]) >>
  conj_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  simp[NoAsms,Abbr `Round`,Abbr `Exit`] >>
  qpat_assum `!a rs ei s G tn. _ ==> gas_outcome_full _ _ _ _ _ _ _ _`
    (drule_all_then ACCEPT_TAC)
QED

Resume for_captured_storage_continue_full[finish]:
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_for cx tyv id loop_body vs) (em,u,Gu,tu)
    (for_array_loop_post (DF,lo,d,ctx,func) c cx lctx (es,sa,s0,G0,tn0) sb)
    (for_array_loop_exit ctx cx RetQ)` by
    (irule gas_outcome_full_zero_prefix_guarded >>
     conj_tac >- simp[NoAsms,cj 4 evaluate_storage_trace_frame] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`G`,`z`,`tn`] >> conj_tac >-
       (gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> _ /\ Inv _ _ _ _ _ _`
          (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
     irule gas_outcome_full_post_mono >>
     qpat_assum `gas_outcome_full _ _ _ _ (eval_for _ _ _ _ _) (em,z,G,tn) _ _` (irule_at Any) >>
     BETA_TAC >> conj_tac >-
       (rpt gen_tac >> strip_tac >> qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
        first_assum (drule_then ACCEPT_TAC)) >>
     simp[NoAsms,Abbr `Exit`] >> rpt strip_tac >>
     qpat_x_assum `res = INR _` SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  suspend "bind"
QED

Resume for_captured_storage_continue_full[bind]:
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >> BETA_TAC >>
  conj_tac >-
    simp[NoAsms,storage_trace_frame_ignore_bind,storage_trace_frame_checks,
         cj 4 evaluate_storage_trace_frame] >>
  conj_tac >- (rpt gen_tac >> strip_tac >> irule gas_exempt_cert_bind_results >>
    goal_assum (drule_at Any) >> BETA_TAC >> first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_error_results >> simp[]) >>
  conj_tac >- simp[NoAsms,Abbr `items`,storage_trace_frame_array_iterator_results] >>
  qexists `\H res ee G tn t. res = INL vs /\ ee = em /\ G = Gu /\ tn = tu /\ t = u` >> BETA_TAC >>
  reverse conj_tac >-
    (irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`Gu`,`em`,`INL vs`,`u`,`tu`] >> BETA_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >> gen_tac >> disch_tac >>
     conj_tac >- (irule (cj 1 gas_origin_ptr_path_rules) >> first_assum ACCEPT_TAC) >>
     qpat_assum `em with gas_obs := [] = em` (rewrite_tac o single)) >>
  rpt gen_tac >> strip_tac >>
  rename1 `storage_trace_domain cx st0 mid.storage_trace` >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 mid.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (drule_then (map_every SUBST_ALL_TAC o CONJUNCTS))) >>
  disj1_tac >> qexists `vs` >> conj_tac >- REFL_TAC >>
  qpat_assum `check _ _ = return ()`
    (fn th => rewrite_tac[th,ignore_bind_def,bind_return]) >>
  first_assum ACCEPT_TAC
QED

Finalise for_captured_storage_continue_full
