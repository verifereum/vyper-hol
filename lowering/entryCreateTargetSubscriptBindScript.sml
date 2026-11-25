(* The ordinary subscript hands off at the installed base and index exits. *)
Theory entryCreateTargetSubscriptBind
Ancestors
  entryCreateTargetTailSpec entryCreateImmSubscriptIntervals
  entryCreateScopedBind entryCreateReplayBind bodyInvCodeProps
  gasShadowCompileStmtHelpers gasShadowCompile gasShadowState gasShadow
  targetSubscriptContinuation targetSubscriptSplit
  bodyFullTargetDefs bodyFullPreds bodyFullShared bodyFullHashKeccakFixed
  exprSimFullBundleProps bodySimAugPlaceLoad targetPlaceSim
  entryCreateStmtUpdateCode createSizeOperandCode createSizeCutOpens
  exprLoweringProps fragExec gasExemptCert gasSummary vyperState
  compileEnv entryCreateIntervalLayout vyperInterpreter
  exprLowering createSizePreparationCode createSizeCutCode
  entryCreateFocusSpec bodyFullIfExpReach fragGasOriginPtrExec
  targetPlaceSimCasesBase vyperStorageTrace vyperStorageFootprint
  exprSimHypsDefs s1PrefixDefs vyperTypeEnv loweringPosts evalNoHalt
  gasContext targetPlaceSimDefs exprSimDefs entryCreateCompletedCut bodyMemoryDefs
  vyperTypeSystem vyperAST vyperValue pair

Theorem target_subscript_shadow_landing[local]:
  gas_shadow_compiles f g /\ gas_shadow_state a ha /\ f a = (x,b) ==>
  ?hb. g ha = (x,hb) /\ gas_shadow_state b hb
Proof
  Cases_on `g ha` >> simp[gas_shadow_compiles_def] >> strip_tac >>
  first_x_assum (qspecl_then [`a`,`ha`] mp_tac) >> simp[]
QED

Theorem target_subscript_installed_splits[local]:
  compile_get_target_ptr compile_expr ce (SubscriptTarget bt e) a = (out,b) /\
  compile_get_target_ptr compile_expr (gas_shadow_env T ce)
    (gas_shadow_target (SubscriptTarget bt e)) ha = (out,hb) /\
  expr_sim_full_code (C,HC,f,hf) (a,b,ha,hb) /\ create_layout a b ==>
  ?rb m hm ix n hn.
    compile_get_target_ptr compile_expr ce bt a = (rb,m) /\
    lower_value compile_expr ce (expr_type e) e m = (ix,n) /\
    target_subscript_suffix ce e rb ix n = (out,b) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T ce)
      (gas_shadow_target bt) ha = (rb,hm) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
      (gas_shadow_expr e) hm = (ix,hn) /\
    expr_sim_full_code (C,HC,f,hf) (a,m,ha,hm) /\
    expr_sim_full_code (C,HC,f,hf) (m,n,hm,hn) /\
    fn_has_code n b f /\ fn_has_code m b f /\
    ci_mono a m /\ ci_mono m n /\ ci_mono n b /\
    create_layout a m /\ create_layout m n /\ create_layout m b /\ create_layout n b
Proof
  strip_tac >> drule target_subscript_compile_decompose >> strip_tac >>
  fs[expr_sim_full_code_def] >>
  `?hm. compile_get_target_ptr compile_expr (gas_shadow_env T ce)
      (gas_shadow_target bt) ha = (rb,hm) /\ gas_shadow_state sm hm` by
    (irule target_subscript_shadow_landing >> first_assum (irule_at Any) >>
     simp[gas_shadow_stmt_get_target_ptr_env]) >>
  `?hn. lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
      (gas_shadow_expr e) hm = (ix,hn) /\ gas_shadow_state sn hn` by
    (irule target_subscript_shadow_landing >> first_assum (irule_at Any) >>
     qexists_tac `lower_value compile_expr ce (expr_type e) e` >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  qpat_assum `compile_get_target_ptr _ _ (gas_shadow_target (SubscriptTarget _ _)) _ = _`
    (mp_tac o REWRITE_RULE[gas_shadow_expr_def]) >>
  disch_then (strip_assume_tac o MATCH_MP target_subscript_compile_decompose) >>
  fs[gas_shadow_expr_type] >> gvs[] >>
  drule_all target_subscript_compile_intervals >> strip_tac >>
  `ci_mono ha hm /\ ci_mono hm hn /\ ci_mono hn hb` by
    (irule target_subscript_compile_intervals >>
     qexistsl_tac [`gas_shadow_target bt`,`gas_shadow_env T ce`,
                   `gas_shadow_expr e`,`ix`,`out`,`rb`] >>
     simp[gas_shadow_expr_type]) >>
  `fn_has_code a sm f /\ fn_has_code sm sn f /\ fn_has_code sn b f`
    by metis_tac[target_subscript_interval_code] >>
  `fn_has_code ha hm hf /\ fn_has_code hm hn hf /\ fn_has_code hn hb hf`
    by metis_tac[target_subscript_interval_code] >>
  simp[] >> fs[ci_mono_def] >>
  `cs_extends sm b` by metis_tac[cs_extends_trans] >>
  rpt conj_tac
  >- metis_tac[fn_has_code_split]
  >- metis_tac[create_layout_subinterval,cs_extends_refl]
  >- metis_tac[create_layout_subinterval]
  >- metis_tac[create_layout_subinterval,cs_extends_refl]
  >- metis_tac[create_layout_subinterval,cs_extends_refl,cs_extends_trans]
QED

Theorem target_subscript_source_bind[local]:
  eval_base_place cx (SubscriptTarget bt e) =
    bind (eval_base_place cx bt)
      (\pv. bind (bind (eval_expr cx e) (read_result cx))
                 (\v. extend_place cx pv (ValueSubscript v)))
Proof
  simp[FUN_EQ_THM,Once evaluate_def,bind_assoc]
QED

Theorem ordinary_subscript_bind_laws[local,simp]:
  immutable_scoped_bind_law (:'a) (:'b) /\
  immutable_replay_bind_law (:'a) (:'b)
Proof
  rewrite_tac[immutable_scoped_bind_law_def,immutable_replay_bind_law_def] >>
  conj_tac >> rpt gen_tac >> strip_tac
  >- (irule scoped_operand_bind_all_mixed >> simp[] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`P`,`m`] >> simp[] >> rpt conj_tac >>
      first_assum ACCEPT_TAC) >>
  irule create_operand_cut_bind_replay >> simp[] >>
  qexistsl_tac [`DF`,`G`,`PG`,`Q`,`lo`,`m`,`tn`] >> simp[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem ordinary_subscript_bind_certs[local,simp]:
  immutable_subscript_bind_certs tops C f
    (source : evaluation_state -> eval_result evaluation_result) next es s /\
  immutable_subscript_bind_certs tops C f
    (source' : evaluation_state -> value evaluation_result) next' es' s'
Proof
  rw[immutable_subscript_bind_certs_def] >>
  rewrite_tac[ignore_bind_def,bind_assoc]
  >- (irule gas_exempt_cert_error_result >> simp[])
  >- (irule gas_exempt_cert_bind_result >> qexistsl_tac [`mid`,`t`,`v`] >>
      simp[GSYM ignore_bind_def])
  >- (irule gas_exempt_cert_error_value >> simp[]) >>
  irule gas_exempt_cert_bind_value >> qexistsl_tac [`mid`,`t`,`v`] >>
  simp[GSYM ignore_bind_def]
QED

Theorem ordinary_target_subscript_suffix_cut_code[local]:
  create_cut_code {} n (SND (target_subscript_suffix ce e rb ix n))
Proof
  PairCases_on `rb` >> Cases_on `rb2` >>
  TRY (rename1 `SOME pt` >> Cases_on `pt`) >>
  simp[target_subscript_suffix_def] >>
  rpt (FIRST [match_mp_tac create_cut_code_bind_all >> conj_tac,
              gen_tac, BETA_TAC >> NO_TAC, BasicProvers.TOP_CASE_TAC,
              IF_CASES_TAC] >>
       simp[update_array_subscript_cut, compile_mapping_subscript_def,
            compile_keccak256_key_def, create_alloc_buffer_cut_code,
            create_cut_code_emit_op,create_cut_code_emit_inst,
            create_cut_code_emit_void,create_cut_targets_def,
            LET_THM,comp_ignore_bind_def])
QED

(* Both admissibility transfers read the exact source equations of the
   selected prefix, with the remaining explicit readings as the tail. *)
Theorem ordinary_target_index_admissible[local]:
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  (!tail. eval_base_place cx bt (es with gas_obs := gs ++ tail) =
          (INL pv,mid with gas_obs := tail)) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid
Proof
  rewrite_tac[gas_admissible_def,target_subscript_source_bind] >>
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `res`
  >- simp[expr_res_ok_def] >>
  qpat_x_assum `!gs res ee. _ ==> _`
    (qspecl_then [`gs ++ gs'`,`INR y`,`ee`] mp_tac) >>
  simp[Once bind_def] >> simp[Once bind_def,target_res_ok_def,expr_res_ok_def]
QED

Theorem ordinary_target_tail_admissible[local]:
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  (!tail. eval_base_place cx bt (es with gas_obs := gs ++ tail) =
          (INL pv,mid with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
           (mid with gas_obs := hs ++ tail) = (INL v,ee with gas_obs := tail)) ==>
  gas_admissible (extend_place cx pv (ValueSubscript v)) target_res_ok ee
Proof
  rewrite_tac[gas_admissible_def,target_subscript_source_bind] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs res ee. _ ==> _`
    (qspecl_then [`gs ++ (hs ++ gs')`,`res`,`ee'`] mp_tac) >>
  simp[Once bind_def] >> simp[Once bind_def]
QED

Theorem ordinary_subscript_return_empty[local]:
  immutable_subscript_return (DF,lo,E,C,f,PG) cx st0 a m source (es,s,G,tn)
    P left v (mid,t,G1,tn1) ==>
  source (es with gas_obs := gas_explicit left s.vs_gas_readings) = (INL v,mid)
Proof
  simp[immutable_subscript_return_def] >> strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem ordinary_target_tail_exit[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 n b
    (extend_place cx pv (ValueSubscript v)) (mid,u,G,tn) Q
    (\H res ee gt r. expr_exit res r) /\
  (!H res ee G' tn' t. Q H res ee G' tn' t ==> P H res ee G' tn' t) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 n b
    (extend_place cx pv (ValueSubscript v)) (mid,u,G,tn) P
    (create_operand_exit_post C cx)
Proof
  simp[scoped_operand_outcome_def] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `marks` assume_tac) assume_tac) >>
  qexists_tac `marks` >>
  qpat_x_assum `_ \/ _` (DISJ_CASES_THEN2 assume_tac
    (DISJ_CASES_THEN2 strip_assume_tac assume_tac)) >> simp[] >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >> simp[] >>
  TRY (qpat_assum `Q H res _ G' tn' t` (drule_then assume_tac) >>
       disj1_tac >> qexists_tac `t` >> simp[] >> NO_TAC) >>
  disj2_tac >> simp[create_operand_exit_post_def,halt_exit_def] >>
  `res <> INR HaltException` by
    (strip_tac >> gvs[] >>
     qpat_assum `!tail. extend_place _ _ _ _ = _`
       (qspec_then `[]` (mp_tac o MATCH_MP extend_place_nh)) >> simp[]) >>
  Cases_on `res` >> gvs[expr_exit_def] >>
  Cases_on `r` >> gvs[expr_exit_def] >>
  Cases_on `y` >> gvs[expr_exit_def]
QED

Definition ordinary_base_post_def:
  ordinary_base_post (DF,lo,d,C,f) ce cx (es,a,m,s,rb,bvt,G,tn)
    H pv mid G1 tn1 t <=>
    target_post H C f ce cx es a m s mid pv bvt rb t /\
    t.vs_current_bb = m.cs_current_bb /\ t.vs_inst_idx = LENGTH m.cs_current_insts /\
    alloca_history f t /\ (ctx_has_dalloca C ==> allocas_below_fmp t) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d ce cx mid G1 tn1 t /\ target_ptr_ok ce pv rb G1 tn1 t /\
    ghost_kept_at lo ce es a G tn s G1 tn1
End

Theorem ordinary_target_index_source[local]:
  target_pre ce cx env (SubscriptTarget bt e) es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  type_place_target env bt = SOME bvt /\
  eval_base_place cx bt (es with gas_obs := gs) = (INL pv,mid) ==>
  expr_sim_inv ce cx env mid /\ expr_body_pre ce cx env e mid /\
  body_const_cells_agree [(NONE,tops)] cx env mid
Proof
  strip_tac >>
  `target_pre ce cx env bt es` by metis_tac[target_pre_sub] >>
  `expr_sim_inv ce cx env mid` by
    (irule eval_base_place_sim_inv >> qexistsl_tac [`bt`,`es with gas_obs := gs`,`INL pv`] >>
     fs[target_pre_def]) >>
  simp[] >> conj_tac >- fs[target_pre_def,target_indices_pre_def] >>
  irule body_const_cells_agree_base >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ordinary_target_index_frame[local]:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  ci_mono a m /\ local_ptrs_reserved ce a /\ return_buf_frame d ce a s /\
  (!fn inst u. frag_reachable C f s fn inst u ==> dalloca_fmp_headroom inst u) /\
  immutable_subscript_return (DF,lo,E,C,f,PG) cx st0 a m source (es,s,G,tn)
    (ordinary_base_post (DF,lo,d,C,f) ce cx (es,a,m,s,rb,bvt,G,tn))
    left pv (mid,t,G1,tn1) ==>
  local_ptrs_reserved ce m /\ return_buf_frame d ce m t /\ alloca_history f t /\
  (ctx_has_dalloca C ==> allocas_below_fmp t) /\
  (!fn inst u. frag_reachable C f t fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H C f ce cx mid t /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d ce cx mid G1 tn1 t)
Proof
  simp[immutable_subscript_return_def,ordinary_base_post_def,ci_mono_def] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >> simp[] >> rpt conj_tac
  >- metis_tac[local_ptrs_reserved_next_var]
  >- (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`a`] >> fs[target_post_def])
  >- (drule gas_origin_ptr_path_dalloca_fmp_headroom >>
      simp[] >> metis_tac[body_inv_no_phi]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >> fs[target_post_def]
QED

Theorem ordinary_target_index_post_type[local]:
  type_place_target env (SubscriptTarget bt e) = SOME vt ==> post_value_type ce e = expr_type e
Proof
  simp[type_place_target_SubscriptTarget] >> strip_tac >>
  Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
  >- (gvs[] >> rename1 `Call ity (IntCall fid) args drv` >>
      PairCases_on `fid` >> fs[well_typed_expr_def,expr_type_def] >>
      `is_int_type ity \/ hashmap_key_type ity` by
        (rename1 `subscript_vtype bvt ity = SOME _` >> Cases_on `bvt`
         >- (rename1 `Type bty` >> Cases_on `bty` >> gvs[subscript_vtype_def,AllCaseEqs()]) >>
         gvs[subscript_vtype_def,AllCaseEqs()]) >>
      Cases_on `ity` >>
      gvs[is_int_type_def,hashmap_key_type_def,post_value_type_def,is_word_type_def,
          is_bytestring_type_def] >>
      rename1 `BaseT key` >> Cases_on `key` >>
      gvs[is_int_type_def,hashmap_key_type_def,post_value_type_def,is_word_type_def,
          is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def,is_bytestring_type_def,well_formed_type_def,evaluate_type_def,
          AllCaseEqs()]) >>
  irule post_value_type_not_int_call >> metis_tac[]
QED

Theorem ordinary_target_base_admissible[local]:
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es ==>
  gas_admissible (eval_base_place cx bt) target_res_ok es
Proof
  simp[target_subscript_source_bind,gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[target_res_ok_def] >>
  first_x_assum (qspecl_then [`gs`,`INR y`,`ee`] mp_tac) >> simp[Once bind_def]
QED

Theorem ordinary_target_index_retype[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m n
    (bind (eval_expr cx e) (read_result cx)) (mid,t,G1,tn1)
    (expr_sim_full_post (DF,lo,d,C,f) ce cx e (mid,m,n,t,ix,G1,tn1))
    (create_operand_exit_post C cx) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m n
    (bind (eval_expr cx e) (read_result cx)) (mid,t,G1,tn1)
    (\H res ee G2 tn2 u. ?v. res = INL v /\
        expr_sim_full_post (DF,lo,d,C,f) ce cx e (mid,m,n,t,ix,G1,tn1)
          H (INL v) ee G2 tn2 u)
    (\H res ee gt r. ?exc. res = INR exc /\
        create_operand_exit_post C cx H (INR exc : eval_result + exception) ee gt r)
Proof
  simp[scoped_operand_outcome_def] >>
  disch_then (qx_choose_then `marks` assume_tac) >>
  qexists_tac `marks` >>
  qpat_x_assum `_ \/ _` (DISJ_CASES_THEN2 assume_tac
    (DISJ_CASES_THEN2 strip_assume_tac assume_tac)) >> simp[] >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >> simp[]
  >- fs[expr_sim_full_post_def] >>
  Cases_on `res` >> fs[create_operand_exit_post_def,expr_exit_def,halt_exit_def] >>
  metis_tac[bodyFullTargetSubscriptTheory.expr_exit_INR_retype]
QED

Theorem ordinary_target_exit_eq[local]:
  (\H res ee gt r. expr_exit (res : eval_result + exception) r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca C ==> !s. r = Halt s ==> allocas_below_fmp s)) =
  (\H res ee gt r. ?exc. res = INR exc /\
    create_operand_exit_post C cx H (INR exc : eval_result + exception) ee gt r)
Proof
  simp[FUN_EQ_THM,create_operand_exit_post_def] >> rpt gen_tac >>
  Cases_on `res` >> simp[expr_exit_def]
QED

Theorem create_target_subscript_from_tail:
  body_inv tops C ce cx /\ target_pre ce cx env (SubscriptTarget bt e) es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  (target_pre ce cx env bt es ==>
    target_sim_judgment scoped_operand_outcome (DF,lo,d,C,HC,PG,f,hf) ce cx env bt es /\
    !st0 a m rb s.
      compile_get_target_ptr compile_expr ce bt a = (rb,m) /\ fn_has_code a m f /\
      create_layout a m /\ create_operand_at a s /\ ~s.vs_halted ==>
      create_operand_cut a m (gas_explicit_sites C HC) C f (cx_tops cx) cx st0
        (eval_base_place cx bt) (es,s)) /\
  (!mid. expr_sim_inv ce cx env mid /\ expr_body_pre ce cx env e mid /\
    body_const_cells_agree [(NONE,tops)] cx env mid ==>
    expr_sim_scoped (DF,lo,d,C,HC,PG,f,hf) ce cx (expr_type e) e mid /\
    !st0 m n hm hn ix t G1 tn1.
      expr_sim_full_pre (DF,lo,d,C,HC,PG,f,hf) ce cx (expr_type e) e mid
        (st0,m,n,hm,hn,ix,t,G1,tn1) /\ create_layout m n ==>
      create_operand_cut m n (gas_explicit_sites C HC) C f (cx_tops cx) cx st0
        (bind (eval_expr cx e) (read_result cx)) (mid,t)) /\
  target_subscript_tail_judgment
    (\(D,L,E,C',f',P) ts c start n b source (ee,u,G',tn') Q R.
      scoped_operand_outcome (D,L,E,C',f',P) ts c start n b source (ee,u,G',tn') Q R /\
      create_operand_cut n b E C' f' ts c start source (ee,u))
    (DF,lo,d,C,HC,PG,f,hf) ce cx env bt e es /\
  type_place_target env (SubscriptTarget bt e) = SOME vt /\
  compile_get_target_ptr compile_expr ce (SubscriptTarget bt e) a = (out,b) /\
  compile_get_target_ptr compile_expr (gas_shadow_env T ce)
    (gas_shadow_target (SubscriptTarget bt e)) ha = (out,hb) /\
  expr_sim_full_code (C,HC,f,hf) (a,b,ha,hb) /\ create_layout a b /\
  local_ptrs_reserved ce a /\ (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  return_buf_frame d ce a s /\ alloca_history f s /\
  (ctx_has_dalloca C ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable C f s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H C f ce cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G tn s) /\
  ~s.vs_halted /\ create_operand_at a s ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites C HC,C,f,PG)
    (cx_tops cx) cx st0 a b (eval_base_place cx (SubscriptTarget bt e)) (es,s,G,tn)
    (\H res ee G' tn' t. ?pv. res = INL pv /\
      ordinary_base_post (DF,lo,d,C,f) ce cx (es,a,b,s,out,vt,G,tn) H pv ee G' tn' t)
    (create_operand_exit_post C cx) /\
  create_operand_cut a b (gas_explicit_sites C HC) C f (cx_tops cx) cx st0
    (eval_base_place cx (SubscriptTarget bt e)) (es,s)
Proof
  strip_tac >> drule_all target_subscript_installed_splits >> strip_tac >>
  `target_pre ce cx env bt es` by metis_tac[target_pre_sub] >>
  qpat_assum `type_place_target _ (SubscriptTarget _ _) = SOME _`
    (strip_assume_tac o REWRITE_RULE[type_place_target_SubscriptTarget]) >>
  rename1 `type_place_target env bt = SOME bvt` >>
  `create_cut_code {} a m /\ create_cut_code {} m n /\ create_cut_code {} n b` by
    metis_tac[ordinary_target_subscript_suffix_cut_code,update_target_ptr_cut,
              create_operand_cut_code,SND] >>
  `create_cut_code {} m b` by metis_tac[create_cut_code_join] >>
  fs[expr_sim_full_code_def] >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    metis_tac[ordinary_target_base_admissible] >>
  `create_operand_cut a m (gas_explicit_sites C HC) C f (cx_tops cx) cx st0
     (eval_base_place cx bt) (es,s)` by (first_x_assum irule >> simp[] >> metis_tac[]) >>
  qpat_x_assum `target_sim_judgment _ _ _ _ _ bt _`
    (mp_tac o REWRITE_RULE[target_sim_judgment_def]) >>
  disch_then (qspecl_then [`st0`,`bvt`,`a`,`m`,`ha`,`hm`,`rb`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (fs[create_operand_at_def] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[ordinary_target_exit_eq,GSYM ordinary_base_post_def] >> strip_tac >>
  rewrite_tac[target_subscript_source_bind] >>
  irule immutable_bind_at_interval >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,storage_trace_frame_extend_place] >>
  conj_tac >- metis_tac[body_inv_main_code] >>
  qexistsl_tac [`ordinary_base_post (DF,lo,d,C,f) ce cx (es,a,m,s,rb,bvt,G,tn)`,`m`] >>
  simp[create_operand_exit_post_def,expr_exit_def] >>
  suspend "index"
QED

Resume create_target_subscript_from_tail[index]:
  qx_genl_tac [`left`,`pv`,`mid`,`t`,`G1`,`tn1`] >> strip_tac >>
  drule_then assume_tac ordinary_subscript_return_empty >>
  drule_all ordinary_target_index_source >> strip_tac >>
  drule_all ordinary_target_index_frame >> strip_tac >>
  qpat_assum `immutable_subscript_return _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[immutable_subscript_return_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid` by
    (drule_all ordinary_target_index_admissible >> simp[]) >>
  `expr_sim_full_pre (DF,lo,d,C,HC,PG,f,hf) ce cx (expr_type e) e mid
      (st0,m,n,hm,hn,ix,t,G1,tn1)` by
    (fs[expr_sim_full_pre_def,create_operand_at_def,ci_mono_def] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `a` >> simp[]) >>
  qpat_x_assum `!mid. _ ==> expr_sim_scoped _ _ _ _ _ mid /\ _`
    (qspec_then `mid` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  `create_operand_cut m n (gas_explicit_sites C HC) C f (cx_tops cx) cx st0
    (bind (eval_expr cx e) (read_result cx)) (mid,t)` by
    (first_x_assum irule >> simp[] >> goal_assum (drule_at Any)) >>
  qpat_x_assum `expr_sim_scoped _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[expr_sim_scoped_def]) >>
  disch_then (drule_then (assume_tac o MATCH_MP ordinary_target_index_retype)) >>
  irule immutable_bind_at_interval >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,storage_trace_frame_extend_place] >>
  conj_tac >- metis_tac[body_inv_main_code] >>
  qexistsl_tac [`\H v ee G2 tn2 u. expr_sim_full_post (DF,lo,d,C,f) ce cx e
                  (mid,m,n,t,ix,G1,tn1) H (INL v) ee G2 tn2 u`,`n`] >>
  simp[] >> suspend "tail"
QED

Resume create_target_subscript_from_tail[tail]:
  qx_genl_tac [`right`,`v`,`ee`,`u`,`G2`,`tn2`] >> strip_tac >>
  qpat_assum `immutable_subscript_return _ _ _ _ _ (bind _ _) _ _ _ _ _`
    (assume_tac o MATCH_MP ordinary_subscript_return_empty) >>
  qpat_x_assum `immutable_subscript_return _ _ _ _ _ (bind _ _) _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[immutable_subscript_return_def]) >>
  `gas_admissible (extend_place cx pv (ValueSubscript v)) target_res_ok ee` by
    (drule_all ordinary_target_tail_admissible >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H mid.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `bind (eval_expr _ _) _ (mid with gas_obs := _) = _`
       (mp_then (Pos (el 2)) mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ gas_origin_ptr_path _ _ _ _`
    (drule_then strip_assume_tac) >>
  `post_value_type ce e = expr_type e` by metis_tac[ordinary_target_index_post_type] >>
  fs[expr_sim_full_post_def,expr_sim_full_endpoint_def,create_operand_at_def,ci_mono_def] >>
  qabbrev_tac `Q = \H (res : eval_result + exception) es' G' tn' t'. ?p'. res = INL p' /\
    target_post H C f ce cx es a b s es' p' vt out t' /\
    t'.vs_current_bb = b.cs_current_bb /\ t'.vs_inst_idx = LENGTH b.cs_current_insts /\
    alloca_history f t' /\ s.vs_alloca_next <= t'.vs_alloca_next /\
    ghost_inv_at (DF H) lo d ce cx es' G' tn' t' /\
    target_ptr_ok ce p' out G' tn' t' /\ ghost_kept_at lo ce es a G tn s G' tn'` >>
  `scoped_operand_outcome (DF,lo,gas_explicit_sites C HC,C,f,PG) (cx_tops cx) cx st0 n b
     (extend_place cx pv (ValueSubscript v)) (ee,u,G2,tn2) Q
     (\H res es' gt q. expr_exit res q) /\
   create_operand_cut n b (gas_explicit_sites C HC) C f (cx_tops cx) cx st0
     (extend_place cx pv (ValueSubscript v)) (ee,u)` by
    (qunabbrev_tac `Q` >>
     qpat_x_assum `target_subscript_tail_judgment _ _ _ _ _ _ _ _`
       (irule o SIMP_RULE (srw_ss()) [target_subscript_tail_judgment_def]) >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`G1`,`gas_explicit left s.vs_gas_readings`,`bvt`,
                   `gas_explicit right t.vs_gas_readings`,`ix`,`mid`,`rb`,`m`,`t`,`tn1`] >>
     asm_rewrite_tac[] >> reverse conj_tac
     >- (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
           fs[storage_trace_domain_def] >>
         qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
                       ordinary_base_post _ _ _ _ H pv mid G1 tn1 t /\ _`
           (drule_then strip_assume_tac) >> fs[ordinary_base_post_def]) >>
     gen_tac >> strip_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by
       (first_x_assum irule >> first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
                   ordinary_base_post _ _ _ _ H pv mid G1 tn1 t /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ gas_origin_ptr_path _ _ _ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     fs[ordinary_base_post_def]) >>
  simp[] >> irule ordinary_target_tail_exit >> simp[] >>
  qexists_tac `Q` >> simp[Abbr `Q`,ordinary_base_post_def] >>
  rpt strip_tac >> qexists_tac `p'` >> asm_rewrite_tac[] >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ t'`
    (strip_assume_tac o REWRITE_RULE[target_post_def,expr_post_def]) >>
  drule_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp
QED

Finalise create_target_subscript_from_tail
