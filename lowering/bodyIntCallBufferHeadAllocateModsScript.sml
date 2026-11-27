Theory bodyIntCallBufferHeadAllocateMods
Ancestors gasOriginPtrLabels[qualified,ignore_grammar]
  bodyIntCallBufferHeadCutsMods bodyIntCallBufferHeadSpecMods bodyIntCallBufferHeadVVMods
  bodyIntCallBufferAllocVVMods bodyIntCallStagePacketMods bodyFullPostsMods exprSimMemorySource
  exprLoweringProps bodyIntCallBufferHeadFrameMods
  wordArgsPtr[qualified,ignore_grammar] freshWrites[qualified,ignore_grammar]
  exprBodyPreProps vyperTypeEvalCaseProofs vyperTypeExprSoundness vyperTypeArgFits
  bodyCopyAtomicRhsTypeMods exprSimProps bodyMemBopRestWordPath venomMemDefs
  vyperStorageTrace bodyWriteSubscriptSourceMods
  gasExplicitSites gasOutcomeFullMods fragGasOriginPtr vyperStorageFootprint
  vyperInterpreter vyperState venomState compileEnv loweringPosts bodyPtrDefs

val _ = Parse.hide "base";

Theorem head_post_value_typed[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  value_runtime_typed env (expr_type e) v ==>
  value_runtime_typed env (post_value_type cenv e) v
Proof
  strip_tac >> Cases_on `post_value_type cenv e = expr_type e` >> simp[] >>
  `?ty fid args drv. e = Call ty (IntCall fid) args drv` by
    metis_tac[post_value_type_not_int_call] >>
  gvs[] >> Cases_on `is_word_type ty \/ is_bytestring_type ty` >>
  gvs[post_value_type_def,vyperASTTheory.expr_type_def] >>
  irule (REWRITE_RULE [ETA_THM] copy_intcall_read_lowered_mods) >>
  fs[exprSimHypsDefsTheory.expr_body_pre_mods_def] >>
  qexistsl_tac [`cx`,`es`,`ee`,`mods`] >> simp[]
QED

Theorem intcall_buffer_head_allocate_mods:
  intcall_buffer_head_input_mods
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    mods exps src tops cenv cx env st0
    (sa,es0,s0,G0,tn0) (si,esi,s,G,tn)
    pin (ops,ws,vals,ptys,pflags) e dty
    (shi,vv,ci,shci,buf,ca,opn,cu,cs) /\
  intcall_buffer_head_raw_post_mods
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    mods cenv cx env st0 (si,esi,s,G,tn)
    e dty marks raw vv ci mid u Gu tu ==>
  ?dst base v a Ga ta.
    read_result cx raw mid = (INL v,mid) /\
    intcall_buffer_head_alloc_post_mods
      (DF,lo,d,ctx,shadow_ctx,PG,func) mods cenv cx env st0
      (si,esi,s,G,tn) (ci,mid,u,Gu,tu) (ca,mid,a,Ga,ta)
      e dty raw vv buf ci.cs_next_id dst base (MAX 32 (type_memory_bytes cenv dty)) v /\
    intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
      (sa,es0,s0,G0,tn0) (ca,mid,a,Ga,ta) pin
Proof
  pure_rewrite_tac [intcall_buffer_head_input_mods_def,
                    intcall_buffer_head_raw_post_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  `valid_horizon cx st0 H0 esi.storage_trace` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `mid.gas_obs` assume_tac) >>
     drule_at (Pat `f st = (res,st')`) valid_horizon_frame >>
     simp[evaluate_storage_trace_frame]) >>
  qpat_assum `intcall_stage_frame_mods _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intcall_stage_frame_mods_def]) >>
  qpat_assum `!H. valid_horizon _ _ H esi.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `expr_body_pre_mods mods cenv cx env e
      (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ mid.gas_obs) /\
   body_const_cells_agree_mods mods cx env
      (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ mid.gas_obs) /\
   eval_expr cx e
      (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ mid.gas_obs) =
      (INL raw,mid) /\
   storage_trace_domain cx st0 mid.storage_trace /\
   (!H. valid_horizon cx st0 H mid.storage_trace ==>
      vv_post_mods H ctx func cenv cx e esi si ci s mid raw vv u /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid Gu tu u /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK u,Gu,tu)) /\
   compile_expr cenv (expr_type e) e si = (vv,ci) /\
   local_ptrs_reserved cenv si /\
   return_buf_frame d cenv si s /\
   stmt_state_rel H0 ctx func cenv cx esi s /\
   s.vs_alloca_next <= u.vs_alloca_next` by
    simp[] >>
  drule_all_then strip_assume_tac intcall_buffer_head_vv_resources_mods >>
  qpat_assum `expr_sim_full_code _ _`
    (strip_assume_tac o MATCH_MP exprSimFullBundlePropsTheory.expr_sim_full_code_fields) >>
  `env.type_defs = get_tenv cx` by
    (qhdtm_assum `expr_sim_inv_mods` (assume_tac o MATCH_MP expr_sim_inv_mods_env) >>
     drule_then ACCEPT_TAC env_consistent_type_defs_get_tenv) >>
  `bind (eval_expr cx e) (read_result cx)
      (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ mid.gas_obs) = (INL v,mid)` by
    simp[bind_def] >>
  drule_all_then assume_tac head_post_value_typed >>
  qpat_x_assum `value_runtime_typed env (post_value_type cenv e) v` mp_tac >>
  rewrite_tac[value_runtime_typed_def] >>
  qpat_assum `env.type_defs = get_tenv cx` (fn th => rewrite_tac[th]) >> strip_tac >>
  qpat_x_assum `value_runtime_typed env (expr_type e) v` mp_tac >>
  rewrite_tac[value_runtime_typed_def] >>
  qpat_assum `env.type_defs = get_tenv cx` (fn th => rewrite_tac[th]) >> strip_tac >>
  `si.cs_next_var <= ci.cs_next_var /\ si.cs_next_id <= ci.cs_next_id` by
    (qspecl_then [`cenv`,`expr_type e`,`e`,`si`] mp_tac (cj 1 compile_expr_ci_mono) >>
     qpat_assum `compile_expr cenv (expr_type e) e si = (vv,ci)`
       (fn th => pure_rewrite_tac [th]) >> simp[ci_mono_def]) >>
  `MAX 32 (type_memory_bytes cenv dty) < dimword (:256)` by
    (irule vyperArithTheory.lt_dimword_256 >> qexists_tac `64` >> simp[]) >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` kall_tac >>
  qpat_assum `compile_alloc_buffer _ _ = _`
    (mp_then (Pat `compile_alloc_buffer _ _ = _`) mp_tac
      (SIMP_RULE bool_ss [LET_THM] intcall_buffer_alloc_vv_mods)) >>
  disch_then (fn th => qpat_assum `stmt_state_rel H0 ctx func cenv cx esi s`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `vv_store_bound _ _ _ _ _ _ u`
    (mp_then (Pat `vv_store_bound`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `read_result cx raw mid = (INL v,mid)`
    (mp_then (Pat `read_result`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME _`
    (mp_then (Pat `evaluate_type _ _ = SOME _`) mp_tac th)) >>
  disch_then (qspecl_then
    [`tu`,`tn`,`st0`,`si`,`lo`,`gas_explicit_sites ctx shadow_ctx`,`d`,`PG`,`G`,`Gu`,`DF`]
    mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`dst`,`base`,`a`,`Ga`,`ta`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`dst`,`base`,`v`,`a`,`Ga`,`ta`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "allocated" >>
    `wb_frame cenv es0 mid sa s0 u` by
         (irule wb_frame_stage_trans >> qexistsl_tac [`esi`,`s`,`si`] >> simp[])
    >> `wb_frame cenv es0 mid sa s0 a` by
         (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
          qexistsl_tac [`ci`,`u`] >> simp[] >> decide_tac)
    >> `ghost_kept_at lo cenv es0 sa G0 tn0 s0 Ga ta` by
         (irule wordArgsPtrTheory.ghost_kept_at_trans >>
          qexistsl_tac [`G`,`esi`,`s`,`si`,`tn`] >> simp[] >>
          qpat_assum `wb_frame cenv es0 esi sa s0 s`
            (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
          first_assum ACCEPT_TAC)
    >> `return_buf_frame d cenv ca a` by
         (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
          qexistsl_tac [`cenv`,`u`,`ci`] >> simp[])
    >> simp[intcall_stage_frame_mods_def]
    >> rpt conj_tac
    >- (Cases_on `pin` >> gvs[] >> PairCases_on `x` >> gvs[] >>
        `not_fresh_at ci x0` by
          (irule freshWritesTheory.not_fresh_at_mono >> qexists `si` >> simp[]) >>
        `not_fresh_at ca x0` by
          (irule freshWritesTheory.not_fresh_at_mono >> qexists `ci` >> simp[]) >>
        `lookup_var x0 u = SOME (n2w x1)` by simp[] >>
        `FLOOKUP u.vs_allocas sa.cs_next_id = SOME (x1,x2)` by simp[] >>
        simp[] >> rpt conj_tac >> TRY decide_tac >>
        rpt gen_tac >> disch_tac >>
        qpat_assum `!n lb sz. local_region _ mid.scopes u n lb sz ==>
                              x1 + x2 <= lb \/ lb + sz <= x1`
          (qspecl_then [`n`,`lb`,`sz`] mp_tac) >>
        qpat_assum `!n b sz. local_region _ mid.scopes a n b sz <=> _`
          (qspecl_then [`n`,`lb`,`sz`] mp_tac) >> simp[])
    >> qx_gen_tac `H` >> disch_tac
    >> qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                       vv_post_mods H ctx func cenv cx e esi si ca s mid raw vv a /\ _`
         (qspec_then `H` mp_tac)
    >> (impl_tac >- first_assum ACCEPT_TAC)
    >> disch_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])
    >> conj_tac >> first_assum ACCEPT_TAC
QED

Resume intcall_buffer_head_allocate_mods[allocated]:
  simp[intcall_buffer_head_alloc_post_mods_def] >> rpt conj_tac
  >- drule_all_then ACCEPT_TAC type_widens_to_value_has_type
  >- (strip_tac >> qx_gen_tac `w` >> disch_tac >>
      qpat_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> ?a'. (INL v,mid) = _ /\ _`
        (mp_tac o SIMP_RULE (srw_ss()) []) >>
      (impl_tac >- simp[]) >>
      disch_then (qspec_then `w` mp_tac) >>
      simp[AC arithmeticTheory.ADD_COMM arithmeticTheory.ADD_ASSOC])
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ u /\ _`
        (qspec_then `H0` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
      first_assum ACCEPT_TAC)
  >- (simp[intcall_buffer_head_edge_mods_def] >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!aid b cap. _ ==> mem_bytes_at b cap u.vs_memory = _ /\ _`
        (qspecl_then [`aid`,`b`,`n`] mp_tac) >>
      simp[AC CONJ_COMM CONJ_ASSOC,AC arithmeticTheory.ADD_COMM arithmeticTheory.ADD_ASSOC] >>
      (impl_tac >-
        (rpt gen_tac >> disch_tac >>
         qpat_assum `!nm p k. local_region cenv mid.scopes u nm p k ==> b + n <= p \/ k + p <= b`
           drule >> decide_tac)) >>
      disch_then ACCEPT_TAC)
  >- (simp[intcall_buffer_head_edge_mods_def] >>
      rpt gen_tac >> strip_tac >> rpt strip_tac >>
      `b + n <= u.vs_alloca_next` by
        (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace) _ _ _ _ _ u`
           (mp_tac o REWRITE_RULE [alloca_inv_def,alloca_next_valid_def] o
            MATCH_MP bodyMemBopRestWordPathTheory.rest_word_state_alloca_inv) >>
         disch_then (mp_tac o CONJUNCT2) >>
         disch_then (qspecl_then [`aid`,`b`,`n`] mp_tac) >> simp[]) >>
      `i < u.vs_alloca_next` by decide_tac >>
      qpat_assum `!i. i < u.vs_alloca_next ==> (i IN ta.t_mem <=> _)`
        (qspec_then `i` mp_tac) >> simp[])
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ a /\ _`
        (qspec_then `H0` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
      qpat_assum `stmt_state_rel _ _ _ _ _ _ a`
        (ACCEPT_TAC o MATCH_MP bodyMemBopRestWordPathTheory.rest_word_state_alloca_inv))
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >>
      qpat_assum `!nm b n. local_region _ mid.scopes a nm b n ==> _`
        (qspecl_then [`nm`,`b`,`n`] mp_tac) >> simp[])
QED

Finalise intcall_buffer_head_allocate_mods
