Theory bodyIntCallBufferHeadAllocateMods
Ancestors gasOriginPtrLabels[qualified,ignore_grammar]
  bodyIntCallBufferHeadCutsMods bodyIntCallBufferHeadSpecMods bodyIntCallBufferHeadVVMods
  bodyIntCallBufferAllocVVMods bodyIntCallStagePacketMods bodyFullPostsMods exprSimMemorySource
  exprLoweringProps bodyIntCallBufferHeadFrameMods
  exprSimWordArgs[qualified,ignore_grammar]
  bodyExtKeywordDefaultAllocMods[qualified,ignore_grammar]
  bodyMemoryDefs[qualified,ignore_grammar] exprSimCopy[qualified,ignore_grammar]
  wordArgsPtr[qualified,ignore_grammar] freshWrites[qualified,ignore_grammar]
  vyperStorageTrace bodyWriteSubscriptSourceMods
  gasExplicitSites gasOutcomeFullMods fragGasOriginPtr vyperStorageFootprint
  vyperInterpreter vyperState venomState compileEnv loweringPosts bodyPtrDefs

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
      (DF,lo,d,ctx,func) cenv cx st0
      (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin
      (ci,mid,u,Gu,tu) (ca,mid,a,Ga,ta) dst base
      (MAX 32 (type_memory_bytes cenv dty))
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
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `mid.gas_obs` mp_tac) >>
     simp[evaluation_state_component_equality]) >>
    drule_all_then strip_assume_tac bodyIntCallBufferHeadVVModsTheory.intcall_buffer_head_vv_resources_mods >>
    `si.cs_next_var <= ci.cs_next_var /\ si.cs_next_id <= ci.cs_next_id` by
      (qspecl_then [`cenv`,`expr_type e`,`e`,`si`] mp_tac
         (cj 1 compile_expr_ci_mono) >>
       qpat_assum `compile_expr cenv (expr_type e) e si = (vv,ci)`
         (fn th => pure_rewrite_tac [th]) >>
       simp[ci_mono_def]) >>
    `ci.cs_next_id < ca.cs_next_id /\ ci.cs_next_var <= ca.cs_next_var` by
      (qpat_assum `compile_alloc_buffer (MAX 32 (type_memory_bytes cenv dty)) ci = (buf,ca)`
         (mp_then Any mp_tac loweringHaltTheory.compile_alloc_buffer_parts) >>
       simp[]) >>
    mp_tac (Q.INST [`n` |-> `MAX 32 (type_memory_bytes cenv dty)`,
                    `sm` |-> `ci`, `sn` |-> `ca`, `buf` |-> `buf`,
                    `sa` |-> `si`, `es` |-> `esi`, `s0` |-> `s`,
                    `ee` |-> `mid`, `tv` |-> `raw`, `vv` |-> `vv`,
                    `Gi` |-> `G`, `ti` |-> `tn`, `G` |-> `Gu`, `tn` |-> `tu`,
                    `H0` |-> `H0`, `s` |-> `u`,
                    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
      (INST_TYPE [alpha |-> ``:256``]
        bodyExtKeywordDefaultAllocModsTheory.ext_kw_default_alloc_mods)) >>
    (impl_tac >-
      (fs[exprSimFullBundlePropsTheory.expr_sim_full_code_def] >> rpt conj_tac >>
       (asm_rewrite_tac[] >>
        TRY (irule vyperArithTheory.lt_dimword_256 >>
             qexists_tac `64` >> simp[])))) >>
    disch_then (qx_choosel_then [`dst`,`w`,`a`,`Ga`,`ta`]
      (map_every assume_tac o CONJUNCTS)) >>
    qexistsl_tac [`dst`,`w2n w`,`v`,`a`,`Ga`,`ta`] >>
    simp[intcall_buffer_head_alloc_post_mods_def] >>
    rpt conj_tac
    >- (qpat_assum `allocas_from lo a`
          (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
        disch_then (qspecl_then
          [`ci.cs_next_id`,`w2n w`,`MAX 32 (type_memory_bytes cenv dty)`] mp_tac) >>
        simp[])
    >- (qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
                         (u,Gu,tu) [] (OK a,Ga,ta)`
          (qspec_then `DF H0`
            (mp_tac o MATCH_MP gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels)) >>
        simp[])
    >> `!x w. not_fresh_at ci x /\ lookup_var x u = SOME w ==>
               lookup_var x a = SOME w` by simp[]
    >> `wb_frame cenv es0 mid sa s0 u` by
         (irule wb_frame_stage_trans >> qexistsl_tac [`esi`,`s`,`si`] >> simp[])
    >> `wb_frame cenv es0 mid sa s0 a` by
         (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
          qexistsl_tac [`ci`,`u`] >> simp[] >> decide_tac)
    >> `!n b sz. local_region cenv mid.scopes a n b sz <=>
                  local_region cenv mid.scopes u n b sz` by
         (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
          qexists `ci` >> simp[])
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
                       vv_post_mods H ctx func cenv cx e esi si ci s mid raw vv a /\ _`
         (qspec_then `H` mp_tac)
    >> (impl_tac >- first_assum ACCEPT_TAC)
    >> disch_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])
    >> conj_tac >> first_assum ACCEPT_TAC
QED
