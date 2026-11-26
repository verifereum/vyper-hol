(* Composition of the reached Extract32 operands. *)
Theory bodyExtractOperandsMods
Ancestors
  bodyExtractOperandCutsMods bodyExtractPrepareMods
  bodyExtractSourceBindMods bodyExtractPreparedOffsetMods
  bodyExtractPreparedBindMods bodyExtractStackReadMods
  bodyFullIfExpReach exprSimFullBundleProps bodyForcedStorageFrameMods
  vyperStorageTrace exprBodyPreTypingProps bodyFullPredsMods bodyFullPostsMods
  vyperTypeSystem compileEnv vyperContext exprBodyPreProps exprSimExtract32Source
  gasContext exprSimDefs vyperState
Libs monadsyntax

Theorem extract32_from_cuts_mods:
  !exps src tops DF lo d ctx shadow_ctx PG func shadow_func cenv env cx ty ann ret args es.
    (type_builtin_args_length_ok Extract32 (LENGTH args) ==>
      body_exprs_full_ok_mods mods exps cx args) /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (TypeBuiltin ann Extract32 ret args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (TypeBuiltin ann Extract32 ret args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (TypeBuiltin ann Extract32 ret args) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (qx_choosel_then [`src0`,`off`,`m`,`k`,`bt`] strip_assume_tac)
    extract32_operand_shape_mods >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  qpat_x_assum `ann = _` SUBST_ALL_TAC >>
  qpat_x_assum `ret = _` SUBST_ALL_TAC >>
  `is_word_type (BaseT bt)` by
    (Cases_on `bt` >> fs[extract32_result_base_ok_def,is_word_type_def] >>
     rename1 `BytesT b` >> Cases_on `b` >> fs[extract32_result_base_ok_def,is_word_type_def]) >>
  reverse conj_asm2_tac >- suspend "vv" >>
  irule extract32_stack_read_from_vv_mods >> asm_rewrite_tac[]
QED

Resume extract32_from_cuts_mods[vv]:
  `body_exprs_full_ok_mods mods exps cx [src0;off]` by
    fs[type_builtin_args_length_ok_def] >>
  `body_expr_full_ok_mods mods exps cx src0` by
    fs[Once body_exprs_full_ok_mods_def] >>
  `expr_body_pre_mods mods cenv cx env src0 es` by
    (irule extract32_operand_pre_mods >> conj_tac
     >- drule_then ACCEPT_TAC expr_body_pre_mods_inv >>
     qexistsl_tac [`BaseT bt`,`es`,`off`,`BaseT bt`,`src0`] >> asm_rewrite_tac[]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type src0) src0 es` by
    (qpat_assum `body_expr_full_ok_mods _ _ _ src0`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full_mods _ _ _ _ src0 _ /\ _`
       (FIRST o map irule o CONJUNCTS o REWRITE_RULE [IMP_CONJ_THM] o SPEC_ALL) >>
     asm_rewrite_tac[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> first_assum ACCEPT_TAC) >>
     qexists_tac `env` >> asm_rewrite_tac[]) >>
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`srcop`,`sm`,`shm`,`lenop`,`dataop`,`sn`,
    `shn`,`offop`,`sq`,`shq`,`raw`,`sr`,`op`] strip_assume_tac) extract32_paired_cuts_mods >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qexists_tac `func` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx src0) (read_result cx)) expr_res_ok es` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV) extract32_vv_first_admissible) >> simp[]) >>
  qpat_assum `expr_sim_full_mods _ _ _ _ src0 _`
    (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shm`,`srcop`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then assume_tac >>
  irule extract32_source_bind_mods >> asm_rewrite_tac[] >>
  qexistsl_tac [`env`,`exps`,`m`,`mods`,
    `\H v mid G tn s.
       expr_post_mods H ctx func cenv cx src0 es sa sm s0 mid v srcop s /\
       expr_store_bound cx (post_value_type cenv src0) v srcop s /\
       s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
       alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
       s0.vs_alloca_next <= s.vs_alloca_next /\
       ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
       ptr_val_ok cx (post_value_type cenv src0) v srcop G tn s /\
       (~is_word_type (post_value_type cenv src0) ==> ptr_buf_ok cenv src0 srcop G s) /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G tn`] >>
  BETA_TAC >> asm_rewrite_tac[] >> suspend "reached"
QED

Resume extract32_from_cuts_mods[reached]:
  qx_genl_tac [`marks`,`bs`,`mid`,`G1`,`tn1`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty off mid` by
    (qpat_assum `body_expr_full_ok_mods _ _ _ off`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full_mods _ _ _ _ off _ /\ _`
       (FIRST o map irule o CONJUNCTS o REWRITE_RULE [IMP_CONJ_THM] o SPEC_ALL) >>
     asm_rewrite_tac[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> first_assum ACCEPT_TAC) >>
     qexists_tac `env` >> asm_rewrite_tac[]) >>
  `gas_admissible (bind (eval_expr cx off) (read_result cx)) expr_res_ok mid` by
    (rewrite_tac[gas_admissible_def] >> qx_genl_tac [`gs`,`res`,`ee`] >> strip_tac >>
     Cases_on `res` >- simp[expr_res_ok_def] >>
     qpat_assum `gas_admissible (eval_expr cx (TypeBuiltin _ Extract32 _ _)) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
     pure_once_rewrite_tac[eval_expr_extract32_vv_bind] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `gs` mp_tac) >>
     simp[bind_def] >> gvs[bind_def,expr_vv_res_ok_def,expr_res_ok_def]) >>
  `evaluate_type (get_tenv cx) (expr_type src0) = SOME (BaseTV (BytesT (Dynamic m)))` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ src0 es`
       (mp_then (Pat `expr_body_pre_mods _ _ _ _ _ _`) strip_assume_tac
         expr_body_pre_mods_runtime_typing) >>
     `env_consistent env cx es` by fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_then assume_tac vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
     `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
       metis_tac[well_formed_type_def, exprSimSourceTheory.env_consistent_var_type_evaluates] >>
     drule_all exprSafeOperandTheory.well_typed_expr_type_well_formed >>
     simp[well_formed_type_def, vyperValueTheory.evaluate_type_def]) >>
  suspend "prepare"
QED

Resume extract32_from_cuts_mods[prepare]:
  qpat_assum `expr_type src0 = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
  qpat_assum `expr_type off = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sn,sq,shn,shq)` by
    asm_rewrite_tac[expr_sim_full_code_def] >>
  `post_value_type cenv src0 = expr_type src0` by
    simp[loweringPostsTheory.post_value_type_bytestring,is_bytestring_type_def] >>
  `~is_word_type (expr_type src0)` by simp[is_word_type_def] >>
  qpat_assum `post_value_type cenv src0 = _` (fn pt =>
    qpat_assum `~is_word_type (expr_type src0)` (fn nw =>
      qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        expr_post_mods _ _ _ _ _ src0 _ _ _ _ _ _ _ _ /\ _`
        (assume_tac o REWRITE_RULE [pt,nw]))) >>
  irule (let val th = SPEC_ALL extract32_prepare_mods
         in MP extract32_prepared_offset_mods (GENL (free_vars (concl th)) th) end) >>
  asm_rewrite_tac[] >> conj_tac
  >- simp[storage_trace_frame_bind_all,
          bodyForcedStorageFrameModsTheory.bop_forced_storage_frame,
          storage_trace_frame_lifts,storage_trace_frame_return] >>
  (* These are the original frame, the reached source state, and the paired cuts. *)
  qexistsl_tac [`G0`,`bs`,`d`,`dataop`,`es`,`lenop`,`m`,`offop`,`s0`,`sa`,
                `shadow_func`,`shn`,`shq`,`sm`,`sn`,`sq`,`src0`,`srcop`,`tn0`,`ty`] >>
  asm_rewrite_tac[] >> suspend "prepared"
QED

Resume extract32_from_cuts_mods[prepared]:
  qx_genl_tac [`sv`,`p`,`u`,`G2`,`tn2`,`len`,`data`] >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (map_every assume_tac o CONJUNCTS) assume_tac)) >>
  qpat_assum `expr_type src0 = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
  qpat_assum `expr_type off = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
  `ci_mono sa sn` by (irule exprLoweringPropsTheory.ci_mono_trans >> qexists_tac `sm` >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `s0.vs_alloca_next <= s.vs_alloca_next` by
    (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
       fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       expr_post_mods _ _ _ _ _ src0 _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  irule (BETA_RULE extract32_prepared_bind_mods) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `gas_explicit marks s0.vs_gas_readings` >> first_assum ACCEPT_TAC)
  >- (qexists_tac `k` >> first_assum ACCEPT_TAC)
  >- (qexists_tac `m` >> conj_tac >> first_assum ACCEPT_TAC)
  >- (qexistsl_tac [`env`,`mods`] >> conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G1`,`data`,`dataop`,`len`,`lenop`,`offop`,`p`,`raw`,
                `s`,`sm`,`sn`,`sq`,`sr`,`sv`,`tn1`,`ty`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `expr_type src0 = _` (fn th => pure_rewrite_tac[th]) >>
  first_assum ACCEPT_TAC
QED

Finalise extract32_from_cuts_mods
