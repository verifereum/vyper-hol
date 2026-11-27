Theory bodyFullSubscriptMap
Ancestors vyperTypeInvariants[qualified,ignore_grammar] bodyPtrDefs[qualified,ignore_grammar] vyperTypeSystem[qualified,ignore_grammar]
  bodyFullShadowBodyInv
  bodyFullPreds bodySimFull gasOutcomeFullCompose bodyFullTargetMappingRun
  bodyFullTargetMappingRep exprSimSubscriptMap exprSimMapDefs exprSimMapKey
  gasShadowCompile gasShadowState gasShadow exprSimHypsDefs vyperStorageTrace
  gasExemptCert vyperInterpreter vyperState vyperAST exprLoweringProps
  instIdxIndep fragGasOriginPtrLoop fragExec venomState venomExecSemantics
  bodyFullIfExpReach bodyFullHashKeccakFixed contextRawReachable bodyFullSubscriptMappingValue
  bodyFullPredsMods[qualified] bodyInvSplit[qualified]

(* The two selections share the base and key evaluation and execute the
   same hash suffix. The continuations differ only in the selected result. *)
val mapping_shadow_type_tac =
  fs[gasShadowCompileBaseTheory.place_type_gas_shadow_env,
     gasShadowCompileBaseTheory.copies_subscript_base_gas_shadow_env,
     gasShadowCompilePureTheory.gas_shadow_place_type,
     exprLoweringTheory.copies_subscript_base_def,
     gasShadowCompilePureTheory.gas_shadow_subscript_overlap];

fun mapping_shadow_parts_tac shadow_type =
  qpat_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _`
    (mp_tac o REWRITE_RULE [gas_shadow_expr_def]) >> strip_tac >>
  shadow_type >>
  qpat_x_assum `compile_expr _ _ (Subscript _ (gas_shadow_expr _) _) _ = _`
    (mp_then (Pos hd) mp_tac compile_expr_mapping_subscript_parts) >>
  simp[] >> strip_tac >> gvs[];

fun mapping_base_tac base_admissible shadow_type index_cont =
  drule_all compile_expr_mapping_subscript_parts >> strip_tac >>
  rename1 `compile_mapping_subscript _ hashed sp = (outop,sb)` >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (drule (cj 1 compile_expr_grows) >> simp[]) >>
  `cs_extends sm sn /\ sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `cs_extends sn sp` by
    (Cases_on `is_bytestring_type kt` >> gvs[compileEnvTheory.cs_extends_refl] >>
     mp_tac (Q.SPECL [`key`, `F`, `sn`] ci_mono_compile_keccak256_key) >>
     simp[ci_mono_def]) >>
  `cs_extends sp sb` by
    (mp_tac (Q.SPECL [`vv_operand bvv`, `hashed`, `sp`]
       ci_mono_compile_mapping_subscript) >> simp[ci_mono_def]) >>
  `cs_extends sn sb /\ cs_extends sm sb` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `gas_admissible (eval_expr cx e1) expr_map_res_ok es` by
    base_admissible >>
  `?shadow_sm. compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1) shadow_sa =
       (bvv,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv ty e1)
        (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1))` by
       irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_compile_expr_env >>
     pop_assum (qspecl_then [`sa`, `shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1) shadow_sa` >> simp[]) >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    (drule (cj 1 compile_expr_grows) >> strip_tac >>
     mapping_shadow_parts_tac shadow_type >>
     `cs_extends shadow_sm sn'` by
       (qpat_assum `lower_value _ _ _ _ shadow_sm = _`
          (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
     `cs_extends sn' sp'` by
       (Cases_on `is_bytestring_type kt` >> gvs[compileEnvTheory.cs_extends_refl] >>
        mp_tac (Q.SPECL [`key'`, `F`, `sn'`] ci_mono_compile_keccak256_key) >>
        simp[ci_mono_def]) >>
     `cs_extends sp' shadow_sb` by
       (mp_tac (Q.SPECL [`vv_operand bvv`, `hashed'`, `sp'`]
          ci_mono_compile_mapping_subscript) >> simp[ci_mono_def]) >>
     metis_tac[compileEnvTheory.cs_extends_trans]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (drule_all fn_has_code_split >> simp[]) >>
  qpat_x_assum `expr_map_sim_full _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_map_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                          `bvv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> (gvs[]))) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ baseR` >>
  `eval_expr cx (Subscript ann e1 e2) =
   bind (eval_expr cx e1) (\res. bind (bind (eval_expr cx e2) (read_result cx))
     (\kv. select_result cx (expr_type e1) res (ValueSubscript kv)))` by
    (qpat_assum `~subscript_reads_base _ _ _`
      (mp_then Any mp_tac exprSimSubscriptArraySourceTheory.eval_expr_subscript_bind) >>
     simp[]) >>
  asm_rewrite_tac[] >> irule gas_outcome_full_bind_all_path >>
  `!res : eval_result + exception. !r.
     (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r) <=> expr_exit res r` by
    (Cases >> simp[]) >>
  simp[] >> rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- (gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
           cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result,
           storage_trace_frame_select])
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[cj 5 evaluate_storage_trace_frame] >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >~ [`storage_trace_domain _ _ _`] >- index_cont >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[Abbr `baseR`] >>
  simp[Abbr `baseQ`, Abbr `baseR`] >>
  gen_tac >> Cases >> simp[exprSimDefsTheory.expr_exit_def];

fun mapping_index_source_tac index_pre parent_res_ok =
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `s`] >> strip_tac >> fs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `baseQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> baseQ H _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  qpat_x_assum `baseQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `baseQ`, NoAsms] >> disch_then strip_assume_tac >> gvs[] >>
  `~s.vs_halted /\ mid.gas_obs = []` by metis_tac[] >>
  `eval_expr cx e1 (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL (HashMapRef tr slot kt' vt),mid)` by
    (`mid with gas_obs := [] = mid` by
       (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
     qpat_assum `!tail. eval_expr _ _ (_ with gas_obs := _ ++ tail) = _`
       (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[listTheory.APPEND_NIL] >> metis_tac[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`IS_SOME (type_place_expr env e1)` by simp[] >>
     irule body_const_cells_agree_expr >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[]) >>
  index_pre >>
  `expr_body_pre cenv cx env e2 mid` by
    (irule (cj 3 mapping_subscript_index_pre) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `body_expr_full_ok cx e2` by metis_tac[] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e2) e2 mid` by
    (qpat_x_assum `body_expr_full_ok _ _` mp_tac >>
     rewrite_tac[Once body_expr_full_ok_def] >> strip_tac >>
     first_x_assum (irule o cj 1) >> simp[] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
    (simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
     Cases_on `res` >- simp[exprSimDefsTheory.expr_res_ok_def] >>
     rename1 `INR ex` >>
     qpat_x_assum `gas_admissible (bind _ _) ^parent_res_ok _` mp_tac >>
     simp[gasContextTheory.gas_admissible_def] >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
     disch_then (qspecl_then [`INR ex`, `ee`] mp_tac) >>
     gvs[vyperStateTheory.bind_def, expr_map_res_ok_def,
         exprSimDefsTheory.expr_vv_res_ok_def, exprSimDefsTheory.expr_res_ok_def]);

fun mapping_index_shadow_tac shadow_type =
  `?shadow_sn. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2)
      (gas_shadow_expr e2) shadow_sm = (key,shadow_sn) /\ gas_shadow_state sn shadow_sn` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (expr_type e2) e2)
        (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2) (gas_shadow_expr e2))` by
       irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sm`, `shadow_sm`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2)
                 (gas_shadow_expr e2) shadow_sm` >> simp[]) >>
  `cs_extends shadow_sm shadow_sn /\ cs_extends shadow_sn shadow_sb` by
    (`cs_extends shadow_sm shadow_sn` by
       (qpat_assum `lower_value _ _ _ _ shadow_sm = _`
          (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
     mapping_shadow_parts_tac shadow_type >>
     `cs_extends shadow_sn sp'` by
       (Cases_on `is_bytestring_type kt` >> gvs[compileEnvTheory.cs_extends_refl] >>
        mp_tac (Q.SPECL [`key`, `F`, `shadow_sn`] ci_mono_compile_keccak256_key) >>
        simp[ci_mono_def]) >>
     `cs_extends sp' shadow_sb` by
       (mp_tac (Q.SPECL [`vv_operand (LocatedValue tp p)`, `hashed'`, `sp'`]
          ci_mono_compile_mapping_subscript) >> simp[ci_mono_def]) >>
     metis_tac[compileEnvTheory.cs_extends_trans]) >>
  `fn_has_code shadow_sm shadow_sn shadow_func` by metis_tac[fn_has_code_split] >>
  `return_buf_frame d cenv sm s` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s`, `sa`] >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       gas_origin_ptr_path _ (s0,G0,tn0) marks (OK s,G1,tn1)`
       (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then assume_tac)) >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK s,G1,tn1)`
       (mp_then (Pos hd) mp_tac bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sm`, `sn`, `shadow_sm`, `shadow_sn`,
                          `key`, `s`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >- (gvs[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ indexQ indexR`;

fun mapping_index_bind_tac selection_cont =
  irule gas_outcome_full_bind_all >> simp[] >> rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
          cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result]
  >~ [`storage_trace_frame (select_result _ _ _ _)`]
  >- simp[storage_trace_frame_select]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid'`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res ee G tn t. indexQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- selection_cont >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ indexQ indexR` (irule_at Any) >>
  conj_tac >- simp[Abbr `indexR`, Abbr `baseR`] >>
  simp[Abbr `indexQ`, Abbr `indexR`, Abbr `baseR`] >>
  gen_tac >> Cases >> simp[exprSimDefsTheory.expr_exit_def] >>
  rpt strip_tac
  >~ [`expr_exit (INR _) _`]
  >- (qpat_assum `expr_exit (INR _) _`
        (mp_then Any MATCH_ACCEPT_TAC bodyFullTargetSubscriptTheory.expr_exit_INR_retype)) >>
  fs[exprSimDefsTheory.halt_exit_def];

val mapping_selection_intro_tac =
  qx_genl_tac [`imarks`, `ires`, `fin`, `Gi`, `tni`, `it`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `indexQ (storage_trace_horizon fin.storage_trace) ires fin Gi tni it /\
   ~it.vs_halted /\ fin.gas_obs = []` by metis_tac[] >>
  qpat_x_assum `indexQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `indexQ`, NoAsms] >> strip_tac >> gvs[];

val mapping_selection_key_tac =
  `expr_type e2 = kt /\ hashmap_key_type kt` by
    metis_tac[mapping_subscript_key_type] >>
  `bind (eval_expr cx e2) (read_result cx)
     (mid with gas_obs := gas_explicit imarks s.vs_gas_readings) = (INL v,fin)` by
    (`fin with gas_obs := [] = fin` by
       (qpat_assum `fin.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[listTheory.APPEND_NIL] >> metis_tac[]) >>
  `expr_body_pre cenv cx env e2
     (mid with gas_obs := gas_explicit imarks s.vs_gas_readings)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`)
    (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >>
  disch_then (qspecl_then [`cenv`, `env`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `?tv. evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv v` by
    (qpat_x_assum `!v'. INL v = INL v' ==> _` (qspec_then `v` mp_tac) >>
     simp[vyperTypeExprResultTheory.expr_result_typed_def,
          vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
          vyperTypeExprSoundnessTheory.value_runtime_typed_def,
          vyperTypeInvariantsTheory.value_result_typed_def] >>
     `env.type_defs = get_tenv cx` by
       gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
           vyperTypeInvariantsTheory.env_context_consistent_def] >> metis_tac[]) >>
  `post_value_type cenv e2 = kt` by
    (`is_word_type kt \/ is_bytestring_type kt` by
       (qpat_assum `hashmap_key_type kt` mp_tac >>
        qpat_assum `evaluate_type _ kt = SOME _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        Cases_on `kt` >> simp[vyperTypeSystemTheory.hashmap_key_type_def,
          compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def] >>
        rename1 `BaseT bt` >> Cases_on `bt` >>
        simp[vyperTypeSystemTheory.hashmap_key_type_def,
             compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def] >>
        rename1 `BytesT bd` >> Cases_on `bd` >>
        simp[compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def,
             vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
     metis_tac[loweringPostsTheory.post_value_type_word,
               loweringPostsTheory.post_value_type_bytestring]) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
     (qspec_then `storage_trace_horizon fin.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `expr_store_bound cx kt v key it` by metis_tac[] >>
  drule_all mapping_index_key_input >> strip_tac;

val mapping_suffix_tac =
  `!z. p.ptr_operand = Var z ==> not_fresh_at sm z` by
    (qpat_assum `compile_expr _ _ e1 _ = _`
       (mp_then Any mp_tac (cj 1 exprOperandVarTheory.compiler_compile_var)) >>
     simp[contextTheory.vv_operand_def]) >>
  `!l. p.ptr_operand <> Label l` by
    (drule_all compile_mapping_operand_not_label >> simp[contextTheory.vv_operand_def]) >>
  `eval_operand p.ptr_operand it = SOME slot /\ op_taint tni p.ptr_operand = {}` by
    (qpat_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni` mp_tac >>
     qpat_assum `!z. p.ptr_operand = Var z ==> not_fresh_at sm z` mp_tac >>
     qpat_assum `!l. p.ptr_operand <> Label l` mp_tac >>
     qpat_assum `eval_operand p.ptr_operand s = SOME slot` mp_tac >>
     qpat_assum `op_taint tn1 p.ptr_operand = {}` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `p.ptr_operand` >>
     simp[eval_operand_def, ptrDisciplineTheory.op_taint_def,
          bodyPtrDefsTheory.ghost_kept_at_def, loweringPostsTheory.expr_post_def,
          lookup_var_def] >> metis_tac[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
   (!x. key = Var x \/ p.ptr_operand = Var x ==> not_fresh_at sn x)` by
    (conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     rpt strip_tac
     >- (irule exprOperandVarTheory.compile_lower_value_var >>
         qexistsl_tac [`cenv`, `e2`, `key`, `sm`, `expr_type e2`] >> simp[]) >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `allocas_from lo it /\ lo <= it.vs_alloca_next` by
    ((qpat_assum `ghost_inv_at (DF (storage_trace_horizon _)) _ _ _ _ _ _ _ _` mp_tac >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >> (metis_tac[bodyPtrDefsTheory.ghost_inv_at_def]))) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
     stmt_state_rel H ctx func cenv cx fin it /\ ghost_inv_at (DF H) lo d cenv cx fin Gi tni it` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o PURE_REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     simp[]) >>
  qpat_assum `compile_mapping_subscript _ _ _ = _`
    (assume_tac o REWRITE_RULE [contextTheory.vv_operand_def]) >>
  `?u Gu tnu.
    eval_operand outop u = SOME (hashmap_slot slot (encode_hashmap_key kt v)) /\
    op_taint tnu outop = {} /\ op_prov Gu outop = NONE /\
    (!x. outop = Var x ==> not_fresh_at sb x) /\
    (!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x it /\
      FLOOKUP Gu x = FLOOKUP Gi x /\ op_taint tnu (Var x) = op_taint tni (Var x)) /\
    wb_frame cenv fin fin sn it u /\ pure_frame cenv func fin sn it u /\
    ghost_kept_at lo cenv fin sn Gi tni it Gu tnu /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ allocas_from lo u /\ it.vs_alloca_next <= u.vs_alloca_next /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (it,Gi,tni) [] (OK u,Gu,tnu) /\
      stmt_state_rel H ctx func cenv cx fin u /\ ghost_inv_at (DF H) lo d cenv cx fin Gu tnu u)` by
    (qspecl_then [`key`, `storage_trace_horizon fin.storage_trace`]
       ho_match_mp_tac (Q.GENL [`key`, `H0`]
         (Q.INST [`bop` |-> `p.ptr_operand`] mapping_suffix_full_run)) >>
     simp[] >> first_assum ACCEPT_TAC);

val mapping_frames_tac =
  `wb_frame cenv es mid sa s0 s` by
    (PURE_REWRITE_TAC [loweringPostsTheory.wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv mid fin sm s it /\
   (~expr_has_effect e2 ==> pure_frame cenv func mid sm s it)` by
    (qpat_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     POP_ASSUM_LIST (K all_tac) >> simp[loweringPostsTheory.wb_frame_def] >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes /\
   MAP FDOM es.scopes = MAP FDOM fin.scopes /\
   MAP FDOM mid.scopes = MAP FDOM fin.scopes` by
    (qpat_assum `wb_frame cenv mid fin sm s it` mp_tac >>
     qpat_assum `wb_frame cenv es mid sa s0 s` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
    (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
       (qpat_assum `eval_expr cx e1 (es with gas_obs := _) = _` mp_tac >>
        qpat_assum `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        `storage_trace_frame (eval_expr cx e1)` by simp[cj 5 evaluate_storage_trace_frame] >>
        drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `wb_frame cenv es fin sa s0 it /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni` by
    (irule (INST_TYPE [Type.beta |-> ``:256``] mapping_suffix_frames_join) >> simp[] >>
     conj_tac >- (qexistsl_tac [`storage_trace_horizon mid.storage_trace`, `ctx`, `cx`, `func`] >> simp[]) >>
     qexistsl_tac [`G1`, `mid`, `s`, `sm`, `tn1`] >> simp[]) >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by decide_tac >>
  `wb_frame cenv es fin sa s0 u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tnu` by
    (irule (INST_TYPE [Type.beta |-> ``:256``] mapping_suffix_frames_join) >> simp[] >>
     conj_tac >- (qexistsl_tac [`storage_trace_horizon mid.storage_trace`, `ctx`, `cx`, `func`] >> simp[]) >>
     qexistsl_tac [`Gi`, `fin`, `it`, `sn`, `tni`] >> simp[]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `return_buf_frame d cenv sa u` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[] >>
     qpat_assum `wb_frame cenv es fin sa s0 u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[loweringPostsTheory.wb_frame_def]);

val mapping_pure_frame_tac =
  `~expr_has_effect e1 /\ ~expr_has_effect e2 ==>
     pure_frame cenv func es sa s0 u` by
    (strip_tac >>
     `pure_frame cenv func mid sm s u` by
       (irule exprSimPropsTheory.pure_frame_trans >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl_tac [`fin`, `sn`, `it`] >> simp[] >>
        qpat_assum `wb_frame cenv mid fin sm s it` mp_tac >>
        qpat_assum `wb_frame cenv fin fin sn it u` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[loweringPostsTheory.wb_frame_def]) >>
     irule exprSimPropsTheory.pure_frame_trans >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`mid`, `sm`, `s`] >> simp[] >>
     qpat_assum `wb_frame cenv es mid sa s0 s` mp_tac >>
     qpat_assum `wb_frame cenv mid fin sm s it` mp_tac >>
     qpat_assum `wb_frame cenv fin fin sn it u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.wb_frame_def] >> metis_tac[]) >>
  `fin with gas_obs := [] = fin` by
    (qpat_assum `fin.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]);

val mapping_map_package_tac =
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gu`, `fin`,
    `INL (HashMapRef tr (hashmap_slot slot (encode_hashmap_key kt v)) ikt ivt)`,
    `u`, `tnu`] >>
  simp[NoAsms] >>
  conj_tac >- simp[vyperHashMapStorageTheory.select_result_hashmap_nested] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o PURE_REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
  `storage_mapping_region cx tr
    (hashmap_slot slot (encode_hashmap_key kt v)) (HashMapT ikt ivt)` by
    metis_tac[vyperStoragePlaceProvenanceTheory.storage_mapping_region_step] >>
  simp[contextTheory.mk_ptr_def, contextTheory.vv_location_def] >>
  qpat_assum `wb_frame cenv es fin sa s0 u`
    (strip_assume_tac o PURE_REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    first_assum (ACCEPT_TAC o MATCH_MP
      bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  rpt conj_tac >> first_assum ACCEPT_TAC;


Theorem subscript_map_map_full:
  !cx ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_full_ok_mods mods exps cx e2) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx env es /\
    expr_map_pre_mods mods cenv cx env (Subscript ann e1 e2) es /\
    expr_map_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e1 es ==>
    expr_map_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_map_pre cenv cx env e1 es` by metis_tac[expr_map_pre_subscript_base] >>
  `?kt vt. type_place_expr env e1 = SOME (HashMapT kt vt)` by fs[expr_map_pre_def] >>
  `place_map_tables_agree_on_defined cenv env` by
    fs[expr_map_pre_def, expr_sim_inv_def] >>
  `place_type cenv e1 = MapPT kt vt` by
    (drule_all placeTypingPropsTheory.place_type_checked_place_on_defined >>
     simp[exprLoweringTheory.value_type_place_def]) >>
  `?ikt ivt. vt = HashMapT ikt ivt` by
    (qpat_assum `expr_map_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[expr_map_pre_def, cj 22 vyperTypeSystemTheory.well_typed_expr_def] >>
     Cases_on `vt` >>
     gvs[expr_map_pre_def, cj 22 vyperTypeSystemTheory.well_typed_expr_def,
         vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]) >>
  gvs[] >>
  `~copies_subscript_base cenv e1 e2 /\ ~subscript_reads_base cx e1 e2` by
    metis_tac[map_base_no_overlap] >>
  rewrite_tac[expr_map_sim_full_def] >> rpt gen_tac >> strip_tac >>
  mapping_base_tac (metis_tac[subscript_map_base_admissible])
    (`place_type (gas_shadow_env T cenv) (gas_shadow_expr e1) = MapPT kt (HashMapT ikt ivt) /\
      ~copies_subscript_base (gas_shadow_env T cenv) (gas_shadow_expr e1) (gas_shadow_expr e2)` by
       mapping_shadow_type_tac)
    (suspend "mapping_index")
QED

Resume subscript_map_map_full[mapping_index]:
  mapping_index_source_tac
    (`expr_map_pre cenv cx env (Subscript ann e1 e2)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[])
    ``expr_map_res_ok`` >>
  mapping_index_shadow_tac
    (`place_type (gas_shadow_env T cenv) (gas_shadow_expr e1) = MapPT kt (HashMapT ikt ivt) /\
      ~copies_subscript_base (gas_shadow_env T cenv) (gas_shadow_expr e1) (gas_shadow_expr e2)` by
       mapping_shadow_type_tac) >>
  mapping_index_bind_tac (suspend "mapping_selection")
QED

Resume subscript_map_map_full[mapping_selection]:
  mapping_selection_intro_tac >>
  `kt' = kt /\ vt = HashMapT ikt ivt` by
      (qpat_assum `eval_expr cx e1 (_ with gas_obs := _) = _`
         (mp_then Any mp_tac expr_map_pre_eval_result) >>
       disch_then (qspecl_then [`cenv`, `env`] mp_tac) >>
       simp[] >> strip_tac >>
       first_x_assum (qspec_then `HashMapT kt (HashMapT ikt ivt)` mp_tac) >>
       simp[vyperPlaceResultTypingTheory.eval_result_typed_mapping]) >>
  mapping_selection_key_tac >>
  mapping_suffix_tac >> mapping_frames_tac >> mapping_pure_frame_tac >>
  mapping_map_package_tac
QED

Finalise subscript_map_map_full

Theorem subscript_map_full:
  !cx ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es kt vt.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_full_ok_mods mods exps cx e2) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Subscript ann e1 e2) es /\
    place_type cenv e1 = MapPT kt vt /\
    expr_map_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e1 es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_map_pre cenv cx env e1 es` by
    metis_tac[expr_body_pre_map_subscript_base] >>
  `type_place_expr env e1 = SOME (HashMapT kt vt)` by
    (drule_all expr_map_pre_checked_type >> simp[]) >>
  `~copies_subscript_base cenv e1 e2 /\ ~subscript_reads_base cx e1 e2` by
    metis_tac[map_base_no_overlap] >>
  rename1 `place_type cenv e1 = MapPT kt declared_vt` >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  mapping_base_tac
    (irule subscript_result_base_admissible >>
     qexists_tac `expr_vv_res_ok` >> simp[subscript_result_predicates_exceptions] >>
     goal_assum (drule_at Any))
    (`place_type (gas_shadow_env T cenv) (gas_shadow_expr e1) = MapPT kt declared_vt /\
      ~copies_subscript_base (gas_shadow_env T cenv) (gas_shadow_expr e1) (gas_shadow_expr e2)` by
       mapping_shadow_type_tac)
    (suspend "leaf_index")
QED

Resume subscript_map_full[leaf_index]:
  mapping_index_source_tac
    (`expr_body_pre cenv cx env (Subscript ann e1 e2)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[])
    ``expr_vv_res_ok`` >>
  mapping_index_shadow_tac
    (`place_type (gas_shadow_env T cenv) (gas_shadow_expr e1) = MapPT kt declared_vt /\
      ~copies_subscript_base (gas_shadow_env T cenv) (gas_shadow_expr e1) (gas_shadow_expr e2)` by
       mapping_shadow_type_tac) >>
  mapping_index_bind_tac (suspend "leaf_selection")
QED

Resume subscript_map_full[leaf_selection]:
  mapping_selection_intro_tac >>
  `kt' = kt /\ vt = declared_vt` by
      (qpat_assum `eval_expr cx e1 (_ with gas_obs := _) = _`
         (mp_then Any mp_tac expr_map_pre_eval_result) >>
       disch_then (qspecl_then [`cenv`, `env`] mp_tac) >>
       simp[] >> strip_tac >>
       first_x_assum (qspec_then `HashMapT kt declared_vt` mp_tac) >>
       simp[vyperPlaceResultTypingTheory.eval_result_typed_mapping]) >>
  mapping_selection_key_tac >>
  mapping_suffix_tac >> mapping_frames_tac >> mapping_pure_frame_tac >>
  `~well_typed_expr env e1` by
    metis_tac[vyperTypeExprResultTheory.well_typed_expr_not_hashmap_place] >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_sim_inv cenv cx env fin` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  qpat_assum `expr_body_pre cenv cx env (Subscript ann e1 e2) es`
    (assume_tac o CONJUNCT1 o CONJUNCT2 o PURE_REWRITE_RULE [expr_body_pre_def]) >>
  `declared_vt = Type ann /\ ?leaf_tv. evaluate_type (get_tenv cx) ann = SOME leaf_tv` by
    (qpat_assum `well_typed_expr env (Subscript ann e1 e2)` mp_tac >>
     qpat_assum `~well_typed_expr env e1` mp_tac >>
     qpat_assum `env.type_defs = get_tenv cx` mp_tac >>
     qpat_assum `type_place_expr env e1 = SOME (HashMapT kt declared_vt)` mp_tac >>
     qpat_assum `expr_type e2 = kt` mp_tac >>
     qpat_assum `hashmap_key_type kt` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt (DISCH_THEN ASSUME_TAC) >>
     qpat_x_assum `well_typed_expr env (Subscript ann e1 e2)` mp_tac >>
     simp[cj 7 vyperTypeSystemTheory.well_typed_expr_def,
          vyperTypeSystemTheory.subscript_vtype_def,
          vyperTypeSystemTheory.well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
     strip_tac >> simp[]) >>
  qpat_x_assum `declared_vt = Type ann` SUBST_ALL_TAC >>
  qpat_x_assum `vt = Type ann` SUBST_ALL_TAC >>
  qpat_x_assum `kt' = kt` SUBST_ALL_TAC >>
  qabbrev_tac `leaf_slot = hashmap_slot slot (encode_hashmap_key kt v)` >>
  qabbrev_tac `leaf_trace = fin.storage_trace ++ [StorageRoot tr (w2n leaf_slot) leaf_tv]` >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gu`, `fin with storage_trace := leaf_trace`,
    `INL (PlaceR (StoragePlace tr leaf_slot leaf_tv))`, `u`, `tnu`] >>
  simp[NoAsms] >>
  conj_tac >-
    (qpat_assum `evaluate_type (get_tenv cx) ann = SOME leaf_tv`
       (mp_then Any mp_tac vyperHashMapStorageTheory.select_result_hashmap_leaf) >>
     disch_then (fn th => simp[th, Abbr `leaf_trace`, Abbr `leaf_slot`,
                                vyperStateTheory.evaluation_state_fupdcanon])) >>
  qx_gen_tac `H` >> simp[Abbr `leaf_trace`] >> strip_tac >>
  `valid_horizon cx st0 H fin.storage_trace` by
    (qpat_assum `valid_horizon cx st0 H (fin.storage_trace ++ _)`
       (mp_then Any ACCEPT_TAC gasOutcomeFullTheory.valid_horizon_append)) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o PURE_REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
  `MEM (tr,leaf_slot,leaf_tv) (FST H) /\ regions_consistent (FST H)` by
    (qpat_assum `valid_horizon cx st0 H (fin.storage_trace ++ _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperStorageFootprintTheory.valid_horizon_def,
          vyperStorageFootprintTheory.storage_observations_ok_def,
          vyperStorageFootprintTheory.storage_trace_regions_def,
          listTheory.MAP_APPEND, listTheory.FLAT_APPEND,
          listTheory.EVERY_APPEND, wordsTheory.n2w_w2n] >>
     metis_tac[]) >>
  `(fin with <|gas_obs := []; storage_trace :=
    fin.storage_trace ++ [StorageRoot tr (w2n leaf_slot) leaf_tv]|>) =
    fin with storage_trace := fin.storage_trace ++ [StorageRoot tr (w2n leaf_slot) leaf_tv]` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `slot_loc tr <> LocCode /\ slot_loc tr <> LocMemory` by
    (Cases_on `tr` >> simp[loweringPostsTheory.slot_loc_def]) >>
  `(case vv_location (LocatedValue tp p) of NONE => LocMemory | SOME loc => loc) =
     slot_loc tr` by simp[contextTheory.vv_location_def] >>
  `(mk_ptr outop (slot_loc tr)).ptr_location = slot_loc tr /\
   vv_location (LocatedValue ann (mk_ptr outop (slot_loc tr))) = SOME (slot_loc tr)` by
    simp[contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
     first_assum (ACCEPT_TAC o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  simp[vyperASTTheory.expr_type_def] >>
  match_mp_tac (Q.INST [`D` |-> `DF H`] subscript_mapping_value_place_post) >>
  qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx` (qspec_then `H` assume_tac) >>
  simp[exprLoweringPropsTheory.stmt_state_rel_storage_trace,
       bodyPtrDefsTheory.ghost_inv_at_storage_trace] >>
  conj_tac >-
    (dep_rewrite.DEP_ONCE_REWRITE_TAC [Q.INST [`st` |-> `fin`]
       vyperStorageFootprintTheory.storage_well_formed_on_backends] >> simp[]) >>
  let
    val frame_defs = [loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def,
                      loweringPostsTheory.popped_kept_def]
  in
    SIMP_TAC (srw_ss()) frame_defs >>
    qpat_assum `wb_frame cenv es fin sa s0 u`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) frame_defs)
  end
QED

Finalise subscript_map_full
