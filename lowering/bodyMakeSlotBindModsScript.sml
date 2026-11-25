(* Bind the actual linked head value to the MakeArray slot landing. *)
Theory bodyMakeSlotBindMods
Ancestors gasShadowCompile[qualified,ignore_grammar]
  bodyMakeElementsContractMods bodyStructFieldsSourceMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  exprSimMemorySource exprSimHypsDefs exprSimDefs
  gasShadowCompileStmtHelpers
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  bodyPtrDefs loweringPosts loweringStateRelDefs
  gasOutcomeFullMods gasOutcomeFull gasSummary gasContext gasShadow gasShadowState
  exprLowering compileEnv context venomState venomInst venomWf
  typeLayoutProps valueEncoding valueEncodingDefs exprSimProps exprSimMemDefs
  vyperStorageFootprint vyperInterpreter vyperState vyperTypeSystem vyperAST
  fragExec fragGasMode fragGasOriginPtr stmtSimProps haltExitProj
  exprSimUnwrap exprSimAccounts externalEntryShape[qualified]
  freshWrites[qualified] bodyFullHashKeccakFixed[qualified] gasStorage vyperStorageTrace
  finite_map list pair option words arithmetic
Libs monadsyntax

val _ = Parse.hide "base";

Theorem make_slot_head_code[local]:
  make_elements_once_mods ce e q off dty sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?vv sm. compile_expr ce (expr_type e) e sa = (vv,sm) /\
          fn_has_code sa sm func
Proof
  simp[make_elements_once_mods_def, comp_bind_def] >>
  Cases_on `compile_expr ce (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sm)` >>
  Cases_on `emit_op ADD [Var q; Lit (n2w off)] sm` >>
  rename1 `emit_op _ _ _ = (dst,a)` >>
  Cases_on `unwrap_value ce vv a` >>
  rename1 `unwrap_value _ _ _ = (op,b)` >> simp[] >> strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_expr_extends] >>
  `cs_extends sm a` by metis_tac[emit_op_extends_next_var] >>
  `cs_extends a b` by metis_tac[unwrap_value_extends] >>
  `cs_extends b sb` by
    (qpat_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     simp[GSYM AND_IMP_INTRO] >>
     metis_tac[externalEntryShapeTheory.compile_store_memory_labels, SND]) >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_split]
QED

(* Keep the single source-and-machine witness across every valid horizon. *)
Theorem make_slot_keep_path[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0 source (es,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0 source (es,s,G,tn)
    (\H res ee G' tn' t. Q H res ee G' tn' t /\ ee.gas_obs = [] /\
      ?marks. (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
                        (res,ee with gas_obs := tail)) /\
              !K. valid_horizon cx st0 K ee.storage_trace ==>
                gas_origin_ptr_path (DF K,lo,explicit,ctx,fn,PG) (s,G,tn) marks (OK t,G',tn')) R
Proof
  rewrite_tac[gas_outcome_full_mods_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      asm_simp_tac bool_ss [] >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
        (drule_then strip_assume_tac) >> gvs[] >>
      disj1_tac >> qexists_tac `marks` >> simp[] >>
      rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem make_slot_exit[local]:
  expr_exit (res : eval_result + exception) r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==>
  ?exc. res = INR exc /\ expr_exit (INR exc : value + exception) r /\
        halt_exit H cx ee (INR exc : value + exception) r /\
        (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)
Proof
  Cases_on `res` >> simp[expr_exit_def] >>
  ONCE_REWRITE_TAC[INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
                   INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]
QED

Theorem make_slot_from_landings_mods:
  make_slot_landing_mods is_word_type /\
  make_slot_landing_mods (\ty. ~is_word_type ty) ==>
  make_slot_contract_mods
Proof
  strip_tac >> rewrite_tac[make_slot_contract_mods_def] >>
  rpt gen_tac >> disch_tac >>
  qhdtm_assum `make_slot_entry_mods`
    (strip_assume_tac o REWRITE_RULE [make_slot_entry_mods_def]) >>
  qhdtm_x_assum `make_elements_entry_mods`
    (strip_assume_tac o REWRITE_RULE [make_elements_entry_mods_def]) >>
  qhdtm_x_assum `make_elements_static_mods`
    (strip_assume_tac o REWRITE_RULE [make_elements_static_mods_def]) >>
  qhdtm_x_assum `make_elements_code_mods`
    (strip_assume_tac o REWRITE_RULE [make_elements_code_mods_def]) >>
  `expr_body_pre_mods mods cenv cx env h es` by
    (qpat_assum `!e ee. MEM e (h::_) /\ _ ==> _`
       (qspecl_then [`h`,`es`] mp_tac) >> simp[]) >>
  qpat_assum `body_exprs_full_ok_mods _ _ _ (h::_)` mp_tac >>
  simp_tac bool_ss [Once body_exprs_full_ok_mods_def] >> strip_tac >>
  qhdtm_x_assum `body_expr_full_ok_mods`
    (strip_assume_tac o REWRITE_RULE [Once body_expr_full_ok_mods_def]) >>
  qpat_assum `!DF lo d PG src tops ctx sh f sf ce env ty es. _ ==> _ /\ _`
    (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type h) h es` by
    (qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_vv_sim_full_mods
         (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty h es` irule >>
     asm_simp_tac bool_ss [] >>
     conj_tac >- (qexistsl_tac [`src`,`tops`] >> first_assum ACCEPT_TAC) >>
     qexists_tac `env` >>
     conj_tac >- qpat_assum `body_const_cells_agree_mods mods cx env es` ACCEPT_TAC >>
     qpat_assum `expr_body_pre_mods mods cenv cx env h es` ACCEPT_TAC) >>
  `?vv sm. compile_expr cenv (expr_type h) h sa = (vv,sm) /\
           fn_has_code sa sm func` by
    (irule make_slot_head_code >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`dty`,`off`,`q`,`sb`] >> asm_simp_tac bool_ss []) >>
  `?svv shm. compile_expr (gas_shadow_env T cenv) (expr_type (gas_shadow_expr h))
       (gas_shadow_expr h) sha = (svv,shm) /\ fn_has_code sha shm shadow_func` by
    (irule make_slot_head_code >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`dty`,`off`,`q`,`shb`] >> asm_simp_tac bool_ss []) >>
  `svv = vv /\ gas_shadow_state sm shm` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type h) h)
        (compile_expr (gas_shadow_env T cenv) (expr_type h) (gas_shadow_expr h))` by
       irule (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env |> SPEC_ALL |>
              Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`sha`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     gvs[gas_shadow_expr_type]) >>
  `compile_expr (gas_shadow_env T cenv) (expr_type h) (gas_shadow_expr h) sha =
      (vv,shm)` by
    metis_tac[gas_shadow_expr_type] >>
  qhdtm_assum `make_elements_cut_mods`
    (strip_assume_tac o REWRITE_RULE [make_elements_cut_mods_def]) >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (simp[make_elements_run_mods_def, gas_outcome_full_mods_def] >>
      qexists_tac `[]` >> disj1_tac >> conj_tac
      >- (irule gas_bad_storage_at_initial >>
          simp[storage_trace_frame_bind_all, storage_trace_frame_read_result,
               evaluate_storage_trace_frame]) >>
      qexistsl_tac [`( [], [] )`,`func`,`PG`,`G`,`tn`,`s`] >>
      simp[gas_origin_ptr_focus_nil]) >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sm`,`sha`,`shm`,`vv`,`s`,`G`,`tn`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  (impl_tac >-
    (asm_simp_tac bool_ss [gas_shadow_expr_type] >>
     conj_tac >-
       (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
        qexists_tac `csbase` >> asm_simp_tac bool_ss [] >>
        qpat_assum `!x n. cenv.ce_return_buf = SOME _ ==> _` irule >>
        HINT_EXISTS_TAC >> first_assum ACCEPT_TAC) >>
     conj_tac >-
       (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
        qexists_tac `csbase` >> asm_simp_tac bool_ss [] >>
        qpat_assum `!x n. cenv.ce_return_pc = SOME _ ==> _` irule >>
        HINT_EXISTS_TAC >> first_assum ACCEPT_TAC) >>
     conj_tac >-
       (irule struct_fields_head_admissible_mods >> conj_tac
        >- (qexists_tac `xs` >> fs[make_elements_admissible_mods_def]) >>
        qexistsl_tac [`cenv`,`env`,`mods`] >> first_assum ACCEPT_TAC) >>
     conj_tac >-
       (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
          fs[storage_trace_domain_def] >>
        qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
          (drule_then strip_assume_tac) >>
        drule_then ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by asm_simp_tac bool_ss [] >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC)) >>
  rewrite_tac[GSYM make_slot_child_post_mods_def] >>
  disch_tac >> drule_then (assume_tac o BETA_RULE) make_slot_keep_path >>
  rewrite_tac[make_elements_run_mods_def] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      goal_assum (drule_at Any) >> BETA_TAC >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result _ v)`]
  >- simp[storage_trace_frame_read_result] >>
  qexists_tac `\H res ee G' tn' t.
    make_slot_child_post_mods DF lo d ctx func cenv cx h es sa sm s G tn vv H res ee G' tn' t /\
    ee.gas_obs = [] /\ ?m.
    (!tail. eval_expr cx h (es with gas_obs := gas_explicit m s.vs_gas_readings ++ tail) =
            (res,ee with gas_obs := tail)) /\
    !K. valid_horizon cx st0 K ee.storage_trace ==>
        gas_origin_ptr_path (DF K,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (s,G,tn) m (OK t,G',tn')` >> BETA_TAC >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ (\H res ee G' tn' t. _ /\ _) _`
        (irule_at Any) >> BETA_TAC >> simp[make_slot_exit]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`g1`,`tt1`,`u`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  `?raw. res = INL raw` by
    (qhdtm_assum `make_slot_child_post_mods`
       (strip_assume_tac o REWRITE_RULE [make_slot_child_post_mods_def]) >>
     qexists_tac `tv` >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `res = INL raw` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `raw` >> asm_simp_tac bool_ss [] >>
  rewrite_tac[GSYM make_elements_run_mods_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s,G,tn) m (OK u,g1,tt1) /\
        make_slot_child_post_mods DF lo d ctx func cenv cx h es sa sm s G tn vv
          H (INL raw) mid g1 tt1 u` by
    (rpt strip_tac >> first_assum (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> make_slot_child_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  Cases_on `is_word_type dty` >>
  FIRST [qpat_assum `is_word_type dty` (K
           (qpat_assum `make_slot_landing_mods is_word_type`
              (irule o REWRITE_RULE [make_slot_landing_mods_def]))),
         qpat_assum `~is_word_type dty` (K
           (qpat_assum `make_slot_landing_mods (\ty. ~is_word_type ty)`
              (irule o REWRITE_RULE [make_slot_landing_mods_def])))] >>
  asm_simp_tac bool_ss [] >>
  qexistsl_tac [`G`,`dty`,`m`,`sha`,`shadow_func`,`shb`,`shm`,`sm`,`src`,`tn`,`tops`,`vv`] >>
  asm_simp_tac bool_ss [] >>
  metis_tac[gas_shadow_expr_type]
QED
