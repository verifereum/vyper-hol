(* Connect the selected runtime entry to the body request-prefix simulation. *)
Theory s1PrefixBodyStartEvidence
Ancestors
  s1PrefixSelectedFrag loweringRuntimeCorrect externalCallSelected
  s1PrefixDefs fragGasOriginPtr bodyPtrDefs loweringPosts bodySimFull vyperStorageFootprint

Theorem runtime_prefix_body_start_evidence:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
  supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  (ctx_has_dalloca unit.cu_context ==>
   !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
               dalloca_fmp_headroom inst s) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  runtime_body_endpoint tops rpolicy unit am tx vs es0 mut nr args dflts ret
    (subst_consts_stmts (module_consts_env tops []) fbody) ==>
  ?cx entry func marks G0 tn0 s0.
    cx = initial_evaluation_context am.sources am.layouts tx NONE /\
    entry = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> /\
    unit.cu_context.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    storage_trace_domain cx (initial_state am []) es0.storage_trace /\
    (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
    (!tail. external_entry_bound tops am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings ++ tail) mut args dflts
      (es0 with gas_obs := tail)) /\
    gas_origin_ptr_focus
      (cx_dead (storage_trace_horizon es0.storage_trace) cx,0,
       gas_explicit_sites unit.cu_context shadow_unit.cu_context,unit.cu_context,func,[])
      (entry,FEMPTY,entry_taint) marks (func,[],G0,tn0,s0) /\
    ((?exc es_abort.
        lock_if_nr cx nr (is_view_mut mut) es0 = (INR exc,es_abort) /\
        (!tail. call_external_trace (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings ++ tail) am tx =
          (INR exc,am,es_abort.requests,es_abort.storage_trace))) \/
     (?es_lock. lock_if_nr cx nr (is_view_mut mut) es0 = (INL (),es_lock) /\
        (storage_trace_domain cx (initial_state am []) es_lock.storage_trace ==>
         ?compiled_body shadow_func cenv RetQ sl sb shadow_sl shadow_sb t G tn cenv'.
           compiled_body = subst_consts_stmts (module_consts_env tops []) fbody /\
           (!gas. eval_stmts cx compiled_body (es_lock with gas_obs := gas) =
                  eval_stmts cx fbody (es_lock with gas_obs := gas)) /\
           t.vs_gas_readings = DROP (LENGTH marks) vs.vs_gas_readings /\
           (!H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
             gas_origin_ptr_path
               (cx_dead H cx,0,gas_explicit_sites unit.cu_context shadow_unit.cu_context,
                unit.cu_context,func,[]) (entry,FEMPTY,entry_taint) marks (OK t,G,tn)) /\
           frame_ret_ok_full ((\H. cx_dead H cx),0,NONE,unit.cu_context,
             shadow_unit.cu_context,[],func,shadow_func) cx RetQ cenv ret /\
           stmt_frag_prefix ((\H. cx_dead H cx),0,NONE,unit.cu_context,
              shadow_unit.cu_context,[],func,shadow_func) cx NoLoop RetQ cenv
             (stmts_env cenv NoLoop ret compiled_body)
             (stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt compiled_body))
             (eval_stmts cx compiled_body) es_lock /\
           stmt_frag_full_pre ((\H. cx_dead H cx),0,NONE,unit.cu_context,
              shadow_unit.cu_context,[],func,shadow_func) cx NoLoop RetQ cenv
             (stmts_env cenv NoLoop ret compiled_body)
             (stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt compiled_body))
             (eval_stmts cx compiled_body) es_lock
             (initial_state am [],sl,sb,shadow_sl,shadow_sb,t,G,tn,cenv'))))
Proof
  strip_tac >>
  drule_all loweringRuntimeCorrectTheory.runtime_body_endpoint_prepare >>
  disch_then (qx_choosel_then [`compiled_body`,`cx`,`entry`,`selected_shadow`,
    `explicit`,`marks0`,`prefix`,`func`,`shadow_func`,`cenv`,`sa`,`st'`,`s0`,`G0`,`tn0`]
    strip_assume_tac) >>
  `selected_shadow = shadow_unit` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `selected_shadow = shadow_unit` SUBST_ALL_TAC >>
  qpat_x_assum `prefix = _` SUBST_ALL_TAC >>
  qpat_x_assum `explicit = _` SUBST_ALL_TAC >>
  `valid_horizon cx (initial_state am []) (storage_trace_horizon es0.storage_trace)
      es0.storage_trace` by fs[storage_trace_domain_def] >>
  qexistsl_tac [`cx`,`entry`,`func`,`marks0`,`G0`,`tn0`,`s0`] >>
  map_every (fn p => qpat_x_assum p
    (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]))
    [`cx = _`,`entry = _`] >>
  asm_simp_tac std_ss [markerTheory.Abbrev_def] >>
  conj_tac
  >- (irule (cj 1 gas_origin_ptr_focus_rules) >> asm_simp_tac std_ss []) >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) es0` >>
  rename1 `lock_if_nr _ _ _ _ = (lr,es_lock)` >>
  Cases_on `lr`
  >- (rename1 `lock_if_nr _ _ _ _ = (INL a,es_lock)` >> Cases_on `a` >>
      disj2_tac >> qexists_tac `es_lock` >>
      conj_tac >- REFL_TAC >> strip_tac >>
      qpat_x_assum `!s. _ /\ storage_trace_domain cx _ s.storage_trace ==> _`
        (qspec_then `es_lock` mp_tac) >>
      impl_tac >- asm_simp_tac std_ss [] >>
      disch_then (qx_choosel_then [`bindings`,`env_t`,`env'`,`sl`,`sb`,`shadow_sl`,
        `shadow_sb`,`s_b`,`G_b`,`tn_b`,`cenv'`,`RetQ`] strip_assume_tac) >>
      qpat_x_assum `compiled_body = _` SUBST_ALL_TAC >>
      qpat_x_assum `RetQ = _`
        (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
      qexistsl_tac [`shadow_func`,`cenv`,`RetQ`,`sl`,`sb`,`shadow_sl`,
        `shadow_sb`,`s_b`,`G_b`,`tn_b`,`cenv'`] >>
      rpt conj_tac >> asm_simp_tac std_ss []
      >- (irule runtime_selected_body_frag_prefix >>
          asm_simp_tac std_ss [] >>
          qexistsl_tac [`am`,`args`,`bindings`,`dflts`,`env_t`,`env'`,`fbody`,
            `mut`,`nr`,`tops`,`tx`] >> asm_rewrite_tac[]) >>
      simp[stmt_frag_full_pre_def, dead_lo_ok_def, ret_pc_ok_def, return_buf_sep_def] >>
      rpt strip_tac >> asm_simp_tac std_ss [] >>
      qpat_assum `!fn inst s. frag_reachable _ _ s_b fn inst s ==> _`
        (fn nowrap => first_assum (ACCEPT_TAC o MATCH_MP nowrap))) >>
  rename1 `lock_if_nr _ _ _ _ = (INR exc,es_lock)` >>
  disj1_tac >> qexistsl_tac [`exc`,`es_lock`] >>
  asm_simp_tac std_ss [] >>
  qunabbrev_tac `cx` >>
  drule_all_then ACCEPT_TAC call_external_selected_lock_failure
QED
