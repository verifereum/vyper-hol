(* Compose word-operand replay with the prepared transaction-calldata call. *)
Theory s1PrefixRawCallCalldata
Ancestors
  s1PrefixRawCallCalldataWordsReplay s1PrefixRawCallCalldataTail
  bodyFullRawCallCalldata s1PrefixCompose s1PrefixDefs s1PrefixProps
  vyperStorageTrace vyperStorageFootprint vyperState gasShadow
  bodyFullWordArgs exprSimPrecompiles fragGasOriginPtr finite_map
  bodyFullRawCall loweringStateRelDefs exprLoweringProps
Libs
  monadsyntax

Theorem raw_call_calldata_vv_prefix:
  body_exprs_full_ok cx args /\ body_exprs_prefix_ok cx args /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann (RawCallCalldataTarget flags) args dflt) es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Call ann (RawCallCalldataTarget flags) args dflt) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_call_calldata_word_schedule >>
  disch_then (qx_choosel_then
    [`a`,`kws`,`addr`,`xs`,`vo`,`go`,`gas`,`ov`,`op`,`dp`,`len`,`result`,
     `s2`,`s3`,`s4`,`s5`,`h2`,`h3`] (map_every assume_tac o CONJUNCTS)) >>
  map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
    [`args = a::kws`,`dflt = NONE`,`ann = raw_call_return_type flags`] >>
  rewrite_tac[raw_call_calldata_eval] >>
  irule raw_call_calldata_words_prefix_replay_by >>
  qpat_assum `lower_word_args cenv expr_type (a::kws) sa = _` (irule_at Any) >>
  qpat_assum `lower_word_args _ expr_type (MAP gas_shadow_expr _) _ = _` (irule_at Any) >>
  qpat_assum `body_const_cells_agree [(NONE,tops)] cx env es` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
  qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (MATCH_ACCEPT_TAC gas_shadow_expr_type)
  >- (gen_tac >> BETA_TAC >> rewrite_tac[ignore_bind_def] >>
      rpt (irule requests_outcomes_frame_bind_all >>
           simp[request_frame_primitives, request_frame_raw_call] >> TRY gen_tac))
  >- (gen_tac >> BETA_TAC >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
      rpt (irule storage_trace_frame_bind_all >>
           simp[storage_trace_frame_lifts, storage_trace_frame_raw_call] >> TRY gen_tac)) >>
  qx_genl_tac [`marksK`,`vs`,`esK`,`tk`,`GK`,`tnK`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon esK.storage_trace) esK.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST [`dframe` |-> `d`] raw_call_calldata_word_success_to_call) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    (gen_tac >> disch_tac) >>
    FIRST
      [qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
         (drule_then (ACCEPT_TAC o CONJUNCT1)),
       qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
         (drule_then (map_every assume_tac o CONJUNCTS)) >>
       rpt conj_tac >> first_assum ACCEPT_TAC])) >>
  disch_then (qx_choosel_then [`n`,`tg`,`GG`,`tnG`,`t7`,`G7`,`tn7`,
    `av`,`kvs`,`target`,`amount`,`gw`,`ib`,`ob`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `vs = av::kvs` SUBST_ALL_TAC >>
  `!msg. vyperState$assert T msg = vyperState$return ()` by
    simp[FUN_EQ_THM, assert_def, return_def] >>
  simp[type_check_def, lift_option_type_def, ignore_bind_def, bind_return] >>
  irule gas_prefix_full_generated_prefix >>
  simp[storage_trace_frame_raw_call] >>
  qexistsl [`G7`,`n`,`t7`,`tn7`] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (tg,GG,tnG) _ _`
        (drule_then assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (tk,GK,tnK) _ _`
        (drule_then (qspecl_then [`tg`,`GG`,`tnG`,`[]`,`OK t7`,`G7`,`tn7`] mp_tac o
                     MATCH_MP gas_origin_ptr_path_append)) >>
      simp[]) >>
  `cenv.ce_is_ctor ==> !src name tv v off.
     (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
     FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
     regions_disjoint off (type_memory_size tv) ob
       (if flags.rcf_max_outsize = 0 then 0
        else ((flags.rcf_max_outsize+31) DIV 32)*32+32)` by
    (mp_tac (Q.INST [`sa` |-> `s3`, `sb` |-> `s4`, `cap` |-> `flags.rcf_max_outsize`,
        `es` |-> `esK`, `t` |-> `t7`, `sz` |-> `if flags.rcf_max_outsize = 0 then 0 else ((flags.rcf_max_outsize+31) DIV 32)*32+32`,
        `H` |-> `storage_trace_horizon esK.storage_trace`]
       (INST_TYPE [alpha |-> ``:256``] raw_call_outbuf_immutable_separation)) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ esK t7 /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     impl_tac >- simp[] >>
     disch_then ACCEPT_TAC) >>
  irule raw_call_calldata_prepared_tail_prefix >>
  qpat_assum `compile_raw_call_finish addr dp len gas _ _ _ _ ov op s5 = _`
    (irule_at Any) >>
  qpat_assum `FLOOKUP t7.vs_allocas s3.cs_next_id = _` (irule_at Any) >>
  qpat_assum `fn_has_code sa sb func` (irule_at Any) >>
  qpat_assum `expr_sim_inv cenv cx env esK` (irule_at Any) >>
  qpat_assum `eval_operand dp t7 = _` (irule_at Any) >>
  qpat_assum `eval_operand gas t7 = SOME gw` (irule_at Any) >>
  qexists `d` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC
  >- (simp_tac bool_ss [DISJ_IMP_THM] >> conj_tac >> first_assum ACCEPT_TAC) >>
  TRY (first_assum (ACCEPT_TAC o ONCE_REWRITE_RULE [arithmeticTheory.MULT_COMM])) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ esK t7 /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  conj_tac >> first_assum ACCEPT_TAC
QED
