(* Readiness-parametric composition over counted pointer outcomes. *)
Theory logStmtComposePtr
Ancestors
  logReadyRunPtr logArgsRunPtr logSuccessSuffixPtr logComposeFacts stmtSimLogCompose
  bodyPtrDefs stmtFragPtr logEmitPtr ptrSafetyTransport stmtSimLogEmit
  stmtSimLogArgs stmtSimLogSource stmtSimLogArgsGrowth stmtSimProps
  exprSimDefs exprSimProps exprSimHypsDefs loweringPosts compileEnv loweringStateRelDefs
  stmtLowering gasSummaryComposePtr gasExemptCert gasOutcome gasContext
  fragGasPathPtr fragGasPath gasSummary gasSummaryCompose
  valueTypingMemoryProps vyperInterpreter vyperState venomState
  exprLoweringProps emitHelperProps list rich_list words
  fragExec fragGasMode stmtSimLogSuffixActual exprSimWordArgs
  gasStorage vyperStorageTrace vyperStorageFootprint
  stmtSimLogTopics whitelistLogWiden valueCopyBytes bodyPtrIfExpMemoryTransport
  typedCopyCompatibility
Libs
  logWidenTacticsLib

Theorem log_args_post_scalars:
  log_args_post H ctx func ce cx es sa sm s0 ee xs vs t /\
  EVERY supported_scalar_type (MAP SND xs) /\
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv v) (MAP SND xs) vs ==>
  LIST_REL (\arg v. log_arg_rel ce cx sa sm ee t arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v) xs vs
Proof
  simp[log_args_post_def, LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >>
  rpt strip_tac >> simp[] >> metis_tac[value_has_type_memory_wf]
QED

Theorem compile_log_ready_stmt_frag_ptr_widen:
  log_args_ready_ptr d ctx PG func cenv cx Inv args /\ Inv es /\
  (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
  expr_sim_inv cenv cx env es /\ well_typed_exprs env args /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id = SOME (h,tys,flags) /\
  LIST_REL event_arg_compatible tys (MAP expr_type args) /\ LENGTH flags = LENGTH tys /\
  LENGTH (FILTER I flags) <= 3 /\ EVERY supported_scalar_type tys /\
  ~exprs_can_mutate cenv args /\
  EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
             is_bytestring_type (expr_type e)) args /\
  SUM (MAP (type_memory_bytes cenv) (log_non_indexed_types flags tys)) < dimword(:256) /\
  abi_size_bound cenv.ce_struct_fields (TupleT (log_non_indexed_types flags tys)) < dimword(:256) ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Log id args)) (eval_stmt cx (Log id args)) es
Proof
  strip_tac >>
  `EVERY supported_scalar_type (MAP expr_type args)` by
    (gvs[EVERY_EL, LIST_REL_EL_EQN] >> metis_tac[scalar_event_arg_compatible]) >>
  `LENGTH flags = LENGTH args` by
    (imp_res_tac LIST_REL_LENGTH >> gvs[]) >>
  simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `?H. valid_horizon cx st0 H es.storage_trace`)
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >>
      fs[storage_trace_domain_def, evaluate_storage_trace_frame]) >>
  qpat_x_assum `?H. _` (qx_choose_then `H0` assume_tac) >>
  gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def] >> pairarg_tac >> gvs[] >>
  `LIST_REL (\fty e. is_bytestring_type fty <=>
      is_bytestring_type (lowered_value_type cenv e)) tys args` by
    logWidenTacticsLib.with_cases logWidenTacticsLib.physical_tags >>
  `?ys xs sm ops st. compile_log_eval_all cenv args sa = (ys,sm) /\
    MAP SND ys = MAP (lowered_value_type cenv) args /\
    xs = ZIP (MAP FST ys,tys) /\ log_eval_view cenv args sa xs sm /\
    compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
    MAP SND xs = tys /\ LENGTH flags = LENGTH xs /\
    inst_extends sm cs' /\ same_blocks sm cs' /\ sm.cs_next_var <= cs'.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sm cs') /\ cs_extends sa sm /\ cs_extends sm cs' /\
    fn_has_code sa sm func /\ fn_has_code sm cs' func` by
    (rename1 `compile_stmt cenv lctx ty (Log id args) sa = ((),sb)` >>
     map_every (fn q => qpat_assum q mp_tac)
       [`cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags)`,
        `LENGTH flags = LENGTH tys`, `LENGTH args = LENGTH tys`,
        `EVERY supported_scalar_type tys`,
        `~exprs_can_mutate cenv args`,
        `LIST_REL (\fty e. is_bytestring_type fty <=>
          is_bytestring_type (lowered_value_type cenv e)) tys args`,
        `compile_stmt cenv lctx ty (Log id args) sa = ((),sb)`,
        `fn_has_code sa sb func`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `LENGTH flags = LENGTH args` by decide_tac >>
     logWidenTacticsLib.declared_evaluation >>
     logWidenTacticsLib.declared_pairs >>
     logWidenTacticsLib.declared_view >>
     logWidenTacticsLib.declared_topics >>
     logWidenTacticsLib.declared_frames >>
     logWidenTacticsLib.declared_structure_finish) >>
  pop_assum strip_assume_tac >>
  qabbrev_tac `axs = ZIP (MAP FST ys,MAP expr_type args)` >>
  `gas_admissible (eval_exprs cx args)
    (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es` by
    metis_tac[log_arguments_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  qspecl_then [`args`,`d`,`ctx`,`PG`,`func`,`cenv`,`cx`,`st0`,`Inv`,`es`,`sa`,`axs`,`sm`,
    `s0`,`G0`,`tn0`,`env`,`env`,`es`,`ys`] mp_tac compile_log_eval_all_gas_ptr >>
  impl_tac >- simp[Abbr `axs`] >>
  rewrite_tac[stmtSimLogSourceTheory.log_eval_bind] >>
  `!vs. storage_trace_frame
     (bind (lift_option (encode_source_event (get_tenv cx) cx.sources
                           cx.txn.target id vs) "Log encode event")
       (\ev. ignore_bind (check_not_static cx) (push_log ev)))` by
    (gen_tac >> irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_lifts, storage_trace_frame_checks,
          storage_trace_frame_ignore_bind, storage_trace_frame_check_not_static,
          storage_trace_frame_bind_all, storage_trace_frame_state_updates]) >>
  `storage_trace_frame (eval_exprs cx args)` by
    simp[evaluate_storage_trace_frame] >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >> simp[])
  >- (qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_def]) >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (qexists_tac `marks` >> disj1_tac >>
          irule gas_bad_storage_at_bind_left >> simp[] >>
          simp[gas_bad_storage_at_def]) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _`
        (drule_then strip_assume_tac o SIMP_RULE bool_ss [])
      >- suspend "args_value" >> suspend "args_exit") >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  qexistsl_tac [`err`,`ee`,`leaf`,`fin`] >>
  rewrite_tac[ignore_bind_bind_return] >>
  irule gas_exempt_cert_error_values >> first_assum ACCEPT_TAC
QED

Resume compile_log_ready_stmt_frag_ptr_widen[args_exit]:
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[expr_exit_def]) >> gvs[] >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR ex`,`es_end`,`G`,`tn`,`r`] >> conj_tac
  >- simp[gas_source_bind_exception] >>
  rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  simp[] >> rpt strip_tac >> simp[stmt_exit_ptr_def] >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_log_ready_stmt_frag_ptr_widen[args_value]:
  markerLib.RESUME_TAC >> gvs[Excl "enc_def"] >>
  qabbrev_tac `Hc = storage_trace_horizon es_end.storage_trace` >>
  suspend "success"
QED

Resume compile_log_ready_stmt_frag_ptr_widen[success]:
  markerLib.RESUME_TAC >>
  `log_args_post Hc ctx func cenv cx es sa sm s0
     (es_end with gas_obs := []) axs vs t /\
   ghost_inv Hc d cenv cx (es_end with gas_obs := []) G tn t` by
    (qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _`
       (qspec_then `Hc` mp_tac) >> simp[Excl "enc_def"]) >>
  `~t.vs_halted` by metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted] >>
  drule_all log_source_event_encoded_widen >> strip_tac >>
  qabbrev_tac `ds = ZIP (MAP FST ys,tys)` >>
  `LENGTH ys = LENGTH args` by
    (mp_tac (Q.SPECL [`cenv`,`args`,`sa`] compile_log_eval_all_length) >> simp[]) >>
  `MAP SND ds = tys /\ LENGTH ds = LENGTH args` by simp[Abbr `ds`, MAP_ZIP] >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
    ?aty tv. event_arg_compatible (SND arg) aty /\ supported_scalar_type aty /\
      log_arg_rel cenv cx sa sm (es_end with gas_obs := []) t (FST arg,aty) v /\
      evaluate_type (get_tenv cx) aty = SOME tv /\ value_has_type tv v /\
      ptr_val_ok cx aty v (FST arg) G tn t /\
      (is_bytestring_type aty <=> is_bytestring_type (SND arg)) /\
      encode_event_topic aty v = encode_event_topic (SND arg) v) ds vs` by
    (qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _` kall_tac >>
     logWidenTacticsLib.source_witness scalar_event_arg_compatible) >>
  `LIST_REL (\arg v. log_arg_rel cenv cx sa sm (es_end with gas_obs := []) t arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v)
    (SND (split_log_ops ds flags)) (log_non_indexed_values flags vs)` by
    (`LENGTH flags = LENGTH ds` by metis_tac[LENGTH_MAP] >>
     qpat_assum `LENGTH flags = LENGTH ds` mp_tac >>
     qpat_assum `LIST_REL (\arg v. supported_scalar_type (SND arg) /\ _) ds vs` mp_tac >>
     qpat_assum `SUM (MAP (type_memory_bytes cenv) (log_non_indexed_types flags tys)) <
       dimword (:256)` mp_tac >>
     qpat_assum `MAP SND ds = tys` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     logWidenTacticsLib.with_cases logWidenTacticsLib.selected_data) >>
  `LIST_REL (\arg v. ptr_val_ok cx (SND arg) v (FST arg) G tn t)
    (SND (split_log_ops ds flags)) (log_non_indexed_values flags vs)` by
    (`LENGTH flags = LENGTH ds` by metis_tac[LENGTH_MAP] >>
     qpat_assum `LENGTH flags = LENGTH ds` mp_tac >>
     qpat_assum `LIST_REL (\arg v. supported_scalar_type (SND arg) /\ _) ds vs` mp_tac >>
     qpat_assum `LIST_REL (\arg v. log_arg_rel _ _ _ _ _ _ arg v /\ _)
       (SND (split_log_ops ds flags)) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     qpat_assum `LIST_REL (\arg v. supported_scalar_type (SND arg) /\ _) ds vs`
       (mp_then Any mp_tac split_log_ops_data_rel) >>
     disch_then (qspec_then `flags` mp_tac) >> simp[] >> strip_tac >>
     gvs[LIST_REL_EL_EQN] >> gen_tac >> disch_tac >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
     qpat_x_assum `!k. k < LENGTH (log_non_indexed_values flags vs) ==>
       log_arg_rel _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
     logWidenTacticsLib.with_cases (fn cases =>
       `aty = SND (EL n (SND (split_log_ops ds flags))) \/
        (is_bytestring_type aty /\
         is_bytestring_type (SND (EL n (SND (split_log_ops ds flags)))))` by
         (drule cases >> strip_tac >>
          gvs[supported_scalar_type_def, supported_word_type_def,
              supported_string_type_def, is_bytestring_type_def]) >>
       Cases_on `aty = SND (EL n (SND (split_log_ops ds flags)))` >- gvs[] >>
       `~is_word_type aty /\
        ~is_word_type (SND (EL n (SND (split_log_ops ds flags))))` by
         metis_tac[is_bytestring_word_type] >>
       gvs[ptr_val_ok_def] >> metis_tac[ptr_mem_ok_bytestring_transport])) >>
  `LIST_REL (\arg v. log_arg_rel cenv cx sa sm (es_end with gas_obs := []) t arg v /\
    supported_scalar_type (SND arg) /\
    (?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v) /\
    ptr_val_ok cx (SND arg) v (FST arg) G tn t)
    (SND (split_log_ops ds flags)) (log_non_indexed_values flags vs)` by
    (fs[LIST_REL_EL_EQN] >> metis_tac[value_has_type_memory_wf]) >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
    ?aty tv. supported_scalar_type aty /\
      log_arg_rel cenv cx sa sm (es_end with gas_obs := []) t (FST arg,aty) v /\
      evaluate_type (get_tenv cx) aty = SOME tv /\ value_has_type tv v /\
      ptr_val_ok cx aty v (FST arg) G tn t /\
      (is_bytestring_type aty <=> is_bytestring_type (SND arg)) /\
      encode_event_topic aty v = encode_event_topic (SND arg) v) ds vs` by
    (irule LIST_REL_mono >> first_assum (irule_at Any) >> simp[] >> metis_tac[]) >>
  `encode_indexed_event_topics flags tys vs = SOME topics /\
   vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags tys)
     (log_non_indexed_values flags vs) = SOME avs /\
   vyper_to_abi_types (get_tenv cx) (log_non_indexed_types flags tys) =
     vyper_to_abi_types (get_tenv cx) (log_non_indexed_types flags (MAP expr_type args))` by
    logWidenTacticsLib.encoding_facts scalar_event_arg_compatible >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) ds` by
    (gvs[EVERY_EL, Abbr `axs`, Abbr `ds`, EL_ZIP, Excl "enc_def"] >> metis_tac[]) >>
  `stmt_state_rel Hc ctx func cenv cx (es_end with gas_obs := []) t` by
    metis_tac[log_args_post_state] >>
  `local_ptrs_reserved cenv sm` by
    (drule_all compile_log_eval_all_grows >> strip_tac >>
     metis_tac[local_ptrs_reserved_next_var]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule_all compile_log_eval_all_grows >> simp[]) >>
  `(!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by
    metis_tac[not_fresh_at_mono] >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm cs') (DROP t.vs_inst_idx bb.bb_instructions)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`fn_has_code sm cs' func`, `same_blocks sm cs'`, `inst_extends sm cs'`,
        `t.vs_current_bb = sm.cs_current_bb`,
        `t.vs_inst_idx = LENGTH sm.cs_current_insts`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[fn_has_code_def, same_blocks_def, inst_extends_def, IS_PREFIX_APPEND,
         Excl "enc_def"] >>
     qexists_tac `l` >> rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  qspecl_then [`t`,`cs'`] strip_assume_tac log_fresh_limit_exists >>
  suspend "path"
QED

Resume compile_log_ready_stmt_frag_ptr_widen[path]:
  markerLib.RESUME_TAC >>
  `LENGTH flags = LENGTH ds` by simp[] >>
  qpat_assum `MAP SND ds = tys`
    (fn th => drule_all (REWRITE_RULE [th]
      (Q.INST [`xs` |-> `ds`] log_suffix_prefix_path_ptr))) >>
  disch_then (qspecl_then [`PG`,
    `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>`] strip_assume_tac) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (es_end with gas_obs := []) u /\
    ghost_inv H d cenv cx (es_end with gas_obs := []) HG tm u /\
    gas_path_ptr (cx_dead H cx) 0 ctx func PG G tn t
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm cs')))
      HG tm (OK u)` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     `stmt_state_rel H ctx func cenv cx (es_end with gas_obs := []) t` by
       metis_tac[log_args_post_state] >>
     conj_tac
     >- (mp_tac (Q.INST [`H0` |-> `Hc`, `H` |-> `H`,
           `u` |-> `u`, `s` |-> `t`, `es` |-> `es_end with gas_obs := []`]
           (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
             stmt_state_rel_fields_transport)) >>
         impl_tac >- asm_simp_tac bool_ss [] >> disch_then ACCEPT_TAC) >>
     conj_tac
     >- (map_every (fn q => qpat_assum q mp_tac)
           [`ghost_inv Hc d cenv cx _ HG tm u`,
            `ghost_inv H d cenv cx _ G tn t`,
            `u.vs_accounts = t.vs_accounts`,
            `u.vs_transient = t.vs_transient`,
            `u.vs_call_ctx = t.vs_call_ctx`,
            `tm.t_stor = tn.t_stor`, `tm.t_trans = tn.t_trans`,
            `tm.t_imm = tn.t_imm`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         fs[ghost_inv_def, stor_taint_ok_def] >> first_assum ACCEPT_TAC) >>
     irule gas_path_ptr_from_no_dead >> first_assum ACCEPT_TAC) >>
  suspend "bind"
QED

Resume compile_log_ready_stmt_frag_ptr_widen[bind]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `n = LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm cs'))` >>
  qabbrev_tac `ev = <|logger := cx.txn.target; topics := n2w h::topics;
    data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
      (log_non_indexed_types flags (MAP expr_type args)))) (ListV avs)|>` >>
  `encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs = SOME ev` by
    simp[Abbr `ev`, Excl "enc_def"] >>
  Cases_on `cx.txn.is_static` >- suspend "static" >>
  drule_all compile_log_emit_path_ptr >>
  disch_then (qspecl_then [`PG`,
    `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>`]
    (qx_choose_then `v` strip_assume_tac)) >>
  qabbrev_tac `t' = v with vs_inst_idx := SUC u.vs_inst_idx` >>
  `gas_path_ptr <|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|> 0 ctx func PG G tn t n HG tm (OK t')` by
    (drule_all gas_path_ptr_then >> simp[Abbr `t'`, Abbr `n`]) >>
  `stmt_state_rel Hc ctx func cenv cx
      ((es_end with logs := es_end.logs ++ [ev]) with gas_obs := []) t' /\
    ghost_inv Hc d cenv cx
      ((es_end with logs := es_end.logs ++ [ev]) with gas_obs := []) HG tm t'` by
    (qpat_x_assum `stmt_state_rel Hc _ _ _ _ (_ with logs := _) _` mp_tac >>
     qpat_x_assum `ghost_inv Hc _ _ _ (_ with logs := _) _ _ _` mp_tac >>
     simp[Abbr `ev`, Abbr `t'`, w2w_id, Excl "enc_def"] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     fs[stmt_state_rel_def, state_rel_def, immutable_alloca_sep_def,
        ghost_inv_def, storage_rel_def, transient_rel_def, accounts_rel_def,
        immutables_rel_def, logs_rel_def, Excl "enc_def"] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `t'.vs_accounts = u.vs_accounts /\ t'.vs_transient = u.vs_transient /\
   t'.vs_requests = u.vs_requests /\ t'.vs_call_ctx = u.vs_call_ctx /\
   t'.vs_current_bb = u.vs_current_bb /\ ~t'.vs_halted /\
   (!x. lookup_var x t' = lookup_var x u)` by
    (fs[venom_state_component_equality, Abbr `t'`, lookup_var_def]) >>
  qexists_tac `marks ++ REPLICATE n F` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL ()`,`es_end with logs := es_end.logs ++ [ev]`,`HG`,`tm`,`OK t'`] >>
  conj_tac
  >- simp[gas_explicit_append, bind_def, lift_option_def, return_def,
           ignore_bind_def, push_log_def, evaluation_state_component_equality,
           Excl "enc_def"] >>
  qx_gen_tac `H` >> simp[Excl "enc_def"] >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==>
    gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==>
    stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (`gas_path_ptr (cx_dead H cx) 0 ctx func PG G tn t n HG tm (OK t')` by
        (irule gas_path_ptr_from_no_dead >> first_assum ACCEPT_TAC) >>
      drule_all (Q.INST [`s` |-> `s0`, `t` |-> `t`, `r` |-> `OK t'`]
        gas_path_ptr_then) >> simp[LENGTH_APPEND]) >>
  disj1_tac >> simp[] >>
  suspend "post"
QED

Resume compile_log_ready_stmt_frag_ptr_widen[static]:
  markerLib.RESUME_TAC >>
  `u.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule_all compile_log_emit_static_path_ptr >>
  disch_then (qspecl_then [`PG`,
    `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>`] assume_tac) >>
  `gas_path_ptr <|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|> 0 ctx func PG G tn t n HG tm
      (Abort ExHalt_abort (halt_state (set_returndata [] u)))` by
    (drule_all gas_path_ptr_then >> simp[Abbr `n`]) >>
  qexists_tac `marks ++ REPLICATE n F` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "write in static context"))`,
    `es_end`,`HG`,`tm`,`Abort ExHalt_abort (halt_state (set_returndata [] u))`] >>
  conj_tac
  >- simp[gas_explicit_append, bind_def, lift_option_def, return_def,
           ignore_bind_def, evaluation_state_component_equality, Excl "enc_def"] >>
  qx_gen_tac `H` >> simp[Excl "enc_def"] >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==>
    gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (`gas_path_ptr (cx_dead H cx) 0 ctx func PG G tn t n HG tm
        (Abort ExHalt_abort (halt_state (set_returndata [] u)))` by
        (irule gas_path_ptr_from_no_dead >> first_assum ACCEPT_TAC) >>
      drule_all (Q.INST [`s` |-> `s0`, `t` |-> `t`,
        `r` |-> `Abort ExHalt_abort (halt_state (set_returndata [] u))`]
        gas_path_ptr_then) >> simp[LENGTH_APPEND]) >>
  simp[exit_result_def, stmt_exit_ptr_def, expr_exit_def]
QED

Resume compile_log_ready_stmt_frag_ptr_widen[post]:
  markerLib.RESUME_TAC >>
  `~block_is_terminated cs'` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags)`,
        `MAP SND ds = tys`, `log_eval_view cenv args sa ds sm`,
        `EVERY supported_scalar_type tys`, `LENGTH flags = LENGTH tys`,
        `compile_log_topic_ops (FST (split_log_ops ds flags)) sm = (ops,st)`,
        `compile_stmt cenv lctx ty (Log id args) sa = ((),cs')`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `EVERY (supported_scalar_type o SND) ds` by
       (qpat_assum `EVERY supported_scalar_type tys` mp_tac >>
        qpat_assum `MAP SND ds = tys` (fn th => rewrite_tac[GSYM th]) >>
        simp[EVERY_MAP, combinTheory.o_DEF]) >>
     `LENGTH flags = LENGTH ds` by metis_tac[LENGTH_MAP] >>
     drule_all log_stmt_open >> simp[]) >>
  `stmt_lands lctx cs' (INL ()) t'` by
    (fs[Abbr `t'`, stmt_lands_def, same_blocks_def, inst_extends_def, IS_PREFIX_APPEND,
        emitted_insts_def] >>
     qpat_assum `cs'.cs_current_insts = sm.cs_current_insts ++ _`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[] >> decide_tac) >>
  drule log_args_post_frame >> strip_tac >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t' = SOME w` by
    (rpt strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
     fs[wb_frame_def] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP HG x = FLOOKUP G0 x /\
       op_taint tm (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
     fs[ghost_kept_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx
      ((es_end with logs := es_end.logs ++ [ev]) with gas_obs := [])
      (u with vs_logs := u.vs_logs ++ [ev])` by
    (drule log_append_stmt_state_rel >>
     disch_then (qspec_then `ev` mp_tac) >>
     qmatch_goalsub_abbrev_tac
       `stmt_state_rel _ _ _ _ _ E1 _ ==> stmt_state_rel _ _ _ _ _ E2 _` >>
     `E1 = E2 with gas_obs := []` by
       simp[Abbr `E1`, Abbr `E2`, evaluation_state_component_equality,
            Excl "enc_def"] >>
     simp[Excl "enc_def"]) >>
  `stmt_state_rel H ctx func cenv cx
      ((es_end with logs := es_end.logs ++ [ev]) with gas_obs := []) t'` by
    (mp_tac (Q.INST [`H0` |-> `Hc`, `H` |-> `H`, `u` |-> `t'`,
        `s` |-> `u with vs_logs := u.vs_logs ++ [ev]`,
        `es` |-> `(es_end with logs := es_end.logs ++ [ev]) with gas_obs := []`]
      (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
        stmt_state_rel_fields_transport)) >>
     impl_tac >- asm_simp_tac (srw_ss()) [Excl "enc_def"] >>
     disch_then ACCEPT_TAC) >>
  `ghost_inv H d cenv cx
      ((es_end with logs := es_end.logs ++ [ev]) with gas_obs := []) HG tm t'` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`ghost_inv Hc d cenv cx ((_ with logs := _) with gas_obs := []) HG tm t'`,
        `ghost_inv H d cenv cx (es_end with gas_obs := []) HG tm u`,
        `t'.vs_accounts = u.vs_accounts`,
        `t'.vs_transient = u.vs_transient`,
        `t'.vs_call_ctx = u.vs_call_ctx`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     fs[ghost_inv_def, stor_taint_ok_def] >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx
      ((es_end with logs := es_end.logs ++ [ev]) with gas_obs := []) (FST H)` by
    (`storage_well_formed_on cx (es_end with gas_obs := []) (FST H)` by
       fs[log_args_post_def, Excl "enc_def"] >>
     qpat_x_assum `storage_well_formed_on cx (es_end with gas_obs := []) (FST H)`
       mp_tac >>
     match_mp_tac (METIS_PROVE [] ``(A <=> B) ==> A ==> B``) >>
     irule storage_well_formed_on_backends >> simp[Excl "enc_def"]) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [evaluation_state_fupdcanon]) >>
  PURE_REWRITE_TAC [evaluation_state_fupdcanon] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[cenv_top_ext_refl, Excl "enc_def"] >> rpt strip_tac >>
  qpat_x_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x t' = SOME w` (qspecl_then [`x`,`w`] mp_tac) >> simp[]
QED
Finalise compile_log_ready_stmt_frag_ptr_widen

Theorem compile_log_ready_stmt_frag_ptr:
  log_args_ready_ptr d ctx PG func cenv cx Inv args /\ Inv es /\
  (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
  expr_sim_inv cenv cx env es /\ well_typed_exprs env args /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id = SOME (h,tys,flags) /\
  MAP expr_type args = tys /\ LENGTH flags = LENGTH tys /\
  LENGTH (FILTER I flags) <= 3 /\ EVERY supported_scalar_type tys /\
  ~exprs_can_mutate cenv args /\
  EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
             is_bytestring_type (expr_type e)) args /\
  SUM (MAP (type_memory_bytes cenv) (log_non_indexed_types flags tys)) < dimword(:256) /\
  abi_size_bound cenv.ce_struct_fields (TupleT (log_non_indexed_types flags tys)) < dimword(:256) ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Log id args)) (eval_stmt cx (Log id args)) es
Proof
  strip_tac >> irule compile_log_ready_stmt_frag_ptr_widen >>
  simp[] >>
  simp[LIST_REL_EL_EQN, CONJUNCT1 event_arg_compatible_reflexive] >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `Inv` >> simp[]
QED
