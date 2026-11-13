(* Typed uint2str memory paths and operand composition. *)
Theory bodyMemBiUint2StrCompose
Ancestors
  bodyMemBiUint2StrPost bodyMemBiSha256Compose exprSimWordBuiltins loweringPosts
  vyperStorageTrace vyperStorageFootprint exprLoweringProps
  vyperTyping vyperTypeSystem exprSimHypsDefs exprSimSource exprSimWordArgs
  exprSimUint2Str exprSimHash exprSimMemDefs exprLoweringProps
  builtinStrings arithmetic words exprSafeOperand exprLowering compileEnv valueEncoding vyperValue loweringSlice context exprSimDefs gasSummary gasOutcome fragGasMode fragGasPath gasContext builtinSimple vyperAST vyperState fragExec vyperContext

Theorem u2s_as_ptr_loc[local]:
  as_ptr_val t LocMemory pr = (vv,sb) ==>
  ?p. vv = LocatedValue t p /\ p.ptr_location = LocMemory
Proof
  Cases_on `pr` >> simp[as_ptr_val_def, mk_ptr_def]
QED

(* A memory pointer's post at one horizon moves to every horizon at which the
   start state is related: only the storage-side Venom fields enter the
   horizon-dependent part, and the uint2str code leaves them alone. *)
Theorem uint2str_typed_mem_path[local]:
  expr_body_pre cenv cx env (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) es /\
  expr_type e = BaseT (UintT k) /\ 78 <= n /\
  lower_value compile_expr cenv ty e sa = (x,sm) /\
  as_ptr_val (BaseT (StringT n)) LocMemory
    (compile_uint2str x n (type_memory_bytes cenv (BaseT (StringT n))) sm) = (vv,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es') /\
  value_has_type (BaseTV (UintT k)) v /\
  expr_post H ctx func cenv cx e es sa sm s0 es' v x s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s ==>
  ?t rv. gas_path_mem ctx func s 0 (OK t) /\
    builtin_result cx es'.accounts (BaseT (StringT n)) (Uint2Str n)
      [expr_type e] [v] = INL rv /\
    vv_post H ctx func cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
      es sa sb s0 es' (Value rv) vv t /\
    vv_store_bound cx (BaseT (StringT n)) (BaseT (StringT n)) es'
      (Value rv) vv t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_requests = s.vs_requests /\ t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> simp[] >>
     qexistsl_tac [`BaseT (StringT n)`, `[e]`, `Uint2Str n`, `es`] >> simp[]) >>
  `well_formed_type env.type_defs (expr_type e)` by
    (irule well_typed_expr_type_well_formed >>
     metis_tac[expr_body_pre_var_types_well_formed, expr_body_pre_def]) >>
  `k <= 256` by gvs[well_formed_type_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  drule_all uint_value_word_rep >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM es'.scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  drule uint2str_body_capacity >> strip_tac >>
  Cases_on `compile_uint2str x n (type_memory_bytes cenv (BaseT (StringT n))) sm` >>
  gvs[as_ptr_val_def] >>
  `n+32 <= type_memory_bytes cenv (BaseT (StringT n))` by
    (simp[type_memory_bytes_def, type_slot_size_def] >>
     mp_tac (Q.SPEC `n` valueTypingMemoryPropsTheory.word_size_capacity) >>
     simp[vfmConstantsTheory.word_size_def]) >>
  `type_memory_bytes cenv (BaseT (StringT n))+n < dimword (:256)` by
    (simp[dimword_def] >> decide_tac) >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  `w2n (val_to_w256 v : bytes32) < dimword (:256)` by simp[w2n_lt] >>
  drule_all uint2str_numeric_mem_path >> strip_tac >>
  qexistsl_tac [`t`, `StringV (num_to_dec_string (w2n (val_to_w256 v)))`] >>
  simp[uint2str_source_result] >>
  irule uint2str_vv_capacity >>
  conj_tac >- (fs[dimword_def] >> decide_tac) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[mk_ptr_def]
QED

Theorem compile_uint2str_typed_vv_sim_mem:
  expr_body_pre cenv cx env (Builtin ann (Uint2Str n) [e]) es /\
  expr_sim_mem ctx func cenv cx ty e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann (Uint2Str n) [e]) es
Proof
  strip_tac >>
  `?k. ann = BaseT (StringT n) /\ expr_type e = BaseT (UintT k) /\ 78 <= n` by
    (fs[expr_body_pre_def] >> drule uint2str_expr_types >> simp[] >> metis_tac[]) >> gvs[] >>
  rewrite_tac[expr_vv_sim_mem_def] >> rpt strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >> fs[expr_body_pre_def]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_uint2str_singleton] >> pairarg_tac >> strip_tac >>
  gvs[] >>
  `cs_appends (\sm. as_ptr_val (BaseT (StringT n)) LocMemory
      (compile_uint2str v n (type_memory_bytes cenv (BaseT (StringT n))) sm))` by
    (rw[cs_appends_def] >>
     Cases_on `compile_uint2str v n (type_memory_bytes cenv (BaseT (StringT n))) sm'` >>
     gvs[as_ptr_val_def] >>
     irule (SRULE [cs_appends_def] uint2str_suffix_appends) >> goal_assum (drule_at Any)) >>
  qmatch_asmsub_abbrev_tac `cs_appends code` >>
  `code sm = (vv,sb)` by simp[Abbr `code`] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  qunabbrev_tac `code` >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  simp[eval_expr_unary_builtin_action, builtin_args_length_ok_def] >>
  irule sha256_expr_sim_mem_suffix >>
  first_assum (irule_at (Pat `expr_sim_mem _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[vyperStorageTraceTheory.storage_trace_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule expr_exit_INR_cast >> simp[]) >>
  rpt strip_tac >> suspend "continuation"
QED

(* The path is chosen at one valid horizon H0 and its endpoint keeps the
   storage-side Venom fields, so the post moves to every valid horizon. *)
Resume compile_uint2str_typed_vv_sim_mem[continuation]:
  qmatch_asmsub_rename_tac `bind (eval_expr cx e) (read_result cx) _ = (INL cv, cee)` >>
  qmatch_asmsub_rename_tac `expr_store_bound cx (expr_type e) cv cop ct` >>
  qpat_x_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    (drule_all valid_horizon_frame >> simp[]) >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  `expr_post H0 ctx func cenv cx e es sa sm s0 cee cv cop ct` by metis_tac[] >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by
    metis_tac[expr_body_pre_gas_obs] >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_base_result) >>
  disch_then (qspecl_then [`env`, `cenv`] mp_tac) >> simp[] >> strip_tac >>
  drule_all uint2str_typed_mem_path >> strip_tac >>
  `?p. vv = LocatedValue (BaseT (StringT n)) p /\ p.ptr_location = LocMemory` by
    (drule u2s_as_ptr_loc >> simp[]) >>
  `cee with gas_obs := [] = cee` by simp[evaluation_state_component_equality] >>
  `s0.vs_alloca_next <= t'.vs_alloca_next` by decide_tac >>
  qexists_tac `[]` >>
  rewrite_tac[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INL (Value rv)`, `cee`, `OK t'`] >>
  rpt conj_tac
  >- simp[]
  >- simp[gas_marked_path_def]
  >> disj1_tac >> qexists_tac `t'` >> conj_tac >- REFL_TAC >>
  BETA_TAC >> qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H cee.storage_trace` by
    (pop_assum mp_tac >> simp[]) >>
  `expr_post H ctx func cenv cx e es sa sm s0 cee cv cop ct` by metis_tac[] >>
  `stmt_state_rel H ctx func cenv cx cee ct /\ storage_well_formed_on cx cee (FST H)` by
    (qpat_x_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  `vv_post H ctx func cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
     es sa sb s0 cee (Value rv) vv t'` by
    (mp_tac (Q.SPECL [`H0`, `H`, `ctx`, `func`, `cenv`, `cx`,
       `Builtin (BaseT (StringT n)) (Uint2Str n) [e]`, `es`, `sa`, `sb`, `s0`,
       `cee`, `Value rv`, `vv`, `t'`, `ct`]
       vv_post_fields_transport) >>
     impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
        strip_tac >> gvs[vv_storage_live_def]) >>
     simp[]) >>
  qexists_tac `Value rv` >>
  simp[expr_type_def, lowered_value_type_def] >>
  TRY (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac)
QED
Finalise compile_uint2str_typed_vv_sim_mem
