(* The ABI result is a materialized value at a memory pointer. *)
Theory bodyAbiResultReadMods
Ancestors
  bodyAggregateReadMods bodyAggregateReadPostMods bodyFullPostsMods
  exprSimUnwrap gasShadowCompile gasShadowState gasShadowCompileBase
  exprLowering compileEnv fragExec exprSimDefs
  decoderNavigationPtr bodyFullUnwrapRun bodyFullTargetArrayLoad emitHelperProps
  exprSimProps venomInst venomExecSemantics venomState
  fragGasOriginPtr context ptrDiscipline exprLoweringProps instIdxIndep finite_map
  bodyArraySelectReadonlyMods exprSimUnwrapProps exprPtrUnwrapLoad exprPtrUnwrapFacts
  loweringPosts exprSimMemDefs bodyPtrDefs bodyFullShadowBodyInv stateRelProj
  gasOutcomeFullPostMods vyperState vyperContext vyperInterpreter gasSummary
  vyperStorageFootprint gasOutcomeFullBindMods gasExemptCertMods
  exprSimMemorySource vyperStorageTrace haltExitProj stmtSimProps freshWrites

Theorem abi_read_compile_cuts[local]:
  lower_value compile_expr ce ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (op,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb fn /\ fn_has_code sha shb shfn ==>
  ?vv sm shm.
    compile_expr ce ty e sa = (vv,sm) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (vv,shm) /\
    gas_shadow_state sm shm /\ fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
    fn_has_code sha shm shfn /\ sa.cs_next_var <= sm.cs_next_var /\
    unwrap_value ce vv sm = (op,sb) /\ unwrap_value ce vv shm = (op,shb)
Proof
  strip_tac >> Cases_on `compile_expr ce ty e sa` >>
  rename1 `compile_expr ce ty e sa = (vv,sm)` >>
  `gas_shadow_compiles (compile_expr ce ty e)
    (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`sha`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha` >>
  simp[] >> strip_tac >>
  rename1 `compile_expr _ _ (gas_shadow_expr _) sha = (_,shm)` >>
  gvs[lower_value_def, comp_bind_def, unwrap_value_gas_shadow_env] >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `compile_expr ce ty e sa = _`
       (mp_tac o MATCH_MP compile_expr_extends) >> simp[]) >>
  `cs_extends sha shm` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr _) sha = _`
       (mp_tac o MATCH_MP (cj 1 compile_expr_extends)) >> simp[]) >>
  `cs_extends sm sb /\ cs_extends shm shb` by
    (conj_tac
     >- (qpat_assum `unwrap_value _ _ sm = _`
           (mp_tac o MATCH_MP unwrap_value_extends) >> simp[]) >>
     qpat_assum `unwrap_value _ _ shm = _`
       (mp_tac o MATCH_MP unwrap_value_extends) >> simp[]) >>
  qspecl_then [`sa`,`sm`,`sb`,`fn`] mp_tac fn_has_code_split >> simp[] >>
  qspecl_then [`sha`,`shm`,`shb`,`shfn`] mp_tac fn_has_code_split >> simp[]
QED

Theorem abi_memory_buffer_value_from_vv_mods:
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
  (!gs raw ee. eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) ==>
     ?v. raw = Value v) /\
  (!sa sm vv. compile_expr ce ty e sa = (vv,sm) /\ fn_has_code sa sm func ==>
     ?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory /\ ~is_word_type tag) ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es
Proof
  strip_tac >> irule materialized_value_from_vv_mods >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac abi_read_compile_cuts >>
  qpat_assum `!a m vv. compile_expr _ _ _ a = (vv,m) /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  gvs[unwrap_value_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac memory_buffer_read_post_mods >> simp[]
QED

(* One clean load, at the actual cursor and with the older ghost data retained. *)
Theorem abi_result_word_load[local]:
  emit_op MLOAD [Var src] sm = (op,sb) /\
  lookup_var src s = SOME w /\ ptr_covers G tn src s 32 /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  w2n w + 32 <= s.vs_alloca_next /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ alloca_inv s /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u Gf tf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
                (s,G,tn) [] (OK u,Gf,tf)) /\
    array_length_frame sm s G tn u Gf tf /\
    eval_operand op u = SOME (mload (w2n w) s) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    alloca_history func u /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_then strip_assume_tac emitted_insts_emit_op >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `raw = update_var out (mload (w2n w) s) s` >>
  `run_inst_seq (emitted_insts sm sb) s = OK raw` by
    simp[Abbr `raw`,run_inst_seq_def,mk_inst_def,step_inst_base_opcode_eqs,
         exec_read1_def,eval_operand_def] >>
  drule_all emit_mload_clean_endpoint_ptr_origin_core_exact_frame >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`,`ARB`] strip_assume_tac) >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  `alloca_history func (raw with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule emitted_alloca_history >> simp[] >> qexistsl [`emitted_insts sm sb`,`s`,`sm`] >>
     simp[mk_inst_def,is_terminator_def]) >>
  qexistsl [`raw with vs_inst_idx := LENGTH sb.cs_current_insts`,`HG`,`u`] >>
  simp[array_length_frame_def,eval_op_inst_idx] >>
  simp[Abbr `raw`,update_var_def,eval_operand_def,lookup_var_def,FLOOKUP_UPDATE,
       venom_state_component_equality] >>
  rpt strip_tac >>
  `out <> x` by (strip_tac >> gvs[Abbr `out`,loweringStateRelDefsTheory.not_fresh_at_def]) >>
  simp[]
QED

Theorem abi_read_word_plain_post[local]:
  p.ptr_location = LocMemory /\
  vv_post_mods H ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue tag p) s ==>
  vv_post H ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue tag p) s
Proof
  strip_tac >> gvs[vv_post_mods_def,vv_holds_mods_def,vv_place_ptr_mods_def,vv_post_def] >>
  first_assum ACCEPT_TAC
QED

Theorem abi_read_word_suffix[local]:
  p.ptr_location = LocMemory /\ is_word_type tag /\ post_value_type ce e = tag /\
  evaluate_type (get_tenv cx) tag = SOME rt /\ value_has_type rt v /\
  unwrap_value ce (LocatedValue tag p) sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue tag p) s /\
      ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx tag (lowered_value_type ce e) ee (Value v) (LocatedValue tag p) s /\
  ptr_vv_ok cx tag (Value v) (LocatedValue tag p) ee G tn s /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    (read_result cx (Value v)) (ee,s,G,tn)
    (\H res ef Gf tf u. ?w. res = INL w /\
      expr_post_mods H ctx func ce cx e es sa sb s0 ef w op u /\
      expr_store_bound cx (post_value_type ce e) w op u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx ef Gf tf u /\
      ptr_val_ok cx (post_value_type ce e) w op Gf tf u /\
      ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf) R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  drule_all_then assume_tac abi_read_word_plain_post >>
  qpat_x_assum `post_value_type ce e = tag` (SUBST_ALL_TAC o SYM) >>
  drule unwrap_memory_word_input >>
  disch_then (qspecl_then [`rt`,`tn`,`G`] mp_tac) >>
  simp[read_result_def,return_def] >> strip_tac >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  `alloca_inv s` by
    (fs[vv_post_mods_def] >> drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  `w2n w + 32 <= s.vs_alloca_next` by
    (drule_all (Q.SPEC `v` (GEN ``v:value`` word_value_memory_extent)) >> strip_tac >>
     qpat_assum `vv_store_bound _ _ _ _ _ _ _`
       (mp_tac o SIMP_RULE (srw_ss()) [vv_store_bound_def]) >>
     disch_then (mp_tac o cj 1) >>
     disch_then (qspecl_then [`v`,`rt`,`w`] mp_tac) >>
     simp[read_result_def,return_def]) >>
  `emit_op MLOAD [Var src] sm = (op,sb)` by
    (qpat_assum `unwrap_value _ _ _ = _` (mp_tac o REWRITE_RULE [unwrap_value_def]) >>
     asm_rewrite_tac[compile_ptr_load_def]) >>
  drule_all abi_result_word_load >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  irule gas_outcome_full_mods_pure >> simp[read_result_def,return_def] >>
  qexistsl [`Gf`,`ee`,`INL v`,`u`,`tf`] >> simp[] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  asm_rewrite_tac[] >> qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `vv_post_mods (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `ghost_inv_at_mods (DF (storage_trace_horizon _)) _ _ _ _ _ _ _ _` kall_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_all_then assume_tac abi_read_word_plain_post >>
  qpat_x_assum `vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `wb_frame ce es ee sa s0 s` by
    (simp[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac array_select_readonly_suffix_mods >>
  simp[expr_store_bound_word,ptr_val_ok_word] >>
  simp[expr_post_mods_def] >>
  irule expr_post_of_vv_post_load_physical >>
  simp[] >> qexistsl_tac [`p`,`s`,`sm`,`post_value_type ce e`] >>
  simp[] >>
  fs[array_length_frame_def,venom_state_component_equality] >> metis_tac[]
QED

Theorem abi_result_read_from_vv_mods:
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
  (!gs raw ee. eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) ==>
     ?v rt. raw = Value v /\
       evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
       value_has_type rt v) /\
  (!sa sm vv. compile_expr ce ty e sa = (vv,sm) /\ fn_has_code sa sm func ==>
     ?p. vv = LocatedValue (post_value_type ce e) p /\ p.ptr_location = LocMemory) ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es
Proof
  strip_tac >> reverse (Cases_on `is_word_type (post_value_type ce e)`)
  >- (irule abi_memory_buffer_value_from_vv_mods >>
      conj_tac >- (rpt gen_tac >> strip_tac >>
        qpat_assum `!a m vv. compile_expr _ _ _ a = (vv,m) /\ _ ==> _`
          (drule_all_then strip_assume_tac) >> simp[] >> metis_tac[]) >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!gs raw ee. _ ==> ?v rt. _` (drule_then strip_assume_tac) >> simp[]) >>
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac abi_read_compile_cuts >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (fn th => drule_all_then assume_tac (REWRITE_RULE [expr_vv_sim_full_mods_def] th)) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >>
      rename1 `gas_marked_exec _ _ _ _ _ (INL reached) mid (OK mid_state)` >>
      irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`mid_state`,`reached`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result _ v)`]
  >- simp[storage_trace_frame_read_result] >>
  qexists_tac `\H res ee G tn u. childQ H res ee G tn u /\ ee.gas_obs = [] /\ ~u.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      BETA_TAC >> conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`,expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`s`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o BETA_RULE)) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,ee)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  qpat_assum `!gs raw ee. _ ==> ?v rt. _` (drule_then strip_assume_tac) >>
  qpat_x_assum `tv = Value _` SUBST_ALL_TAC >>
  qpat_assum `!a m vv. compile_expr _ _ _ a = (vv,m) /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `Value v` >> simp[] >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono] >>
  irule abi_read_word_suffix >> simp[] >>
  qexistsl_tac [`p`,`sm`] >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _`
    (qspec_then `H` (mp_tac o BETA_RULE)) >> simp[]
QED
