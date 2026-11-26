(* Retain the compiled bytestring capacity when forcing the Convert operand. *)
Theory bodyConvertOperandBufferMods
Ancestors
  bodyIfExpArmUnwrapMods
  bodyFullPostsMods bodyFullShared exprSimUnwrap exprSimMemorySource
  gasShadowCompile gasShadowState gasOutcomeFullBindMods
  gasOutcomeFullPostMods gasExemptCertMods haltExitProj stmtSimProps
  vyperStorageTrace vyperStorageFootprint exprLowering compileEnv fragExec
  exprSimDefs loweringPosts vyperAST vyperState words
Libs monadsyntax

Theorem convert_operand_unwrap_cut[local]:
  lower_value compile_expr ce ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr e) sha = (op,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\
  fn_has_code sha shb shadow_func ==>
  ?vv sm shm.
    compile_expr ce ty e sa = (vv,sm) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (vv,shm) /\
    unwrap_value ce vv sm = (op,sb) /\ gas_shadow_state sm shm /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code sha shm shadow_func
Proof
  strip_tac >>
  qpat_x_assum `lower_value compile_expr ce ty e sa = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr ce ty e sa` >>
  rename1 `_ = (vv,sm)` >> simp[] >> strip_tac >>
  qpat_x_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha` >>
  rename1 `_ = (vsh,shm)` >>
  simp[gasShadowCompileBaseTheory.unwrap_value_gas_shadow_env] >> strip_tac >>
  `gas_shadow_compiles (compile_expr ce ty e)
     (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  qpat_x_assum `vsh = vv` SUBST_ALL_TAC >>
  qpat_assum `compile_expr ce ty e sa = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `unwrap_value ce vv sm = _`
    (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `unwrap_value ce vv shm = _`
    (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sha shm shadow_func /\ fn_has_code shm shb shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  asm_rewrite_tac[]
QED

Theorem convert_operand_buffer_outcome_mods:
  expr_body_pre_mods mods ce cx env e es /\ is_bytestring_type (expr_type e) /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es ==>
  !st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
    lower_value compile_expr ce (expr_type e) e sa = (op,sb) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (op,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
    (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
    (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
    (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
    gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
    return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es s0 /\ immutable_frame_mods func ce cx es s0 /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      ce.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
      (\H res ee G tn t. ?v pt rt w. res = INL v /\
        expr_post_mods H ctx func ce cx e es sa sb s0 ee v op t /\
        storage_well_formed_on cx ee (FST H) /\
        expr_store_bound cx (post_value_type ce e) v op t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d ce cx ee G tn t /\
        ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
        ptr_val_ok cx (post_value_type ce e) v op G tn t /\ ptr_buf_ok ce e op G t /\
        ~is_word_type (post_value_type ce e) /\
        evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
        evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
        type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
        value_has_type pt v /\ value_has_type rt v /\ val_wf rt v /\
        eval_operand op t = SOME w /\ op_taint tn op = {} /\
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem) /\
        (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next) /\
        w2n w + type_memory_size rt < dimword (:256) /\
        (0 < type_memory_size rt ==>
          ?x. op = Var x /\ not_fresh_at sb x /\ ptr_covers G tn x t (type_memory_size rt)))
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`vv`,`sm`,`shm`] strip_assume_tac)
    convert_operand_unwrap_cut >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shm`,`vv`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
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
      conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`,expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "read"
QED

Resume convert_operand_buffer_outcome_mods[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (assume_tac o BETA_RULE) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,ee)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> (?r. _ = INL r /\ _) /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  disj1_tac >> qexists_tac `tv` >> simp[] >>
  `~is_word_type (expr_type e)` by simp[valueCopyBytesTheory.is_bytestring_word_type] >>
  `~is_word_type (post_value_type ce e)` by simp[] >>
  `!tag x. vv = StackValue tag x ==> ptr_buf_ok ce e x G s` by simp[] >>
  drule_all_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac)
    (SIMP_RULE bool_ss [arithmeticTheory.LESS_EQ_REFL]
      (Q.INST [`k` |-> `sm`] (SPEC_ALL ifexp_arm_nonword_unwrap_mods))) >>
  disch_then (qx_choosel_then [`vr`,`u`,`Gf`,`tf`,`pt`,`rt`,`w`]
    (map_every assume_tac o CONJUNCTS)) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl [`Gf`,`ee`,`INL vr`,`u`,`tf`] >> simp[read_result_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  drule post_value_type_bytestring >> disch_then (qspec_then `ce` SUBST_ALL_TAC) >>
  qexists_tac `pt` >> asm_rewrite_tac[]
QED

Finalise convert_operand_buffer_outcome_mods
