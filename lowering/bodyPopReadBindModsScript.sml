(* Bind the linked Pop value read at the actual endpoint of its VV run. *)
Theory bodyPopReadBindMods
Ancestors
  bodyFullPostsMods bodyFullShared bodyAttributeReadOperandMods
  gasShadowCompileStmtHelpers gasShadowCompileBase gasShadowState
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  exprSimUnwrap exprSimMemorySource stmtSimForRounds stmtSimProps haltExitProj
  vyperStorageTrace vyperStorageFootprint exprLowering compileEnv fragExec
  exprSimDefs vyperAST vyperState
Libs monadsyntax

Theorem pop_read_compile_cut[local]:
  lower_value compile_expr cenv ty (Pop ann bt) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Pop ann bt)) sha = (op,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\
  fn_has_code sha shb shadow_func ==>
  ?vv sm shm.
    compile_expr cenv ty (Pop ann bt) sa = (vv,sm) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Pop ann bt)) sha = (vv,shm) /\
    unwrap_value cenv vv sm = (op,sb) /\ gas_shadow_state sm shm /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code sha shm shadow_func
Proof
  strip_tac >>
  qpat_x_assum `lower_value compile_expr cenv ty (Pop _ _) sa = _` mp_tac >>
  simp[lower_value_def,comp_bind_def] >>
  Cases_on `compile_expr cenv ty (Pop ann bt) sa` >>
  rename1 `_ = (vv,sm)` >> simp[] >> strip_tac >>
  qpat_x_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[lower_value_def,comp_bind_def] >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Pop ann bt)) sha` >>
  rename1 `_ = (vsh,shm)` >>
  simp[unwrap_value_gas_shadow_env] >> strip_tac >>
  `gas_shadow_compiles (compile_expr cenv ty (Pop ann bt))
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Pop ann bt)))` by
    irule gas_shadow_stmt_compile_expr_env >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  qpat_x_assum `vsh = vv` SUBST_ALL_TAC >>
  qpat_assum `compile_expr cenv ty (Pop _ _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `unwrap_value cenv vv sm = _`
    (assume_tac o MATCH_MP unwrap_value_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `unwrap_value cenv vv shm = _`
    (assume_tac o MATCH_MP unwrap_value_extends) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sha shm shadow_func /\ fn_has_code shm shb shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  asm_rewrite_tac[]
QED

val pop_read_vv_post = ``
  vv_post_mods (H : (bool # bytes32 # type_value) list # num list)
    ctx func cenv cx (Pop ann bt) es sa sm s0 ee tv vv s /\
  vv_store_bound cx (post_value_type cenv (Pop ann bt))
    (lowered_value_type cenv (Pop ann bt)) ee tv vv s /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
  ptr_vv_ok cx (post_value_type cenv (Pop ann bt)) tv vv ee G tn s /\
  (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Pop ann bt)) /\
       ~is_bytestring_type (post_value_type cenv (Pop ann bt)) ==>
       vv_own cenv cx (post_value_type cenv (Pop ann bt)) sa sm ee tv vv s /\
       (!tag p. vv = LocatedValue tag p ==> p.ptr_location = LocMemory)) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?v. read_result cx tv ee = (INL v,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Pop ann bt)) = SOME rt /\
              eval_operand (vv_operand vv) s = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                val_in_memory rt v (w2n w) mem)) /\
  (!tag x. vv = StackValue tag x /\ ~is_word_type (post_value_type cenv (Pop ann bt)) ==>
           ptr_buf_ok cenv (Pop ann bt) x G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
           ptr_buf_ok cenv (Pop ann bt) p.ptr_operand G s) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

(* Only the reached read is conditional. The VV prefix and prior exits are
   taken from the supplied VV judgment, not reconstructed by the callback. *)
Theorem pop_read_bind_mods:
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Pop ann bt) es /\
  (!st0 sa sm sb op s0 G0 tn0 marks ee tv vv v s G tn.
     compile_expr cenv ty (Pop ann bt) sa = (vv,sm) /\
     unwrap_value cenv vv sm = (op,sb) /\
     fn_has_code sa sm func /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
     sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
     local_ptrs_reserved cenv sa /\
     (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
     (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
     (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
     (!tail. eval_expr cx (Pop ann bt)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL tv,ee with gas_obs := tail)) /\
     eval_expr cx (Pop ann bt) (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL tv,ee) /\
     storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\ ~s.vs_halted /\
     gas_admissible (read_result cx tv) expr_res_ok ee /\
     read_result cx tv ee = (INL v,ee) /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> ^pop_read_vv_post) ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv.ce_modules cx st0 (read_result cx tv) (ee,s,G,tn)
       (\H res ee' G' tn' u. ?value. res = INL value /\
          expr_post_mods H ctx func cenv cx (Pop ann bt) es sa sb s0 ee' value op u /\
          expr_store_bound cx (post_value_type cenv (Pop ann bt)) value op u /\
          u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          s0.vs_alloca_next <= u.vs_alloca_next /\
          ghost_inv_at_mods (DF H) lo d cenv cx ee' G' tn' u /\
          ptr_val_ok cx (post_value_type cenv (Pop ann bt)) value op G' tn' u /\
          (~is_word_type (post_value_type cenv (Pop ann bt)) ==>
           ptr_buf_ok cenv (Pop ann bt) op G' u) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
       (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
          (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))) ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Pop ann bt) es
Proof
  strip_tac >> rewrite_tac[expr_sim_full_mods_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`vv`,`sm`,`shm`] strip_assume_tac) pop_read_compile_cut >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shm`,`vv`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result _ v)`]
  >- simp[storage_trace_frame_read_result] >>
  qexists `\H res ee G tn s. childQ H res ee G tn s /\ ee.gas_obs = [] /\ ~s.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`,expr_exit_def] >>
      once_rewrite_tac [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
                        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "read"
QED

Resume pop_read_bind_mods[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`s`] >> BETA_TAC >>
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
  `eval_expr cx (Pop ann bt) (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL tv,ee)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  `gas_admissible (read_result cx tv) expr_res_ok ee` by
    (drule_all gas_admissible_bind_tail >> asm_rewrite_tac[]) >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule_then (qx_choosel_then [`value`,`word`] strip_assume_tac) attribute_read_operand_mods >>
     qexists `value` >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> ^pop_read_vv_post` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> (?r. _ = INL r /\ _) /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disj1_tac >> qexists `tv` >> conj_tac >- REFL_TAC >>
  qpat_assum `!st0 sa sm sb op s0 G0 tn0 marks ee tv vv v s G tn. _` irule >>
  rpt (first_assum (irule_at Any)) >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise pop_read_bind_mods
