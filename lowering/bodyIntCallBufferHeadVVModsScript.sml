(* The source and resource cuts of one memory-passed argument. The raw
   expression runs before the formal's buffer is allocated. *)
Theory bodyIntCallBufferHeadVVMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyWriteSubscriptSourceMods
  bodyBranchCellFrameMods bodyPtrAttributeSource bodyFullShadowBodyInv
  bodyFullHashKeccakFixed bodyMemoryDefs wordArgsPtr gasOriginPtrLabels
  fragGasOriginPtrExec fragExec exprOperandVar exprLoweringProps exprSimDefs
  gasContext vyperStorageFootprint vyperInterpreter vyperState
  context compileEnv loweringPosts bodyPtrDefs ptrDiscipline
  venomState finite_map words

Theorem intcall_buffer_head_vv_admissible_mods:
  body_exprs_full_ok_mods mods exps cx (e::es) /\
  gas_admissible (bind (eval_exprs cx (e::es)) k) P esi /\
  (!err. P (INR err) ==> expr_vv_res_ok (INR err)) ==>
  body_expr_full_ok_mods mods exps cx e /\
  bind (eval_exprs cx (e::es)) k =
    bind (eval_expr cx e) (\tv. bind (read_result cx tv)
      (\v. bind (eval_exprs cx es) (\vs. k (v::vs)))) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok esi
Proof
  strip_tac >>
  `body_expr_full_ok_mods mods exps cx e` by
    fs[Once body_exprs_full_ok_mods_def] >>
  `bind (eval_exprs cx (e::es)) k =
     bind (eval_expr cx e) (\tv. bind (read_result cx tv)
       (\v. bind (eval_exprs cx es) (\vs. k (v::vs))))` by
    simp[evaluate_def,bind_assoc,bind_return] >>
  simp[gas_admissible_def] >> rpt gen_tac >> disch_tac >>
  qpat_x_assum `gas_admissible _ P esi` (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
  disch_then (qspec_then `gs` mp_tac) >>
  Cases_on `res`
  >- (rename1 `eval_expr _ _ _ = (INL tv,ee)` >>
      Cases_on `tv` >> simp[expr_vv_res_ok_def,bind_apply,read_result_def,raise_def] >>
      qpat_x_assum `!err. P (INR err) ==> _`
        (qspec_then `Error (TypeError "read_result mapping")` mp_tac) >>
      simp[expr_vv_res_ok_def]) >>
  simp[bind_apply] >> strip_tac >> first_x_assum irule >> simp[]
QED

Triviality raw_post_read:
  vv_post_mods H ctx func cenv cx e es si ci s ee tv vv t ==>
  ?v. read_result cx tv ee = (INL v,ee)
Proof
  simp[vv_post_mods_def] >> strip_tac >> Cases_on `vv`
  >- fs[vv_holds_mods_def,vv_holds_def] >>
  rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location = LocCode`
  >- fs[vv_holds_mods_def,immutable_holds_mods_def,immutable_holds_def] >>
  fs[vv_holds_mods_def] >> drule_then strip_assume_tac attribute_vv_holds_read_operand >> simp[]
QED

(* Byte equality follows from value writeback; the no-new-taint clause
   instead comes from ghost preservation on the same nonlocal row. *)
Triviality head_old_window:
  wb_frame cenv es ee si s t /\
  ghost_kept_at lo cenv es si G tn s G1 tn1 /\
  FLOOKUP s.vs_allocas aid = SOME (b,cap) /\ aid < si.cs_next_id /\
  (!n lb sz. local_region cenv es.scopes s n lb sz ==>
    b+cap <= lb \/ lb+sz <= b) ==>
  mem_bytes_at b cap t.vs_memory = mem_bytes_at b cap s.vs_memory /\
  (!i. b <= i /\ i < b+cap /\ i IN tn1.t_mem ==> i IN tn.t_mem)
Proof
  rewrite_tac[wb_frame_def,ghost_kept_at_def] >> strip_tac >>
  conj_tac
  >- (qpat_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _`
        (qspecl_then [`aid`,`b`,`cap`] mp_tac) >>
      impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >> metis_tac[]) >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!aid off sz i. _ ==> i IN _`
    (qspecl_then [`aid`,`b`,`cap`,`i`] mp_tac) >>
  impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >> metis_tac[]) >> simp[]
QED

val head_input = ``
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func cenv cx e es si ci s ee tv vv t /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1)) /\
  ghost_kept_at lo cenv es si G tn s G1 tn1 /\
  compile_expr cenv (expr_type e) e si = (vv,ci) /\
  local_ptrs_reserved cenv si /\
  return_buf_frame d cenv si s /\
  stmt_state_rel H0 ctx func cenv cx es s /\
  s.vs_alloca_next <= t.vs_alloca_next``;

Theorem intcall_buffer_head_vv_resources_mods:
  ^head_input ==>
  (?v. read_result cx tv ee = (INL v,ee) /\
       value_runtime_typed env (expr_type e) v) /\
  expr_sim_inv_mods mods cenv cx env ee /\
  body_const_cells_agree_mods mods cx env ee /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\
    immutable_frame_mods func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t) /\
  stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee t /\
  local_ptrs_reserved cenv ci /\
  allocas_from lo t /\ lo <= t.vs_alloca_next /\
  ~t.vs_halted /\ t.vs_labels = s.vs_labels /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at ci x) /\
  return_buf_frame d cenv ci t /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!n b sz. local_region cenv es.scopes s n b sz <=>
            local_region cenv ee.scopes t n b sz) /\
  wb_frame cenv es ee si s t /\
  (!x. not_fresh_at si x ==>
     (!w. lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
     FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!aid b cap. FLOOKUP s.vs_allocas aid = SOME (b,cap) /\ aid < si.cs_next_id /\
     (!n lb sz. local_region cenv es.scopes s n lb sz ==> b+cap <= lb \/ lb+sz <= b) ==>
     mem_bytes_at b cap t.vs_memory = mem_bytes_at b cap s.vs_memory /\
     (!i. b <= i /\ i < b+cap /\ i IN tn1.t_mem ==> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac raw_post_read >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `body_const_cells_agree_mods mods cx env (es with gas_obs := gs)` by simp[] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[bind_def] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  `ci_mono si ci` by
    (qspecl_then [`cenv`,`expr_type e`,`e`,`si`] mp_tac (cj 1 compile_expr_ci_mono) >> simp[]) >>
  `local_ptrs_reserved cenv ci` by
    (irule compiler_ci_mono_reserved >> qexists `si` >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at ci x` by
    (drule (cj 1 compiler_compile_var) >> simp[]) >>
  `wb_frame cenv es ee si s t` by
    (qhdtm_assum `vv_post_mods` mp_tac >>
     pure_rewrite_tac[vv_post_mods_def,wb_frame_def] >> strip_tac >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by fs[wb_frame_def,locals_kept_def] >>
  drule_all_then assume_tac wb_frame_local_regions >>
  `~t.vs_halted` by (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  drule_then assume_tac gas_origin_ptr_path_preserves_labels >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee t` by
    fs[vv_post_mods_def] >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  `return_buf_frame d cenv ci t` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`s`,`si`] >>
     fs[wb_frame_def,ci_mono_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists `v` >> simp[])
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      fs[vv_post_mods_def])
  >- (rpt strip_tac >> fs[wb_frame_def,ghost_kept_at_def])
  >- fs[wb_frame_def] >>
  rpt gen_tac >> strip_tac >> drule_all head_old_window >> simp[]
QED
