(* Physical capture at the delayed-read seam. *)
Theory createCtorTupleCapture
Ancestors
  createCtorTupleCaptureSource exprSimHyps aggregateCountedOutcome
  exprSimUnwrap exprSimSource vyperTypeExprSoundness
  vyperState vyperInterpreter gasStorage gasSummary fragGasPath
  exprLowering context compileEnv gasExemptCert vyperStorageTrace exprSimDefs
  loweringPosts vvOrigin exprLoweringProps gasOutcome vyperStorageFootprint
  exprSimMemorySource valueEncodingTyping fragGasMode
  createCtorTupleCaptureFrame exprSimWordArgs

Theorem ctor_capture_singleton_from_boundaries:
  (!ce cx env e es_eval es_child es_capture raw value ca cb vv origin endpoint s.
    expr_body_pre ce cx env e es_eval /\
    compile_expr ce (expr_type e) e ca = (vv,cb) /\
    eval_expr cx e es_eval = (INL raw,es_child) /\
    read_result cx raw es_capture = (INL value,es_capture) /\
    (~is_word_type (expr_type e) ==>
      ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
           value_has_type tv value /\ val_wf tv value) /\
    vv_holds ce cx (post_value_type ce e) raw vv es_capture s /\
    vv_at ce cx (post_value_type ce e) origin endpoint es_capture raw vv s ==>
    vv_holds ce cx (lowered_value_type ce e) raw vv es_capture s /\
    vv_at ce cx (lowered_value_type ce e) origin endpoint es_capture raw vv s) /\
  expr_body_pre ce cx env e es /\
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  compile_multi_vvs compile_expr ce [e] c1 = ([vv],c_vvs) /\
  fn_has_code c1 c_vvs func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce c1 /\ ci_mono c1 c_vvs /\
  (!x. vv_operand vv = Var x ==> not_fresh_at c_vvs x) /\
  (!l. vv_operand vv <> Label l) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s_buf /\
    storage_well_formed_on cx es (FST H)) /\
  ~s_buf.vs_halted /\
  s_buf.vs_current_bb = c1.cs_current_bb /\
  s_buf.vs_inst_idx = LENGTH c1.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr_results cx [e])
      (\raws. bind (read_results cx raws) (\values. return (raws,values))))
    (es,s_buf)
    (\H res ee t. ?raw value tv.
      res = INL ([raw],[value]) /\
      vv_holds ce cx (lowered_value_type ce e) raw vv ee t /\
      vv_at ce cx (lowered_value_type ce e) c1 c_vvs ee raw vv t /\
      read_result cx raw ee = (INL value,ee) /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      value_has_type tv value /\ val_wf tv value /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      alloca_inv t /\ alloca_room ctx func t /\ local_ptrs_reserved ce c_vvs /\
      t.vs_current_bb = c_vvs.cs_current_bb /\
      t.vs_inst_idx = LENGTH c_vvs.cs_current_insts /\
      (!x. vv_operand vv = Var x ==> not_fresh_at c_vvs x) /\
      (!l. vv_operand vv <> Label l) /\
      (!x w. not_fresh_at c1 x /\ lookup_var x s_buf = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s_buf.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!aid off sz. FLOOKUP s_buf.vs_allocas aid = SOME (off,sz) /\
        aid < c1.cs_next_id /\
        (!n b sz'. local_region ce es.scopes s_buf n b sz' ==>
          off + sz <= b \/ b + sz' <= off) ==>
        mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s_buf.vs_memory))
    (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >>
  `compile_expr ce (expr_type e) e c1 = (vv,c_vvs)` by
    (Cases_on `compile_expr ce (expr_type e) e c1` >>
     gvs[compile_multi_vvs_def, comp_bind_def, comp_return_def]) >>
  drule_all ctor_capture_singleton_raw_outcome >> strip_tac >>
  irule counted_outcome_bind_exec >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_results, storage_trace_frame_return]) >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_results >> goal_assum (drule_at Any) >>
      gvs[GSYM ignore_bind_def]) >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_results >> simp[]) >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `res` >> gvs[oneline expr_exit_def, halt_exit_def, AllCaseEqs()]) >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `storage_trace_domain cx st0 mid.storage_trace`
      >- (qpat_assum `!H. _ ==> ?raw. _`
            (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
          (impl_tac >- gvs[storage_trace_domain_def]) >> strip_tac >> gvs[] >>
          Cases_on `read_result cx raw (mid with gas_obs := [])` >>
          rename1 `read_result cx raw (mid with gas_obs := []) = (rr,ee)` >>
          `ee = mid with gas_obs := []` by metis_tac[read_result_state] >>
          gvs[] >> Cases_on `rr`
          >- suspend "normal_read" >>
          metis_tac[vv_post_failed_read]) >>
      rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >> simp[] >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_results, storage_trace_frame_return]) >>
  rpt strip_tac >> gvs[]
QED

Resume ctor_capture_singleton_from_boundaries[normal_read]:
  rename1 `read_result cx raw (mid with gas_obs := []) = (INL value,_)` >>
  `value_runtime_typed env (lowered_value_type ce e) value` by
    (irule memory_rhs_read_lowered_typed_unwidened >>
     qexistsl [`cx`, `es with gas_obs := gs`, `mid with gas_obs := []`] >>
     simp[bind_def]) >>
  `env.type_defs = get_tenv cx` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def,
          exprSimHypsDefsTheory.expr_sim_inv_def,
          vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  gvs[value_runtime_typed_def] >>
  `val_wf tv value` by metis_tac[value_has_type_val_wf] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `local_ptrs_reserved ce c_vvs` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  qpat_assum `read_result _ _ _ = (INL _,_)`
    (mp_tac o MATCH_MP read_result_gas_obs) >> simp[] >> strip_tac >>
  rewrite_tac[gas_outcome_def] >> qexists `[]` >>
  disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INL ([raw],[value])`, `mid`, `OK t`] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
          read_results_def, bind_def, return_def] >>
  disj1_tac >> qexists `t` >>
  conj_tac >- simp[] >> BETA_TAC >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  gvs[vv_post_def] >>
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  `read_result cx raw (mid with gas_obs := []) =
     (INL value,mid with gas_obs := [])` by simp[] >>
  `~is_word_type (expr_type e) ==>
     ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
          value_has_type tv value /\ val_wf tv value` by metis_tac[] >>
  qpat_x_assum `!ce cx env e es_eval es_child es_capture raw value ca cb vv origin endpoint s. _`
    drule_all >> strip_tac >>
  gvs[stmt_state_rel_def] >> metis_tac[]
QED

Finalise ctor_capture_singleton_from_boundaries

(* All delayed reads are performed at the same captured source state. *)
Theorem ctor_capture_reads_indexed[local]:
  !raws values.
    LENGTH raws = LENGTH values /\
    (!i. i < LENGTH raws ==>
      read_result cx (EL i raws) es = (INL (EL i values),es)) ==>
    read_results cx raws es = (INL values,es)
Proof
  Induct >> Cases_on `values` >> simp[read_results_def, return_def] >>
  rpt strip_tac >>
  rename1 `read_result cx raw` >>
  `read_result cx raw es = (INL h,es)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `read_results cx raws es = (INL t,es)` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
  simp[read_results_def, bind_def, return_def]
QED

(* Raw evaluation retains a suffix-wide frame, so the head can be rebased
   without a growing accumulator of earlier compilation witnesses. *)
Theorem ctor_capture_pure_raw[local]:
  !args c1 vvs c_vvs es s_buf.
  (!ce cx env e es_eval es_child es_capture raw value ca cb vv origin endpoint s.
    expr_body_pre ce cx env e es_eval /\
    compile_expr ce (expr_type e) e ca = (vv,cb) /\
    eval_expr cx e es_eval = (INL raw,es_child) /\
    read_result cx raw es_capture = (INL value,es_capture) /\
    (~is_word_type (expr_type e) ==>
      ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
           value_has_type tv value /\ val_wf tv value) /\
    vv_holds ce cx (post_value_type ce e) raw vv es_capture s /\
    vv_at ce cx (post_value_type ce e) origin endpoint es_capture raw vv s ==>
    vv_holds ce cx (lowered_value_type ce e) raw vv es_capture s /\
    vv_at ce cx (lowered_value_type ce e) origin endpoint es_capture raw vv s) /\
  EVERY (\e. ~expr_has_effect e) args /\
  expr_sim_inv ce cx env es /\
  (!e ea. MEM e args /\ expr_sim_inv ce cx env ea ==>
    expr_body_pre ce cx env e ea /\
    expr_vv_sim ctx func ce cx (expr_type e) e ea /\
    gas_admissible (eval_expr cx e) expr_vv_res_ok ea) /\
  compile_multi_vvs compile_expr ce args c1 = (vvs,c_vvs) /\
  fn_has_code c1 c_vvs func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce c1 /\ ci_mono c1 c_vvs /\
  (!e ca cb vv. MEM e args /\
    compile_expr ce (expr_type e) e ca = (vv,cb) ==>
    (!x. vv_operand vv = Var x ==> not_fresh_at cb x) /\
    (!l. vv_operand vv <> Label l)) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s_buf /\
    storage_well_formed_on cx es (FST H)) /\
  ~s_buf.vs_halted /\
  s_buf.vs_current_bb = c1.cs_current_bb /\
  s_buf.vs_inst_idx = LENGTH c1.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (eval_expr_results cx args) (es,s_buf)
    (\H res ee t. ?raws values.
      res = INL raws /\
      LENGTH vvs = LENGTH args /\
      LENGTH raws = LENGTH args /\ LENGTH values = LENGTH args /\
      (!i. i < LENGTH args ==>
        vv_holds ce cx (lowered_value_type ce (EL i args))
          (EL i raws) (EL i vvs) ee t /\
        vv_at ce cx (lowered_value_type ce (EL i args)) c1 c_vvs ee
          (EL i raws) (EL i vvs) t /\
        read_result cx (EL i raws) ee = (INL (EL i values),ee) /\
        (?tv. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
          value_has_type tv (EL i values) /\ val_wf tv (EL i values) /\
          type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size tv) /\
        (!x. vv_operand (EL i vvs) = Var x ==> not_fresh_at c_vvs x) /\
        (!l. vv_operand (EL i vvs) <> Label l)) /\
      stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      alloca_inv t /\ alloca_room ctx func t /\ local_ptrs_reserved ce c_vvs /\
      t.vs_current_bb = c_vvs.cs_current_bb /\
      t.vs_inst_idx = LENGTH c_vvs.cs_current_insts /\
      expr_sim_inv ce cx env ee /\ wb_frame ce es ee c1 s_buf t /\
      ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
        es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>)
    (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  Induct >> rpt gen_tac
  >- (simp[compile_multi_vvs_def, comp_return_def] >> strip_tac >> gvs[] >>
      simp[evaluate_def] >> irule counted_outcome_return >> simp[] >>
      rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >>
      simp[wb_frame_refl, stmt_state_rel_def, storage_well_formed_on_backends] >>
      rpt strip_tac >>
      `storage_well_formed_on cx (es with gas_obs := []) (FST H) =
       storage_well_formed_on cx es (FST H)` by
        (irule storage_well_formed_on_backends >> simp[]) >> simp[]) >>
  strip_tac >>
  Cases_on `compile_expr ce (expr_type h) h c1` >>
  rename1 `compile_expr ce (expr_type h) h c1 = (head_vv,cm)` >>
  Cases_on `compile_multi_vvs compile_expr ce args cm` >>
  rename1 `compile_multi_vvs compile_expr ce args cm = (tail_vvs,cend)` >>
  gvs[compile_multi_vvs_def, comp_bind_def, comp_return_def] >>
  `ci_mono c1 cm` by
    (qspecl_then [`ce`,`expr_type h`,`h`,`c1`] mp_tac
       (cj 1 compile_expr_ci_mono) >> simp[]) >>
  `ci_mono cm c_vvs` by
    (qspecl_then [`compile_expr`,`ce`,`args`,`cm`] mp_tac
       ci_mono_compile_multi_vvs >> simp[compile_expr_ci_mono]) >>
  `fn_has_code c1 cm func /\ fn_has_code cm c_vvs func` by
    metis_tac[fragExecTheory.fn_has_code_split, ci_mono_def] >>
  `local_ptrs_reserved ce cm` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `expr_body_pre ce cx env h es /\
   expr_vv_sim ctx func ce cx (expr_type h) h es /\
   gas_admissible (eval_expr cx h) expr_vv_res_ok es` by metis_tac[] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`st0`,`c1`,`cm`,`head_vv`,`s_buf`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[Once evaluate_def] >> irule counted_outcome_bind_exec >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_result >> goal_assum (drule_at Any) >>
      gvs[GSYM ignore_bind_def]) >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_result >> simp[]) >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `res` >>
      gvs[oneline expr_exit_def, halt_exit_def, AllCaseEqs()]) >>
  conj_tac >- suspend "head_cont" >>
  rpt strip_tac >> gvs[]
QED

Resume ctor_capture_pure_raw[head_cont]:
  rpt strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 mid.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >> simp[] >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- gvs[storage_trace_domain_def]) >> strip_tac >>
  `eval_expr cx h (es with gas_obs := gas_explicit marks s_buf.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  Cases_on `read_result cx v (mid with gas_obs := [])` >>
  rename1 `read_result cx v (mid with gas_obs := []) = (rr,ee)` >>
  `ee = mid with gas_obs := []` by metis_tac[read_result_state] >>
  gvs[] >> Cases_on `rr`
  >- suspend "head_read" >>
  metis_tac[vv_post_failed_read]
QED

Resume ctor_capture_pure_raw[head_read]:
  rename1 `read_result cx v (mid with gas_obs := []) = (INL value,_)` >>
  `expr_body_pre ce cx env h (es with gas_obs := gas_explicit marks s_buf.vs_gas_readings)` by
    (simp[] >> metis_tac[]) >>
  `expr_sim_inv ce cx env (mid with gas_obs := [])` by
    (drule_all expr_body_pre_eval_result >> simp[]) >>
  `value_runtime_typed env (lowered_value_type ce h) value` by
    (irule memory_rhs_read_lowered_typed_unwidened >>
     qexistsl [`cx`, `es with gas_obs := gas_explicit marks s_buf.vs_gas_readings`,
               `mid with gas_obs := []`] >> simp[bind_def]) >>
  `env.type_defs = get_tenv cx` by
    metis_tac[exprSimHypsDefsTheory.expr_body_pre_def,
      exprSimHypsDefsTheory.expr_sim_inv_def,
      vyperTypeInvariantsTheory.env_consistent_def,
      vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[value_runtime_typed_def] >>
  `val_wf tv value` by metis_tac[value_has_type_val_wf] >>
  `mid with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
   es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>` by
    (drule_all targetPureSourceFrameTheory.effect_free_source_projection >> simp[]) >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func ce cx (mid with gas_obs := []) t /\
     storage_well_formed_on cx (mid with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     pure_rewrite_tac[vv_post_def] >> strip_tac >> simp[]) >>
  qpat_x_assum `!c1' vvs' c_vvs' es' s_buf'. _`
    (qspecl_then [`cm`,`tail_vvs`,`c_vvs`,`mid with gas_obs := []`,`t`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (mk_asm "tail_outcome") >>
  irule counted_outcome_bind_exec >>
  conj_tac >- simp[storage_trace_frame_return] >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_results >> goal_assum (drule_at Any) >>
      gvs[GSYM ignore_bind_def]) >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_results >> simp[]) >>
  asm_x "tail_outcome" assume_tac >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `res` >>
      gvs[oneline expr_exit_def, halt_exit_def, AllCaseEqs()]) >>
  conj_tac >- suspend "tail_cont" >>
  rpt strip_tac >> gvs[]
QED

Resume ctor_capture_pure_raw[tail_cont]:
  rpt strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 mid'.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >> simp[storage_trace_frame_return]) >>
  `~t'.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `eval_expr_results cx args
     (mid with gas_obs := gas_explicit marks' t.vs_gas_readings) =
     (INL v',mid' with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_expr_results _ _) _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `eval_expr_results _ _ _ = _`
       (mp_then Any mp_tac valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame]) >>
  irule counted_outcome_return >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> ?values. _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  pure_rewrite_tac[vv_post_def] >> strip_tac >>
  suspend "tail_join"
QED

Resume ctor_capture_pure_raw[tail_join]:
  `expr_body_pre ce cx env h
     (es with gas_obs := gas_explicit marks s_buf.vs_gas_readings)` by
    (simp[] >> metis_tac[]) >>
  `~is_word_type (expr_type h) ==>
    ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce h) = SOME tv /\
         value_has_type tv value /\ val_wf tv value` by metis_tac[] >>
  qpat_x_assum `!ce cx env e es_eval es_child es_capture raw value ca cb vv origin endpoint s. _`
    drule_all >> strip_tac >>
  `(!x. vv_operand head_vv = Var x ==> not_fresh_at cm x) /\
   (!l. vv_operand head_vv <> Label l)` by metis_tac[] >>
  `vv_holds ce cx (lowered_value_type ce h) v head_vv (mid' with gas_obs := []) t' /\
   vv_at ce cx (lowered_value_type ce h) c1 c_vvs (mid' with gas_obs := []) v head_vv t' /\
   read_result cx v (mid' with gas_obs := []) = (INL value,mid' with gas_obs := []) /\
   vv_storage_live H cx head_vv (mid' with gas_obs := []) t'` by
    (irule ctor_capture_live_frame >>
     qexistsl [`ctx`,`cm`,`cm`,`mid with gas_obs := []`,`func`,`t`] >>
     simp[ci_mono_def] >>
     Cases_on `head_vv` >> gvs[vv_operand_def, ci_mono_def]) >>
  `wb_frame ce es (mid with gas_obs := []) c1 s_buf t` by
    (rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H ctx func ce cx es s_buf` by
    (qpat_assum `eval_expr cx h _ = _` (mp_then Any mp_tac valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame] >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    gvs[evaluation_state_component_equality] >>
  `wb_frame ce es (mid' with gas_obs := []) c1 s_buf t'` by
    (qpat_assum `stmt_state_rel H ctx func ce cx es s_buf`
       (mp_then Any irule wb_frame_trans) >> simp[] >>
     qexistsl [`mid with gas_obs := []`,`cm`,`t`] >>
     simp[] >> gvs[ci_mono_def]) >>
  qexists `value::values` >> simp[] >>
  reverse conj_tac
  >- gvs[evaluation_state_component_equality] >>
  Cases >> simp[]
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists `cm` >> simp[] >> gvs[ci_mono_def]) >>
  strip_tac >>
  qpat_x_assum `!i. i < LENGTH args ==> _` drule >> strip_tac >>
  simp[] >> irule vv_at_start_mono >> qexists `cm` >> simp[] >> gvs[ci_mono_def]
QED

Finalise ctor_capture_pure_raw

Theorem ctor_capture_pure_from_boundaries:
  (!ce cx env e es_eval es_child es_capture raw value ca cb vv origin endpoint s.
    expr_body_pre ce cx env e es_eval /\
    compile_expr ce (expr_type e) e ca = (vv,cb) /\
    eval_expr cx e es_eval = (INL raw,es_child) /\
    read_result cx raw es_capture = (INL value,es_capture) /\
    (~is_word_type (expr_type e) ==>
      ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
           value_has_type tv value /\ val_wf tv value) /\
    vv_holds ce cx (post_value_type ce e) raw vv es_capture s /\
    vv_at ce cx (post_value_type ce e) origin endpoint es_capture raw vv s ==>
    vv_holds ce cx (lowered_value_type ce e) raw vv es_capture s /\
    vv_at ce cx (lowered_value_type ce e) origin endpoint es_capture raw vv s) /\
  EVERY (\e. ~expr_has_effect e) args /\
  expr_sim_inv ce cx env es /\
  (!e ea. MEM e args /\ expr_sim_inv ce cx env ea ==>
    expr_body_pre ce cx env e ea /\
    expr_vv_sim ctx func ce cx (expr_type e) e ea /\
    gas_admissible (eval_expr cx e) expr_vv_res_ok ea) /\
  compile_multi_vvs compile_expr ce args c1 = (vvs,c_vvs) /\
  fn_has_code c1 c_vvs func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce c1 /\ ci_mono c1 c_vvs /\
  (!e ca cb vv. MEM e args /\
    compile_expr ce (expr_type e) e ca = (vv,cb) ==>
    (!x. vv_operand vv = Var x ==> not_fresh_at cb x) /\
    (!l. vv_operand vv <> Label l)) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s_buf /\
    storage_well_formed_on cx es (FST H)) /\
  ~s_buf.vs_halted /\
  s_buf.vs_current_bb = c1.cs_current_bb /\
  s_buf.vs_inst_idx = LENGTH c1.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr_results cx args)
      (\raws. bind (read_results cx raws) (\values. return (raws,values))))
    (es,s_buf)
    (\H res ee t. ?raws values.
      res = INL (raws,values) /\
      LENGTH vvs = LENGTH args /\
      LENGTH raws = LENGTH args /\ LENGTH values = LENGTH args /\
      (!i. i < LENGTH args ==>
        vv_holds ce cx (lowered_value_type ce (EL i args))
          (EL i raws) (EL i vvs) ee t /\
        vv_at ce cx (lowered_value_type ce (EL i args)) c1 c_vvs ee
          (EL i raws) (EL i vvs) t /\
        read_result cx (EL i raws) ee = (INL (EL i values),ee) /\
        (?tv. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
          value_has_type tv (EL i values) /\ val_wf tv (EL i values) /\
          type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size tv) /\
        (!x. vv_operand (EL i vvs) = Var x ==> not_fresh_at c_vvs x) /\
        (!l. vv_operand (EL i vvs) <> Label l)) /\
      stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      alloca_inv t /\ alloca_room ctx func t /\ local_ptrs_reserved ce c_vvs /\
      t.vs_current_bb = c_vvs.cs_current_bb /\
      t.vs_inst_idx = LENGTH c_vvs.cs_current_insts /\
      (!x w. not_fresh_at c1 x /\ lookup_var x s_buf = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s_buf.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!aid off sz. FLOOKUP s_buf.vs_allocas aid = SOME (off,sz) /\
        aid < c1.cs_next_id /\
        (!n b sz'. local_region ce es.scopes s_buf n b sz' ==>
          off + sz <= b \/ b + sz' <= off) ==>
        mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s_buf.vs_memory))
    (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >> drule_all ctor_capture_pure_raw >> strip_tac >>
  irule counted_outcome_bind_exec >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_results, storage_trace_frame_return]) >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_results >> goal_assum (drule_at Any) >>
      gvs[GSYM ignore_bind_def]) >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_results >> simp[]) >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `res` >>
      gvs[oneline expr_exit_def, halt_exit_def, AllCaseEqs()]) >>
  conj_tac >- suspend "delayed_reads" >>
  rpt strip_tac >> gvs[]
QED

Resume ctor_capture_pure_from_boundaries[delayed_reads]:
  rpt strip_tac >>
  rename1 `gas_marked_exec _ _ _ _ _ (INL raws) _ _` >>
  reverse (Cases_on `storage_trace_domain cx st0 mid.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >> simp[] >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_results, storage_trace_frame_return]) >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> ?values. _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- gvs[storage_trace_domain_def]) >> strip_tac >> gvs[] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `!gs. read_results cx raws (mid with gas_obs := gs) =
    (INL values,mid with gas_obs := gs)` by
    (gen_tac >> irule ctor_capture_reads_indexed >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH args ==> _` drule >> strip_tac >>
     qpat_assum `read_result _ _ _ = (INL _,_)`
       (mp_tac o MATCH_MP read_result_gas_obs) >> simp[]) >>
  rewrite_tac[gas_outcome_def] >> qexists `[]` >>
  disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INL (raws,values)`,`mid`,`OK t`] >> conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
          bind_def, return_def] >>
  disj1_tac >> qexists `t` >> conj_tac >- simp[] >> BETA_TAC >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  gvs[wb_frame_def] >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!i. i < LENGTH args ==> _` drule >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Finalise ctor_capture_pure_from_boundaries
