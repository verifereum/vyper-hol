(* Evaluate the positional head once and pass its successful read to the
   snapshot suffix at the actual child endpoint. *)
Theory bodyExtPosAggregateHeadMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  exprSimMemorySource bodyPtrAttributeSource haltExitProj stmtSimProps exprSimDefs
  vyperStorageTrace vyperStorageFootprint loweringPosts bodyPtrDefs exprSimMemDefs
  gasOutcomeFullMods gasOutcomeFullPostPathMods gasOutcome gasContext gasSummary
  fragExec fragGasOriginPtr bodyFullIfExpReach venomExecSemantics contextRawReachable
  unitTransformDefs exprSimHypsDefs bodyInvSplit
  bodyExtPosSavedRowMods bodyExtPosAggregateCopyMods bodyExtPosAggregateRetainedMods
  exprLowering compileEnv venomState vyperInterpreter vyperState words
Libs monadsyntax

Theorem aggregate_raw_read[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s ==>
  ?v. read_result cx tv ee = (INL v,ee)
Proof
  simp[vv_post_mods_def] >> strip_tac >> Cases_on `vv`
  >- fs[vv_holds_mods_def,vv_holds_def] >>
  rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location = LocCode`
  >- fs[vv_holds_mods_def,immutable_holds_mods_def,immutable_holds_def] >>
  fs[vv_holds_mods_def] >> drule_then strip_assume_tac attribute_vv_holds_read_operand >> simp[]
QED

val head_entry = ``
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_sm) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\ immutable_frame_mods func ce cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

val head_exit = ``\(H : (bool # 256 word # type_value) list # num list)
    (res : value + vyperState$exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

val head_raw_post = ``
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list)) lo d ce cx ee G tn s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
  (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn``;

Theorem ext_pos_aggregate_read_bind[local]:
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\ ^head_entry /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!marks tv v ee G tn s.
    eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,ee) /\
    ee.gas_obs = [] /\ storage_trace_domain cx st0 ee.storage_trace /\ ~s.vs_halted /\
    read_result cx tv ee = (INL v,ee) /\
    (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> ^head_raw_post) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      ce.ce_modules cx st0 (read_result cx tv) (ee,s,G,tn) Q (^head_exit)) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    ce.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) Q (^head_exit)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`] mp_tac o
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
  qexists_tac `\H res ee G tn s. childQ H res ee G tn s /\ ee.gas_obs = [] /\ ~s.vs_halted /\
     (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z)` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >> irule_at Any gas_outcome_full_mods_post_path >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      qexists_tac `\H res ee G tn s. childQ H res ee G tn s /\
        (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z)` >>
      conj_tac
      >- (BETA_TAC >> rpt gen_tac >> strip_tac >> simp[] >>
          drule gas_origin_ptr_path_dalloca_fmp_headroom >>
          disch_then (fn th => rpt gen_tac >> disch_tac >> irule th) >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          qexists_tac `fn` >> first_assum ACCEPT_TAC) >>
      conj_tac
      >- (BETA_TAC >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
          rpt conj_tac >> first_assum ACCEPT_TAC) >>
      rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`,expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "read"
QED

Resume ext_pos_aggregate_read_bind[read]:
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
  drule_then strip_assume_tac aggregate_raw_read >>
  disj1_tac >> qexists_tac `tv` >> simp[] >>
  qpat_assum `!marks tv v ee G tn s. eval_expr _ _ _ = _ /\ _ ==> _`
    (qspecl_then [`marks`,`tv`,`v`,`ee`,`G`,`tn`,`s`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> qx_gen_tac `H` >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> (?r. _ = INL r /\ _) /\ _`
      (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [sumTheory.INL_11]) >>
    gvs[])) >>
  disch_then ACCEPT_TAC
QED

Finalise ext_pos_aggregate_read_bind

(* The saved row and its frames refer to the same snapshot endpoint. *)
fun head_frame reach = ``
  ext_pos_saved_row_mods lo ce cx (xs ++ kw_es) sa ss
    (H : (bool # 256 word # type_value) list # num list) e sv v ee Gu tu u /\
  stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
  storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce ss u /\
  ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu /\ alloca_history func u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  ^reach /\ ~u.vs_halted /\ u.vs_current_bb = ss.cs_current_bb /\ u.vs_inst_idx = LENGTH ss.cs_current_insts /\
  wb_frame ce es ee sa s0 u /\ (~expr_has_effect e ==> pure_frame ce func es sa s0 u) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b)``;

val head_reach = ``!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z``;
val head_copy_frame = head_frame head_reach;
val head_retained_frame = head_frame ``T``;

Theorem ext_pos_aggregate_head_mods:
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (expr_type e) /\
  compile_snapshot_vv ce (exprs_can_mutate ce (xs ++ kw_es))
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
  fn_has_code sm ss func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (exprs_can_mutate ce (xs ++ kw_es) ==>
    ~is_word_type (lowered_value_type ce e) /\
    type_memory_bytes ce (lowered_value_type ce e) < dimword (:256)) /\
  (~exprs_can_mutate ce (xs ++ kw_es) ==>
    ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv))) /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\ ^head_entry ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    ce.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee Gu tu u. ?v. res = INL v /\ ^head_copy_frame)
    (^head_exit)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule ext_pos_aggregate_read_bind >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`d`,`sa`,`shadow_func`,`shadow_sa`,`shadow_sm`,`sm`,`vv`] >>
  asm_rewrite_tac[] >>
  qx_genl_tac [`marks`,`tv`,`v`,`ee`,`G`,`tn`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `?u Gu tu. !H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s,G,tn) [] (OK u,Gu,tu) /\ ^head_copy_frame` by
    (Cases_on `exprs_can_mutate ce (xs ++ kw_es)` >> fs[]
     >- (irule ext_pos_aggregate_copy_landing_mods >> simp[] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac
         >- (qexistsl_tac [`gas_explicit marks s0.vs_gas_readings`,`tv`] >>
             simp[] >> gen_tac >> disch_tac >>
             qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
               (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
             simp[] >> strip_tac >> first_x_assum drule >> simp[]) >>
         qexistsl_tac [`env`,`mods`] >> first_assum ACCEPT_TAC) >>
     `?u Gu tu. !H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s,G,tn) [] (OK u,Gu,tu) /\ ^head_retained_frame` by
       (pure_rewrite_tac[AND_CLAUSES] >> irule ext_pos_aggregate_retained_landing_mods >>
        simp[] >> conj_tac
        >- (qexistsl_tac [`gas_explicit marks s0.vs_gas_readings`,`tv`] >>
            simp[] >> gen_tac >> disch_tac >>
            qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
              (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
            simp[] >> strip_tac >> first_x_assum drule >> simp[]) >>
        qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> asm_rewrite_tac[]) >>
     qexistsl_tac [`u`,`Gu`,`tu`] >> gen_tac >> disch_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     `^head_reach` by
       (drule gas_origin_ptr_path_dalloca_fmp_headroom >>
        disch_then (fn th => rpt gen_tac >> disch_tac >> irule th) >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexists_tac `fn` >> first_assum ACCEPT_TAC) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[gas_outcome_full_mods_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL v`,`ee`,`OK u`,`Gu`,`tu`] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  simp[] >> conj_tac >- (drule_then ACCEPT_TAC read_result_gas_obs) >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
