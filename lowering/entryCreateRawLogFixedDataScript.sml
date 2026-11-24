(* Fixed data is read after the actual scratch allocation, and only its
   normal first exit starts the MSTORE/LOG continuation. *)
Theory entryCreateRawLogFixedData
Ancestors
  bodyFullRawLogFixedCompose exprSimExtract32Post entryCreateRawStageJoins
  entryCreateScopedBind entryCreateReplayBind entryCreateNeutralVisitCut
  entryCreateFocusSpec entryCreateCompletedCut venomExecSemantics
  entryCreateIntervalLayout createSizeOperandCode
  entryIntCallStageNeutral entryCreateNativeFirstExit createSizeCutOpens
  fragGasOriginPtrExec exprSimFullBundleProps vyperStorageTrace
  vyperStorageFootprint vyperInterpreter vyperState vyperValue vyperEvent
  exprSimDefs gasContext gasExemptCert gasSummary gasOutcomeFullCompose
  loweringPosts bodyPtrDefs exprLoweringProps exprOperandVar fragExec
  exprSimMemDefs stmtSimDefs fragGasOriginPtr s1PrefixDefs fragGasOrigin
  gasShadowState gasExplicitSites createSizeCutCode createSizeCutRegion
  gasShadow compileEnv emitHelper words list arithmetic finite_map pred_set
  emitHelperProps entryCreateBodyCut entryCreateAdminSequence freshWrites
  bodyFullHashKeccakFixed bodyFullIfExpReach bodyFullRawLogFixedTransport gasOutcomeFull
  abiBufferAllocationCode deadStoreElimStructure abiEncoderProps venomInst venomWf
  venomExecProofs tupleLoadProps loweringShapeProps
Libs pairLib

Definition raw_log_fixed_next_def:
  raw_log_fixed_next cx vals v =
    do bs <- lift_option_type (dest_BytesV v) "raw_log data";
       type_check (LENGTH vals <= 4) "raw_log too many topics";
       check_not_static cx;
       push_log (encode_raw_event_values cx.txn.target vals bs);
       return NoneV
    od
End

Theorem raw_log_fixed_next_frame[local]:
  storage_trace_frame (raw_log_fixed_next cx vals v)
Proof
  rewrite_tac[raw_log_fixed_next_def] >>
  match_mp_tac storage_trace_frame_bind_all >>
  conj_tac >- simp[storage_trace_frame_lifts] >>
  gen_tac >> BETA_TAC >> match_mp_tac storage_trace_frame_ignore_bind >>
  conj_tac >- simp[storage_trace_frame_checks] >>
  match_mp_tac storage_trace_frame_ignore_bind >>
  conj_tac >- simp[storage_trace_frame_check_not_static] >>
  match_mp_tac storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_state_updates, storage_trace_frame_return]
QED

Theorem raw_log_fixed_exit_exception[local]:
  create_operand_exit_post ctx cx H res ee gt r ==>
  ?exc. res = INR exc
Proof
  Cases_on `res` >> Cases_on `r` >>
  simp[create_operand_exit_post_def, expr_exit_def]
QED

Theorem raw_log_fixed_exit_guard[local]:
  (\H res ee gt r. (?exc. res = INR exc) /\ create_operand_exit_post ctx cx H res ee gt r) =
    create_operand_exit_post ctx cx
Proof
  simp[FUN_EQ_THM] >> metis_tac[raw_log_fixed_exit_exception]
QED

Theorem raw_log_fixed_next_bytes[local]:
  gas_admissible (bind source (raw_log_fixed_next cx vals)) expr_res_ok es /\
  source (es with gas_obs := gs) = (INL v, mid) ==>
  ?bs. v = BytesV bs
Proof
  strip_tac >> Cases_on `dest_BytesV v`
  >- (qpat_x_assum `gas_admissible _ _ _` (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
      disch_then (qspec_then `gs` mp_tac) >>
      simp[raw_log_fixed_next_def, bind_def, lift_option_type_def,
           lift_option_def, raise_def, expr_res_ok_def]) >>
  qpat_x_assum `dest_BytesV v = SOME _` mp_tac >>
  Cases_on `v` >> simp[dest_BytesV_def]
QED

Theorem raw_log_fixed_next_eval[local]:
  LENGTH vals <= 4 ==>
  raw_log_fixed_next cx vals (BytesV bs) mid =
    (if cx.txn.is_static then
       (INR (Error (RuntimeError "write in static context")),mid)
     else (INL NoneV,
       mid with logs := mid.logs ++ [encode_raw_event_values cx.txn.target vals bs]))
Proof
  strip_tac >> Cases_on `cx.txn.is_static` >>
  simp[raw_log_fixed_next_def, bind_def, lift_option_type_def, lift_option_def,
       dest_BytesV_def, ignore_bind_def, type_check_def, assert_def,
       push_log_def, return_def]
QED

(* Keep the pre-tail geometry common to the successful and static endpoints. *)
Definition raw_log_fixed_tail_ready_def:
  raw_log_fixed_tail_ready (DF,lo,d,ctx,func) cenv cx data
    (sa,sm,data_op,s0,es,G0,tn0) (buf,ops,vals,p,w)
    (bs,word,mid,t,G,tn) H <=>
    expr_post H ctx func cenv cx data es sa sm s0 mid (BytesV bs) data_op t /\
    expr_store_bound cx (expr_type data) (BytesV bs) data_op t /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn t /\
    ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G tn t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    LENGTH bs = 32 /\ eval_operand data_op t = SOME word /\
    TAKE 32 (word_to_bytes_be word) = bs /\
    buf.buf_operand = Var p /\ eval_operand buf.buf_operand t = SOME w /\
    ptr_covers G tn p t 32 /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\
    (!name b n. local_region cenv mid.scopes t name b n ==>
       regions_disjoint (w2n w) 32 b n) /\
    (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
       regions_disjoint (w2n w) 32 b n) /\
    eval_operands ops t = SOME (MAP event_value_to_word vals) /\
    EVERY (\op. op_taint tn op = {}) ops /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts
End

Definition raw_log_fixed_scratch_row_def:
  raw_log_fixed_scratch_row (DF,lo,d,ctx,func,explicit,PG) cenv cx
    (sa,sd,es,s,G,tn,buf) (u,Gu,tnu,p,w) H <=>
    create_operand_full_scope sa sd explicit ctx func s [] (OK u) /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tnu) /\
    stmt_state_rel H ctx func cenv cx es u /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es Gu tnu u /\ return_buf_frame d cenv sd u /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    buf.buf_operand = Var p /\ not_fresh_at sd p /\
    eval_operand buf.buf_operand u = SOME w /\ ptr_covers Gu tnu p u 32 /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\ u.vs_memory = s.vs_memory /\
    tnu.t_mem = tn.t_mem UNION new_site_bytes s u /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
       regions_disjoint (w2n w) 32 b n) /\
    (!name b n. local_region cenv es.scopes u name b n ==>
       regions_disjoint (w2n w) 32 b n) /\
    ghost_kept_at lo cenv es sa G tn s Gu tnu
End

Theorem fixed_log_scratch_child_pre[local]:
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    raw_log_fixed_scratch_row (DF,lo,d,ctx,func,gas_explicit_sites ctx shctx,PG)
      cenv cx (sa,sd,es,s0,G0,tn0,buf) (u,Gu,tnu,p,w) H) /\
  valid_horizon cx st0 H0 es.storage_trace /\
  ci_mono sa sd /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!fn inst t. frag_reachable ctx func s0 fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  gas_admissible (bind (eval_expr cx data) (read_result cx)) expr_res_ok es /\
  lower_value compile_expr cenv (expr_type data) data sd = (data_op,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type data)
    (gas_shadow_expr data) shd = (data_op,shm) /\
  expr_sim_full_code (ctx,shctx,func,shfunc) (sd,sm,shd,shm) ==>
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx (expr_type data) data es
    (st0,sd,sm,shd,shm,data_op,u,Gu,tnu)
Proof
  simp_tac bool_ss [expr_sim_full_pre_def,expr_sim_full_code_def,ci_mono_def] >>
  strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> raw_log_fixed_scratch_row _ _ _ _ _ _`
    (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  rewrite_tac[raw_log_fixed_scratch_row_def] >> strip_tac >>
  simp[] >> rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[])
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[])
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[])
  >- (qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
        (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp))
  >- (rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[raw_log_fixed_scratch_row_def]
QED

Theorem fixed_log_child_ready[local]:
  expr_body_pre cenv cx env (Call ann RawLog es_call dflt) es0 /\
  MEM data es_call /\ expr_sim_inv cenv cx env es /\
  bind (eval_expr cx data) (read_result cx) (es with gas_obs := gs) =
     (INL (BytesV bs),mid with gas_obs := []) /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  post_value_type cenv data = expr_type data /\
  evaluate_type (get_tenv cx) (expr_type data) = SOME (BaseTV (BytesT (Fixed 32))) /\
  compile_alloc_buffer 32 sa = (buf,sd) /\ ci_mono sa sd /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sd /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l)) ops /\
  eval_operands ops s0 = SOME (MAP event_value_to_word vals) /\
  EVERY (\op. op_taint tn0 op = {}) ops /\
  stmt_state_rel H ctx func cenv cx es s0 /\ ~t.vs_halted /\
  raw_log_fixed_scratch_row (DF,lo,d,ctx,func,E,PG) cenv cx
    (sa,sd,es,s0,G0,tn0,buf) (u,Gu,tnu,p,w) H /\
  expr_sim_full_post (DF,lo,d,ctx,func) cenv cx data (es,sd,sm,u,data_op,Gu,tnu)
    H (INL (BytesV bs)) mid G1 tn1 t ==>
  ?word. raw_log_fixed_tail_ready (DF,lo,d,ctx,func) cenv cx data
     (sa,sm,data_op,s0,es,G0,tn0) (buf,ops,vals,p,w) (bs,word,mid,t,G1,tn1) H
Proof
  simp_tac bool_ss [raw_log_fixed_scratch_row_def, expr_sim_full_post_def,
    expr_sim_full_endpoint_def, ci_mono_def, sumTheory.INL_11, UNWIND_THM1] >>
  strip_tac >>
  `expr_post H ctx func cenv cx data es sa sm s0 mid (BytesV bs) data_op t` by
    (irule raw_log_fixed_data_reanchor >> simp[] >> qexists_tac `u` >> simp[]) >>
  rewrite_tac[raw_log_fixed_tail_ready_def] >>
  irule raw_log_fixed_child_tail_input >>
  qpat_assum `ptr_covers Gu tnu p u 32` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ (Call _ RawLog _ _) _` (irule_at Any) >>
  qpat_assum `bind (eval_expr _ _) _ _ = _` (irule_at Any) >>
  rfs[] >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
QED

Theorem fixed_log_child_window[local]:
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  create_cut_code {} sd sm /\ fn_has_code sd sm func /\
  create_cut_code {} sm sb /\ fn_has_code sm sb func /\
  create_operand_cut sd sm E ctx func tops cx st0 source (es,u) /\
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
     i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts sm sb) ==>
  create_operand_cut sd sb E ctx func tops cx st0 (bind source next) (es,u)
Proof
  strip_tac >> simp[create_operand_cut_def] >> rpt gen_tac >> strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (irule create_cut_bind_left >> simp[] >> fs[create_operand_cut_def] >> metis_tac[]) >>
  `create_operand_cut sm sb E ctx func tops cx st0 (return ()) (es,t)` by
    (irule create_admin_sequence_cut >> simp[]) >>
  qpat_x_assum `create_operand_cut sm sb _ _ _ _ _ _ _ _`
    (drule_then mp_tac o REWRITE_RULE[create_operand_cut_def]) >>
  Cases_on `hit` >> PairCases_on `r` >>
  simp[create_body_cut_def, return_def, create_cut_failure_def] >>
  rpt strip_tac >>
  `storage_trace_frame (bind source next)` by simp[storage_trace_frame_bind_all] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_all valid_horizon_frame >> simp[]) >>
  metis_tac[]
QED

(* Once the actual child supplies its value and ghost pair, the primitive
   endpoints differ only in the selected static check. *)
Theorem fixed_log_scoped_tail[local]:
  LENGTH vals <= 4 /\ storage_trace_domain cx st0 mid.storage_trace /\
  (~cx.txn.is_static ==>
     ?u G2 tn2. !H. valid_horizon cx st0 H mid.storage_trace ==>
       create_operand_full_scope sm sb E ctx func t [] (OK u) /\
       gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (t,G,tn) [] (OK u,G2,tn2) /\
       Q H (INL NoneV)
          (mid with <|logs := mid.logs ++ [encode_raw_event_values cx.txn.target vals bs];
                      gas_obs := []|>) G2 tn2 u) /\
  (cx.txn.is_static ==>
     ?u G2 tn2. !H. valid_horizon cx st0 H mid.storage_trace ==>
       create_operand_full_scope sm sb E ctx func t [] (Abort ExHalt_abort u) /\
       gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (t,G,tn) [] (Abort ExHalt_abort u,G2,tn2)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sm sb
    (raw_log_fixed_next cx vals (BytesV bs)) (mid,t,G,tn) Q (create_operand_exit_post ctx cx)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  simp[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  Cases_on `cx.txn.is_static`
  >- (qpat_x_assum `cx.txn.is_static ==> _` drule >> strip_tac >>
      qexistsl_tac [`INR (Error (RuntimeError "write in static context"))`,
        `mid`,`Abort ExHalt_abort u`,`G2`,`tn2`] >>
      simp[raw_log_fixed_next_eval,exit_result_def,create_operand_exit_post_def,
           expr_exit_def,halt_exit_def] >> metis_tac[]) >>
  qpat_x_assum `~cx.txn.is_static ==> _` drule >> strip_tac >>
  qexistsl_tac [`INL NoneV`,
    `mid with logs := mid.logs ++ [encode_raw_event_values cx.txn.target vals bs]`,
    `OK u`,`G2`,`tn2`] >> simp[raw_log_fixed_next_eval,exit_result_def] >> metis_tac[]
QED

Theorem fixed_log_scoped_bind[local]:
  let source = bind (eval_expr cx data) (read_result cx) in
  let next = raw_log_fixed_next cx vals in
  let R = create_operand_exit_post ctx cx in
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sd sm
    source (es,u,Gu,tnu) Qdata R /\
  (!marks res mid G1 tn1 t.
     (!tail. source (es with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
       (res,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       Qdata H res mid G1 tn1 t /\
       gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (u,Gu,tnu) marks (OK t,G1,tn1)) ==>
     ?v. res = INL v /\ scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sm sb
       (next v) (mid,t,G1,tn1) Q R) /\
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  create_cut_code {} sd sm /\ create_cut_code {} sm sb /\ fn_has_code sd sb func /\
  create_layout sd sb /\ create_operand_at sd u ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sd sb
    (bind source next) (es,u,Gu,tnu) Q R
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all raw_create_scope_at_split >> disch_then (qspec_then `E` strip_assume_tac) >>
  irule scoped_operand_bind_all >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result,raw_log_fixed_next_frame] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
     pure_once_rewrite_tac[bind_assoc] >> irule gas_exempt_cert_bind_value >>
     qexistsl_tac [`mid`,`t`,`v`] >> fs[ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
     pure_once_rewrite_tac[bind_assoc] >> irule gas_exempt_cert_error_value >>
     simp[ignore_bind_def]) >>
  qexistsl_tac [`Qdata`,`sm`] >> pure_rewrite_tac[raw_log_fixed_exit_guard] >> simp[] >>
  rpt strip_tac >> TRY (first_assum ACCEPT_TAC) >>
  FIRST [qpat_assum `!marks res mid G1 tn1 t. _` (drule_all_then ACCEPT_TAC), metis_tac[]]
QED

Theorem fixed_log_reached_tail[local]:
  let source = bind (eval_expr cx data) (read_result cx) in
  let Q = expr_sim_full_post (DF,lo,d,ctx,func) cenv cx (Call ann RawLog es_call dflt)
             (es,sa,sb,s0,Lit 0w,G0,tn0) in
  let ready = raw_log_fixed_tail_ready (DF,lo,d,ctx,func) cenv cx data
                  (sa,sm,data_op,s0,es,G0,tn0) (buf,ops,vals,p,w) in
  expr_body_pre cenv cx env (Call ann RawLog es_call dflt) es0 /\
  MEM data es_call /\ expr_sim_inv cenv cx env es /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  post_value_type cenv data = expr_type data /\
  evaluate_type (get_tenv cx) (expr_type data) = SOME (BaseTV (BytesT (Fixed 32))) /\
  compile_alloc_buffer 32 sa = (buf,sd) /\ ci_mono sa sd /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sd /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l)) ops /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       eval_operands ops s0 = SOME (MAP event_value_to_word vals) /\
       EVERY (\op. op_taint tn0 op = {}) ops /\
       raw_log_fixed_scratch_row (DF,lo,d,ctx,func,E,PG) cenv cx
          (sa,sd,es,s0,G0,tn0,buf) (u,Gu,tnu,p,w) H) /\
  LENGTH vals <= 4 /\
  gas_admissible (bind source (raw_log_fixed_next cx vals)) expr_res_ok es /\
  (!bs word mid t G tn. ~cx.txn.is_static /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> ready (bs,word,mid,t,G,tn) H) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
     ?z G2 tn2. !H. valid_horizon cx st0 H mid.storage_trace ==>
       create_operand_full_scope sm sb E ctx func t [] (OK z) /\
       gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2) /\
       Q H (INL NoneV)
         (mid with <|logs := mid.logs ++ [encode_raw_event_values cx.txn.target vals bs];
                     gas_obs := []|>) G2 tn2 z) /\
  (!bs word mid t G tn. cx.txn.is_static /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> ready (bs,word,mid,t,G,tn) H) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
     ?z G2 tn2. !H. valid_horizon cx st0 H mid.storage_trace ==>
       create_operand_full_scope sm sb E ctx func t [] (Abort ExHalt_abort z) /\
       gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (t,G,tn) [] (Abort ExHalt_abort z,G2,tn2)) /\
    (!tail. source (es with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_sim_full_post (DF,lo,d,ctx,func) cenv cx data
        (es,sd,sm,u,data_op,Gu,tnu) H res mid G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (u,Gu,tnu) marks (OK t,G1,tn1)) ==>
    ?v. res = INL v /\ scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sm sb
       (raw_log_fixed_next cx vals v) (mid,t,G1,tn1) Q (create_operand_exit_post ctx cx)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  `?v. res = INL v` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o SIMP_RULE bool_ss [expr_sim_full_post_def])) >>
     goal_assum (drule_at Any)) >>
  gvs[] >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  `?bs. v = BytesV bs` by (drule_all raw_log_fixed_next_bytes >> simp[]) >> gvs[] >>
  `storage_trace_frame (bind (eval_expr cx data) (read_result cx))` by
    simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H (mid with gas_obs := []).storage_trace` by simp[] >>
     drule_all valid_horizon_frame >> simp[]) >>
  `~t.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule gas_origin_ptr_path_exec >> simp[exit_result_def] >>
     fs[expr_sim_full_post_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    ?word. raw_log_fixed_tail_ready (DF,lo,d,ctx,func) cenv cx data
      (sa,sm,data_op,s0,es,G0,tn0) (buf,ops,vals,p,w) (bs,word,mid,t,G1,tn1) H` by
    (qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by simp[] >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     irule fixed_log_child_ready >>
     qpat_assum `raw_log_fixed_scratch_row _ _ _ _ _ H` (irule_at Any) >>
     qexistsl_tac [`gas_explicit marks u.vs_gas_readings`,`es_call`,`es0`,`env`,`dflt`,`ann`] >>
     gvs[expr_sim_full_post_def]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?word. _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    raw_log_fixed_tail_ready (DF,lo,d,ctx,func) cenv cx data
      (sa,sm,data_op,s0,es,G0,tn0) (buf,ops,vals,p,w) (bs,word,mid,t,G1,tn1) H` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?word. _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `eval_operand data_op t = SOME word /\ eval_operand data_op t = SOME word'` by
       fs[raw_log_fixed_tail_ready_def] >>
     `word' = word` by fs[] >> qpat_x_assum `word' = word` SUBST_ALL_TAC >>
     first_assum ACCEPT_TAC) >>
  irule fixed_log_scoped_tail >> simp[] >>
  conj_tac >> strip_tac >> first_x_assum irule >> simp[] >>
  TRY (qexists_tac `bs`) >> qexists_tac `word` >> simp[]
QED

Theorem fixed_log_cut_horizon[local]:
  storage_trace_frame source /\
  ((?H. valid_horizon cx st0 H es.storage_trace) ==>
    create_operand_cut a b E ctx func tops cx st0 source (es,s)) ==>
  create_operand_cut a b E ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> Cases_on `?H. valid_horizon cx st0 H es.storage_trace` >- metis_tac[] >>
  gvs[create_operand_cut_def,create_body_cut_def] >> rpt strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by (drule_all valid_horizon_frame >> simp[]) >>
  metis_tac[]
QED

Theorem raw_log_fixed_cut_code[local]:
  compile_alloc_buffer 32 sa = (buf,sd) /\
  lower_value compile_expr cenv (expr_type data) data sd = (data_op,sm) /\
  emit_inst MSTORE [buf.buf_operand;data_op] [] sm = ((),s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) ==>
  create_cut_code {} sa sd /\ create_cut_code {} sd sm /\ create_cut_code {} sm sb
Proof
  strip_tac >>
  conj_tac >- (mp_tac (Q.INST [`exits` |-> `{}`,`a` |-> `sa`,`n` |-> `32`]
    create_alloc_buffer_cut_code) >> simp[]) >>
  conj_tac >- (mp_tac (Q.SPECL [`cenv`,`expr_type data`,`data`,`sd`]
    (cj 2 create_operand_cut_code)) >> simp[]) >>
  irule create_cut_code_join >> qexists_tac `s1` >>
  conj_tac
  >- (mp_tac (Q.INST [`exits` |-> `{}`,`opc` |-> `MSTORE`,
        `ops` |-> `[buf.buf_operand;data_op]`,`outs` |-> `[]`,`a` |-> `sm`]
        create_cut_code_emit_inst) >> simp[create_cut_targets_def]) >>
  mp_tac (Q.INST [`exits` |-> `{}`,`opc` |-> `LOG`,
      `ops` |-> `Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]`,
      `outs` |-> `[]`,`a` |-> `s1`] create_cut_code_emit_inst) >> simp[create_cut_targets_def]
QED

Theorem raw_log_fixed_data_from_rows[local]:
  let E = gas_explicit_sites ctx shctx in
  let source = bind (eval_expr cx data) (read_result cx) in
  let next = raw_log_fixed_next cx vals in
  let Q = expr_sim_full_post (DF,lo,d,ctx,func) cenv cx (Call ann RawLog es_call dflt)
    (es,sa,sb,s0,Lit 0w,G0,tn0) in
  body_inv (cx_tops cx) ctx cenv cx /\
  expr_body_pre cenv cx env (Call ann RawLog es_call dflt) es0 /\
  MEM data es_call /\ expr_sim_inv cenv cx env es /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  post_value_type cenv data = expr_type data /\
  evaluate_type (get_tenv cx) (expr_type data) = SOME (BaseTV (BytesT (Fixed 32))) /\
  compile_alloc_buffer 32 sa = (buf,sd) /\
  lower_value compile_expr cenv (expr_type data) data sd = (data_op,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type data)
    (gas_shadow_expr data) shd = (data_op,shm) /\
  expr_sim_full_code (ctx,shctx,func,shfunc) (sd,sm,shd,shm) /\
  emit_inst MSTORE [buf.buf_operand;data_op] [] sm = ((),s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
  fn_has_code sa sb func /\ create_layout sa sb /\
  (!bb i. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb (LENGTH sb.cs_current_insts) = SOME i ==> i.inst_id NOTIN frag_ids sa sd) /\
  sd.cs_current_bb = sa.cs_current_bb /\
  sd.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sd /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts sa sd) /\
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts sm sb) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!fn inst t. frag_reachable ctx func s0 fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  create_operand_at sa s0 /\ ~s0.vs_halted /\
  gas_admissible source expr_res_ok es /\ gas_admissible (bind source next) expr_res_ok es /\
  LENGTH vals <= 4 /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l)) ops /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    eval_operands ops s0 = SOME (MAP event_value_to_word vals) /\
    EVERY (\op. op_taint tn0 op = {}) ops) /\
  expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx (expr_type data) data es /\
  (!u Gu tnu.
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx (expr_type data) data es
      (st0,sd,sm,shd,shm,data_op,u,Gu,tnu) ==>
    create_operand_cut sd sm E ctx func (cx_tops cx) cx st0 source (es,u)) /\
  (?u Gu tnu p w. !H. valid_horizon cx st0 H es.storage_trace ==>
     raw_log_fixed_scratch_row (DF,lo,d,ctx,func,E,PG) cenv cx
       (sa,sd,es,s0,G0,tn0,buf) (u,Gu,tnu,p,w) H) /\
  (!p w bs word mid t G tn. ~cx.txn.is_static /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       raw_log_fixed_tail_ready (DF,lo,d,ctx,func) cenv cx data
         (sa,sm,data_op,s0,es,G0,tn0) (buf,ops,vals,p,w) (bs,word,mid,t,G,tn) H) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
     ?z G2 tn2. !H. valid_horizon cx st0 H mid.storage_trace ==>
       create_operand_full_scope sm sb E ctx func t [] (OK z) /\
       gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2) /\
       Q H (INL NoneV)
         (mid with <|logs := mid.logs ++ [encode_raw_event_values cx.txn.target vals bs];
                     gas_obs := []|>) G2 tn2 z) /\
  (!p w bs word mid t G tn. cx.txn.is_static /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       raw_log_fixed_tail_ready (DF,lo,d,ctx,func) cenv cx data
         (sa,sm,data_op,s0,es,G0,tn0) (buf,ops,vals,p,w) (bs,word,mid,t,G,tn) H) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
     ?z G2 tn2. !H. valid_horizon cx st0 H mid.storage_trace ==>
       create_operand_full_scope sm sb E ctx func t [] (Abort ExHalt_abort z) /\
       gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (t,G,tn) [] (Abort ExHalt_abort z,G2,tn2)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sa sb
    (bind source next) (es,s0,G0,tn0) Q (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb E ctx func (cx_tops cx) cx st0 (bind source next) (es,s0)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `E = gas_explicit_sites ctx shctx` >>
  qabbrev_tac `source = bind (eval_expr cx data) (read_result cx)` >>
  qabbrev_tac `next = raw_log_fixed_next cx vals` >>
  qabbrev_tac `Q = expr_sim_full_post (DF,lo,d,ctx,func) cenv cx (Call ann RawLog es_call dflt)
    (es,sa,sb,s0,Lit 0w,G0,tn0)` >>
  `storage_trace_frame source /\ !v. storage_trace_frame (next v)` by
    simp[Abbr `source`,Abbr `next`,storage_trace_frame_bind_all,evaluate_storage_trace_frame,
         storage_trace_frame_read_result,raw_log_fixed_next_frame] >>
  `storage_trace_frame (bind source next)` by simp[storage_trace_frame_bind_all] >>
  `create_cut_code {} sa sd /\ create_cut_code {} sd sm /\ create_cut_code {} sm sb` by
    (drule_all raw_log_fixed_cut_code >> simp[]) >>
  `create_cut_code {} sd sb` by metis_tac[create_cut_code_join] >>
  `cs_extends sa sd /\ cs_extends sd sm /\ cs_extends sm sb /\ cs_extends sd sb /\
   sd.cs_next_id <= sb.cs_next_id` by fs[create_cut_code_def] >>
  `create_layout sd sb /\ fn_has_code sa sd func /\ fn_has_code sd sb func /\ fn_has_code sm sb func` by
    metis_tac[create_layout_subinterval,cs_extends_refl,fn_has_code_split] >>
  `ci_mono sa sd` by metis_tac[ci_mono_compile_alloc_buffer,pairTheory.SND] >>
  `local_ptrs_reserved cenv sd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `!H0. valid_horizon cx st0 H0 es.storage_trace ==>
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx (expr_type data) data es
      (st0,sd,sm,shd,shm,data_op,u,Gu,tnu)` by
    (rpt strip_tac >> irule fixed_log_scratch_child_pre >> simp[Abbr `source`] >>
     conj_tac >-
       (qexistsl_tac [`G0`,`buf`,`p`,`s0`,`sa`,`tn0`,`w`] >>
        fs[Abbr `E`] >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
     metis_tac[]) >>
  conj_tac
  >- (irule stage_scoped_initial_domain >> simp[] >> suspend "scope") >>
  irule fixed_log_cut_horizon >> simp[] >> suspend "cut"
QED


Resume raw_log_fixed_data_from_rows[scope]:
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
    by fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     create_operand_full_scope sa sd E ctx func s0 [] (OK u) /\
     gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s0,G0,tn0) [] (OK u,Gu,tnu) /\
     create_operand_at sd u` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ _ _ ==> raw_log_fixed_scratch_row _ _ _ _ _ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [raw_log_fixed_scratch_row_def])) >>
     simp[create_operand_at_def]) >>
  `create_operand_at sd u /\ create_operand_full_scope sa sd E ctx func s0 [] (OK u)` by metis_tac[] >>
  `create_cut_region sd sb u` by
    (drule_all create_cut_region_rules >> strip_tac >>
     qpat_assum `!s. s.vs_current_bb = sd.cs_current_bb /\ _ ==> create_cut_region sd sb s` irule >>
     fs[create_operand_at_def]) >>
  irule stage_scoped_zero_prefix >> simp[] >>
  conj_tac >- fs[expr_sim_full_code_def] >>
  conj_tac >- (qexists_tac `cenv` >> simp[]) >>
  qexistsl_tac [`Gu`,`sd`,`u`,`tnu`] >>
  `sa.cs_next_id <= sd.cs_next_id` by fs[ci_mono_def] >>
  `LENGTH sm.cs_current_insts + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts`
    by simp[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
  `scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sd sm
      source (es,u,Gu,tnu)
      (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx data (es,sd,sm,u,data_op,Gu,tnu))
      (create_operand_exit_post ctx cx)` by
    (qpat_assum `expr_sim_scoped _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_sim_scoped_def]) >>
     simp[Abbr `source`,Abbr `E`] >> metis_tac[]) >>
  qunabbrev_tac `source` >> qunabbrev_tac `next` >>
  irule (SIMP_RULE bool_ss [LET_THM] fixed_log_scoped_bind) >>
  qpat_assum `scoped_operand_outcome _ _ _ _ sd sm _ _ _ _` (irule_at Any) >>
  qexists_tac `cenv` >> simp[] >>
  conj_tac >-
    (qpat_assum `expr_sim_full_code _ _` (mp_tac o REWRITE_RULE [expr_sim_full_code_def]) >>
     simp_tac bool_ss []) >>
  rpt gen_tac >> strip_tac >>
  irule (SIMP_RULE bool_ss [LET_THM] fixed_log_reached_tail) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qexistsl_tac [`Gu`,`buf`,`data`,`data_op`,`marks`,`ops`,`p`,`sd`,`tnu`,`u`,`w`] >>
      rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
      TRY (rpt strip_tac >> first_assum ACCEPT_TAC) >>
      metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`env`,`es0`] >> simp[]
QED

Resume raw_log_fixed_data_from_rows[cut]:
  strip_tac >>
  `create_operand_full_scope sa sd E ctx func s0 [] (OK u)` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> raw_log_fixed_scratch_row _ _ _ _ _ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [raw_log_fixed_scratch_row_def])) >>
     first_assum ACCEPT_TAC) >>
  `MEM func ctx.ctx_functions` by fs[expr_sim_full_code_def] >>
  `create_operand_cut sd sm E ctx func (cx_tops cx) cx st0 source (es,u)` by metis_tac[] >>
  irule create_neutral_prefix_visit_cut >> simp[] >>
  conj_tac >- (qexists_tac `cenv` >> simp[]) >>
  qexistsl_tac [`sd`,`u`] >> simp[] >>
  irule fixed_log_child_window >> simp[] >>
  conj_tac >- (qexists_tac `cenv` >> simp[]) >>
  qexists_tac `sm` >> simp[] >> metis_tac[expr_sim_full_code_fields]
QED
Finalise raw_log_fixed_data_from_rows

(* Match the ordinary endpoint frame to the normalized scoped post without
   changing the terminal state or the delivered ghost pair. *)
Theorem raw_log_fixed_tail_normal_post:
  expr_type e = post_value_type cenv e /\
  expr_post H ctx func cenv cx e es sa sb s0 ee NoneV (Lit 0w) z /\
  expr_store_bound cx (expr_type e) NoneV (Lit 0w) z /\
  z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
  ghost_inv_at (DF H) lo d cenv cx ee G tn z /\
  ptr_val_ok cx (post_value_type cenv e) NoneV (Lit 0w) G tn z /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e (Lit 0w) G z) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
  expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e
    (es,sa,sb,s0,Lit 0w,G0,tn0) H (INL NoneV : value + vyperState$exception)
    (ee with gas_obs := []) G tn z
Proof
  strip_tac >>
  qpat_x_assum `expr_type e = post_value_type cenv e` (assume_tac o SYM) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     drule_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp) >>
  simp[expr_sim_full_post_def,expr_sim_full_endpoint_def,
       extract32_expr_post_end_gas_obs] >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ ee _ _ z` mp_tac >>
  simp[ghost_inv_at_def] >> metis_tac[]
QED

(* The scratch operand and topic operands are still nonfresh after compiling
   the data. This is compile-time framing, not another run of the data child. *)
Theorem raw_log_fixed_tail_compile_ready:
  compile_alloc_buffer 32 sa = (buf,sd) /\
  lower_value compile_expr cenv (expr_type data) data sd = (data_op,sm) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l)) ops ==>
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (buf.buf_operand::data_op::ops) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)
Proof
  strip_tac >>
  `ci_mono sa sd` by metis_tac[ci_mono_compile_alloc_buffer,pairTheory.SND] >>
  `ci_mono sd sm` by metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND] >>
  `local_ptrs_reserved cenv sd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sd.cs_next_var <= sm.cs_next_var`
    by (fs[ci_mono_def] >> decide_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x`
    by metis_tac[compiler_alloc_buffer_var,not_fresh_at_mono] >>
  `!x. data_op = Var x ==> not_fresh_at sm x` by metis_tac[compile_lower_value_var] >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

(* The scratch ALLOCA is at the entry cursor, which is strictly before its
   own first exit and cannot be the enclosing exit. IDs are unique in func. *)
Theorem raw_log_fixed_exit_not_scratch[local]:
  compile_alloc_buffer 32 sa = (buf,sd) /\ fn_has_code sa sd func /\
  fn_inst_ids_distinct func /\ cs_extends sa sd /\ cs_extends sd sb /\
  create_layout sa sb /\ lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH sb.cs_current_insts) = SOME i ==>
  i.inst_id NOTIN frag_ids sa sd
Proof
  strip_tac >> strip_tac >> drule compile_alloc_buffer_code >> strip_tac >>
  `i.inst_id = sa.cs_next_id` by (fs[frag_ids_def] >> decide_tac) >>
  `?entry. lookup_block sa.cs_current_bb func.fn_blocks = SOME entry /\
      get_instruction entry (LENGTH sa.cs_current_insts) = SOME
        (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
          [STRING #"%" (toString sa.cs_next_var)])` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb'` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qabbrev_tac `s = ARB with <|vs_current_bb := sa.cs_current_bb;
    vs_inst_idx := LENGTH sa.cs_current_insts|>` >>
  `create_cut_region sa sd s /\ ~create_operand_at sd s` by
    simp[create_cut_region_def,create_operand_at_def,Abbr `s`] >>
  `~create_operand_at sb s` by metis_tac[create_layout_left_stop] >>
  `entry = bb /\ LENGTH sa.cs_current_insts = LENGTH sb.cs_current_insts` suffices_by
    (fs[create_operand_at_def,Abbr `s`] >> metis_tac[lookup_block_label]) >>
  irule (flat_map_occurrence_unique |> Q.GEN `f` |>
    Q.ISPEC `(\inst. inst.inst_id)` |> Q.GEN `g` |>
    Q.ISPEC `(\blk. blk.bb_instructions)`) >>
  `MEM bb func.fn_blocks /\ MEM entry func.fn_blocks` by metis_tac[lookup_block_MEM] >>
  rpt (conj_tac >- gvs[get_instruction_def, AllCaseEqs(), venomInstTheory.mk_inst_def]) >>
  qexists_tac `func.fn_blocks` >> fs[fn_inst_ids_distinct_def, combinTheory.o_DEF]
QED

(* Static compiler facts at the two real LOG endpoints.  The horizon guard
   for their reached input is kept separately in raw_log_fixed_tail_ready. *)
Definition raw_log_fixed_log_site_def:
  raw_log_fixed_log_site (buf,data_op,ops,sa,sd,sm,s1,sb) func cenv e data <=>
    emit_void MSTORE [buf.buf_operand;data_op] sm = ((),s1) /\
    emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
    compile_alloc_buffer 32 sa = (buf,sd) /\ fn_has_code sa sd func /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
    LENGTH ops < dimword (:256) /\ sa.cs_next_var <= sm.cs_next_var /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (buf.buf_operand::data_op::ops) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    expr_type data = BaseT (BytesT (Fixed 32)) /\ post_value_type cenv data = expr_type data /\
    expr_type e = NoneT /\ post_value_type cenv e = NoneT /\ expr_has_effect e /\
    sb.cs_current_bb = sm.cs_current_bb /\
    sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
    EVERY (\i. i.inst_id IN frag_ids sm sb /\ i.inst_opcode <> INVOKE /\
      i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
      ~MEM i.inst_opcode [CREATE;CREATE2]) (emitted_insts sm sb)
End

(* Preserve the exact state and ghosts from the normal LOG endpoint. *)
Definition raw_log_fixed_log_post_def:
  raw_log_fixed_log_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sb,s0,G0,tn0) H ee G tn z <=>
    expr_post H ctx func cenv cx e es sa sb s0 ee NoneV (Lit 0w) z /\
    expr_store_bound cx (expr_type e) NoneV (Lit 0w) z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn z /\
    ptr_val_ok cx (post_value_type cenv e) NoneV (Lit 0w) G tn z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e (Lit 0w) G z) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
End

Theorem create_raw_log_fixed_data_scoped_cut:
  let E = gas_explicit_sites ctx shctx in
  let source = bind (eval_expr cx data) (read_result cx) in
  let next = raw_log_fixed_next cx vals in
  let e = Call ann RawLog es_call dflt in
  let Q = expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e
    (es,sa,sb,s0,Lit 0w,G0,tn0) in
  let site = raw_log_fixed_log_site (buf,data_op,ops,sa,sd,sm,s1,sb) func cenv e data in
  let ready = \p w. raw_log_fixed_tail_ready (DF,lo,d,ctx,func) cenv cx data
      (sa,sm,data_op,s0,es,G0,tn0) (buf,ops,vals,p,w) in
  body_inv (cx_tops cx) ctx cenv cx /\
  expr_body_pre cenv cx env e es0 /\ MEM data es_call /\ expr_sim_inv cenv cx env es /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  post_value_type cenv data = expr_type data /\
  evaluate_type (get_tenv cx) (expr_type data) = SOME (BaseTV (BytesT (Fixed 32))) /\
  expr_type e = NoneT /\ post_value_type cenv e = NoneT /\ expr_has_effect e /\
  compile_alloc_buffer 32 sa = (buf,sd) /\
  lower_value compile_expr cenv (expr_type data) data sd = (data_op,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type data)
    (gas_shadow_expr data) shd = (data_op,shm) /\
  expr_sim_full_code (ctx,shctx,func,shfunc) (sd,sm,shd,shm) /\
  emit_inst MSTORE [buf.buf_operand;data_op] [] sm = ((),s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ create_layout sa sb /\
  sd.cs_current_bb = sa.cs_current_bb /\
  sd.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sd /\
  EVERY (\i. i.inst_id IN frag_ids sa sd /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
    ~MEM i.inst_opcode [CREATE;CREATE2]) (emitted_insts sa sd) /\
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. i.inst_id IN frag_ids sm sb /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
    ~MEM i.inst_opcode [CREATE;CREATE2]) (emitted_insts sm sb) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!fn inst t. frag_reachable ctx func s0 fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  create_operand_at sa s0 /\ ~s0.vs_halted /\
  gas_admissible source expr_res_ok es /\ gas_admissible (bind source next) expr_res_ok es /\
  LENGTH vals <= 4 /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l)) ops /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    eval_operands ops s0 = SOME (MAP event_value_to_word vals) /\
    EVERY (\op. op_taint tn0 op = {}) ops) /\
  expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx (expr_type data) data es /\
  (!u Gu tnu.
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx (expr_type data) data es
      (st0,sd,sm,shd,shm,data_op,u,Gu,tnu) ==>
    create_operand_cut sd sm E ctx func (cx_tops cx) cx st0 source (es,u)) /\
  (fn_has_code sa sd func ==>
    ?u Gu tnu p w. !H. valid_horizon cx st0 H es.storage_trace ==>
      raw_log_fixed_scratch_row (DF,lo,d,ctx,func,E,PG) cenv cx
        (sa,sd,es,s0,G0,tn0,buf) (u,Gu,tnu,p,w) H) /\
  (!p w bs word mid t G tn. ~cx.txn.is_static /\ site /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> ready p w (bs,word,mid,t,G,tn) H) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
     ?z G2 tn2. !H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2) /\
       raw_log_fixed_log_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sb,s0,G0,tn0) H
         (mid with logs := mid.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G2 tn2 z /\
       create_operand_full_scope sm sb E ctx func t [] (OK z)) /\
  (!p w bs word mid t G tn. cx.txn.is_static /\ site /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> ready p w (bs,word,mid,t,G,tn) H) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
     ?z G2 tn2. !H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (t,G,tn) [] (Abort ExHalt_abort z,G2,tn2) /\
       create_operand_full_scope sm sb E ctx func t [] (Abort ExHalt_abort z)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sa sb
    (bind source next) (es,s0,G0,tn0) Q (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb E ctx func (cx_tops cx) cx st0 (bind source next) (es,s0)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `source = bind (bind (eval_expr cx data) (read_result cx)) (raw_log_fixed_next cx vals)` >>
  `storage_trace_frame source` by
    simp[Abbr `source`,storage_trace_frame_bind_all,evaluate_storage_trace_frame,
         storage_trace_frame_read_result,raw_log_fixed_next_frame] >>
  Cases_on `?H. valid_horizon cx st0 H es.storage_trace`
  >- suspend "live" >>
  conj_tac
  >- (irule stage_scoped_initial_domain >> fs[storage_trace_domain_def]) >>
  irule fixed_log_cut_horizon >> simp[]
QED

Resume create_raw_log_fixed_data_scoped_cut[live]:
  `LENGTH ops <= 4` by
    (qpat_x_assum `?H. valid_horizon _ _ H _` strip_assume_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule eval_operands_length >> simp[]) >>
  `LENGTH ops < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `create_cut_code {} sa sd /\ create_cut_code {} sd sm /\ create_cut_code {} sm sb` by
    (drule_all raw_log_fixed_cut_code >> simp[]) >>
  `create_cut_code {} sd sb` by metis_tac[create_cut_code_join] >>
  `cs_extends sa sd /\ cs_extends sd sb /\ cs_extends sa sm /\ cs_extends sm sb`
    by metis_tac[create_cut_code_def,cs_extends_trans] >>
  `fn_has_code sa sd func /\ fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  `!bb i. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sb.cs_current_insts) = SOME i ==> i.inst_id NOTIN frag_ids sa sd` by
    (rpt strip_tac >> metis_tac[raw_log_fixed_exit_not_scratch]) >>
  `raw_log_fixed_log_site (buf,data_op,ops,sa,sd,sm,s1,sb) func cenv
    (Call ann RawLog es_call dflt) data` by
    (drule_all raw_log_fixed_tail_compile_ready >> strip_tac >>
     simp[raw_log_fixed_log_site_def,GSYM extbodies_emit_inst_void]) >>
  qunabbrev_tac `source` >>
  irule (SIMP_RULE bool_ss [LET_THM] raw_log_fixed_data_from_rows) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl_tac [`env`,`es0`] >> simp[]) >>
  qexistsl_tac [`buf`,`data_op`,`ops`,`s1`,`sd`,`shd`,`shfunc`,`shm`,`sm`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "abort_row" >>
  conj_tac >- suspend "ok_row" >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `fn_has_code sa sd func ==> _` (drule_then ACCEPT_TAC)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (gvs[EVERY_MEM] >> metis_tac[]) >>
  conj_tac >- (gvs[EVERY_MEM] >> metis_tac[]) >>
  simp[]
QED

Resume create_raw_log_fixed_data_scoped_cut[abort_row]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!p w bs word mid t G tn. cx.txn.is_static /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qexistsl_tac [`z`,`G2`,`tn2`] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (Abort _ _,_,_) /\ _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Resume create_raw_log_fixed_data_scoped_cut[ok_row]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!p w bs word mid t G tn. ~cx.txn.is_static /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qexistsl_tac [`z`,`G2`,`tn2`] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (OK _,_,_) /\ _`
    (drule_then strip_assume_tac) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `raw_log_fixed_log_post _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[raw_log_fixed_log_post_def]) >>
  `expr_type (Call ann RawLog es_call dflt) = post_value_type cenv (Call ann RawLog es_call dflt)` by simp[] >>
  drule_all raw_log_fixed_tail_normal_post >> simp[NoAsms, evaluation_state_fupdcanon]
QED

Finalise create_raw_log_fixed_data_scoped_cut
