(* The physical LOG step after the linked topics and data suffixes. *)
Theory bodyLogEmitOutcomeMods
Ancestors
  bodyFullLog bodyFullLogSuffix bodyFullPostsMods bodyFullShadowBodyInv
  bodyFullPathHistory gasOutcomeFullPostMods fragGasOriginPtrLoop
  stmtSimLogEmit logComposeFacts bodyFullShared bodyMemoryDefs bodyInvSplit
  exprSimWordArgs bodyPtrDefs stmtSimDefs exprSimDefs loweringPosts
  loweringStateRelDefs exprLoweringProps stateRelProj emitHelperProps
  vyperStorageFootprint vyperState vyperContext vyperEvent venomState venomInst
  stmtLowering compileEnv words list pred_set finite_map fragExec bodySimFull
  ptrDiscipline venomExecSemantics bodyFullHashKeccakFixed stmtSimProps
Libs horizonTypeLib

Theorem log_emit_immutable_frame[local]:
  immutable_frame_mods func ce cx
    ((mid with logs := logs) with gas_obs := gs)
    (u with <|vs_logs := vlogs; vs_inst_idx := idx|>) <=>
  immutable_frame_mods func ce cx mid u
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def,
       immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
       local_region_def, lookup_var_def]
QED

Theorem log_emit_ghost_frame[local]:
  ghost_inv_at_mods D lo d ce cx ((mid with logs := logs) with gas_obs := gs) G tn
    (u with <|vs_logs := vlogs; vs_inst_idx := idx|>) <=>
  ghost_inv_at_mods D lo d ce cx mid G tn u
Proof
  Cases_on `d` >-
    simp[ghost_inv_at_mods_def, ptr_covers_def, stor_taint_ok_at_def,
         lookup_var_def, allocas_from_def, return_buf_ptr_def] >>
  PairCases_on `x` >>
  simp[ghost_inv_at_mods_def, ptr_covers_def, stor_taint_ok_at_def,
       lookup_var_def, allocas_from_def, return_buf_ptr_def]
QED

val log_post = ``\(H:(bool # bytes32 # type_value) list # num list) res ee G tn v. ?ce'.
  stmt_lands lctx sb res v /\ ~v.vs_halted /\
  (res = INL () ==> ~block_is_terminated sb /\ ce' = ce) /\
  cenv_top_ext ce ce' ee.scopes /\ stmt_state_rel H ctx func ce' cx ee v /\
  immutable_frame_mods func ce' cx ee v /\ storage_well_formed_on cx ee (FST H) /\
  return_buf_frame d ce' sb v /\ alloca_history func v /\ return_buf_sep d ce' ee v /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
  s0.vs_alloca_next <= v.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d ce' cx ee G tn v /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x v = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP v.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame ce es sa s0 ce' ee v /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region ce es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)``;

Theorem log_emit_normal_post[local]:
  ~block_is_terminated sb /\ sb.cs_current_bb = u.vs_current_bb /\
  sa.cs_next_var <= sb.cs_next_var /\ ~u.vs_halted /\
  s0.vs_alloca_next <= u.vs_alloca_next /\ alloca_history func fin /\
  fin = (u with vs_logs := u.vs_logs ++ [ev]) with vs_inst_idx := LENGTH sb.cs_current_insts /\
  ee = (mid with logs := mid.logs ++ [ev]) with gas_obs := [] /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx mid u /\
  immutable_frame_mods func ce cx mid u /\
  storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx mid Gu tu u /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ return_buf_frame d ce sa s0 /\ return_buf_sep d ce es s0 /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) u) /\
  MAP FDOM mid.scopes = MAP FDOM es.scopes /\ wb_frame ce es mid sa s0 u /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu ==>
  ^log_post H (INL ()) ee Gu tu fin
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> BETA_TAC >>
  `wb_frame ce es ee sa s0 fin` by
    (simp[wb_frame_gas_obs] >> fs[wb_frame_def, locals_kept_def, popped_kept_def, lookup_var_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `wb_frame ce es ee sa s0 fin`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  `stmt_state_rel H ctx func ce cx ee fin` by
    (qpat_assum `ee = _` (fn e => qpat_assum `fin = _` (fn v =>
       PURE_REWRITE_TAC [e,v])) >>
     PURE_REWRITE_TAC [stmt_state_rel_inst_idx, stmt_state_rel_gas_obs] >>
     irule (horizonTypeLib.at_horizon_named "H" log_append_stmt_state_rel) >> simp[]) >>
  `storage_well_formed_on cx ee (FST H)` by
    (irule (iffLR storage_well_formed_on_backends) >> qexists `mid` >> simp[]) >>
  `return_buf_frame d ce sb fin` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s0`,`sa`] >> simp[]) >>
  `alloca_frame ce es sa s0 ce ee fin` by
    (irule (horizonTypeLib.at_horizon_named "H" alloca_frame_of_mem_frame) >>
     asm_rewrite_tac[] >> simp[] >>
     qexistsl [`H0`,`ctx`,`cx`,`func`] >> simp[]) >>
  `return_buf_sep d ce ee fin` by
    (irule (horizonTypeLib.at_horizon_named "H" return_buf_sep_locals_kept) >>
     conj_tac >- (fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
     qexistsl [`H0`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >> asm_rewrite_tac[] >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp fin` by
    (qpat_assum `stmt_state_rel H ctx func ce cx ee fin`
      (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  qpat_assum `ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  qexists `ce` >> asm_rewrite_tac[] >>
  simp[stmt_lands_def, cenv_top_ext_refl,
       SIMP_RULE (srw_ss()) [] log_emit_immutable_frame,
       SIMP_RULE (srw_ss()) [] log_emit_ghost_frame]
QED

Theorem log_emit_outcome_mods:
  encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs = SOME ev /\
  ev = <|logger := cx.txn.target; topics := topics;
          data := mem_bytes_at (w2n off) (w2n len) u.vs_memory|> /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] send = ((),sb) /\
  LENGTH ops < dimword (:256) /\ eval_operands ops u = SOME topics /\
  eval_operand ptr_op u = SOME off /\ eval_operand len_op u = SOME len /\
  EVERY (\op. op_taint tu op = {}) (ptr_op::len_op::ops) /\
  (w2n len <> 0 ==> ?p. ptr_op = Var p /\ ptr_covers Gu tu p u (w2n len)) /\
  (!i. w2n off <= i /\ i < w2n off + w2n len ==> i NOTIN tu.t_mem) /\
  (w2n len = 0 \/ w2n off + w2n len <= u.vs_alloca_next) /\
  fn_has_code send sb func /\ fn_inst_ids_distinct func /\
  ~u.vs_halted /\ ~t.vs_halted /\
  u.vs_current_bb = send.cs_current_bb /\ u.vs_inst_idx = LENGTH send.cs_current_insts /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid u /\ immutable_frame_mods func ce cx mid u /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx mid Gu tu u) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,Gu,tu)) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ return_buf_frame d ce sa s0 /\ return_buf_sep d ce es s0 /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) u) /\
  sa.cs_next_var <= send.cs_next_var /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  alloca_history func u /\ MAP FDOM mid.scopes = MAP FDOM es.scopes /\
  wb_frame ce es mid sa s0 u /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    (bind (lift_option (encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs)
      "Log encode event") (\event. ignore_bind (check_not_static cx) (push_log event)))
    (mid,t,G,tn) ^log_post
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
       halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `cx.txn.is_static`
  >- (irule gas_outcome_full_mods_exit >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`Gu`,`mid`,`Abort ExHalt_abort (halt_state (set_returndata [] u))`,
                `INR (Error (RuntimeError "write in static context"))`,`tu`] >>
      simp[exit_result_def, stmt_exit_ptr_def, expr_exit_def, halt_exit_def,
           Excl "create_size_exit_ok_inr"] >>
      conj_tac >- (qx_gen_tac `tail` >> drule log_full_source_suffix_result >> simp[]) >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >>
      `u.vs_call_ctx.cc_static` by
        (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
         fs[call_ctx_rel_def]) >>
      reverse conj_tac
      >- (irule createSizeExitTheory.create_size_exit_ok_static >>
          simp[halt_state_def, set_returndata_def]) >>
      `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
        (qpat_assum `stmt_state_rel H ctx func ce cx mid u`
          (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
      irule gas_origin_ptr_path_trans >> qexistsl [`Gu`,`u`,`tu`] >>
      conj_tac >- simp[] >>
      drule_all compile_log_emit_static_origin_ptr_path >> simp[]) >>
  qabbrev_tac `done_es = mid with logs := mid.logs ++ [ev]` >>
  qabbrev_tac `fin = u with <|vs_logs := u.vs_logs ++ [ev]; vs_inst_idx := LENGTH sb.cs_current_insts|>` >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gu`,`done_es`,`INL ()`,`fin`,`tu`] >> BETA_TAC >>
  conj_tac >- (qx_gen_tac `tail` >> drule log_full_source_suffix_result >> simp[Abbr `done_es`]) >>
  `done_es.storage_trace = mid.storage_trace` by simp[Abbr `done_es`] >>
  pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `~u.vs_call_ctx.cc_static /\ u.vs_call_ctx.cc_address = cx.txn.target` by
    (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >> fs[call_ctx_rel_def]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel H ctx func ce cx mid u`
      (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK fin,Gu,tu)` by
    (drule_all compile_log_emit_origin_ptr_path >> simp[Abbr `fin`]) >>
  conj_tac >- (irule gas_origin_ptr_path_trans >> qexistsl [`Gu`,`u`,`tu`] >> simp[]) >>
  `alloca_history func fin` by
    (drule body_full_path_alloca_history >> disch_then irule >>
     qpat_assum `stmt_state_rel H ctx func ce cx mid u`
       (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  drule emit_inst_extends >> strip_tac >>
  `~block_is_terminated sb` by (drule log_emit_not_terminated >> simp[]) >>
  `sb.cs_current_bb = u.vs_current_bb /\ sa.cs_next_var <= sb.cs_next_var` by simp[] >>
  `fin = (u with vs_logs := u.vs_logs ++ [ev]) with vs_inst_idx := LENGTH sb.cs_current_insts` by
    simp[Abbr `fin`] >>
  `(done_es with gas_obs := []) = (mid with logs := mid.logs ++ [ev]) with gas_obs := []` by
    simp[Abbr `done_es`] >>
  drule_all (BETA_RULE log_emit_normal_post) >> disch_then (qspec_then `lctx` ACCEPT_TAC)
QED
