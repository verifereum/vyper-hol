(* Linked RawLog continuation after the topics, for fixed bytes32 data. *)
Theory bodyRawLogFixedDataMods
Ancestors
  bodyFullPostsMods bodySliceFixedAllocMods bodyForcedStorageFrameMods
  bodyWriteSubscriptSourceMods exprBodyPreTypingProps vyperTypeExtCallCore
  gasOutcomeFullBindMods gasOutcomeFullZeroPrefixMods gasOutcomeFullPostMods
  gasContext exprSimDefs exprSimFullBundleProps stmtSimForRounds
  bodyFullPredsMods exprBodyPreProps bodyFullRawLogFixedCompose
  bodyFullRawLogFixedBoundary bodyFullIfExpReach bodyMemoryDefs
  wordArgsPtr stateRelProj valueEncodingProofs bodyPtrDefs venomMemDefs
  compileEnv venomState rich_list valueEncoding loweringPosts exprLoweringProps
  gasStorage bodyFullHashKeccakFixed stmtSimDefs loweringStateRelDefs list
  venomExecSemantics unitTransformDefs loweringShapeDefs
  vyperEvent vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  vyperValue vyperTyping vyperTypeExprSoundness
Libs monadsyntax

val raw_log_next = ``\v. do
    bs <- lift_option_type (dest_BytesV v) "raw_log data";
    type_check (LENGTH vals <= 4) "raw_log too many topics";
    check_not_static cx;
    push_log (encode_raw_event_values cx.txn.target vals bs);
    return NoneV
  od``;

Theorem fixed_log_next_replay[local]:
  LENGTH vals <= 4 ==>
  (^raw_log_next) (BytesV bs) (ee with gas_obs := tail) =
    if cx.txn.is_static then
      (INR (Error (RuntimeError "write in static context")),ee with gas_obs := tail)
    else
      (INL NoneV,ee with <|logs := ee.logs ++
          [encode_raw_event_values cx.txn.target vals bs]; gas_obs := tail|>)
Proof
  simp[dest_BytesV_def, lift_option_type_def, type_check_def, check_not_static_def,
       check_def, assert_def, push_log_def, bind_def, ignore_bind_def,
       raise_def, return_def] >>
  Cases_on `cx.txn.is_static` >> simp[]
QED

Theorem fixed_log_next_frame[local]:
  storage_trace_frame ((^raw_log_next) v)
Proof
  BETA_TAC >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_lifts] >> gen_tac >> BETA_TAC >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_check_not_static] >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_state_updates, storage_trace_frame_return]
QED

Theorem fixed_log_data_bytes[local]:
  expr_body_pre_mods mods cenv cx env data es /\
  body_const_cells_agree_mods mods cx env es /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  bind (eval_expr cx data) (read_result cx) (es with gas_obs := obs) = (INL v,mid) ==>
  ?bs. v = BytesV bs /\ LENGTH bs = 32
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env data (es with gas_obs := obs) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := obs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac runtime_consistent_get_tenv >>
  gvs[value_runtime_typed_def, evaluate_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

Theorem fixed_log_alloc_kept[local]:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx es s0 /\
  (!x. not_fresh_at sa x ==> FLOOKUP Ga x = FLOOKUP G0 x /\
    op_taint ta (Var x) = op_taint tn0 (Var x)) /\
  (!i. i < s0.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn0.t_mem)) ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 Ga ta
Proof
  strip_tac >> simp[ghost_kept_at_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
      fs[alloca_inv_def, alloca_next_valid_def] >>
      `off + sz <= s0.vs_alloca_next` by (first_x_assum irule >> goal_assum (drule_at Any)) >>
      `i < s0.vs_alloca_next` by decide_tac >>
      qpat_assum `!i. i < s0.vs_alloca_next ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >> drule_all_then assume_tac body_local_region_frontier >>
  `i < s0.vs_alloca_next` by decide_tac >>
  qpat_assum `!i. i < s0.vs_alloca_next ==> _` (qspec_then `i` mp_tac) >> simp[]
QED

Theorem fixed_log_topic_eval[local]:
  !ops ws. EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l)) ops /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  eval_operands ops s0 = SOME ws ==> eval_operands ops s = SOME ws
Proof
  Induct >> simp[eval_operands_def] >>
  Cases_on `h` >> simp[eval_operand_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem fixed_log_topic_clean[local]:
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l)) ops /\
  EVERY (\op. op_taint tn0 op = {}) ops /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
  EVERY (\op. op_taint tn op = {}) ops
Proof
  simp[EVERY_MEM, ghost_kept_at_def] >> rpt strip_tac >>
  Cases_on `op` >> simp[ptrDisciplineTheory.op_taint_def] >>
  rename1 `MEM (Var x) ops` >>
  `not_fresh_at sa x` by metis_tac[] >>
  `op_taint tn (Var x) = op_taint tn0 (Var x)` by metis_tac[] >>
  `op_taint tn0 (Var x) = {}` by metis_tac[] >>
  gvs[ptrDisciplineTheory.op_taint_def]
QED

Theorem fixed_log_word[local]:
  expr_post H ctx func cenv cx data es sd sm u ee (BytesV bs) data_op s /\
  post_value_type cenv data = BaseT (BytesT (Fixed 32)) /\ LENGTH bs = 32 ==>
  ?word. eval_operand data_op s = SOME word /\ TAKE 32 (word_to_bytes_be word) = bs
Proof
  strip_tac >>
  `expr_val_rel cx (BaseT (BytesT (Fixed 32))) (BytesV bs) data_op s` by
    gvs[expr_post_def] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def, is_word_type_def, evaluate_type_def] >>
  strip_tac >> simp[typed_val_to_w256_def] >>
  `PAD_RIGHT (0w:word8) 32 bs = bs` by simp[PAD_RIGHT] >>
  gvs[] >> qspec_then `bs` mp_tac TAKE_word_to_bytes_be_word_of_bytes_be >> simp[]
QED

Theorem raw_log_fixed_forced_cut_mods:
  expr_body_pre_mods mods cenv cx env data es /\
  body_const_cells_agree_mods mods cx env es /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\ post_value_type cenv data = expr_type data /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type data) data es /\
  compile_alloc_buffer 32 sa = (buf,sd) /\
  compile_alloc_buffer 32 shadow_sa = (buf,shadow_sd) /\
  fn_has_code sa sd func /\ fn_has_code shadow_sa shadow_sd shadow_func /\
  lower_value compile_expr cenv (expr_type data) data sd = (data_op,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type data)
    (gas_shadow_expr data) shadow_sd = (data_op,shadow_sm) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sd,sm,shadow_sd,shadow_sm) /\
  local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!bb. MEM bb func.fn_blocks ==> venomExecSemantics$phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst t. frag_reachable ctx func s0 fn inst t ==> unitTransformDefs$dalloca_fmp_headroom inst t) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (bind (eval_expr cx data) (read_result cx)) expr_res_ok es /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l)) ops /\
  eval_operands ops s0 = SOME (MAP event_value_to_word vals) /\
  EVERY (\op. op_taint tn0 op = {}) ops ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx data) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn s. ?bs word p w. res = INL (BytesV bs) /\
      expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
      expr_store_bound cx (expr_type data) (BytesV bs) data_op s /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
      immutable_frame_mods func cenv cx ee s /\
      ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G tn s /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_history func s /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ LENGTH bs = 32 /\
      eval_operand data_op s = SOME word /\ TAKE 32 (word_to_bytes_be word) = bs /\
      buf.buf_operand = Var p /\ eval_operand buf.buf_operand s = SOME w /\ ptr_covers G tn p s 32 /\
      FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\ w2n w + 32 < dimword (:256) /\
      (!name b n. local_region cenv ee.scopes s name b n ==> regions_disjoint (w2n w) 32 b n) /\
      (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
        regions_disjoint (w2n w) 32 b n) /\
      eval_operands ops s = SOME (MAP event_value_to_word vals) /\
      EVERY (\op. op_taint tn op = {}) ops /\ ~s.vs_halted /\
      s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >> drule_then strip_assume_tac expr_sim_full_code_fields >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- suspend "allocated"
  >> suspend "bad"
QED

Resume raw_log_fixed_forced_cut_mods[bad]:
  irule gas_outcome_full_mods_bad_nil >> simp[] >> gen_tac >>
  Cases_on `bind (eval_expr cx data) (read_result cx) (es with gas_obs := tail)` >>
  simp[] >> qpat_assum `bind (eval_expr _ _) _ _ = _`
    (mp_then (Pat `f st = _`) mp_tac storage_trace_frame_preserves_bad_domain) >>
  simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]
QED

Resume raw_log_fixed_forced_cut_mods[allocated]:
  mp_tac (Q.INST [`ce` |-> `cenv`, `sm` |-> `sd`, `s` |-> `s0`,
    `G` |-> `G0`, `tn` |-> `tn0`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    slice_fixed_capture_alloc_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`p`,`w`,`u`,`Ga`,`ta`] strip_assume_tac) >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl [`Ga`,`u`,`ta`] >> conj_tac >- simp[] >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then strip_assume_tac) >>
  drule_then assume_tac (SPEC_ALL stmt_state_rel_allocas_below_fmp) >>
  `!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK u,Ga,ta)` (qspec_then `DF (storage_trace_horizon es.storage_trace)` assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) [] _`
       (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     disch_then (mk_asm "after_alloc_safe") >> rpt gen_tac >> strip_tac >>
     asm_x "after_alloc_safe" irule >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE goal_assum (drule_at Any))) >>
  qhdtm_x_assum `expr_sim_full_mods`
    (qspecl_then [`st0`,`sd`,`sm`,`shadow_sd`,`shadow_sm`,`data_op`,`u`,`Ga`,`ta`] mp_tac o
     REWRITE_RULE [expr_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ ChildQ ChildR` >>
  irule gas_outcome_full_mods_post_source >> qexistsl [`ChildQ`,`ChildR`] >>
  simp[Abbr `ChildR`, Abbr `ChildQ`, expr_post_mods_def] >>
  rpt gen_tac >> strip_tac >>
  suspend "normal"
QED

Resume raw_log_fixed_forced_cut_mods[normal]:
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  drule_all_then (qx_choose_then `bs` strip_assume_tac) fixed_log_data_bytes >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `bind (eval_expr _ _) _ _ = _`
       (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
     simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s0 /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id` by
    (qspecl_then [`32`,`sa`] mp_tac ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sd x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op t` by
    (irule raw_log_fixed_data_reanchor >>
     qpat_assum `compile_alloc_buffer 32 sa = _` (irule_at Any) >> qexists `u` >>
     simp[] >> gen_tac >> strip_tac >> first_x_assum drule >> simp[]) >>
  `ptr_covers G' tn' p t 32 /\ FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32)` by
    (drule_all_then ACCEPT_TAC raw_log_fixed_scratch_post) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Ga ta` by
    (irule fixed_log_alloc_kept >> simp[] >>
     qexistsl [`H`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC) >>
  `!name b n. local_region cenv es.scopes u name b n <=> local_region cenv es.scopes s0 name b n` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (irule ghost_kept_at_trans >> qexistsl [`Ga`,`es`,`u`,`sd`,`ta`] >> simp[]) >>
  suspend "payload"
QED

Resume raw_log_fixed_forced_cut_mods[payload]:
  qpat_assum `expr_post H _ _ _ _ _ es sd sm u ee _ _ t`
    (mp_then (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac fixed_log_word) >>
  simp[] >> disch_then (qx_choose_then `word` strip_assume_tac) >>
  `lookup_var p t = SOME w` by
    (qpat_assum `expr_post H _ _ _ _ _ es sd sm u ee _ _ t`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     first_x_assum irule >> simp[]) >>
  `!name b n. local_region cenv ee.scopes t name b n ==> local_region cenv es.scopes u name b n` by
    (qpat_assum `expr_post H _ _ _ _ _ es sd sm u ee _ _ t`
       (strip_assume_tac o REWRITE_RULE [expr_post_def, locals_kept_def]) >>
     rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC local_region_kept) >>
  `eval_operands ops t = SOME (MAP event_value_to_word vals)` by
    (irule fixed_log_topic_eval >> qexistsl [`s0`,`sa`] >> simp[] >>
     qpat_assum `expr_post H _ _ _ _ _ es sa sm s0 ee _ _ t`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  `EVERY (\op. op_taint tn' op = {}) ops` by
    (drule_all_then ACCEPT_TAC fixed_log_topic_clean) >>
  qexists `word` >> simp[eval_operand_def] >> conj_tac
  >- (map_every qx_gen_tac [`name`,`b`,`n`] >> disch_tac >>
      qpat_assum `!name b n. local_region cenv es.scopes u name b n ==> _` irule >>
      qexists `name` >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Finalise raw_log_fixed_forced_cut_mods
