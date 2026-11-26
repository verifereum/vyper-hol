(* Join the two keyword-read producers at the same linked endpoint. *)
Theory bodyExtKeywordHeadRunMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullIfExpReach
  bodyWriteSubscriptSourceMods bodyBranchCellFrameMods
  gasOutcomeFullMods gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  fragGasOriginPtr fragExec exprSimDefs stmtSimDefs vyperState vyperInterpreter
  exprLowering compileEnv bodyPtrDefs loweringPosts venomState
  finite_map list pair arithmetic
Libs monadsyntax

Theorem keyword_source_landing[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\ ee.gas_obs = [] /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := obs ++ tail) = (INL v,ee with gas_obs := tail)) ==>
  expr_sim_inv_mods mods cenv cx env ee /\
  body_const_cells_agree_mods mods cx env ee /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes
Proof
  strip_tac >>
  qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
  simp[] >> strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := obs)` by simp[] >>
  `body_const_cells_agree_mods mods cx env (es with gas_obs := obs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  drule_then (assume_tac o SRULE []) eval_read_preserves_scopes_dom >>
  fs[write_subscript_source_gas_obs_mods, body_const_cells_agree_mods_branch_updates]
QED

Theorem keyword_head_exit[local]:
  expr_exit (res : value + exception) r ==> ?exc. res = INR exc
Proof
  Cases_on `res` >> simp[] >> Cases_on `r` >> simp[expr_exit_def]
QED

val common = ``\(H : (bool # bytes32 # type_value) list # num list) ee G tn t.
  stmt_state_rel H ctx func cenv cx ee t /\
  immutable_frame_mods func cenv cx ee t /\
  storage_well_formed_on cx ee (FST H) /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  return_buf_frame d cenv sb t /\ wb_frame cenv es ee sa s0 t /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  t.vs_labels = s0.vs_labels /\
  (!x. op = Var x ==> not_fresh_at sb x)``;

val scalar = ``\v G tn t.
  (k <> EKDefault ==> ?w. eval_operand op t = SOME w /\
    dest_NumV v = SOME (w2n w) /\ op_taint tn op = {}) /\
  (k = EKDefault ==> dt = rt /\ expr_val_rel cx rt v op t /\
    ptr_val_ok cx rt v op G tn t)``;

val owned = ``\v ee G tn t.
  dt = lowered_value_type cenv e /\ ptr_val_ok cx dt v op G tn t /\
  ptr_mem_ok cx dt v op G tn t /\ ptr_buf_ok cenv e op G t /\
  (!w. eval_operand op t = SOME w /\ type_memory_bytes cenv dt <> 0 ==>
    w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next) /\
  (?w aid tv. eval_operand op t = SOME w /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
    val_wf tv v /\ FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
    aid < sb.cs_next_id /\
    (!n b sz. local_region cenv ee.scopes t n b sz ==>
      regions_disjoint (w2n w) (type_memory_size tv) b sz))``;

val guard = ``k = EKDefault /\ ~is_word_type rt``;
val scalar_post = ``\H (res : value + exception) ee G tn t. ?v. res = INL v /\
  ^common H ee G tn t /\ ^scalar v G tn t``;
val owned_post = ``\H (res : value + exception) ee G tn t. ?v. res = INL v /\
  ^common H ee G tn t /\ ^owned v ee G tn t``;
val selected = ``\H (res : value + exception) ee G tn t. ?v. res = INL v /\
  ^common H ee G tn t /\
  (k <> EKDefault ==> ?w. eval_operand op t = SOME w /\
    dest_NumV v = SOME (w2n w) /\ op_taint tn op = {}) /\
  (k = EKDefault ==> if is_word_type rt then
     dt = rt /\ expr_val_rel cx rt v op t /\ ptr_val_ok cx rt v op G tn t
   else ^owned v ee G tn t)``;
val exit_post = ``\(H : (bool # bytes32 # type_value) list # num list)
  (res : value + exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;
val outcome = ``gas_outcome_full_mods
    (DF : (bool # bytes32 # type_value) list # num list -> dead,
     lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    mods cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)``;

Theorem extcall_keyword_head_outcome_mods:
  contract_inv mods exps ctx cenv cx /\ MEM func ctx.ctx_functions /\
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (~^guard ==> ^outcome ^scalar_post ^exit_post) /\
  (^guard ==> ^outcome ^owned_post ^exit_post) ==>
  ^outcome
    (\H res ee G tn t. ?v. res = INL v /\
      ^common H ee G tn t /\ ee.gas_obs = [] /\
      expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
      (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u) /\
      (k <> EKDefault ==> ?w. eval_operand op t = SOME w /\
        dest_NumV v = SOME (w2n w) /\ op_taint tn op = {}) /\
      (k = EKDefault ==> if is_word_type rt then
         dt = rt /\ expr_val_rel cx rt v op t /\ ptr_val_ok cx rt v op G tn t
       else ^owned v ee G tn t))
    (\H res ee gt r. ?exc. res = INR exc /\ ^exit_post H (INR exc) ee gt r)
Proof
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  `^outcome ^selected ^exit_post` by
    (Cases_on `^guard` >> gvs[] >>
     irule gas_outcome_full_mods_post_source >>
     goal_assum (drule_at Any) >> simp[] >>
     rpt gen_tac >> strip_tac >> qexists_tac `v` >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC body_inv_no_phi_mods) >>
  `^outcome
     (\H res ee G tn t. ^selected H res ee G tn t /\
       (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u))
     ^exit_post` by
    (irule gas_outcome_full_mods_post_path >>
     goal_assum (drule_at Any) >> BETA_TAC >> rpt gen_tac >> strip_tac >>
     simp[] >> rpt strip_tac >>
     drule_all_then ACCEPT_TAC gas_origin_ptr_path_dalloca_fmp_headroom) >>
  irule gas_outcome_full_mods_post_source >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      drule_all_then strip_assume_tac keyword_source_landing >>
      simp[] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> drule_then strip_assume_tac keyword_head_exit >>
  qexists_tac `exc` >> gvs[]
QED
