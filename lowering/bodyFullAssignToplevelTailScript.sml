(* Joint Assign storage continuation, after the forced RHS. *)
Theory bodyFullAssignToplevelTail
Ancestors
  stmtSimAssignStorage augAssignFullStore augAssignFullStoreGhost
  bodyMemoryDefs bodySimFull gasOutcomeFullCompose accountsRelProps stmtSimProps
  allocaHistory exprLoweringProps vyperTyping loweringPosts stmtSimDefs
  vyperStorageFootprint vyperStorageBackend vyperState emitHelper
  compileEnv context emitHelperProps venomInst loweringStateRelDefs stmtSimDeclMem
  entryDecoderHistoryFrame fragExec venomExecSemantics venomState bodyPtrDefs ptrDiscipline
  list finite_map pred_set

Theorem body_assign_toplevel_word_store_history[local]:
  emit_void (if tr then TSTORE else SSTORE) [Lit slot;op] sb = ((),sf) /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  alloca_history func t /\ alloca_inv t /\ ~t.vs_call_ctx.cc_static /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  eval_operand op t = SOME w ==>
  alloca_history func
    ((if tr then tstore slot w t else sstore slot w t)
      with vs_inst_idx := LENGTH sf.cs_current_insts)
Proof
  strip_tac >> irule entry_straight_line_alloca_history >>
  simp[] >> qexistsl [`t`, `sb`] >> Cases_on `tr` >>
  gvs[emitted_insts_emit_void, emit_void_def, emit_inst_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def,
      fresh_id_def, emitted_insts_def, run_inst_seq_def,
      step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
      is_terminator_def, eval_operand_def, DROP_APPEND]
QED

Theorem body_assign_toplevel_word_full_store_post:
  expr_post H ctx func cenv cx e es0 sa sb s0 ee v op t /\
  stmt_state_rel H ctx func cenv cx es0 s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM ee.scopes = MAP FDOM es0.scopes /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\ type_slot_size tvt = 1 /\
  encode_value tvt v = SOME [(0,w)] /\ value_has_type tvt v /\
  eval_operand op t = SOME w /\
  write_storage_slot cx tr (n2w slot) tvt v ee = (INL (),ef) /\
  MEM (tr,n2w slot,tvt) (FST H) /\ regions_consistent (FST H) /\
  emit_void (if tr then TSTORE else SSTORE) [Lit (n2w slot);op] sb = ((),sf) /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  return_buf_frame d cenv sb t /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  dead_lo_ok H D lo cenv cx /\ ghost_inv_at D lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn ==>
  stmt_post H ctx func cx lctx cenv cenv sa sf es0 s0 (INL ()) ef
    ((if tr then tstore (n2w slot) w t else sstore (n2w slot) w t)
      with vs_inst_idx := LENGTH sf.cs_current_insts) /\
  return_buf_frame d cenv sf
    ((if tr then tstore (n2w slot) w t else sstore (n2w slot) w t)
      with vs_inst_idx := LENGTH sf.cs_current_insts) /\
  alloca_history func
    ((if tr then tstore (n2w slot) w t else sstore (n2w slot) w t)
      with vs_inst_idx := LENGTH sf.cs_current_insts) /\
  s0.vs_alloca_next <=
    (if tr then tstore (n2w slot) w t else sstore (n2w slot) w t).vs_alloca_next /\
  ghost_inv_at D lo d cenv cx ef G
    (if tr then tn with t_trans := key_update tn.t_trans (n2w slot) {}
     else tn with t_stor := key_update tn.t_stor (n2w slot) {})
    ((if tr then tstore (n2w slot) w t else sstore (n2w slot) w t)
      with vs_inst_idx := LENGTH sf.cs_current_insts) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint (if tr then tn with t_trans := key_update tn.t_trans (n2w slot) {}
              else tn with t_stor := key_update tn.t_stor (n2w slot) {}) (Var x) =
    op_taint tn0 (Var x))
Proof
  strip_tac >>
  `!u st. storage_dead H tr (update_storage (n2w slot) u st) = storage_dead H tr st`
    by metis_tac[storage_dead_update_word_region] >>
  `stmt_state_rel H ctx func cenv cx ee t /\
   storage_well_formed_on cx ee (FST H)` by fs[expr_post_def] >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >>
  `storage_well_formed_on cx ef (FST H)` by
    (drule (cj 1 evaluate_type_well_formed) >> strip_tac >>
     metis_tac[typed_write_preserves_storage_well_formed_on]) >>
  `ef.scopes = ee.scopes` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq] >> Cases_on `tr` >>
     simp[set_storage_def] >> strip_tac >> gvs[AllCaseEqs()]) >>
  `sf.cs_current_bb = sb.cs_current_bb /\
   LENGTH sf.cs_current_insts = SUC (LENGTH sb.cs_current_insts) /\
   sb.cs_next_var <= sf.cs_next_var` by
    (Cases_on `tr` >>
     gvs[emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def,
         comp_ignore_bind_def, comp_return_def, emit_def]) >>
  `~block_is_terminated sf` by
    (Cases_on `tr` >> gvs[] >> drule emit_void_nonterminator_open >>
     simp[is_terminator_def]) >>
  `alloca_frame cenv es0 sa s0 cenv ee t` by
    metis_tac[expr_post_alloca_frame] >>
  `t.vs_call_ctx.cc_address = cx.txn.target` by fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `!k b. storage_dead H tr (update_storage (n2w slot) w
      (if tr then contract_transient t else contract_storage t)) k b =
      storage_dead H tr (if tr then contract_transient t else contract_storage t) k b` by simp[] >>
  drule_all ghost_inv_at_storage_word_store >>
  disch_then (qspec_then `LENGTH sf.cs_current_insts` assume_tac) >>
  drule_all ghost_kept_at_storage_word_store >> strip_tac >>
  conj_tac
  >- (simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl,
           stmt_state_rel_inst_idx] >>
      Cases_on `tr` >>
      gvs[sstore_def, tstore_def, lookup_var_def, alloca_frame_def,
          expr_post_def, local_region_def, local_backed_def] >>
      first_assum MATCH_ACCEPT_TAC) >>
  conj_tac
  >- (irule return_buf_frame_frame >> qexistsl [`cenv`, `t`, `sb`] >>
      Cases_on `tr` >> simp[sstore_def, tstore_def, lookup_var_def]) >>
  conj_tac
  >- (irule body_assign_toplevel_word_store_history >>
      fs[stmt_state_rel_def, state_rel_def] >> qexistsl [`op`, `sb`] >> simp[]) >>
  Cases_on `tr` >> gvs[sstore_def, tstore_def, ghost_kept_at_def]
QED

Theorem body_assign_toplevel_word_full_continue:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\ type_slot_size tvt = 1 /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  is_word_type (expr_type e) /\ value_has_type tvt v /\
  encode_value tvt v = SOME [(0,typed_val_to_w256 etv v)] /\
  emit_void (if tr then TSTORE else SSTORE) [Lit (n2w slot);op] sb = ((),sf) /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  local_ptrs_reserved cenv sa /\ MAP FDOM ee.scopes = MAP FDOM es0.scopes /\
  ee.gas_obs = [] /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\ op_taint tn op = {} /\
  return_buf_frame d cenv sb t /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
  storage_trace_domain cx st0 (ee.storage_trace ++ [StorageRoot tr slot tvt]) /\
  (!H. valid_horizon cx st0 H (ee.storage_trace ++ [StorageRoot tr slot tvt]) ==>
    expr_post H ctx func cenv cx e es0 sa sb s0 ee v op t /\
    stmt_state_rel H ctx func cenv cx es0 s0 /\ dead_lo_ok H (DF H) lo cenv cx /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn t) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (ignore_bind (record_storage_event (StorageRoot tr slot tvt))
      (write_storage_slot cx tr (n2w slot) tvt v)) (ee,t,G,tn)
    (\H res ef Gf tnf tf.
      res = INL () /\ stmt_post H ctx func cx lctx cenv cenv sa sf es0 s0 res ef tf /\
      return_buf_frame d cenv sf tf /\ alloca_history func tf /\
      s0.vs_alloca_next <= tf.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ef Gf tnf tf /\
      (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
           op_taint tnf (Var x) = op_taint tn0 (Var x))) R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon
      (ee.storage_trace ++ [StorageRoot tr slot tvt]))
      (ee.storage_trace ++ [StorageRoot tr slot tvt])` by fs[storage_trace_domain_def] >>
  `~cx.txn.is_static /\ ~t.vs_call_ctx.cc_static` by
    (first_x_assum drule >> simp[expr_post_def, stmt_state_rel_def, state_rel_def]) >>
  Cases_on `write_storage_slot cx tr (n2w slot) tvt v ee` >>
  rename1 `write_storage_slot _ _ _ _ _ _ = (res,ef)` >>
  `res = INL ()` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >> simp[write_storage_slot_eq]) >>
  gvs[] >>
  `ef.storage_trace = ee.storage_trace` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq] >> Cases_on `tr` >> simp[set_storage_def] >> strip_tac >> gvs[]) >>
  irule gas_outcome_full_intro >>
  qexistsl [`G`,
    `ef with storage_trace := ee.storage_trace ++ [StorageRoot tr slot tvt]`, `[]`,
    `OK ((if tr then tstore (n2w slot) (typed_val_to_w256 etv v) t
           else sstore (n2w slot) (typed_val_to_w256 etv v) t)
          with vs_inst_idx := LENGTH sf.cs_current_insts)`, `INL ()`,
    `if tr then tn with t_trans := key_update tn.t_trans (n2w slot) {}
     else tn with t_stor := key_update tn.t_stor (n2w slot) {}`] >>
  simp[] >> conj_tac
  >- (simp[ignore_bind_def, record_storage_event_def, return_def, bind_def] >>
      gen_tac >> drule write_storage_slot_storage_trace >>
      disch_then (qspec_then `ee.storage_trace ++ [StorageRoot tr slot tvt]` assume_tac) >>
      simp[write_storage_slot_gas_obs]) >>
  qx_gen_tac `H` >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `eval_operand op t = SOME (typed_val_to_w256 etv v)` by
    (gvs[expr_post_def, expr_val_rel_def, post_value_type_word] >> metis_tac[]) >>
  conj_tac
  >- (irule storage_word_store_origin_ptr >> simp[] >>
      conj_tac >- fs[ghost_inv_at_def] >>
      conj_tac >- fs[ghost_inv_at_def] >>
      qexistsl [`Lit (n2w slot)`, `op`, `sb`] >>
      simp[eval_operand_def, op_taint_def]) >>
  `ef.gas_obs = []` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq] >> Cases_on `tr` >>
     simp[set_storage_def] >> strip_tac >> gvs[]) >>
  `MEM (tr,n2w slot,tvt) (FST H) /\ regions_consistent (FST H)` by
    (qpat_x_assum `valid_horizon cx st0 H _` mp_tac >>
     simp[valid_horizon_def, storage_observations_ok_def,
          storage_trace_regions_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND]) >>
  drule_all body_assign_toplevel_word_full_store_post >>
  disch_then (qspec_then `lctx` strip_assume_tac) >>
  disj1_tac >> pure_once_rewrite_tac[GSYM evaluation_state_fupdcanon] >>
  `(ef with gas_obs := []) = ef` by simp[evaluation_state_component_equality] >>
  simp[stmt_post_storage_trace]
QED
