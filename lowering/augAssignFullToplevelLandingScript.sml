(* Literal scalar AugAssign store: concrete landing with semantic relations supplied. *)
Theory augAssignFullToplevelLanding
Ancestors
  augAssignFullStore augAssignFullHistory bodyMemoryDefs stmtSimDefs stmtSimProps
  loweringPosts exprOpenPrimitives emitHelperProps emitHelper exprLoweringProps
  ptrDiscipline allocaHistory venomExecSemantics venomInst venomState
  compileEnv loweringStateRelDefs list finite_map pred_set

Theorem augassign_toplevel_store_landing_full:
  emit_void (if tr then TSTORE else SSTORE) [Lit (n2w slot);res_op] s3 = ((),sb) /\
  fn_has_code s3 sb func /\ fn_inst_ids_distinct func /\
  ~operated.vs_halted /\ ~ctx_has_dalloca ctx /\
  operated.vs_current_bb = s3.cs_current_bb /\
  operated.vs_inst_idx = LENGTH s3.cs_current_insts /\
  ~operated.vs_call_ctx.cc_static /\ eval_operand res_op operated = SOME w /\
  op_taint tnop res_op = {} /\
  last = (if tr then tstore (n2w slot) w operated else sstore (n2w slot) w operated)
    with vs_inst_idx := LENGTH sb.cs_current_insts /\
  tnlast = (if tr then tnop with t_trans := key_update tnop.t_trans (n2w slot) {}
    else tnop with t_stor := key_update tnop.t_stor (n2w slot) {}) /\
  fin.scopes = mid.scopes /\
  alloca_frame cenv es sa s0 cenv mid operated /\
  (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
    lookup_var x operated = SOME v) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP operated.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP Gop x = FLOOKUP G0 x /\
    op_taint tnop (Var x) = op_taint tn0 (Var x)) /\
  return_buf_frame d cenv s3 operated /\ alloca_history func operated /\
  alloca_inv operated /\ s0.vs_alloca_next <= operated.vs_alloca_next /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx fin last /\
    storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx fin Gop tnlast last) ==>
  (!D lo. allocas_from lo operated /\ lo <= operated.vs_alloca_next ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (operated,Gop,tnop) []
      (OK last,Gop,tnlast)) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_post H ctx func cx lctx cenv cenv sa sb es s0 (INL ()) fin last /\
    return_buf_frame d cenv sb last /\ alloca_history func last /\
    s0.vs_alloca_next <= last.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx fin Gop tnlast last /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gop x = FLOOKUP G0 x /\
      op_taint tnlast (Var x) = op_taint tn0 (Var x)))
Proof
  strip_tac >>
  `step_inst_base (mk_inst s3.cs_next_id (if tr then TSTORE else SSTORE)
    [Lit (n2w slot);res_op] []) operated =
    OK (if tr then tstore (n2w slot) w operated else sstore (n2w slot) w operated)` by
    (Cases_on `tr` >> simp[step_inst_base_opcode_eqs, mk_inst_def,
      exec_write2_def, eval_operand_def]) >>
  `~is_terminator (if tr then TSTORE else SSTORE)` by
    (Cases_on `tr` >> simp[is_terminator_def]) >>
  drule_all augassign_emit_void_history >> strip_tac >>
  `~block_is_terminated sb` by metis_tac[emit_void_terminated] >>
  `sb.cs_current_bb = s3.cs_current_bb /\ s3.cs_next_var <= sb.cs_next_var` by
    (drule emit_void_same_blocks >> drule emitted_insts_emit_void >>
     simp[same_blocks_def]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `last = _` SUBST1_TAC >>
      qpat_x_assum `tnlast = _` SUBST1_TAC >>
      irule storage_word_store_origin_ptr >> simp[] >>
      qexistsl_tac [`Lit (n2w slot)`, `res_op`, `s3`] >>
      simp[eval_operand_def, op_taint_def] >>
      qpat_x_assum `op_taint tnop res_op = {}` mp_tac >> simp[op_taint_def]) >>
  qx_gen_tac `H` >> disch_tac >>
  `alloca_frame cenv es sa s0 cenv fin last` by
    (Cases_on `tr` >> gvs[alloca_frame_def, local_region_def, lookup_var_def,
      sstore_def, tstore_def] >> first_assum MATCH_ACCEPT_TAC) >>
  `return_buf_frame d cenv sb last` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `operated`, `s3`] >>
     Cases_on `tr` >> simp[sstore_def, tstore_def, lookup_var_def]) >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  Cases_on `tr` >> gvs[sstore_def, tstore_def, lookup_var_def, op_taint_def]
QED
