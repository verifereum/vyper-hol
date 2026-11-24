(* Land the two scalar slot stores of a qualified Assign.  The frame at
   the store cursor is relative to the origin of the whole statement. *)
Theory bodyQualifiedPlaceSlotScalarMods
Ancestors
  bodyAssignQualifiedStageJoinMods bodyWriteSlotCopyMods bodyWriteSlotWordMods
  gasOutcomeFullZeroPrefixMods gasOutcomeFullPostMods tuplePlaceStep
  stmtLowering placeStoreSlots compileEnv bodyPtrDefs loweringPosts

val store_frame =
  ``(!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee s /\
      immutable_frame_mods func cenv cx ee s /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
      return_buf_sep d cenv ee s) /\
    return_buf_frame d cenv sm s /\ alloca_history func s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    alloca_frame cenv es sa s0 cenv ee s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\ fn_has_code sm sb func``;

val store_post =
  ``\(H : (bool # bytes32 # type_value) list # num list) res ef Gf tf t.
      ?ce. stmt_lands lctx sb res t /\ ~t.vs_halted /\
        (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
        cenv_top_ext cenv ce ef.scopes /\ stmt_state_rel H ctx func ce cx ef t /\
        immutable_frame_mods func ce cx ef t /\ storage_well_formed_on cx ef (FST H) /\
        return_buf_frame d ce sb t /\ alloca_history func t /\ return_buf_sep d ce ef t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d ce cx ef Gf tf t /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa x ==>
          FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame cenv es sa s0 ce ef t /\
        (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
          (!n b len. local_region cenv es.scopes s0 n b len ==> off + sz <= b \/ b + len <= off) /\
          off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)``;

(* Both physical store rules return the same frame, packaged as ghost_kept_at. *)
val store_core =
  ``\(H : (bool # bytes32 # type_value) list # num list) res ef Gf tf t.
      res = INL () /\ stmt_lands lctx sb res t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
      cenv_top_ext cenv cenv ef.scopes /\ stmt_state_rel H ctx func cenv cx ef t /\
      immutable_frame_mods func cenv cx ef t /\ storage_well_formed_on cx ef (FST H) /\
      return_buf_frame d cenv sb t /\ return_buf_sep d cenv ef t /\ alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ef Gf tf t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf /\ alloca_frame cenv es sa s0 cenv ef t``;

val store_exit =
  ``\(H : (bool # bytes32 # type_value) list # num list) res ef (gt : (string |-> num # num) # taint) r.
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) res gt r) /\
      halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !t. (r = Halt t \/ ?ir. r = IntRet ir t) ==>
        allocas_below_fmp t)``;

Theorem qualified_slot_finish[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    source (ee,s,G,tn) ^store_core ^store_exit ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    source (ee,s,G,tn) ^store_post (assign_qualified_exit_mods ctx cx RetQ)
Proof
  disch_tac >> drule_then irule gas_outcome_full_mods_post_source >>
  reverse conj_tac >- (pure_rewrite_tac[assign_qualified_exit_mods_def] >> BETA_TAC >> simp[NoAsms, EQ_REFL]) >>
  BETA_TAC >>
  rpt gen_tac >> disch_then (strip_assume_tac) >>
  qexists_tac `cenv` >> fs[ghost_kept_at_def] >> first_assum ACCEPT_TAC
QED

Theorem qualified_place_slot_empty_mods:
  ^store_frame /\ fn_inst_ids_distinct func /\ sa.cs_next_var <= sm.cs_next_var /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    storage_place_observed H (StoragePlace tr dw dtv)) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ v = default_value dtv /\ has_length_word dty /\
  assign_place_store_code_mods cenv e NONE (dst,SOME (slot_loc tr),SOME (ValPT dty)) sm = ((),sb) /\
  eval_operand dst s = SOME dw /\ op_taint tn dst = {} ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (StoragePlace tr dw dtv) v) (ee,s,G,tn)
    ^store_post (assign_qualified_exit_mods ctx cx RetQ)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> irule qualified_slot_finish >>
  irule slot_copy_writeback_mods >>
  qpat_assum `evaluate_type (get_tenv cx) dty = SOME _` (irule_at Any) >>
  qpat_assum `fn_has_code sm sb func` (irule_at Any) >>
  qpat_assum `eval_operand dst s = SOME _` (irule_at Any) >>
  `compile_store_at_loc cenv.ce_imm_alloca dst (Lit 0w)
      (SOME (if tr then LocTransient else LocStorage)) sm = ((),sb)` by
    fs[qualified_assign_store_code_mods, slot_loc_def] >>
  simp[SF CONJ_ss] >>
  qexistsl_tac [`ARB`, `ARB`, `ARB`, `ARB`, `ARB`, `cenv.ce_imm_alloca`] >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Theorem qualified_place_slot_word_mods:
  ^store_frame /\
  MEM (StorageRoot tr offset tv0) ee.storage_trace /\
  storage_subregion tv0 path delta dtv /\ dw = n2w offset + n2w delta /\
  is_word_type dty /\ evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  write_place cx (StoragePlace tr dw dtv) v ee = (res,ef) /\
  assign_place_store_code_mods cenv e (SOME vv)
    (dst,SOME (slot_loc tr),SOME (ValPT dty)) st = ((),sb) /\
  unwrap_value cenv vv st = (op,sm) /\
  (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK s,G,tn)) /\
  eval_operand dst s = SOME dw /\ eval_operand op s = SOME (typed_val_to_w256 dtv v) /\
  op_taint tn dst = {} /\ op_taint tn op = {} ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (StoragePlace tr dw dtv) v) (ee,z,Gz,tz)
    ^store_post (assign_qualified_exit_mods ctx cx RetQ)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `emit_void (if tr then TSTORE else SSTORE) [dst;op] sm = ((),sb)` by
    (qpat_x_assum `assign_place_store_code_mods _ _ (SOME _) _ _ = _` mp_tac >>
     simp[qualified_assign_store_code_mods, comp_bind_def, IgnAsm `is_word_type dty`] >>
     disch_tac >> drule_then strip_assume_tac place_store_storage_compile >> gvs[]) >>
  drule_then assume_tac write_place_storage_trace >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl_tac [`G`, `s`, `tn`] >> conj_tac >- first_assum ACCEPT_TAC >>
  irule qualified_slot_finish >>
  irule gas_outcome_full_mods_post_source >>
  irule_at (Pat `gas_outcome_full_mods _ _ _ _ _ _ _ _`) slot_word_writeback_mods >>
  qpat_assum `emit_void _ [dst;op] sm = _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ ee = _` (irule_at Any) >>
  qpat_assum `storage_subregion tv0 path delta dtv` (irule_at Any) >>
  qpat_assum `evaluate_type (get_tenv cx) dty = SOME _` (irule_at Any) >>
  simp[Excl "AND_IMP_INTRO"] >>
  qexistsl_tac [`tn0`, `sa`, `s0`, `offset`, `lctx`, `es`, `d`, `cenv`, `RetQ`, `G0`] >>
  simp[Excl "AND_IMP_INTRO"] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED
