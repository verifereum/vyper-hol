(* Land the nonword qualified Assign suffix at the actual storage or
   transient destination.  The delayed unwrap may have an empty interval
   (e.g. a snapshot already in memory), or a counted, gas-silent prefix. *)
Theory bodyQualifiedPlaceSlotAggregateMods
Ancestors
  bodyWriteSlotCopyMods bodyAssignQualifiedStageJoinMods gasOutcomeFullZeroPrefixMods
  gasOutcomeFullPostMods bodyPtrDefs bodyFullPostsMods bodyFullShadowBodyInv
  loweringPosts loweringStateRelDefs placeStoreStorage fragGasOriginPtr fragExec
  compileEnv exprLowering stmtSimDefs bodySimFull bodyInvSplit vyperStorageFootprint
  vyperTypeSystem vyperStorageBackend finite_map words

val slot_cut =
  ``fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    sa0.cs_next_var <= sa.cs_next_var /\ storage_trace_domain cx st0 es.storage_trace /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      storage_place_observed H (StoragePlace tr dw dtv) /\
      stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx es G tn s /\ return_buf_sep d cenv es s) /\
    return_buf_frame d cenv sa s /\ alloca_history func s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\
    alloca_frame cenv es0 sa0 s0 cenv es s /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    eval_operand dst s = SOME dw /\ op_taint tn dst = {}``;

val rhs_cut =
  ``acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
        sz = type_memory_size rt) fields) /\
    local_ptrs_reserved cenv sa /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ op_taint tn src = {} /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n sw) mem) /\
    (type_memory_size tv <> 0 ==> ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
    w2n sw + type_memory_size tv < dimword (:256) /\
    (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next)``;

val slot_types =
  ``evaluate_type (get_tenv cx) dty = SOME dtv /\ assignable_type (get_tenv cx) dty /\
    ~is_word_type dty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv v /\ type_widens_to (get_tenv cx) ty dty /\ ~is_word_type ty /\
    (dty <> ty /\ ~(is_bytestring_type dty /\ is_bytestring_type ty) ==>
      sa0.cs_next_id <= sa.cs_next_id /\ local_ptrs_reserved cenv sa0 /\
      MAP FDOM es0.scopes = MAP FDOM es.scopes /\ 0 < type_memory_size tv /\
      type_memory_size dtv < dimword (:256) /\ (?start. expr_val_at cenv cx ty start sa es v src s))``;

val slot_post =
  ``\(H : (bool # 256 word # type_value) list # num list) res ee Gf tf u.
    res = INL () /\ stmt_lands lctx sb res u /\ ~u.vs_halted /\ ~block_is_terminated sb /\
    cenv_top_ext cenv cenv ee.scopes /\ stmt_state_rel H ctx func cenv cx ee u /\
    immutable_frame_mods func cenv cx ee u /\ storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv sb u /\ return_buf_sep d cenv ee u /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee Gf tf u /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa0 x ==> FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es0 sa0 s0 cenv ee u /\
    (!aid off sz i.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
      (!n b sz'. local_region cenv es0.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)``;

Theorem qualified_place_slot_copy_mods:
  assign_place_store_code_mods cenv e (SOME vv) (dst,SOME (slot_loc tr),SOME (ValPT dty))
    st = ((),sb) /\ unwrap_value cenv vv st = (src,sa) /\
  ty = lowered_value_type cenv e /\ ^slot_cut /\ ^rhs_cut /\ ^slot_types /\
  (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK s,G,tn)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (StoragePlace tr dw dtv) v) (es,z,Gz,tz)
    ^slot_post (assign_qualified_exit_mods ctx cx RetQ)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_assign_value cenv dst (slot_loc tr) src (is_word_type dty)
     (vv_location vv) dty ty (type_memory_bytes cenv dty) sa = ((),sb)` by
    (qpat_assum `assign_place_store_code_mods _ _ _ _ _ = _`
       (mp_tac o REWRITE_RULE [qualified_assign_store_code_mods]) >>
     pure_asm_rewrite_tac[comp_bind_def, LET_THM, pairTheory.UNCURRY] >> simp[]) >>
  irule gas_outcome_full_mods_zero_prefix >> qexistsl_tac [`G`,`s`,`tn`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  mp_tac (Q.INST [`src_loc` |-> `vv_location vv`] (SPEC_ALL slot_copy_writeback_mods)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[SF CONJ_ss])) >>
  strip_tac >> irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  reverse conj_tac
  >- (rewrite_tac[assign_qualified_exit_mods_def] >> rpt gen_tac >>
      disch_then ACCEPT_TAC) >>
  map_every qx_gen_tac [`H`,`res`,`ee`,`Gf`,`tf`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ Gf tf`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ghost_kept_at_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
