(* Adapt the reached operand cut to the aggregate slot writeback. *)
Theory bodyQualifiedAssignSlotCopyLandingMods
Ancestors
  bodyQualifiedAssignOperandCutMods bodyQualifiedPlaceSlotAggregateMods
  bodyAssignQualifiedStageJoinMods
  bodyInvCodeProps exprSimHypsDefs placeDestinationBounds annassignRelayoutPost
  stmtSimAugAssignPlaceStorage typedMemoryCopy bodySim allocLimits
  bodyFullTargetDefs bodyWriteTargetStageMods bodyFullPostsMods
  gasOutcomeFullPostMods loweringStateRelDefs loweringPosts
  finite_map words arithmetic

val landing_post =
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

Theorem qualified_assign_slot_copy_landing_mods:
  qualified_assign_operand_cut_mods (DF,lo,d,explicit,ctx,func,PG)
    cenv cx st0 (bt,e,dty) (vv,op,StoragePlace tr dw dtv,
      (dst,SOME (slot_loc tr),SOME (ValPT dty)),v) (sa,st,su,sb)
    (es,s0,G0,tn0) (ee,z,Gz,tz) (s,G,tn) /\
  eval_target_place cx bt mid = (INL (StoragePlace tr dw dtv),ee) /\
  assign_place_rhs_code_mods cenv bt e sa = (SOME vv,sr) /\
  compile_get_target_ptr compile_expr cenv bt sr =
    ((dst,SOME (slot_loc tr),SOME (ValPT dty)),st) /\
  assign_place_store_code_mods cenv e (SOME vv)
    (dst,SOME (slot_loc tr),SOME (ValPT dty)) st = ((),sb) /\
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env ee /\
  stmt_exprs_ok cenv (Assign (BaseTarget bt) e) /\
  assignable_type (get_tenv cx) dty /\ ~is_word_type dty /\ ~is_word_type (expr_type e) /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (StoragePlace tr dw dtv) v) (ee,z,Gz,tz)
    ^landing_post (assign_qualified_exit_mods ctx cx RetQ)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `qualified_assign_operand_cut_mods`
    (map_every assume_tac o CONJUNCTS o
      SRULE [qualified_assign_operand_cut_mods_def]) >>
  qpat_x_assum `write_target_location_mods _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o
      SRULE [write_target_location_mods_def,place_ptr_rel_def]) >>
  qpat_x_assum `target_ptr_ok _ _ _ _ _ _`
    (assume_tac o SRULE [target_ptr_ok_def]) >>
  qpat_x_assum `wb_frame _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [wb_frame_def]) >>
  drule_then assume_tac contract_inv_acyclic_struct_metadata >>
  qhdtm_x_assum `expr_sim_inv_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  `~is_word_type (lowered_value_type cenv e)` by
    (disch_tac >> drule_all_then assume_tac return_source_word_widens_eq >> gvs[]) >>
  qpat_x_assum `if is_word_type (expr_type e) then _ else _` mp_tac >> simp[] >>
  disch_then (qx_choosel_then [`tv`,`sw`] (map_every assume_tac o CONJUNCTS)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     storage_place_observed H (StoragePlace tr dw dtv) /\
     stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
     storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\ return_buf_sep d cenv ee s` by
    (gen_tac >> disch_tac >> drule_all_then assume_tac aug_place_target_observed >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> asm_rewrite_tac[]) >>
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at su x` by
    (qpat_assum `local_ptrs_reserved cenv su`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
  `!x. op = Var x \/ dst = Var x ==> not_fresh_at su x` by (rpt strip_tac >> simp[]) >>
  `sa.cs_next_var <= su.cs_next_var /\ sa.cs_next_id <= su.cs_next_id` by decide_tac >>
  `type_memory_size tv <> 0 ==> ?x. op = Var x /\ ptr_covers G tn x s (type_memory_size tv)` by
    (disch_tac >> `0 < type_memory_size tv` by decide_tac >> simp[]) >>
  `~(has_length_word (expr_type e) /\ is_empty_value_expr e)` by
    (drule qualified_assign_rhs_code_view_mods >> simp[]) >>
  `assign_alloc_ok cenv bt e` by fs[stmt_exprs_ok_def, Once alloc_limits_stmt_def] >>
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `(dty <> lowered_value_type cenv e /\
     ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e))) ==>
   sa.cs_next_id <= su.cs_next_id /\ local_ptrs_reserved cenv sa /\
   MAP FDOM es.scopes = MAP FDOM ee.scopes /\ 0 < type_memory_size tv /\
   type_memory_size dtv < dimword (:256) /\
   ?start. expr_val_at cenv cx (lowered_value_type cenv e) start su ee v op s` by
    (disch_tac >>
     `~is_bytestring_type (lowered_value_type cenv e)` by
       (strip_tac >> drule_all_then assume_tac type_widens_from_bytestring >> fs[]) >>
     `0 < type_memory_size tv` by
       (drule_at (Pat `type_widens_to _ _ _`) strict_widening_source_positive >>
        simp[Once EQ_SYM_EQ]) >>
     `type_memory_bytes cenv dty < 2 ** 64` by
       (drule storage_target_normalization_bound >> disch_then (qspec_then `e` mp_tac) >>
        Cases_on `tr` >> fs[slot_loc_def]) >>
     `type_memory_size dtv < dimword (:256)` by
       (irule LESS_TRANS >> qexists_tac `2 ** 64` >> conj_tac
        >- (qpat_assum `type_memory_bytes cenv dty = _` (SUBST1_TAC o SYM) >>
            first_assum ACCEPT_TAC) >> simp[dimword_def]) >>
     qpat_assum `~is_bytestring_type _ ==> ?start. expr_val_at _ _ _ start _ _ _ _ _`
       (drule_then assume_tac) >> asm_rewrite_tac[]) >>
  irule gas_outcome_full_mods_post_source >>
  irule_at (Pat `gas_outcome_full_mods _ _ _ _ _ _ _ _`) qualified_place_slot_copy_mods >>
  qpat_assum `assign_place_store_code_mods _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `unwrap_value _ _ _ = _` (irule_at Any) >>
  qpat_assum `alloca_frame _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ _ _` (irule_at Any) >>
  qpat_assum `eval_operand op s = SOME sw` (irule_at Any) >>
  qpat_assum `evaluate_type _ (lowered_value_type cenv e) = SOME tv` (irule_at Any) >>
  qexistsl_tac [`lctx`,`RetQ`] >>
  BETA_TAC >>
  rpt (first_assum ACCEPT_TAC ORELSE REFL_TAC ORELSE conj_tac)
  >- simp[ADD_COMM]
  >- simp[ADD_COMM]
  >- simp[ADD_COMM]
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qexists_tac `cenv` >> asm_rewrite_tac[]) >>
  simp[]
QED
