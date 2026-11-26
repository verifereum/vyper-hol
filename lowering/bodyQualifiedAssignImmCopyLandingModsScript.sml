(* Land the aggregate immutable store at the same normalization cut as its
   physical execution. The source floor accompanies the prepared operand. *)
Theory bodyQualifiedAssignImmCopyLandingMods
Ancestors
  bodyQualifiedAssignOperandCutMods bodyQualifiedPlaceImmCopyPathMods
  bodyQualifiedPlaceImmAggregateMods bodyAssignQualifiedStageJoinMods
  bodyWriteTargetStageMods bodyFullTargetDefs bodyPtrDefs bodyFullShadowBodyInv
  bodyInvCodeProps bodyInvSplit immutableRegionFrameProps exprSimHypsDefs
  immutableAssignRepresentation immutableAssignOpen bodyImmutableAugAssignStore
  bodyFullImmutablePathStore gasOutcomeFullPostMods stmtSimProps loweringPosts
  exprSimCopy exprSimProps exprLoweringProps stateRelProj vyperTypeInitialState
  vyperTypeInvariants vyperTypeArgFits vyperTypeEnv typedMemoryCopy vyperStorageFootprint
  wordArgsPtr exprSimWordArgs gasOutcomeFullPostPathMods
  venomState freshWrites compileEnv finite_map words arithmetic stmtSimDefs
  gasContext vyperState context loweringStateRelDefs ptrDiscipline

val normal_post =
  ``\(H : (bool # bytes32 # type_value) list # num list) res fin Gf tf q.
      ?ce. stmt_lands lctx sb res q /\ ~q.vs_halted /\
        (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
        cenv_top_ext cenv ce fin.scopes /\
        stmt_state_rel H ctx func ce cx fin q /\ immutable_frame_mods func ce cx fin q /\
        storage_well_formed_on cx fin (FST H) /\ return_buf_frame d ce sb q /\
        alloca_history func q /\ return_buf_sep d ce fin q /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\ s0.vs_alloca_next <= q.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d ce cx fin Gf tf q /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
          op_taint tf (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame cenv es sa s0 ce fin q /\
        (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
           (!n b cap. local_region cenv es.scopes s0 n b cap ==> off+sz <= b \/ b+cap <= off) /\
           off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)``;

Theorem imm_copy_base_ready[local]:
  stmt_state_rel H ctx func cenv cx ee s /\ ghost_inv_at_mods D lo d cenv cx ee G tn s /\
  local_ptrs_reserved cenv su /\ 0 < lo ==>
  !base. cenv.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
    copy_old_operand su base /\ op_taint tn base = {} /\ op_prov G base = NONE
Proof
  strip_tac >>
  drule_then (assume_tac o REWRITE_RULE [immutable_base_zero_def])
    stmt_state_rel_immutable_base_zero >>
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==>
      not_fresh_at su x /\ FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}` by
    (rpt strip_tac >- drule_all_then ACCEPT_TAC local_ptrs_reserved_imm_base >>
     fs[ghost_inv_at_mods_def]) >>
  Cases >> simp[copy_old_operand_def,op_prov_def,op_taint_def]
QED

Theorem qualified_assign_imm_copy_landing_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  expr_sim_inv_mods mods cenv cx env ee /\
  qualified_assign_route_mods AssignImmCopy (owner,id) p (SOME vv) dty r /\
  assign_place_store_code_mods cenv e (SOME vv) r st = ((),sb) /\
  qualified_assign_operand_cut_mods (DF,lo,d,explicit,ctx,func,PG)
    cenv cx st0 (bt,e,dty) (vv,op,p,r,v) (sa,st,su,sb)
    (es,s0,G0,tn0) (ee,z,Gz,tz) (s,G,tn) /\
  (!sw. eval_operand op s = SOME sw ==> lo <= w2n sw) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  ~is_word_type (expr_type e) /\ assignable_type (get_tenv cx) (lowered_value_type cenv e) /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
  gas_admissible (write_place cx p v) (stmt_res_ok lctx) ee /\ ee.gas_obs = [] /\
  local_ptrs_reserved cenv sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx p v) (ee,z,Gz,tz) ^normal_post (assign_qualified_exit_mods ctx cx RetQ)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `qualified_assign_route_mods _ _ _ _ _ _` mp_tac >>
  simp[qualified_assign_route_mods_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  gvs[] >>
  qpat_x_assum `qualified_assign_operand_cut_mods _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o SRULE [qualified_assign_operand_cut_mods_def]) >>
  qpat_x_assum `if is_word_type (expr_type e) then _ else _` mp_tac >> simp[] >>
  disch_then (qx_choosel_then [`rt`,`w`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "destination"
QED

Resume qualified_assign_imm_copy_landing_mods[destination]:
  markerLib.RESUME_TAC >>
  qpat_assum `r = (FST r,_,_)`
    (fn eq => qpat_x_assum `assign_place_store_code_mods _ _ _ r _ = _`
       (assume_tac o ONCE_REWRITE_RULE [eq])) >>
  qpat_x_assum `write_target_location_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE [write_target_location_mods_def]) >>
  qpat_assum `target_ptr_ok _ _ _ _ _ _`
    (strip_assume_tac o SRULE [target_ptr_ok_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `dead_lo_ok_mods (storage_trace_horizon ee.storage_trace)
     (DF (storage_trace_horizon ee.storage_trace)) lo cenv cx` by simp[] >>
  drule_all_then strip_assume_tac immutable_region_value_layout_mods >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  drule_all_then strip_assume_tac immutable_assign_widened_memory_positive >>
  `off+k + type_memory_size ptv <= lo /\ 0 < lo` by decide_tac >>
  suspend "source"
QED

Resume qualified_assign_imm_copy_landing_mods[source]:
  markerLib.RESUME_TAC >>
  qpat_assum `0 < _ ==> ?x. _` (drule_then (qx_choose_then `xs` strip_assume_tac)) >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  `lookup_var xs s = SOME (n2w (w2n w))` by fs[eval_operand_def] >>
  `lo <= w2n w` by
    (qpat_assum `!sw. eval_operand _ s = SOME sw ==> _` (drule_then ACCEPT_TAC)) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `lo < dimword (:256)` by
    (`s.vs_alloca_next < dimword (:256)` by
       drule_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt) stmt_state_rel_alloca_room >>
     decide_tac) >>
  `copy_old_operand su (FST r)` by simp[copy_old_operand_def] >>
  `w2n w + type_memory_size rt <= s.vs_alloca_next` by decide_tac >>
  `!base. cenv.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
    copy_old_operand su base /\ op_taint tn base = {} /\ op_prov G base = NONE` by
    (drule_then (drule_then (drule_then (drule_then ACCEPT_TAC)))
       (REWRITE_RULE [GSYM AND_IMP_INTRO] imm_copy_base_ready)) >>
  `value_has_type ptv v` by
    (qpat_assum `type_widens_to _ _ _` (drule_all_then strip_assume_tac o
       REWRITE_RULE [GSYM AND_IMP_INTRO] o MATCH_MP
         (REWRITE_RULE [GSYM AND_IMP_INTRO] type_widens_to_value_has_type)) >> gvs[]) >>
  drule_then assume_tac contract_inv_acyclic_struct_metadata >>
  qpat_assum `expr_sim_inv_mods _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  `type_memory_bytes cenv dty = type_memory_size ptv` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  `?start. dty <> lowered_value_type cenv e /\ ~is_bytestring_type dty ==>
     expr_val_at cenv cx (lowered_value_type cenv e) start su ee v (Var xs) s` by
    (Cases_on `dty <> lowered_value_type cenv e /\ ~is_bytestring_type dty`
     >- (`~is_bytestring_type (lowered_value_type cenv e)` by
           (strip_tac >> drule_all_then assume_tac type_widens_from_bytestring >>
            qpat_assum `_ /\ ~is_bytestring_type dty` mp_tac >> simp[]) >> simp[]) >>
     simp[]) >>
  `not_fresh_at su xs` by simp[] >>
  `w2n w + type_memory_size rt < dimword (:256)` by decide_tac >>
  suspend "path"
QED

Resume qualified_assign_imm_copy_landing_mods[path]:
  markerLib.RESUME_TAC >>
  drule_at (Pat `assign_place_store_code_mods _ _ _ (_,SOME LocCode,_) _ = _`)
    qualified_place_imm_copy_path_mods >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `type_memory_bytes _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `type_widens_to _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (lowered_value_type _ _) = _`)) >>
  disch_then (mp_tac o Q.INST [`es` |-> `ee`, `dest` |-> `off+k`,
    `H0` |-> `storage_trace_horizon ee.storage_trace`] o SPEC_ALL) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
     disch_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[])) >>
  disch_then (qx_choosel_then [`sm`,`u`,`Gu`,`tu`,`q`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "landing"
QED

Resume qualified_assign_imm_copy_landing_mods[landing]:
  markerLib.RESUME_TAC >>
  `ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops` by
    (drule_then SUBST1_TAC contract_inv_cenv_modules >> fs[module_body_inv_def]) >>
  `value_has_type itv iv` by
    (drule_all_then assume_tac state_well_typed_immutables_ALOOKUP >>
     drule_all_then strip_assume_tac imms_well_typed_get_source_immutables >> simp[]) >>
  Cases_on `write_place cx (ImmutablePlace owner id path) v ee` >>
  rename1 `write_place cx (ImmutablePlace owner id path) v ee = (wr,fin)` >>
  `stmt_res_ok lctx wr` by
    (qpat_assum `gas_admissible (write_place _ _ _) _ _`
       (qspec_then `[]` mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
     asm_rewrite_tac[] >> disch_then (qspecl_then [`wr`,`fin`] mp_tac) >> simp[]) >>
  `wr = INL ()` by
    drule_all_then (ACCEPT_TAC o CONJUNCT1) immutable_augassign_path_write_source >>
  qpat_x_assum `wr = INL ()` SUBST_ALL_TAC >>
  suspend "frame"
QED

Resume qualified_assign_imm_copy_landing_mods[frame]:
  markerLib.RESUME_TAC >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> valid_horizon _ _ H es.storage_trace`
       (drule_then (fn th => first_assum (fn imp => ACCEPT_TAC (MATCH_MP (SPEC_ALL imp) th))))) >>
  `!name b n. local_region cenv ee.scopes s name b n <=>
               local_region cenv es.scopes s0 name b n` by
    (rpt gen_tac >> CONV_TAC (REWR_CONV EQ_SYM_EQ) >>
     drule_all_then (qspecl_then [`name`,`b`,`n`] ACCEPT_TAC) wb_frame_local_regions) >>
  `sa.cs_next_var <= su.cs_next_var /\ sa.cs_next_id <= su.cs_next_id` by decide_tac >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `su` >> simp[]) >>
  qpat_assum `wb_frame _ _ _ _ _ _`
    (map_every assume_tac o List.take o (fn th => (CONJUNCTS th,2)) o REWRITE_RULE [wb_frame_def]) >>
  suspend "close"
QED

Resume qualified_assign_imm_copy_landing_mods[close]:
  markerLib.RESUME_TAC >>
  irule gas_outcome_full_mods_post_path >>
  qpat_assum `immutable_path_store_post _ _ _ _ _ _ _ _`
    (mp_then (Pat `immutable_path_store_post _ _ _ _ _ _ _ _`) mp_tac
      qualified_place_imm_copy_landing_mods) >>
  disch_then (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  disch_then (fn th => qpat_assum `FLOOKUP (get_source_immutables _ _) _ = _`
    (mp_then (Pat `FLOOKUP (get_source_immutables _ _) _ = _`) mp_tac th)) >>
  disch_then (drule_at (Pat `!D. gas_origin_ptr_path (D,_,_,_,_,_) _ _ (OK q,Gf,tf)`)) >>
  disch_then (mp_tac o Q.INST [`es0` |-> `es`, `sa0` |-> `sa`, `sa` |-> `su`,
    `cenv0` |-> `cenv`, `R` |-> `assign_qualified_exit_mods ctx cx RetQ`] o SPEC_ALL) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[cenv_top_ext_refl] >> rpt strip_tac >> simp[])) >>
  disch_then (irule_at Any) >>
  rpt gen_tac >> disch_then (strip_assume_tac o BETA_RULE) >>
  CONV_TAC (TOP_DEPTH_CONV BETA_CONV) >> qexists_tac `cenv` >> simp[] >>
  first_assum ACCEPT_TAC
QED

Finalise qualified_assign_imm_copy_landing_mods
