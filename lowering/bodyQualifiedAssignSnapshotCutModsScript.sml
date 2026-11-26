(* A materialized Assign operand survives the target fragment.  Its unwrap
   is an identity at the reached target cursor, not a source reread. *)
Theory bodyQualifiedAssignSnapshotCutMods
Ancestors
  bodyQualifiedAssignOperandCutMods bodyQualifiedPlaceTargetEntryMods
  bodyCopyReadPhysicalTypeMods aggregateEvaluatedLayout abiEncodeArgsSim
  exprReasonOperand exprSimUnwrap exprBodyPreProps exprBodyPreTypingProps
  exprSimHypsDefs exprLoweringProps stmtLoweringMono typedMemoryCopy
  assignTuplePtrCopyLen bodyPtrMakeArrayMemoryFrame exprSimProps wordArgsPtr
  stmtSimLogCompose bodyFullShared fragExec freshWrites ptrDiscipline
  bodyMemoryDefs stateRelProj venomMemDefs words
  compileEnv context exprLowering bodyPtrDefs loweringPosts venomState
  bodyAssignQualifiedStageJoinMods bodyQualifiedPlaceRhsPostMods
  bodyWriteTargetStageMods fragGasOriginPtr loweringStateRelDefs
  bodySimFull vyperStorageFootprint vyperTypeSystem exprSimMemDefs
Libs horizonTypeLib

val operand_at =
  ``\op. (!x. op = Var x ==> not_fresh_at st x) /\
    (if is_word_type (expr_type e) then
       ?rt. evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
         value_has_type rt v /\ eval_operand op z = SOME (typed_val_to_w256 rt v) /\
         op_taint tz op = {} /\ op_prov Gz op = NONE
     else
       ?rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
         value_has_type rt v /\ type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size rt /\
         eval_operand op z = SOME w /\ op_taint tz op = {} /\
         (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==> val_in_memory rt v (w2n w) mem) /\
         w2n w + type_memory_size rt < dimword (:256) /\
         (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
         (0 < type_memory_size rt ==> ?x. op = Var x /\ ptr_covers Gz tz x z (type_memory_size rt)) /\
         (~is_bytestring_type (lowered_value_type cenv e) ==>
           ?start. expr_val_at cenv cx (lowered_value_type cenv e) start st ee v op z))``;

Theorem snapshot_cut_word[local]:
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  is_word_type (expr_type e) /\ lowered_value_type cenv e = expr_type e /\
  compile_expr cenv (expr_type e) e sa = (raw,sm) /\
  compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) raw) sm =
    (StackValue (lowered_value_type cenv e) op,sr) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  eval_operand op u = SOME (typed_val_to_w256 tv v) /\
  ptr_val_ok cx (expr_type e) v op Gu tu u /\
  (!x. op = Var x ==> not_fresh_at sr x) /\ sr.cs_next_var <= st.cs_next_var /\
  wb_frame cenv mid ee sr u z /\ ghost_kept_at lo cenv mid sr Gu tu u Gz tz ==>
  unwrap_value cenv (StackValue (lowered_value_type cenv e) op) st = (op,st) /\
  ^operand_at op
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `reason_uniform_shape compile_expr cenv (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >> fs[expr_sim_inv_mods_def]) >>
  `vv_type raw = expr_type e` by
    (fs[reason_uniform_shape_def] >> first_x_assum drule >>
     Cases_on `raw` >> gvs[reason_result_shape_def,vv_type_def]) >>
  `vv_with_type (expr_type e) raw = raw` by
    (Cases_on `raw` >> gvs[vv_with_type_def,vv_type_def]) >>
  `lower_value compile_expr cenv (expr_type e) e sa = (op,sr)` by
    (Cases_on `unwrap_value cenv raw sm` >>
     gvs[lower_value_def,compile_snapshot_vv_def,comp_bind_def,comp_return_def]) >>
  `!l. op <> Label l` by
    (irule lower_compile_expr_not_label >> goal_assum (drule_at Any) >>
     fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  fs[wb_frame_def,ghost_kept_at_def,ptr_val_ok_def] >>
  Cases_on `op` >> gvs[unwrap_value_def,comp_return_def,eval_operand_def,op_taint_def,op_prov_def] >>
  metis_tac[not_fresh_at_mono,op_taint_def]
QED

Theorem snapshot_cut_memory[local]:
  ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type cenv e) /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
  FLOOKUP u.vs_allocas aid = SOME (b,type_memory_size tv) /\ aid < sr.cs_next_id /\
  b + type_memory_size tv < dimword (:256) /\
  (!n off len. local_region cenv mid.scopes u n off len ==>
     loweringStateRelDefs$regions_disjoint b (type_memory_size tv) off len) /\
  not_fresh_at sr x /\ lookup_var x u = SOME (n2w b) /\
  ptr_covers Gu tu x u (type_memory_size tv) /\
  (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==> val_in_memory tv v b mem) /\
  sr.cs_next_var <= st.cs_next_var /\ sr.cs_next_id <= st.cs_next_id /\
  wb_frame cenv mid ee sr u z /\ ghost_kept_at lo cenv mid sr Gu tu u Gz tz /\
  (!n off len. local_region cenv mid.scopes u n off len <=> local_region cenv ee.scopes z n off len) /\
  alloca_inv z /\ allocas_from lo z ==>
  unwrap_value cenv (LocatedValue (lowered_value_type cenv e) (mk_ptr (Var x) LocMemory)) st = (Var x,st) /\
  ^operand_at (Var x) /\
  (!sw. eval_operand (Var x) z = SOME sw ==> lo <= w2n sw)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b : bytes32) = b` by simp[w2n_n2w_compute] >>
  `val_footprint tv v <= type_memory_size tv` by simp[val_footprint_le] >>
  `!n off len. local_region cenv mid.scopes u n off len ==>
     b + type_memory_size tv <= off \/ off + len <= b` by
    (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  fs[wb_frame_def,ghost_kept_at_def,alloca_inv_def,alloca_next_valid_def] >>
  `lookup_var x z = SOME (n2w b)` by metis_tac[] >>
  `FLOOKUP z.vs_allocas aid = SOME (b,type_memory_size tv)` by metis_tac[] >>
  `lo <= b` by
    (qpat_assum `allocas_from lo z`
       (drule_then ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `b + type_memory_size tv <= z.vs_alloca_next` by metis_tac[] >>
  `ptr_covers Gz tz x z (type_memory_size tv)` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`Gu`,`u`,`tu`] >> simp[] >> metis_tac[]) >>
  `op_taint tz (Var x) = {} /\ op_taint tu (Var x) = {}` by fs[ptr_covers_def] >>
  `!n off len. local_region cenv ee.scopes z n off len ==>
     b + type_memory_size tv <= off \/ off + len <= b` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  `mem_bytes_at b (type_memory_size tv) z.vs_memory =
   mem_bytes_at b (type_memory_size tv) u.vs_memory` by
    (qpat_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _`
       (qspecl_then [`aid`,`b`,`type_memory_size tv`] mp_tac) >>
     (impl_tac >- rpt (conj_tac ORELSE first_assum ACCEPT_TAC)) >> simp[]) >>
  `!i. b <= i /\ i < b + type_memory_size tv /\ i IN tz.t_mem ==> i IN tu.t_mem` by
    (rpt strip_tac >> qpat_assum `!aid off sz i. _ ==> i IN tu.t_mem`
       (qspecl_then [`aid`,`b`,`type_memory_size tv`,`i`] mp_tac) >>
     (impl_tac >- rpt (conj_tac ORELSE first_assum ACCEPT_TAC)) >> simp[]) >>
  `!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==> val_in_memory tv v b mem` by
    (gen_tac >> disch_tac >> irule robust_val_in_memory_shrinking_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`tu.t_mem`,`tz.t_mem`,`u.vs_memory`,`z.vs_memory`,`type_memory_size tv`] >>
     rpt (conj_tac ORELSE first_assum ACCEPT_TAC)) >>
  simp[unwrap_value_def,mk_ptr_def,comp_return_def,eval_operand_def] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  strip_tac >> qexists_tac `st with cs_next_id := aid` >>
  simp[expr_val_at_def,eval_operand_def] >> disj1_tac >>
  qexistsl_tac [`aid`,`b`,`type_memory_size tv`] >> simp[] >> rpt strip_tac >>
  qpat_assum `!n off len. local_region _ _ _ _ _ _ <=> _`
    (qspecl_then [`n`,`lb`,`lsz`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem qualified_assign_snapshot_cut_mods:
  target_root bt = TopLevelNameTarget (owner,id) /\
  type_place_target env bt = SOME (Type dty) /\
  type_widens_to env.type_defs (expr_type e) dty /\
  (!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env se ==>
     expr_body_pre_mods mods cenv cx env i se) /\
  expr_body_pre_mods mods cenv cx env e es /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  fn_has_code sr st func /\ fn_has_code st sb func /\
  return_buf_sep d cenv es s0 /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb (SOME vv) sr st
    shadow_sr shadow_st dst /\
  expr_can_mutate cenv (target_to_expr bt) /\
  qualified_assign_rhs_reached_mods cx st0 e es s0
    (qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
       es sa shadow_sa sr shadow_sr (SOME vv) s0 G0 tn0) ms v mid Gu tu u /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks p ee Gz tz z ==>
  ?op su s G tn.
    qualified_assign_operand_cut_mods (DF,lo,d,explicit,ctx,func,PG) cenv cx st0
      (bt,e,dty) (vv,op,p,dst,v) (sa,st,su,sb) (es,s0,G0,tn0) (ee,z,Gz,tz) (s,G,tn) /\
    (qualified_assign_route_mods AssignImmCopy (owner,id) p (SOME vv) dty dst ==>
     !sw. eval_operand op s = SOME sw ==> lo <= w2n sw)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def,Abbr `H0`] >>
  drule_all_then (map_every assume_tac o CONJUNCTS) qualified_place_store_frame_mods >>
  qhdtm_assum `write_target_post_mods`
    (strip_assume_tac o MATCH_MP write_target_post_view_mods) >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  `alloca_inv z` by drule_then (ACCEPT_TAC o CONJUNCT2) stmt_state_rel_local_ptrs_alloca >>
  `alloca_frame cenv es sa s0 cenv ee z` by
    (irule (horizonTypeLib.at_horizon_named "H" log_wb_alloca_frame) >>
     simp[] >> conj_tac >- (qexists_tac `ee` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`H0`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC) >>
  `return_buf_sep d cenv ee z` by
    (irule (horizonTypeLib.at_horizon_named "H" return_buf_sep_locals_kept) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`H0`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >>
     fs[wb_frame_def]) >>
  `fn_has_code st st func` by fs[fn_has_code_def,emitted_blocks_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee z /\ immutable_frame_mods func cenv cx ee z /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee Gz tz z /\
    storage_well_formed_on cx ee (FST H)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> write_target_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ z`
       (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods)) >>
     rpt (conj_tac ORELSE first_assum ACCEPT_TAC)) >>
  qhdtm_x_assum `qualified_assign_code_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  `ci_mono sr st` by (qspecl_then [`bt`,`cenv`,`sr`] mp_tac ci_mono_compile_get_target_ptr >> simp[]) >>
  qhdtm_x_assum `qualified_assign_rhs_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_rhs_reached_mods_def]) >>
  qpat_assum `expr_can_mutate cenv (target_to_expr bt)` (fn mut =>
    qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
      (qspec_then `H0` (drule_then
        (strip_assume_tac o CONJUNCT2 o SRULE [mut] o
         MATCH_MP qualified_place_rhs_saved_view_mods)))) >>
  `expr_sim_inv_mods mods cenv cx env es` by metis_tac[expr_body_pre_mods_inv] >>
  `well_typed_expr env e` by metis_tac[expr_body_pre_mods_well_typed] >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    (irule copy_lowered_fits_mods >> qexistsl_tac [`cx`,`env`,`es`,`mods`] >> simp[]) >>
  `ci_mono sa sm` by (simp[ci_mono_def] >> drule compile_expr_extends >> simp[]) >>
  `ci_mono sm sr` by
    (qspecl_then [`cenv`,`T`,`vv_with_type (lowered_value_type cenv e) raw`,`sm`] mp_tac
       ci_mono_compile_snapshot_vv >> simp[]) >>
  `ci_mono sa st` by metis_tac[ci_mono_trans] >>
  `allocas_from lo z` by fs[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
  `is_word_type (lowered_value_type cenv e) <=> is_word_type (expr_type e)` by
    (irule arg_type_fits_word_type >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id /\
   sr.cs_next_var <= st.cs_next_var /\ sr.cs_next_id <= st.cs_next_id` by fs[ci_mono_def] >>
  `?op. unwrap_value cenv vv st = (op,st) /\ ^operand_at op /\
        (qualified_assign_route_mods AssignImmCopy (owner,id) p (SOME vv) dty dst ==>
         !sw. eval_operand op z = SOME sw ==> lo <= w2n sw)` by
    (Cases_on `is_word_type (lowered_value_type cenv e)`
     >- (qpat_assum `is_word_type (lowered_value_type cenv e)` (fn word =>
           qpat_x_assum `if is_word_type (lowered_value_type cenv e) then _ else _`
             (qx_choose_then `op` (map_every assume_tac o CONJUNCTS) o SRULE [word])) >>
         `is_word_type (expr_type e)` by fs[] >>
         `lowered_value_type cenv e = expr_type e` by metis_tac[abi_args_word_fits_eq] >>
         `is_word_type dty` by metis_tac[return_source_word_widens_eq] >>
         qpat_x_assum `vv = StackValue _ _` SUBST_ALL_TAC >> qexists_tac `op` >>
         `~qualified_assign_route_mods AssignImmCopy (owner,id) p
            (SOME (StackValue (lowered_value_type cenv e) op)) dty dst` by
           simp[qualified_assign_route_mods_def] >>
         `(unwrap_value cenv (StackValue (lowered_value_type cenv e) op) st = (op,st)) /\
          ^operand_at op` suffices_by simp[] >>
         irule snapshot_cut_word >> simp[] >> conj_tac
         >- (qexistsl_tac [`env`,`es`,`mods`] >> simp[]) >>
         first_assum (irule_at (Pat `compile_expr _ _ _ _ = _`)) >>
         first_assum (irule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
         first_assum (irule_at (Pat `eval_operand _ _ = _`)) >> fs[]) >>
     qpat_assum `~is_word_type (lowered_value_type cenv e)` (fn nonword =>
       qpat_x_assum `if is_word_type (lowered_value_type cenv e) then _ else _`
         (qx_choose_then `x` (qx_choose_then `aid` (qx_choose_then `b`
            (map_every assume_tac o CONJUNCTS))) o SRULE [nonword])) >>
     `~is_word_type (expr_type e)` by fs[] >>
     `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv` by
       (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
        qpat_assum `expr_sim_inv_mods mods cenv cx env es`
          (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
        simp[] >> rpt strip_tac >>
        qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _`
          (drule_then strip_assume_tac) >> simp[]) >>
     qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >> qexists_tac `Var x` >>
     `unwrap_value cenv (LocatedValue (lowered_value_type cenv e)
          (mk_ptr (Var x) LocMemory)) st = (Var x,st) /\ ^operand_at (Var x) /\
      (!sw. eval_operand (Var x) z = SOME sw ==> lo <= w2n sw)` suffices_by simp[] >>
     irule snapshot_cut_memory >> simp[] >>
     first_assum (irule_at (Pat `FLOOKUP _ _ = _`)) >>
     first_assum (irule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >> simp[] >>
     qpat_assum `!n off len. local_region cenv mid.scopes u n off len <=> _`
       (pure_rewrite_tac o single o GSYM) >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`op`,`st`,`z`,`Gz`,`tz`] >>
  qpat_x_assum `^operand_at op` (strip_assume_tac o BETA_RULE) >>
  simp[qualified_assign_operand_cut_mods_def, cj 1 gas_origin_ptr_path_rules]
QED
