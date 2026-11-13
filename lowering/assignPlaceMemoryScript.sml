Theory assignPlaceMemory
Ancestors
  assignPlaceRelayoutProvenance assignPlaceStorage assignPlaceDirectCopy assignPlaceStaging assignPlaceStagedEndpoint
  assignPlacePhysicalBytes assignPlaceLayout placeMemoryCopyEffect
  placeMemoryLiveRegion loweringPosts stmtLowering placeStore
  stmtSimDefs compileEnv exprLowering placeDestinationBounds context
  externalEntryShape exprLoweringProps exprSimProps loweringHalt
  abiTupleProps rich_list fragExec aggregateEvaluatedLayout vyperTypeSystem
  targetPlaceSimCasesBase stmtSimReturn venomState fragGasMode
Libs monadsyntax

Theorem assign_place_memory_from_expr_post:
  compile_assign_value cenv dst LocMemory src (is_word_type dty) src_loc dty
    (lowered_value_type cenv e)
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32,
             type_memory_bytes cenv et) | _ => NONE)
    (type_memory_bytes cenv dty) su = ((),sb) /\
  expr_post ctx func cenv cx e es sa su s0 ee v src s /\
  expr_sim_inv cenv cx env ee /\
  type_widens_to (get_tenv cx) (post_value_type cenv e) dty /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\
  (!x. src = Var x ==> not_fresh_at su x) /\
  (!x. dst = Var x ==> not_fresh_at su x) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
  storage_place_region cx p /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  write_place cx p v ee = (INL (),ff) /\
  local_ptrs_reserved cenv su /\ cenv.ce_target CapMcopy /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  expr_body_pre cenv cx env0 e es0 /\
  (do pv <- eval_expr cx e; read_result cx pv od) es0 = (INL v,er) /\
  type_widens_to env0.type_defs (expr_type e) dty /\
  post_value_type cenv e = expr_type e /\
  (lowered_value_type cenv e = expr_type e \/
   is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type cenv e) /\
   arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
  0 < type_slot_size dtv /\ 0 < type_memory_size dtv ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_frame cenv ee su s cenv ff t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type dty`
  >- suspend "word" >>
  Cases_on `is_bytestring_type (lowered_value_type cenv e) /\ is_bytestring_type dty`
  >- suspend "bytes" >>
  suspend "aggregate"
QED

Resume assign_place_memory_from_expr_post[word]:
  fs[expr_post_def] >>
  `post_value_type cenv e = dty` by
    metis_tac[compileEnvTheory.type_widens_to_word] >>
  `lowered_value_type cenv e = dty` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  fs[] >>
  `emit_void MSTORE [dst;src] su = ((),sb)` by
    gvs[compile_assign_value_def, comp_return_def, comp_bind_def] >>
  `compile_store_memory cenv src dst dty dty su = ((),sb)` by
    gvs[compile_store_memory_def] >>
  `val_wf dtv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_size dtv < dimword (:256)` by
    (drule_all memory_place_destination_bound >> simp[]) >>
  `?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
       typed_copy_effect ctx func su sb s t (w2n dw) (type_memory_size dtv)` by
    (irule assign_place_direct_copy_effect >> simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ff t /\
   alloca_frame cenv ee su s cenv ff t` by
    (irule assign_place_copy_effect_state_frame >> simp[] >>
     metis_tac[]) >>
  qexists_tac `t` >> fs[typed_copy_effect_def]
QED

Resume assign_place_memory_from_expr_post[aggregate]:
  `~is_bytestring_type dty` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  `~is_word_type (post_value_type cenv e) /\
   ~is_bytestring_type (post_value_type cenv e)` by
    metis_tac[exprSimIfExpWidenedArmTheory.aggregate_widen_source] >>
  `lowered_value_type cenv e = post_value_type cenv e` by metis_tac[] >>
  Cases_on `dty = post_value_type cenv e`
  >- suspend "same_layout" >>
  fs[expr_post_def] >>
  `0 < type_memory_size stv` by
    metis_tac[assignPlaceLayoutTheory.widening_source_memory_size_pos] >>
  Cases_on `src_loc = NONE \/ src_loc = SOME LocMemory`
  >- (irule assignPlaceRelayoutProvenanceTheory.assign_place_relayout_from_provenance >>
      simp[] >> (conj_tac >- metis_tac[]) >>
      goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
      simp[] >> metis_tac[]) >>
  suspend "relayout_direct"
QED

Resume assign_place_memory_from_expr_post[bytes]:
  `~is_word_type dty` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  drule_all immutableDeployPhysicalSourceTheory.immutable_rhs_physical_typed >> strip_tac >>
  `value_has_type dtv v` by
    (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
     strip_tac >> gvs[]) >>
  `is_bytestring_type (expr_type e)` by metis_tac[] >>
  qpat_x_assum `lowered_value_type _ _ = _ \/ _` kall_tac >>
  fs[expr_post_def] >>
  `?sw. eval_operand src s = SOME sw /\
        val_in_memory stv v (w2n sw) s.vs_memory` by
    (gvs[expr_val_rel_def, valueCopyBytesTheory.is_bytestring_word_type] >> metis_tac[]) >>
  `val_in_memory stv' v (w2n sw) s.vs_memory` by
    (gvs[] >> metis_tac[valueCopyBytesTheory.bytestring_val_in_memory_transfer]) >>
  `val_wf dtv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_size dtv < dimword (:256)` by
    (drule_all memory_place_destination_bound >> simp[]) >>
  Cases_on `src_loc = SOME LocMemory`
  >- suspend "bytes_staged" >>
  `compile_store_memory cenv src dst dty (lowered_value_type cenv e) su = ((),sb)` by
    gvs[compile_assign_value_def, comp_return_def, comp_bind_def] >>
  `?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
       typed_copy_effect ctx func su sb s t (w2n dw) (type_memory_size dtv)` by
    (irule assign_place_bytes_copy_effect >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ff t /\
   alloca_frame cenv ee su s cenv ff t` by
    (irule assign_place_copy_effect_state_frame >> simp[] >> metis_tac[]) >>
  qexists_tac `t` >> fs[typed_copy_effect_def]
QED

Resume assign_place_memory_from_expr_post[same_layout]:
  qpat_x_assum `lowered_value_type _ _ = _ \/ _` kall_tac >>
  fs[expr_post_def] >>
  Cases_on `src_loc = SOME LocMemory`
  >- suspend "same_staged" >>
  `compile_store_memory cenv src dst dty dty su = ((),sb)` by
    gvs[compile_assign_value_def, comp_return_def, comp_bind_def] >>
  `val_wf dtv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_size dtv < dimword (:256)` by
    (drule_all memory_place_destination_bound >> simp[]) >>
  `?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
       typed_copy_effect ctx func su sb s t (w2n dw) (type_memory_size dtv)` by
    (irule assign_place_direct_copy_effect >> simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ff t /\
   alloca_frame cenv ee su s cenv ff t` by
    (irule assign_place_copy_effect_state_frame >> simp[] >> metis_tac[]) >>
  qexists_tac `t` >> fs[typed_copy_effect_def]
QED

Resume assign_place_memory_from_expr_post[bytes_staged]:
  markerLib.RESUME_TAC >> (rpt strip_tac >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_assign_value_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_alloc_buffer _ su = (buf,sm)` >>
  rename1 `compile_copy_memory _ _ _ sm = (uu,sn)` >>
  Cases_on `uu` >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty` by
    metis_tac[immutableDeployPhysicalSourceTheory.immutable_rhs_physical_widens] >>
  `type_memory_size stv' <= type_memory_size dtv` by
    (qpat_x_assum `type_widens_to _ (lowered_value_type _ _) _` mp_tac >>
     simp[type_widens_to_def] >> strip_tac >- gvs[] >>
     metis_tac[aggregateEvaluatedLayoutTheory.arg_fits_evaluated_memory_size]) >>
  `type_memory_size stv' < dimword (:256)` by decide_tac >>
  irule assign_place_staged_copy_endpoint >> simp[] >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  simp[] >> qexistsl_tac [`p`, `src`, `sw`, `v`] >> gvs[])
QED

Resume assign_place_memory_from_expr_post[same_staged]:
  markerLib.RESUME_TAC >> (rpt strip_tac >>
  `~is_word_type (expr_type e)` by metis_tac[] >>
  `val_wf dtv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_size dtv < dimword (:256)` by
    (drule_all memory_place_destination_bound >> simp[]) >>
  `?sw. eval_operand src s = SOME sw /\
        val_in_memory dtv v (w2n sw) s.vs_memory` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_assign_value_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_copy_memory _ _ _ _ = (uu,sn)` >> Cases_on `uu` >>
  irule assign_place_staged_copy_endpoint >> simp[] >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  simp[] >> qexistsl_tac [`p`, `src`, `sw`, `v`] >> gvs[])
QED

Resume assign_place_memory_from_expr_post[relayout_direct]:
  markerLib.RESUME_TAC >> (rpt strip_tac >>
  `compile_assign_value cenv dst LocMemory src F NONE dty
    (lowered_value_type cenv e)
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32,
             type_memory_bytes cenv et) | _ => NONE)
    (type_memory_bytes cenv dty) su = ((),sb)` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_assign_value_def] >> metis_tac[]) >>
  irule assignPlaceRelayoutProvenanceTheory.assign_place_relayout_from_provenance >>
  simp[] >> (conj_tac >- metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[])
QED

Finalise assign_place_memory_from_expr_post
