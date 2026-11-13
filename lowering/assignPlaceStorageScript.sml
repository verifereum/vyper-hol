Theory assignPlaceStorage
Ancestors
  assignPlaceRelayoutProvenance assignPlacePhysicalBytes assignPlaceNormalizeFrame
  assignPlaceStorageSuffix assignPlaceStorageCompile assignPlaceLayout
  loweringPosts stmtSimDefs stmtLowering compileEnv placeStore valueCopyBytes
Libs monadsyntax

Theorem assign_place_storage_from_expr_post:
  compile_assign_value cenv dst loc src (is_word_type dty) src_loc dty
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
  (loc = LocStorage \/ loc = LocTransient) /\
  (!x. src = Var x ==> not_fresh_at su x) /\
  (!x. dst = Var x ==> not_fresh_at su x) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type dty) /\
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
  0 < type_slot_size dtv /\ 0 < type_memory_size dtv /\
  (~is_word_type dty /\ dty <> lowered_value_type cenv e /\
   ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e)) ==>
   type_alloc_ok cenv dty) ==>
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
  Cases_on `is_bytestring_type (lowered_value_type cenv e) /\ is_bytestring_type dty`
  >- suspend "bytes" >>
  Cases_on `is_word_type dty`
  >- suspend "word" >>
  suspend "aggregate"
QED

Resume assign_place_storage_from_expr_post[bytes]:
  `stmt_state_rel ctx func cenv cx ee s` by fs[expr_post_def] >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    alloca_frame cenv ee su s cenv ff t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule assign_place_physical_bytes_storage >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  qexists_tac `t` >> simp[]
QED

Resume assign_place_storage_from_expr_post[word]:
  fs[expr_post_def] >>  `post_value_type cenv e = dty` by
    metis_tac[compileEnvTheory.type_widens_to_word] >>
  `lowered_value_type cenv e = dty` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  fs[] >>
  `emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                        | _ => MSTORE) [dst;src] su = ((),sb)` by
    (Cases_on `loc` >> gvs[compile_assign_value_def,
        comp_return_def, comp_bind_def]) >>
  gs[] >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (loc = LocStorage \/ loc = LocTransient ==> t.vs_memory = s.vs_memory)` by
    (irule place_store_word_run >> simp[] >>
     goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> simp[] >>
     goal_assum (drule_at (Pat `expr_val_rel _ _ _ _ _`)) >> simp[] >>
     goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >> simp[] >>
     metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  `MAP FDOM ff.scopes = MAP FDOM ee.scopes` by
    metis_tac[vyperScopePreservationTheory.write_place_scopes_dom] >>
  irule alloca_frame_of_mem_frame >> simp[] >>
  goal_assum (drule_at Any)
QED

Resume assign_place_storage_from_expr_post[aggregate]:
  all_tac >>
  `~is_bytestring_type dty` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  `~is_word_type (post_value_type cenv e) /\
   ~is_bytestring_type (post_value_type cenv e)` by
    metis_tac[exprSimIfExpWidenedArmTheory.aggregate_widen_source] >>
  `lowered_value_type cenv e = post_value_type cenv e` by metis_tac[] >>
  Cases_on `dty = post_value_type cenv e`
  >- suspend "equal_layout" >>
  suspend "normalize"
QED

Resume assign_place_storage_from_expr_post[equal_layout]:
  fs[expr_post_def] >>
  `?sw. eval_operand src s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory` by
    gvs[expr_val_rel_def] >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (irule assignPlaceSourceBoundsTheory.nonbytes_expr_val_at_bound >> metis_tac[]) >>
  `well_formed_type_value stv` by
    metis_tac[vyperTypingTheory.evaluate_type_well_formed] >>
  gvs[] >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_frame cenv ee su s cenv ff t` by
    (irule assign_place_typed_storage_suffix_run >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ s _ _ _ _`)) >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ s.vs_memory`)) >>
     qexistsl_tac [`dst`, `src`] >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     `type_memory_bytes cenv (expr_type e) = type_memory_size dtv` by
       metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
     Cases_on `?et n. expr_type e = ArrayT et (Dynamic n)`
     >- (pop_assum strip_assume_tac >> gvs[compile_assign_value_def,
           comp_bind_def, comp_return_def]) >>
     Cases_on `type_memory_size dtv <= 32` >>
     qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `expr_type e` >>
     simp[compile_assign_value_def, comp_bind_def, comp_return_def]
     >>~- ([`ArrayT et bd`], Cases_on `bd` >>
        fs[compile_assign_value_def, comp_bind_def, comp_return_def] >>
        simp[GSYM pairTheory.pair_case_eq, pairTheory.pair_CASE_UNCURRY,
             combinTheory.C_DEF, comp_ignore_bind_def, comp_bind_def, comp_return_def,
             pairTheory.UNCURRY, quantHeuristicsTheory.PAIR_EQ_EXPAND]) >>
     simp[GSYM pairTheory.pair_case_eq, pairTheory.pair_CASE_UNCURRY,
             combinTheory.C_DEF, comp_ignore_bind_def, comp_bind_def, comp_return_def,
             pairTheory.UNCURRY, quantHeuristicsTheory.PAIR_EQ_EXPAND]) >>
  qexists_tac `t` >> simp[]
QED

Resume assign_place_storage_from_expr_post[normalize]:
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)
    assign_place_storage_normalize_compile >>
  disch_then (qspecl_then [`func`, `dtv`] mp_tac) >>
  (impl_tac >- gvs[]) >>
  disch_then (qx_choosel_then [`buf`, `sm`, `sn`] (map_every assume_tac o CONJUNCTS)) >>
  fs[expr_post_def] >>
  `?sw. eval_operand src s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory` by gvs[expr_val_rel_def] >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (irule assignPlaceSourceBoundsTheory.nonbytes_expr_val_at_bound >> metis_tac[]) >>
  `type_alloc_ok cenv dty` by metis_tac[] >>
  drule_all placeStoreStorageTheory.place_store_destination_alloc_bound >> strip_tac >>
  `value_has_type dtv v` by
    (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
     simp[] >> metis_tac[]) >>
  `val_wf stv v /\ val_wf dtv v` by
    simp[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) assign_place_normalize_framed_path >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
  disch_then (drule_at (Pat `eval_operand src s = _`)) >>
  disch_then (qspecl_then [`stv`, `dtv`, `v`] mp_tac) >>
  (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >>
    (conj_tac >- (fs[exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[])) >>
    (conj_tac >- (fs[exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[])) >>
    drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)
      exprSimHashBoundaryTheory.expr_val_at_footprint >>
    disch_then (drule_at (Pat `evaluate_type _ _ = SOME stv`)) >>
    disch_then (drule_at (Pat `eval_operand src s = _`)) >>
    `0 < type_memory_size stv` by
      (irule widening_source_memory_size_pos >> metis_tac[]) >>
    `val_footprint stv v = type_memory_size stv` by
      (irule annassignRelayoutSourceTheory.nonbytes_evaluated_val_footprint >> metis_tac[]) >>
    gvs[arithmeticTheory.ADD_COMM] >> metis_tac[])) >>
  suspend "normalized_suffix"
QED

Resume assign_place_storage_from_expr_post[normalized_suffix]:
  markerLib.RESUME_TAC >> strip_tac >>
  `su.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
   su.cs_next_id <= sn.cs_next_id` by
    (qspec_then `type_memory_bytes cenv dty` (qspec_then `su` mp_tac)
       exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >>
     drule exprSimTypedAllocTheory.typed_return_store_mono >>
     gvs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sn` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `su` >> simp[]) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by
    (drule loweringHaltTheory.compile_alloc_buffer_emission >> strip_tac >> gvs[]) >>
  `!x. buf.buf_operand = Var x \/ dst = Var x ==> not_fresh_at sn x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `u.vs_labels = s.vs_labels` by
    metis_tac[stmtSimAugAssignPlaceMemoryTheory.aug_place_marked_path_labels] >>
  `eval_operand dst u = SOME dw` by
    (qspecl_then [`su`, `s`, `u`, `dst`] mp_tac
      stmtSimReturnTheory.eval_operand_old_vars >> simp[]) >>
  `place_ptr_rel cenv cx u (PlaceR p) dw (SOME loc) (Type dty)` by
    (irule targetPlaceSimCasesBaseTheory.place_ptr_rel_vars_frame >> metis_tac[]) >>
  `well_formed_type_value dtv` by
    metis_tac[vyperTypingTheory.evaluate_type_well_formed] >>
  `?t. gas_marked_path F ctx func u 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x u) /\
    t.vs_memory = u.vs_memory /\ t.vs_allocas = u.vs_allocas /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_frame cenv ee sn u cenv ff t` by
    (irule assign_place_typed_storage_suffix_run >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ u _ _ _ _`)) >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ u.vs_memory`)) >>
     qexistsl_tac [`dst`, `buf.buf_operand`] >> simp[] >>
     first_assum ACCEPT_TAC) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_0] >>
  qexists_tac `t` >> simp[] >>
  (conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  irule alloca_frame_trans >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
Finalise assign_place_storage_from_expr_post
