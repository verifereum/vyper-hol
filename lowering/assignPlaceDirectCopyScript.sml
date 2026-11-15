Theory assignPlaceDirectCopy
Ancestors
  exprSimBufferStore placeMemoryPrimitiveForward placeMemoryTypedPrimitive
  valueCopyBytes context exprLoweringProps emitHelper compileEnv
  fragGasSeq fragExec words list rich_list venomInst iterate
  placeMemoryCopyEffect venomState loweringPosts placeRelayoutState
  placeMemoryLiveRegion stmtSimDefs vyperScopePreservation

Theorem assign_place_direct_copy_straight:
  compile_store_memory cenv src dst ty ty sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  simp[compile_store_memory_def] >>
  Cases_on `is_word_type ty`
  >- (simp[emit_void_def, comp_ignore_bind_def, comp_bind_def, comp_return_def, fresh_id_def, emit_def] >>
      strip_tac >> gvs[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def]) >>
  Cases_on `is_bytestring_type ty`
  >- (simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
           emit_op_def, emit_void_def, comp_ignore_bind_def, comp_bind_def, comp_return_def,
           fresh_var_def, fresh_id_def, emit_def] >>
      strip_tac >> gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def, emit_def,
        emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def] >>
      simp[ADD_SUBR2, is_terminator_def]) >>
  Cases_on `type_memory_bytes cenv ty` >>
  simp[compile_copy_memory_def, emit_void_def, comp_ignore_bind_def, comp_bind_def, comp_return_def,
       fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem assign_place_direct_copy_effect:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  val_wf tv v /\ expr_val_rel cx ty v src s /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory tv v (w2n d) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n d) (type_memory_size tv)
Proof
  rpt strip_tac >>
  drule_all buffer_store_memory_encoding >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH q.vs_memory` by
    (drule_all buffer_store_memory_capacity >> simp[]) >>
  drule buffer_store_memory_shape >> strip_tac >>
  `gas_marked_path F ctx func s 0
     (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >>
     conj_tac >- simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >>
     fs[same_blocks_def] >>
     metis_tac[assign_place_direct_copy_straight,
               compile_store_memory_same_type_no_gas]) >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[typed_copy_effect_def, same_blocks_def] >>
  gvs[venom_state_component_equality, lookup_var_def] >> metis_tac[]
QED

Theorem assign_place_bytes_copy_effect:
  compile_store_memory cenv src dst dty sty sa = ((),sb) /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v /\
  eval_operand src s = SOME w /\ val_in_memory stv v (w2n w) s.vs_memory /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size dtv < dimword (:256) /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n d) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n d) (type_memory_size dtv)
Proof
  rpt strip_tac >>
  `~is_word_type dty` by
    metis_tac[is_bytestring_word_type] >>
  `compile_store_memory cenv src dst dty dty sa = ((),sb)` by
    gvs[compile_store_memory_def] >>
  `val_in_memory dtv v (w2n w) s.vs_memory` by
    (drule_all bytestring_val_in_memory_transfer >> simp[]) >>
  `expr_val_rel cx dty v src s` by
    (simp[expr_val_rel_def] >> qexists_tac `w` >> simp[]) >>
  irule assign_place_direct_copy_effect >> metis_tac[]
QED

Theorem assign_place_copy_effect_state_frame:
  stmt_state_rel ctx func cenv cx ee s /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  val_in_memory dtv v (w2n w) t.vs_memory /\
  typed_copy_effect ctx func sa sb s t (w2n w) (type_memory_size dtv) ==>
  stmt_state_rel ctx func cenv cx ff t /\
  alloca_frame cenv ee sa s cenv ff t
Proof
  strip_tac >> conj_tac
  >- (irule memory_place_write_copy_effect >> metis_tac[]) >>
  drule_all memory_place_live_region >> strip_tac >>
  irule alloca_frame_of_mem_frame >>
  simp[] >> conj_tac >- metis_tac[typed_copy_effect_lookup] >>
  reverse conj_tac
  >- (conj_tac >- metis_tac[write_place_scopes_dom] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >>
  qpat_x_assum `!n b sz'. local_region _ _ _ _ _ _ ==> _` drule >>
  simp[] >> decide_tac
QED
