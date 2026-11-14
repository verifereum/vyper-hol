Theory assignPlaceStagedEndpoint
Ancestors
  loweringStateRelDefs
  assignPlaceStaging assignPlaceDirectCopy exprSimBufferStore
  stmtSimDefs loweringPosts exprLoweringProps loweringHalt
  abiTupleProps rich_list fragGasMode exprLowering compileEnv
  externalEntryShape venomState fragExec placeMemoryCopyEffect exprSimProps
  stmtSimReturn targetPlaceSimCasesBase

Theorem assign_place_staged_copy_endpoint:
  compile_alloc_buffer (type_memory_bytes cenv sty) sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src (type_memory_bytes cenv sty) sm = ((),sn) /\
  compile_store_memory cenv buf.buf_operand dst dty sty sn = ((),sb) /\
  ~is_word_type dty /\
  (sty = dty \/ (is_bytestring_type sty /\ is_bytestring_type dty)) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_wf stv v /\ val_wf dtv v /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size stv < dimword (:256) /\
  type_memory_size dtv < dimword (:256) /\
  eval_operand src s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  eval_operand dst s = SOME dw /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx ee s /\ expr_sim_inv cenv cx env ee /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_frame cenv ee sa s cenv ff t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by
    (drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends sn sb` by
    (mp_tac compile_store_memory_labels >>
     disch_then (qspecl_then [`cenv`, `buf.buf_operand`, `dst`, `dty`, `sty`, `sn`] mp_tac) >> simp[]) >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `val_footprint stv v <= type_memory_size stv` by metis_tac[val_footprint_le] >>
  fs[] >> drule_all assign_place_staging_live >> strip_tac >>
  (
  `u.vs_labels = s.vs_labels` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
       vs_current_bb := _; vs_inst_idx := _|>) = r`
       (strip_assume_tac o SRULE [venom_state_component_equality]) >>
     qpat_x_assum `(r with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|>) = s`
       (strip_assume_tac o SRULE [venom_state_component_equality]) >> simp[]) >>
  `eval_operand dst u = SOME dw` by metis_tac[eval_operand_old_vars] >>
  `place_ptr_rel cenv cx u (PlaceR p) dw (SOME LocMemory) (Type dty)` by
    (irule place_ptr_rel_vars_frame >> qexistsl_tac [`s`, `sa`] >> simp[]) >>
  `sn.cs_next_var = sm.cs_next_var /\ sm.cs_next_var = sa.cs_next_var + 1` by
    metis_tac[buffer_copy_memory_shape, compile_alloc_buffer_parts] >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. buf.buf_operand = Var x \/ dst = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[]) >>
  `?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
       typed_copy_effect ctx func sn sb u t (w2n dw) (type_memory_size dtv)` by
    (Cases_on `sty = dty`
     >- (gvs[] >>
         `expr_val_rel cx dty v buf.buf_operand u` by
           (simp[expr_val_rel_def] >> metis_tac[]) >>
         irule assign_place_direct_copy_effect >> simp[] >>
         goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
         simp[] >> metis_tac[]) >>
     irule assign_place_bytes_copy_effect >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ff t /\
   alloca_frame cenv ee sn u cenv ff t` by
    (irule assign_place_copy_effect_state_frame >> simp[] >> metis_tac[]) >>
  `alloca_frame cenv ee sa s cenv ff t` by
    (irule alloca_frame_trans >>
     qexistsl_tac [`cenv`, `ee`, `u`, `sn`] >> simp[] >>
     drule buffer_copy_memory_shape >> strip_tac >>
     fs[typed_copy_effect_def] >> metis_tac[]) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK u)` mp_tac >>
     qpat_assum `typed_copy_effect _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[typed_copy_effect_def] >>
     metis_tac[gas_marked_path_then, arithmeticTheory.ADD]) >>
  qexists_tac `t` >> fs[typed_copy_effect_def] >> simp[not_fresh_at_def])
QED



