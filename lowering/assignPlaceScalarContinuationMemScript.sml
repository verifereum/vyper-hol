(* Single-store continuations for scalar and empty place assignments. *)
Theory assignPlaceScalarContinuationMem
Ancestors
  placeStore placeMemoryLiveRegion bodyMemoryDefs placeTypedCopyPrimitiveMem
  fragGasMode fragGasPathMem fragGasSeqMem instMemFrontier memSafeRun
  bodyDeclMemoryCore bodyDeclMemoryCounted compileEnv context
  emitHelperProps emitHelper exprLoweringProps
  venomInst venomState venomExecSemantics valueEncodingProps
  exprSimDefs exprSimProps loweringPosts stmtLowering

Theorem assign_place_emit_store_path_mem[local]:
  (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                       | _ => MSTORE) [dst; op] sa = ((),sb) /\
  eval_operand dst s = SOME w /\ eval_operand op s = SOME wd /\
  (loc = LocMemory ==> w2n w + 32 <= s.vs_alloca_next) /\
  (loc = LocMemory \/ ~s.vs_call_ctx.cc_static) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_mem ctx func s 0
    (OK ((case loc of LocStorage => sstore w wd s
                   | LocTransient => tstore w wd s
                   | _ => mstore (w2n w) wd s)
         with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> (
  drule emitted_insts_emit_void >> strip_tac >>
  `same_blocks sa sb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def, same_blocks_def] >>
     strip_tac >> gvs[]) >>
  irule body_decl_zero_gas_path >> conj_tac >- simp[] >>
  qexists_tac `sa` >> simp[] >>
  Cases_on `loc` >> gvs[] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, exec_write2_def,
       eval_operands_def, is_terminator_def, mk_inst_def,
       fragExecMemTheory.run_inst_seq_mem_ok_def,
       below_frontier_MSTORE, inst_dload_in_section_def] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def])
QED

Theorem assign_place_word_continuation_mem:
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                       | _ => MSTORE) [dst_op; op] sa = ((),sb) /\
  eval_operand dst_op s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  is_word_type dty /\ expr_val_rel cx dty v op s /\
  expr_sim_inv cenv cx env ee /\ storage_place_region cx p /\
  (!id path entry t0.
     p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
     cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p v ee = (INL (),ff) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx ff t /\
      (!x. lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `eval_operand op s = SOME (typed_val_to_w256 dtv v)` by
    (fs[expr_val_rel_def] >> metis_tac[]) >>
  qabbrev_tac `u = (case loc of LocStorage => sstore w (typed_val_to_w256 dtv v) s
                  | LocTransient => tstore w (typed_val_to_w256 dtv v) s
                  | _ => mstore (w2n w) (typed_val_to_w256 dtv v) s)` >>
  `stmt_state_rel ctx func cenv cx ff u` by
    (Cases_on `p`
     >- (gvs[place_ptr_rel_def, Abbr `u`, slot_loc_def] >>
         drule_all place_store_word_backend_state >> Cases_on `b` >> gvs[])
     >- (rename1 `MemoryPlace id path` >>
         `loc = LocMemory` by fs[place_ptr_rel_def] >>
         gvs[Abbr `u`] >> irule place_store_word_memory_state >>
         qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
         qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[])
     >> gvs[place_ptr_rel_def, Abbr `u`, slot_loc_def] >>
     drule_all place_store_word_backend_state >> Cases_on `b` >> gvs[]) >>
  drule_all place_store_write_location >> strip_tac >>
  `loc = LocMemory ==> w2n w + 32 <= s.vs_alloca_next` by
    (strip_tac >> gvs[] >> drule_all memory_place_live_region >> strip_tac >>
     drule_all body_local_region_frontier >>
     drule_all word_tv_memory_size >> simp[]) >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    metis_tac[assign_place_emit_store_path_mem] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emitted_insts_emit_void >> strip_tac >>
     gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
         fresh_id_def, emit_def, comp_return_def]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[stmt_state_rel_inst_idx, Abbr `u`, mstore_def, sstore_def, tstore_def,
     lookup_var_def]
QED

Theorem assign_place_empty_continuation_mem:
  compile_store_at_loc imm dst_op (Lit 0w) (SOME loc) sa = ((),sb) /\
  eval_operand dst_op s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  has_length_word dty /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
  expr_sim_inv cenv cx env ee /\
  (!id path entry t0.
     p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
     cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p (default_value dtv) ee = (INL (),ff) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx ff t /\
      (!x. lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  qabbrev_tac `u = (case loc of LocStorage => sstore w 0w s
                  | LocTransient => tstore w 0w s
                  | _ => mstore (w2n w) 0w s)` >>
  `stmt_state_rel ctx func cenv cx ff u` by
    (Cases_on `p`
     >- (gvs[place_ptr_rel_def, Abbr `u`, slot_loc_def] >>
         drule_all place_store_empty_backend_state >> Cases_on `b` >> gvs[])
     >- (rename1 `MemoryPlace id path` >>
         `loc = LocMemory` by fs[place_ptr_rel_def] >>
         gvs[Abbr `u`] >> irule place_store_empty_memory_state >>
         qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
         qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[])
     >> gvs[place_ptr_rel_def]) >>
  drule_all place_store_write_location >> strip_tac >>
  `32 <= type_memory_size dtv` by
    (irule (cj 2 place_store_empty_representation) >>
     conj_tac >- (qexistsl_tac [`w2n w`, `(mstore (w2n w) 0w s).vs_memory`] >>
                   simp[mstore_mem_word_at_same]) >>
     metis_tac[]) >>
  `loc = LocMemory ==> w2n w + 32 <= s.vs_alloca_next` by
    (strip_tac >> gvs[] >> drule_all memory_place_live_region >> strip_tac >>
     drule_all body_local_region_frontier >> decide_tac) >>
  `emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                         | _ => MSTORE) [dst_op; Lit 0w] sa = ((),sb)` by
    (Cases_on `loc` >> gvs[compile_store_at_loc_def]) >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (`eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
     metis_tac[assign_place_emit_store_path_mem]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
         fresh_id_def, emit_def, comp_return_def]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[stmt_state_rel_inst_idx, Abbr `u`, mstore_def, sstore_def, tstore_def,
      lookup_var_def]
QED
