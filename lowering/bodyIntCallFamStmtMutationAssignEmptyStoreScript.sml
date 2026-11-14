(* The empty Assign optimization writes just the destination length word.
   Source RHS evaluation/read correspondence is discharged by the constructor. *)
Theory bodyIntCallFamStmtMutationAssignEmptyStore
Ancestors
  bodyIntCallFamStmtMutationResource placeStore placeMemoryLiveRegion
  vyperPlaceFrames vyperScopePreservation exprSimProps exprLoweringProps
  valueEncodingProps loweringStateRelDefs venomState compileEnv
  bodyIntCallJointContract loweringPosts valueEncoding stmtLowering
  exprSimHypsDefs emitHelper

Theorem intcall_assign_empty_store_path:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env ee sa s /\
  expr_sim_inv ce fp.jc_cx env ff /\
  compile_store_at_loc imm dst (Lit 0w) (SOME loc) sa = ((),sb) /\
  loc <> LocCode /\ loc <> LocCalldata /\
  eval_operand dst s = SOME w /\
  place_ptr_rel ce fp.jc_cx s (PlaceR p) w (SOME loc) (Type dty) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  has_length_word dty /\ evaluate_type (get_tenv fp.jc_cx) dty = SOME tv /\
  acyclic_struct_metadata ce.ce_struct_fields /\ storage_place_region fp.jc_cx p /\
  (!id path entry t0.
    p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
    ce.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv fp.jc_cx) t0 = SOME entry.type) /\
  write_place fp.jc_cx p (default_value tv) ee = (INL (),ff) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_joint_res fp ce env ff sb t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!a k. (loc = LocMemory ==> regions_disjoint a k (w2n w) 32) ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee s /\
   expr_sim_inv ce fp.jc_cx env ee /\ local_ptrs_reserved ce sa` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  qabbrev_tac `u = (case loc of LocStorage => sstore w 0w s
                  | LocTransient => tstore w 0w s
                  | _ => mstore (w2n w) 0w s)` >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ff u` by
    (Cases_on `p`
     >- (gvs[place_ptr_rel_def,Abbr `u`,slot_loc_def] >>
         drule_all place_store_empty_backend_state >> Cases_on `b` >> gvs[])
     >- (rename1 `MemoryPlace id path` >>
         `loc = LocMemory` by fs[place_ptr_rel_def] >>
         gvs[Abbr `u`] >> irule place_store_empty_memory_state >>
         qpat_assum `expr_sim_inv _ _ _ ee` (irule_at Any) >>
         qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[])
     >> gvs[place_ptr_rel_def]) >>
  drule_all place_store_write_location >> disch_tac >>
  `emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                         | _ => MSTORE) [dst; Lit 0w] sa = ((),sb)` by
    (Cases_on `loc` >> gvs[compile_store_at_loc_def]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s 0
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
   (!x. lookup_var x u = lookup_var x s) /\
   u.vs_allocas = s.vs_allocas /\ ~u.vs_halted /\
   u.vs_current_bb = sb.cs_current_bb /\
   SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule place_store_emit_run >> simp[Abbr `u`] >>
     qpat_assum `emit_void _ _ _ = _` (irule_at Any) >>
     simp[eval_operand_def]) >>
  qpat_x_assum `(_ \/ _ \/ _) /\ _` kall_tac >>
  suspend "resources"
QED

Resume intcall_assign_empty_store_path[resources]:
  markerLib.RESUME_TAC >>
  `MAP FDOM ee.scopes = MAP FDOM ff.scopes` by
    metis_tac[write_place_scopes_dom] >>
  `ff.immutables = ee.immutables` by
    (Cases_on `p` >> gvs[place_ptr_rel_def] >>
     metis_tac[write_storage_place_immutables,write_memory_place_immutables]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def,comp_bind_def,fresh_id_def,emit_def,
          comp_ignore_bind_def,comp_return_def] >> strip_tac >> gvs[]) >>
  `local_ptrs_reserved ce sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (Cases_on `loc` >> simp[Abbr `u`,mstore_def,sstore_def,tstore_def]) >>
  `!a k. (loc = LocMemory ==> regions_disjoint a k (w2n w) 32) ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory` by
    (Cases_on `loc` >> simp[Abbr `u`,sstore_def,tstore_def] >>
     rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >>
     fs[regions_disjoint_def]) >>
  `!a k. fp.jc_prot a k ==> regions_disjoint a k (w2n w) 32 \/
    loc <> LocMemory` by
    (rpt strip_tac >> Cases_on `loc = LocMemory` >> simp[] >> gvs[] >>
     drule_all memory_place_live_region >> strip_tac >>
     `32 <= type_memory_size tv` by
       (mp_tac (Q.SPECL [`get_tenv fp.jc_cx`,`dty`,`tv`,`w2n w`,
                        `(mstore (w2n w) 0w s).vs_memory`]
                  place_store_empty_representation) >>
        simp[mstore_mem_word_at_same]) >>
     drule_all intcall_local_region_protected >>
     fs[regions_disjoint_def] >> decide_tac) >>
  suspend "landing"
QED

Resume intcall_assign_empty_store_path[landing]:
  markerLib.RESUME_TAC >>
  qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!x. lookup_var x (u with vs_inst_idx := SUC s.vs_inst_idx) = lookup_var x s` by
    (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  simp[] >>
  qpat_assum `intcall_joint_res _ _ _ _ _ _`
    (mp_then Any mp_tac intcall_joint_res_mutation) >>
  disch_then irule >>
  simp[stmt_state_rel_inst_idx] >>
  suspend "joint"
QED

Resume intcall_assign_empty_store_path[joint]:
  markerLib.RESUME_TAC >> (
  `allocas_above fp.jc_lo s /\ ce_locals_declared ce env /\ locals_alloc_ok ce env` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  simp[intCallFrameTheory.allocas_above_def] >>
  conj_tac
  >- fs[intcall_joint_res_def,intcall_expr_res_def] >>
  conj_tac
  >- (rpt strip_tac >> irule local_region_frame >>
      conj_tac
      >- (qexists_tac `fp.jc_func` >> fs[stmt_state_rel_def,state_rel_def]) >>
      qexistsl_tac [`sa`,`ff.scopes`,`u with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
      fs[lookup_var_def]) >>
  fs[lookup_var_def] >>
  conj_tac
  >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  conj_tac
  >- (Cases >> Cases_on `loc` >>
      simp[eval_operand_def,lookup_var_def,Abbr `u`,mstore_def,sstore_def,tstore_def]) >>
  fs[intCallFrameTheory.allocas_above_def] >> metis_tac[])
QED

Finalise intcall_assign_empty_store_path
