Theory bodyPtrAssignPlaceCoverage
Ancestors
  bodyPtrPopTargetSimIndexSource assignBasePtrOffset ptrDiscipline exprSimHyps
  exprSimHypsDefs exprSimProps bodyPtrDefs bodyPtrPopTargetDefs loweringPosts
  loweringStateRelDefs exprLoweringProps venomMemDefs compileEnv venomState
  finite_map words

(* Capacity follows from the declared local allocation and the typed path,
   not from the current value's live footprint. *)
Theorem target_memory_place_coverage_ptr:
  target_post ctx func cenv cx es sa sb s0 ee
    (PlaceR (MemoryPlace id path)) (Type ty) r s /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) r G tn s /\
  ghost_inv d cenv cx ee G tn s /\
  expr_sim_inv cenv cx env ee ==>
  ?dst w. FST r = Var dst /\ lookup_var dst s = SOME w /\
    ptr_covers G tn dst s (type_memory_bytes cenv ty)
Proof
  strip_tac >>
  `place_readable cx ee (PlaceR (MemoryPlace id path))` by
    (gvs[target_post_def] >> metis_tac[]) >>
  drule_all target_readable_local_type_ptr >> strip_tac >>
  `?w. eval_operand (FST r) s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w
      (FST (SND r)) (Type ty)` by
    (gvs[target_post_def] >> metis_tac[]) >>
  qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
  simp[place_ptr_rel_def] >> strip_tac >> gvs[] >>
  `local_ptrs_rel func cenv ee.scopes s /\
    s.vs_alloca_next < dimword(:256)` by
    (gvs[target_post_def, stmt_state_rel_def, state_rel_def,
         alloca_inv_def, alloca_next_valid_def, alloca_room_def] >> metis_tac[]) >>
  `cenv.ce_var_type id = SOME ty'` by
    (gvs[expr_sim_inv_def] >> metis_tac[]) >>
  gvs[] >>
  `k + type_memory_size tv <= sz` by
    (drule mem_path_offset_sound >> strip_tac >>
     gvs[local_ptrs_rel_def] >> first_x_assum drule_all >>
     strip_tac >> decide_tac) >>
  `w2n b + k < dimword(:256)` by
    (gvs[local_ptrs_rel_def] >> first_x_assum drule_all >>
     strip_tac >> gvs[] >> decide_tac) >>
  `ptr_covers G tn p s sz` by (gvs[ghost_inv_def] >> metis_tac[]) >>
  `?base cap. FLOOKUP G p = SOME (base,cap)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `op_taint tn (FST r) = {} /\ op_prov G (FST r) = FLOOKUP G p` by
    (gvs[target_ptr_ok_def] >> metis_tac[]) >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (drule_all expr_sim_inv_memory_size >> simp[]) >>
  Cases_on `FST r` >> gvs[op_prov_def, eval_operand_def] >>
  drule assign_base_ptr_covers_offset_address >>
  disch_then irule >>
  simp[] >> qexists_tac `k` >>
  `k < dimword(:256)` by decide_tac >>
  simp[arithmeticTheory.LESS_MOD]
QED
