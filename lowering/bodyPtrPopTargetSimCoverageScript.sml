Theory bodyPtrPopTargetSimCoverage
Ancestors
  bodyPtrPopTargetSimCurrentLocal assignBasePtrOffset assignBasePtrLocalSource
  bodyPtrDefs bodyPtrPopTargetDefs ptrDiscipline compileEnv
  loweringPosts exprSimProps exprSimHypsDefs vyperTypeInvariants
  venomState words finite_map vyperState stmtSimAugAssign
  stmtSimAugAssignPlaceMemory augAssignPtrRhsFrame

(* Use an address bound, not a bound on the ghost site's end: a site's
   capacity may exceed the compiler local's reserved extent. *)
Theorem target_local_header_coverage_ptr:
  local_ptrs_rel func cenv es.scopes s /\ ghost_inv d cenv cx es G tn s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\ s.vs_alloca_next < dimword(:256) /\
  off + 32 <= type_memory_size entry.type /\
  eval_operand op s = SOME (w + n2w off) /\
  op_prov G op = FLOOKUP G p /\ op_taint tn op = {} ==>
  ?src. op = Var src /\ ptr_covers G tn src s 32 /\
        lookup_var src s = SOME (w + n2w off) /\
        w2n (w + n2w off) = w2n w + off
Proof
  strip_tac >>
  `ptr_covers G tn p s sz` by (gvs[ghost_inv_def] >> metis_tac[]) >>
  `type_memory_size entry.type <= sz` by
    (gvs[local_ptrs_rel_def] >> metis_tac[]) >>
  `w2n w + off < dimword(:256)` by
    (gvs[local_ptrs_rel_def] >> first_x_assum drule_all >>
     strip_tac >> gvs[] >> decide_tac) >>
  `?b cap. FLOOKUP G p = SOME (b,cap)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  Cases_on `op` >> gvs[op_prov_def, eval_operand_def] >>
  `off + 32 <= sz /\ w2n w + off < dimword(:256)` by decide_tac >>
  conj_tac >- (irule assign_base_ptr_covers_offset_address >>
              metis_tac[arithmeticTheory.ADD_COMM]) >>
  `off < dimword(:256)` by decide_tac >>
  simp[w2n_add_2, w2n_n2w, arithmeticTheory.LESS_MOD]
QED

Theorem target_current_dynamic_header_ptr:
  expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\ s.vs_alloca_next < dimword(:256) /\
  mem_path_offset tv path = SOME (off,ArrayTV etv (Dynamic cap)) /\
  ISL (evaluate_subscripts entry.type entry.value path) /\
  eval_operand (FST rb) s = SOME (w + n2w off) /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) rb G tn s ==>
  ?src vs. FST rb = Var src /\ ptr_covers G tn src s 32 /\
       lookup_var src s = SOME (w + n2w off) /\
       evaluate_subscripts tv entry.value path = INL (ArrayV (DynArrayV vs)) /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
            (w2n (w + n2w off)) mem)
Proof
  strip_tac >>
  `entry.type = tv` by
    (drule_all stmtSimAugAssignTheory.expr_sim_inv_local >>
     strip_tac >> metis_tac[optionTheory.SOME_11]) >>
  drule_all target_current_local_dynamic_ptr >> strip_tac >>
  `off + 32 <= type_memory_size entry.type` by
    (drule mem_path_offset_sound >>
     gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `op_taint tn (FST rb) = {} /\ op_prov G (FST rb) = FLOOKUP G p` by
    (gvs[target_ptr_ok_def] >> metis_tac[]) >>
  drule_all target_local_header_coverage_ptr >> strip_tac >>
  qexistsl_tac [`src`, `vs`] >> gvs[]
QED

(* Transport only the saved address and its site.  The current source value
   is deliberately absent: index evaluation may have changed it. *)
Theorem target_memory_index_frame_ptr:
  target_post ctx func cenv cx es sa sm s0 ee
    (PlaceR (MemoryPlace id path)) vt rb s /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) rb G tn s /\
  expr_post ctx func cenv cx e ee sm sb s ef v x u /\
  ghost_kept cenv ee sm G tn s H un /\ local_ptrs_reserved cenv sm /\
  ghost_inv d cenv cx ee G tn s ==>
  (?w. eval_operand (FST rb) u = SOME w /\
       place_ptr_rel cenv cx u (PlaceR (MemoryPlace id path)) w
         (FST (SND rb)) vt) /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) rb H un u
Proof
  strip_tac >>
  `!z w. not_fresh_at sm z /\ lookup_var z s = SOME w ==>
          lookup_var z u = SOME w` by (gvs[expr_post_def] >> metis_tac[]) >>
  `?w. eval_operand (FST rb) s = SOME w /\
       place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w
         (FST (SND rb)) vt` by (gvs[target_post_def] >> metis_tac[]) >>
  `!z. FST rb = Var z ==> not_fresh_at sm z` by
    (gvs[target_post_def] >> metis_tac[]) >>
  `?src. FST rb = Var src` by
    (`?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
       (gvs[place_ptr_rel_def] >> metis_tac[]) >>
     `?entry. lookup_scopes id ee.scopes = SOME entry` by
       (qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[target_post_def, place_readable_def, read_place_def,
             get_scopes_def, bind_def, lift_option_type_def,
             return_def, raise_def] >>
        Cases_on `lookup_scopes id ee.scopes` >> simp[vyperStateTheory.raise_def]) >>
     `ptr_covers G tn p s sz` by (gvs[ghost_inv_def] >> metis_tac[]) >>
     Cases_on `FST rb` >> gvs[target_ptr_ok_def, op_prov_def, ptr_covers_def] >>
     metis_tac[]) >>
  conj_tac
  >- (qexists_tac `w` >> conj_tac
      >- (Cases_on `FST rb` >> gvs[eval_operand_def] >> metis_tac[]) >>
      irule stmtSimAugAssignPlaceMemoryTheory.aug_place_memory_ptr_frame >>
      metis_tac[]) >>
  gvs[target_ptr_ok_def] >> conj_tac
  >- (drule_all augAssignPtrRhsFrameTheory.ghost_kept_old_operand >>
      strip_tac >> gvs[]) >>
  rpt strip_tac >>
  `not_fresh_at sm p` by (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  Cases_on `FST rb` >> gvs[op_prov_def] >>
  metis_tac[augAssignPtrRhsFrameTheory.ghost_kept_old_operand]
QED

Theorem target_index_dynamic_header_ptr:
  target_post ctx func cenv cx es sa sm s0 ee
    (PlaceR (MemoryPlace id path)) (Type aty) rb s /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) rb G tn s /\
  ghost_inv d cenv cx ee G tn s /\
  expr_post ctx func cenv cx e ee sm sb s ef v x u /\
  ghost_kept cenv ee sm G tn s H un /\ local_ptrs_reserved cenv sm /\
  expr_sim_inv cenv cx env ef /\ FLOOKUP env.var_types id = SOME ty /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV etv (Dynamic cap)) /\
  ghost_inv d cenv cx ef H un u /\
  (!entry. lookup_scopes id ef.scopes = SOME entry ==>
     ISL (evaluate_subscripts entry.type entry.value path)) ==>
  ?src a vs. FST rb = Var src /\ ptr_covers H un src u 32 /\
    lookup_var src u = SOME a /\
    (!mem. mem_agree_outside un.t_mem u.vs_memory mem ==>
      val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
        (w2n a) mem)
Proof
  strip_tac >> drule_all target_memory_index_frame_ptr >> strip_tac >>
  drule_all stmtSimAugAssignTheory.expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by (gvs[expr_sim_inv_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ef u` by (gvs[expr_post_def] >> metis_tac[]) >>
  `local_ptrs_rel func cenv ef.scopes u /\ u.vs_alloca_next < dimword(:256)` by
    (gvs[exprLoweringPropsTheory.stmt_state_rel_def,
         compileEnvTheory.state_rel_def, venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.alloca_next_valid_def,
         exprLoweringPropsTheory.alloca_room_def] >>
     metis_tac[]) >>
  qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
  simp[place_ptr_rel_def] >> strip_tac >> gvs[] >>
  drule_all target_current_dynamic_header_ptr >> strip_tac >>
  metis_tac[]
QED
