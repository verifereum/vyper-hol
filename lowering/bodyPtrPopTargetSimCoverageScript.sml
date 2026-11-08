Theory bodyPtrPopTargetSimCoverage
Ancestors
  bodyPtrPopTargetSimCurrentLocal assignBasePtrOffset assignBasePtrLocalSource
  bodyPtrDefs bodyPtrPopTargetDefs ptrDiscipline compileEnv
  loweringPosts exprSimProps exprSimHypsDefs vyperTypeInvariants
  venomState words finite_map vyperState stmtSimAugAssign

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
