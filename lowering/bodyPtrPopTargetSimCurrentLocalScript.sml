Theory bodyPtrPopTargetSimCurrentLocal
Ancestors
  bodyPtrPopTargetSimBoundary bodyPtrPopTargetDefs bodyPtrDefs
  stmtSimAugAssign exprSimHypsDefs exprSimProps bodySimAugPlaceLoad
  vyperTypeEnv vyperTypeInvariants vyperPlaceStatePreservation
  vyperTyping vyperState venomState finite_map words

(* The entry and representation are from the final index state, not from
   the base cut.  Only successful resolution, not value stability, is used. *)
Theorem target_current_local_path_ptr:
  expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\ ghost_inv d cenv cx es G tn s /\
  mem_path_offset tv path = SOME (off,ptv) /\
  ISL (evaluate_subscripts entry.type entry.value path) ==>
  entry.type = tv /\
  ?v. evaluate_subscripts tv entry.value path = INL v /\
      value_has_type ptv v /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory ptv v (w2n w + off) mem)
Proof
  strip_tac >>
  drule_all stmtSimAugAssignTheory.expr_sim_inv_local >> strip_tac >>
  `entry.type = tv` by metis_tac[optionTheory.SOME_11] >> simp[] >>
  `value_has_type tv entry.value /\ well_formed_type_value tv` by
    (gvs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[scope_well_typed_lookup_scopes]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv entry.value (w2n w) mem` by
    (gvs[ghost_inv_def] >> metis_tac[]) >>
  Cases_on `evaluate_subscripts tv entry.value path` >> gvs[] >>
  rename1 `evaluate_subscripts tv entry.value path = INL v` >>
  conj_tac >- metis_tac[mem_path_offset_sound, evaluate_subscripts_type] >>
  metis_tac[aug_place_path_project, arithmeticTheory.ADD_COMM]
QED

Theorem target_current_local_dynamic_ptr:
  expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\ ghost_inv d cenv cx es G tn s /\
  mem_path_offset tv path = SOME (off,ArrayTV etv (Dynamic cap)) /\
  ISL (evaluate_subscripts entry.type entry.value path) ==>
  ?vs. evaluate_subscripts tv entry.value path = INL (ArrayV (DynArrayV vs)) /\
       LENGTH vs <= cap /\ all_have_type etv vs /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
            (w2n w + off) mem)
Proof
  strip_tac >> drule_all target_current_local_path_ptr >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  metis_tac[]
QED

