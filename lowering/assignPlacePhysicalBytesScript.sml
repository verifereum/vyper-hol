Theory assignPlacePhysicalBytes
Ancestors
  immutableDeployPhysicalSource assignPlaceBytesStore exprSimTypedAlloc
  valueCopyBytes loweringPosts exprSimHyps
Libs monadsyntax

(* Original source evaluation supplies physical typing; the current rebased
   post supplies representation and provenance after the pure target walk. *)
Theorem assign_place_physical_bytes_storage:
  (loc = LocStorage \/ loc = LocTransient) /\
  is_bytestring_type (lowered_value_type cenv e) /\
  is_bytestring_type dty /\
  compile_assign_value cenv dst loc src (is_word_type dty) src_loc dty
    (lowered_value_type cenv e)
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32,
             type_memory_bytes cenv et) | _ => NONE)
    (type_memory_bytes cenv dty) sa = ((),sb) /\
  expr_body_pre cenv cx env e es /\
  (do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,er) /\
  type_widens_to env.type_defs (expr_type e) dty /\
  expr_post ctx func cenv cx e ers si sa s0 ee v src s /\
  eval_operand dst s = SOME k /\
  place_ptr_rel cenv cx s (PlaceR p) k (SOME loc) (Type dty) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  expr_sim_inv cenv cx env' ee /\ local_ptrs_reserved cenv sa /\
  storage_place_region cx p /\ stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p v ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    alloca_frame cenv ee sa s cenv ff t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all immutable_rhs_physical_typed >> strip_tac >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty` by
    metis_tac[immutable_rhs_physical_widens] >>
  `is_bytestring_type (post_value_type cenv e)` by
    metis_tac[immutable_rhs_post_physical_classify] >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e)
     (post_value_type cenv e)` by
    metis_tac[immutable_rhs_physical_post_widens] >>
  drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> strip_tac >>
  `?ptv sw. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv /\
     value_has_type ptv v /\ eval_operand src s = SOME sw /\
     val_in_memory ptv v (w2n sw) s.vs_memory /\
     expr_val_at cenv cx (post_value_type cenv e) si sa ee v src s` by
    (gvs[expr_post_def, expr_val_rel_def, is_bytestring_word_type] >> metis_tac[]) >>
  `val_in_memory stv v (w2n sw) s.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `val_footprint stv v = val_footprint ptv v` by
    metis_tac[bytestring_val_footprint_eq] >>
  `w2n sw + val_footprint ptv v < dimword (:256)` by
    (irule expr_val_at_bound >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     simp[is_bytestring_word_type] >> goal_assum (drule_at Any) >> simp[]) >>
  `(case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32,
             type_memory_bytes cenv et) | _ => NONE) = NONE` by
    (Cases_on `dty` >> gvs[compileEnvTheory.is_bytestring_type_def]) >>
  fs[] >> irule assign_place_bytes_storage_run >> simp[] >>
  (conj_tac >- metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED
