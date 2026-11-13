(* Allocation limits at the actual compiled storage-place destination. *)
Theory placeAssignAllocationBounds
Ancestors
  allocLimits allocLimitsProps bodySim placeAssignSourceClassification targetPlaceSimMem

Theorem assign_relayout_destination_limit[local]:
  stmt_exprs_ok ce (Assign (BaseTarget bt) e) /\
  target_store_place ce bt = SOME (SOME (ValPT dty)) /\
  ~is_word_type dty /\ dty <> lowered_value_type ce e /\
  ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type ce e)) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
  type_memory_bytes ce dty < dimword (:256)
Proof
  strip_tac >>
  `type_memory_bytes ce dty < 2 ** 64` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def, assign_alloc_ok_def] >>
  fs[wordsTheory.dimword_def]
QED

Theorem assign_relayout_nonempty:
  expr_sim_inv ce cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ~is_empty_value_expr e
Proof
  strip_tac >>
  `env_consistent env cx es` by fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  `well_typed_expr env e` by fs[vyperTypeSystemTheory.type_stmt_def] >>
  `env.type_defs = get_tenv cx` by
    fs[vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty` by
    (simp[vyperTypeSystemTheory.well_formed_type_def] >> rpt strip_tac >>
     metis_tac[exprSimSourceTheory.env_consistent_var_type_evaluates]) >>
  drule_all exprSimIfExpCompatTheory.ifexp_lowered_type_classify >>
  strip_tac >> gvs[stmtLoweringTheory.is_empty_value_expr_def]
QED

Theorem assign_relayout_compiled_destination_bound:
  expr_sim_inv ce cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  stmt_exprs_ok ce (Assign (BaseTarget bt) e) /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  type_place_target env bt = SOME (Type dty) /\
  compile_get_target_ptr compile_expr ce bt sa = (r,sb) /\
  target_post ctx func ce cx es sa sb s0 ee pv (Type dty) r s /\
  (FST (SND r) = SOME LocStorage \/ FST (SND r) = SOME LocTransient) ==>
  type_memory_bytes ce
    (case SND (SND r) of SOME (ValPT dt) => dt | _ => lowered_value_type ce e)
    < dimword (:256)
Proof
  strip_tac >>
  drule_all assign_relayout_source_classify >> strip_tac >>
  `~is_empty_value_expr e` by metis_tac[assign_relayout_nonempty] >>
  `SND (SND r) = SOME (ValPT dty)` by
    fs[loweringPostsTheory.target_post_def, exprLoweringTheory.value_type_place_def] >>
  drule compile_get_target_ptr_store_place >> simp[] >> strip_tac >>
  simp[] >> irule assign_relayout_destination_limit >>
  metis_tac[]
QED
