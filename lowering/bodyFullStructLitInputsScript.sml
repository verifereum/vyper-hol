(* Store-input projection at the same endpoint returned by joint unwrap. *)
Theory bodyFullStructLitInputs
Ancestors
  bodyFullStructLitPhysical bodyFullStructLitAdd bodyFullUnwrap
  assignBasePtrBoundary exprSimMemDefs bodyPtrDefs
  loweringStateRelDefs loweringPosts
Libs monadsyntax

Theorem structlit_unwrapped_physical_inputs:
  expr_body_pre ce cx env e es /\
  (do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee) /\
  expr_post H ctx func ce cx e es si su s0 ee v op s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G s) /\
  (~is_word_type (post_value_type ce e) ==>
   !rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
          eval_operand op s = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= s.vs_alloca_next) /\
  ~is_word_type (lowered_value_type ce e) ==>
  ?stv sw.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    value_has_type stv v /\ val_wf stv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    eval_operand op s = SOME sw /\ op_taint tn op = {} /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory stv v (w2n sw) mem) /\
    (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
    (0 < type_memory_size stv ==>
     ?src. op = Var src /\ ptr_covers G tn src s (type_memory_size stv))
Proof
  strip_tac >>
  drule_all immutableDeployPhysicalSourceTheory.immutable_rhs_physical_typed >> strip_tac >>
  `~is_word_type (post_value_type ce e)` by
    (drule immutableDeployPhysicalSourceTheory.immutable_rhs_post_physical_classify >>
     metis_tac[valueCopyBytesTheory.is_bytestring_word_type]) >>
  drule_all structlit_child_physical_robust >> strip_tac >>
  qexistsl_tac [`stv`, `w`] >> simp[] >>
  conj_tac >- gvs[ptr_val_ok_def] >>
  strip_tac >>
  irule ptr_buf_ok_read_covers >>
  conj_tac >- gvs[ptr_val_ok_def] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`ce`, `e`] >> simp[]
QED

Theorem structlit_physical_footprint_bounds:
  expr_val_at ce cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  0 < val_footprint tv v /\
  eval_operand op s = SOME sw /\ stmt_state_rel H ctx func ce cx es s /\
  FLOOKUP s.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= dst /\ dst + dlen <= b+k /\
  (!name a n. local_region ce es.scopes s name a n ==>
    a+n <= dst \/ dst+dlen <= a) ==>
  w2n sw + val_footprint tv v < dimword (:256) /\
  (w2n sw + val_footprint tv v <= dst \/ dst+dlen <= w2n sw)
Proof
  strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[exprLoweringPropsTheory.alloca_room_next_lt,
              exprLoweringPropsTheory.stmt_state_rel_def] >>
  `local_ptrs_rel func ce es.scopes s` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[] >>
  rename1 `w2n sw + val_footprint tv v <= source_base + source_size`
  >- (rename1 `sa.cs_next_id <= source_id` >>
      `alloca_inv s` by
        gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
      `source_base+source_size <= s.vs_alloca_next` by
        (fs[venomMemDefsTheory.alloca_inv_def,
            venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
      `source_base+source_size <= b \/ b+k <= source_base` by
        (fs[venomMemDefsTheory.alloca_inv_def,
            venomMemDefsTheory.allocas_non_overlapping_def] >>
         `source_id <> did` by decide_tac >> metis_tac[]) >> decide_tac) >>
  `source_base + source_size <= s.vs_alloca_next` by
    (fs[local_ptrs_rel_def, local_region_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  first_x_assum drule >> decide_tac
QED
