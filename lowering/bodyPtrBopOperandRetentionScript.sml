Theory bodyPtrBopOperandRetention
Ancestors
  bodyPtrDefs stmtSimLogArgs loweringPosts bodyPtrBopRepresentationFrame ptrDiscipline

Theorem bop_argument_taint_kept:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  log_arg_clear cenv cx ty v /\ eval_operand op s = SOME w /\
  ghost_kept cenv es sb G tn s G' tn' /\
  w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn'.t_mem ==>
  i IN tn.t_mem
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (`b <= i /\ i < b + sz` by decide_tac >>
      fs[ghost_kept_def] >>
      qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _`
        (qspecl_then [`aid`, `b`, `sz`, `i`] mp_tac) >>
      simp[] >> disch_then irule >> metis_tac[])
  >- (`b <= i /\ i < b + sz` by decide_tac >>
      `!k. dynarray_len_at cenv n k ==>
        i < b + k \/ b + (k + 32) <= i` by
        (rpt strip_tac >>
         `w2n w - b + val_footprint tv v <= k \/ k + 32 <= w2n w - b` by
           metis_tac[log_arg_clear_def] >> decide_tac) >>
      fs[ghost_kept_def] >>
      qpat_x_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _`
        (qspecl_then [`n`, `b`, `sz`, `i`] mp_tac) >>
      simp[] >> disch_then irule >> metis_tac[]) >>
  gvs[]
QED

Theorem bop_argument_ptr_val_kept:
  ptr_val_ok cx ty v op G tn s /\
  expr_val_at cenv cx ty sa sb es v op s /\
  wb_frame cenv es sb s t /\ ghost_kept cenv es sb G tn s G' tn' /\
  log_arg_clear cenv cx ty v /\
  (!x. op = Var x ==> not_fresh_at sb x) /\
  eval_operand op t = eval_operand op s /\
  (~is_word_type ty ==> evaluate_type (get_tenv cx) ty = SOME tv) ==>
  ptr_val_ok cx ty v op G' tn' t
Proof
  strip_tac >>
  `op_taint tn' op = op_taint tn op` by
    (Cases_on `op` >> gvs[op_taint_def, ghost_kept_def]) >>
  `op_prov G' op = op_prov G op` by
    (Cases_on `op` >> gvs[op_prov_def, ghost_kept_def]) >>
  `is_word_type ty ==> op_prov G' op = NONE` by
    metis_tac[ptr_val_ok_def] >>
  irule bop_ptr_val_ok_frame >> simp[] >>
  qexistsl_tac [`G`, `s`, `tn`, `tv`] >> simp[] >> strip_tac >> simp[] >>
  conj_tac >- metis_tac[expr_val_at_def] >>
  conj_tac >- metis_tac[ghost_kept_def] >>
  rpt strip_tac >> gvs[]
  >- (drule_all log_argument_footprint_kept >> simp[]) >>
  drule_all bop_argument_taint_kept >> simp[]
QED
