(* Saved non-word values retain their robust footprint through later operands. *)
Theory bodyPtrTypeBuiltinsSavedOperand
Ancestors
  bodyPtrTypeBuiltinsRepresentation exprSimAttributeFields exprSimOperands
  loweringPosts bodyPtrDefs valueEncodingProofs valueEncoding arithmetic
  exprBopSimProps

Theorem saved_operand_footprint_window:
  !cenv cx ty sa sb es v op s tv w env ctx func e sc es' v' op' s'
   G tn G' tn'.
    expr_val_at cenv cx ty sa sb es v op s /\ ~is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\ expr_sim_inv cenv cx env es /\
    dynarray_free tv /\
    expr_post ctx func cenv cx e es sb sc s es' v' op' s' /\
    ghost_kept cenv es sb G tn s G' tn' ==>
    mem_bytes_at (w2n w) (val_footprint tv v) s'.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
    !i. i < val_footprint tv v /\ w2n w + i IN tn'.t_mem ==>
        w2n w + i IN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  gvs[expr_val_at_def]
  >- (`mem_bytes_at b sz s'.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (gvs[expr_post_def] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> strip_tac >>
      conj_tac >- metis_tac[] >>
      rpt strip_tac >>
      qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
      simp[ghost_kept_def] >> strip_tac >>
      qpat_x_assum `!aid off sz i. FLOOKUP _ aid = _ /\ _ ==> _` irule >>
      simp[] >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> metis_tac[])
  >- (`!k. dynarray_len_at cenv n k ==>
             w2n w + val_footprint tv v <= b + k \/ b + k + 32 <= w2n w` by
        (rpt strip_tac >> drule_all local_val_at_dynarray_apart >> decide_tac) >>
      conj_tac
      >- (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
          simp[expr_post_def] >> strip_tac >>
          qpat_x_assum `locals_kept _ _ _ _` mp_tac >>
          simp[locals_kept_def] >> strip_tac >>
          first_x_assum irule >> qexistsl_tac [`b`, `n`, `sz`] >> simp[] >>
          rpt strip_tac >> first_x_assum drule >> decide_tac) >>
      rpt strip_tac >>
      qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
      simp[ghost_kept_def] >> strip_tac >>
      qpat_x_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _` irule >>
      simp[] >> qexistsl_tac [`b`, `n`, `sz`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  simp[mem_bytes_at_def]
QED

Theorem saved_ptr_mem_ok:
  !cx ty v op G tn s cenv sa sb es env ctx func e sc es' v' op' s' G' tn'.
    ptr_mem_ok cx ty v op G tn s /\
    expr_val_at cenv cx ty sa sb es v op s /\ ~is_word_type ty /\
    (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> dynarray_free tv) /\
    expr_sim_inv cenv cx env es /\
    (!x. op = Var x ==> not_fresh_at sb x) /\ (!l. op <> Label l) /\
    expr_post ctx func cenv cx e es sb sc s es' v' op' s' /\
    ghost_kept cenv es sb G tn s G' tn' ==>
    ptr_mem_ok cx ty v op G' tn' s'
Proof
  rpt gen_tac >> strip_tac >> simp[ptr_mem_ok_def] >> rpt strip_tac >>
  `val_wf tv v /\ ?w0. eval_operand op s = SOME w0` by
    (gvs[expr_val_at_def] >> metis_tac[]) >>
  `eval_operand op s' = SOME w0` by
    (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sb`, `s`] >>
     gvs[expr_post_def]) >>
  gvs[] >>
  drule_all saved_operand_footprint_window >> strip_tac
  >~ [`val_in_memory _ _ _ _`]
  >- (irule robust_val_in_memory_decreasing_taint_transport >> simp[] >>
      qexistsl_tac [`s.vs_memory`, `s'.vs_memory`, `val_footprint tv v`,
                     `w2n w`, `tn.t_mem`, `tn'.t_mem`] >>
      simp[] >> gvs[ptr_mem_ok_def]) >>
  gvs[ptr_mem_ok_def, ghost_kept_def] >> metis_tac[]
QED
