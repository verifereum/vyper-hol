(* A saved aggregate footprint gains no taint across a ghost frame. *)
Theory bodyPtrArgumentFootprint
Ancestors bodyPtrDefs loweringPosts exprLoweringProps context
  venomState valueEncoding valueEncodingDefs words arithmetic

Theorem pure_argument_taint_kept:
  !lo cenv cx ty tv v op sa sb es s G0 tn0 G tn w i.
    expr_val_at cenv cx ty sa sb es v op s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand op s = SOME w /\
    ghost_kept_at lo cenv es sb G0 tn0 s G tn /\
    w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn.t_mem ==>
    i IN tn0.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  disch_then (qspec_then `tv` mp_tac) >> simp[] >> strip_tac
  >- (gvs[] >> fs[ghost_kept_at_def] >>
      qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _`
        (qspecl_then [`aid`, `b`, `sz`, `i`] mp_tac) >>
      simp[] >> disch_then irule >> metis_tac[])
  >- (gvs[] >> fs[ghost_kept_at_def] >>
      qpat_x_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _`
        (qspecl_then [`n`, `b`, `sz`, `i`] mp_tac) >>
      simp[]) >>
  gvs[]
QED
