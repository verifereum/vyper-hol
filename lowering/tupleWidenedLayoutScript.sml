(* Physical source layout for tuple assignment from an internal call. *)
Theory tupleWidenedLayout
Ancestors
  bodyMemoryPreds exprSimHyps exprSimHypsDefs vyperTypeValues
  vyperTypeInvariants vyperTypeSystem loweringPosts exprLowering compileEnv
  exprSimIfExpCompat exprSimSource typedNormalizeWidening stmtLowering

Theorem tuple_call_physical_layout[local]:
  !ce cx env es tys fid args drv.
    expr_body_pre ce cx env (Call (TupleT tys) (IntCall fid) args drv) es ==>
    ?src_tys tvs.
      lowered_value_type ce (Call (TupleT tys) (IntCall fid) args drv) =
        TupleT src_tys /\
      post_value_type ce (Call (TupleT tys) (IntCall fid) args drv) =
        TupleT src_tys /\
      evaluate_type (get_tenv cx) (TupleT src_tys) = SOME (TupleTV tvs) /\
      type_widens_to (get_tenv cx) (TupleT src_tys) (TupleT tys)
Proof
  rpt strip_tac >>
  drule ifexp_intcall_copy_source >>
  simp[is_word_type_def, is_bytestring_type_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `type_widens_to _ sty (TupleT tys)` >>
  `?src_tys. sty = TupleT src_tys` by
    (Cases_on `sty` >>
     fs[type_widens_to_def, arg_type_fits_def]) >>
  gvs[] >> drule evaluate_type_TupleT_cases >> strip_tac >> gvs[]
QED

Theorem tuple_widened_source_ready:
  !ce cx env es e tys.
    expr_body_pre ce cx env e es /\ expr_type e = TupleT tys /\
    lowered_value_type ce e <> expr_type e ==>
    ~is_memory_view e /\
    ?fid args drv src_tys tvs.
      e = Call (TupleT tys) (IntCall fid) args drv /\
      lowered_value_type ce e = TupleT src_tys /\
      post_value_type ce e = TupleT src_tys /\
      evaluate_type (get_tenv cx) (TupleT src_tys) = SOME (TupleTV tvs) /\
      LENGTH src_tys = LENGTH tys /\ LENGTH tvs = LENGTH src_tys /\
      (!i. i < LENGTH src_tys ==>
        type_widens_to (get_tenv cx) (EL i src_tys) (EL i tys))
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_var_types_well_formed >> disch_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  drule_all ifexp_lowered_type_classify >>
  simp[is_bytestring_type_def] >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def] >>
  drule tuple_call_physical_layout >> strip_tac >>
  drule type_widens_to_tuple_length >> disch_tac >>
  `LENGTH tvs = LENGTH src_tys` by
    (drule evaluate_type_TupleT_cases >> simp[] >> strip_tac >>
     metis_tac[listTheory.LIST_REL_LENGTH]) >>
  simp[is_memory_view_def] >>
  gvs[type_widens_to_tuple_EL]
QED
