(* Physical source layout for tuple assignment from an internal call. *)
Theory tupleWidenedLayout
Ancestors
  bodyMemoryPreds exprSimHyps exprSimHypsDefs vyperTypeValues
  vyperTypeInvariants vyperTypeSystem loweringPosts exprLowering compileEnv

Theorem tuple_call_physical_layout:
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
