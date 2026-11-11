(* Compilation and evaluated layout of a tuple literal's allocation prefix. *)
Theory bodyMemTupleLayout
Ancestors
  exprSimAggregateLayout exprSimAlloc exprLoweringProps exprSimHypsDefs
  fragExec allocLimits valueEncoding vyperAST

Theorem tuple_body_allocation_layout:
  expr_body_pre ce cx env (Builtin ann (MakeArray NONE bnd) args) st /\
  compile_expr ce ty (Builtin ann (MakeArray NONE bnd) args) sa = (vv,sb) /\
  fn_has_code sa sb func ==>
  ?tvs ba sm u.
    ann = TupleT (MAP expr_type args) /\
    vv = LocatedValue ann (mk_ptr u LocMemory) /\
    compile_alloc_buffer (type_memory_size_list tvs) sa = (ba,sm) /\
    compile_make_tuple compile_expr ce args ba.buf_operand 0 sm = (u,sb) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
    evaluate_type (get_tenv cx) ann = SOME (TupleTV tvs) /\
    SUM (MAP (type_memory_bytes ce o expr_type) args) = type_memory_size_list tvs /\
    type_memory_size_list tvs < dimword (:256) /\
    ci_mono sa sm /\ ci_mono sm sb /\ cs_extends sa sm /\ cs_extends sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size_list tvs))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >> drule compile_tuple_literal_inv >> strip_tac >> gvs[] >>
  drule make_tuple_evaluated_layout >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `SUM (MAP (type_memory_bytes ce o expr_type) args) < dimword (:256)` by
    (gvs[expr_body_pre_def, alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all buffer_alloc_code >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
