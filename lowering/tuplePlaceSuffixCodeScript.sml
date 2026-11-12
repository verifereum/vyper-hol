(* Indexed decomposition of the actual arbitrary-place store suffix. *)
Theory tuplePlaceSuffixCode
Ancestors
  tupleAssignParts tuplePlaceCompilerStep rich_list stmtLowering compileEnv
  stmtLoweringMono exprLowering exprLoweringProps fragExec loweringSlice

Theorem tuple_place_suffix_code_parts:
  i < LENGTH tys /\ LENGTH ltys = LENGTH tys /\
  LENGTH gs = LENGTH tys /\ LENGTH elems = LENGTH tys /\
  EL i gs = BaseTarget bt /\
  compile_tuple_store_all cenv (DROP i ltys) (DROP i gs) (DROP i elems) sp = ((),sf) /\
  fn_has_code sp sf func ==>
  ?r sa sb.
    compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
    (let dst = FST r; loc_opt = FST (SND r); dst_ty_opt = SND (SND r);
         loc = case loc_opt of SOME l => l | NONE => LocMemory;
         dty = case dst_ty_opt of SOME (ValPT t) => t | _ => EL i ltys
     in (if is_word_type (EL i ltys) then
           if is_word_type dty then
             compile_store_at_loc cenv.ce_imm_alloca dst (EL i elems) loc_opt
           else emit_void INVALID []
         else compile_assign_value cenv dst loc (EL i elems) (is_word_type dty)
           NONE dty (EL i ltys) (type_memory_bytes cenv dty)) sa) = ((),sb) /\
    compile_tuple_store_all cenv (DROP (SUC i) ltys) (DROP (SUC i) gs)
      (DROP (SUC i) elems) sb = ((),sf) /\
    cs_extends sp sa /\ cs_extends sa sb /\ cs_extends sb sf /\
    sp.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_next_var <= sf.cs_next_var /\
    sp.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id <= sb.cs_next_id /\
    fn_has_code sp sa func /\ fn_has_code sa sb func /\ fn_has_code sb sf func
Proof
  strip_tac >>
  `DROP i ltys = EL i ltys :: DROP (SUC i) ltys` by simp[DROP_CONS_EL] >>
  `DROP i gs = BaseTarget bt :: DROP (SUC i) gs` by simp[DROP_CONS_EL] >>
  `DROP i elems = EL i elems :: DROP (SUC i) elems` by simp[DROP_CONS_EL] >>
  qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [Once compile_tuple_store_all_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `store cs'` >>
  pairarg_tac >> simp[] >> strip_tac >>
  `ci_mono sp cs'` by
    (mp_tac (Q.SPECL [`bt`,`cenv`,`sp`] ci_mono_compile_get_target_ptr) >> simp[]) >>
  `ci_mono cs' cs''` by
    (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
     rpt IF_CASES_TAC >> simp[] >> strip_tac >>
     metis_tac[cj 1 ci_mono_stmt_helpers, cj 2 ci_mono_stmt_helpers,
               ci_mono_emit_void, pairTheory.SND]) >>
  fs[Abbr `store`] >>
  drule tuple_target_stores_growth >> strip_tac >>
  fs[ci_mono_def] >>
  `cs_extends cs' sf` by metis_tac[cs_extends_trans] >>
  `fn_has_code sp cs' func /\ fn_has_code cs' sf func` by
    metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]

QED
