Theory bodyPtrIfExpNonwordCallerPremises
Ancestors exprSimIfExp exprSimOperators exprLoweringProps fragExec compileEnv
  exprSimDefs loweringPosts exprSimUnwrap

Theorem ifexp_nonword_code_layout:
  ~is_word_type t /\ compile_expr cenv ty (IfExp t c a b) st = (vv,st') /\
  fn_has_code st st' fn /\ local_ptrs_reserved cenv st /\
  (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id) /\
  (!e sa sb op. (e = a \/ e = b) /\ lower_value compile_expr cenv ty e sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id) ==>
  ?cop sc sj sn tl el xl rv se av sea aop sx sy sz.
    lower_value compile_expr cenv (BaseT BoolT) c st = (cop,sc) /\
    emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
    sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
    compile_expr cenv ty (if sel then a else b) se = (av,sea) /\
    compile_ifexp_arm cenv t (lowered_value_type cenv (if sel then a else b)) av sea = (aop,sx) /\
    emit_inst ASSIGN [aop] [rv] sx = ((),sy) /\
    emit_inst JMP [Label xl] [] sy = ((),sz) /\
    se.cs_current_bb = (if sel then tl else el) /\ se.cs_current_insts = [] /\
    st'.cs_current_bb = xl /\ st'.cs_current_insts = [] /\
    vv = LocatedValue t (mk_ptr (Var rv) LocMemory) /\
    fn_has_code st sc fn /\ fn_has_code sj sn fn /\
    fn_has_code se sea fn /\ fn_has_code sea sx fn /\
    fn_has_code sx sy fn /\ fn_has_code sy sz fn /\
    local_ptrs_reserved cenv se /\ cs_extends sc st' /\ cs_extends se sx /\
    st.cs_next_var <= sc.cs_next_var /\ st.cs_next_id <= sc.cs_next_id /\
    sc.cs_next_var <= se.cs_next_var /\ sc.cs_next_id <= se.cs_next_id /\
    sx.cs_next_id <= st'.cs_next_id /\ (!x. not_fresh_at st x ==> x <> rv)
Proof
  strip_tac >> drule_all compile_expr_ifexp_states >> strip_tac >>
  `cs_extends s5 s6 /\ cs_extends s8 s9 /\ cs_extends s9 s10 /\
   cs_extends s12 s13 /\ cs_extends s13 s14` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s6 s7 /\ cs_extends s10 s11 /\ cs_extends s14 st'` by
    metis_tac[cs_extends_new_block] >>
  `fn_has_code st s1 fn /\ fn_has_code s5 s6 fn /\
   fn_has_code s7 s8 fn /\ fn_has_code s8 s9 fn /\ fn_has_code s9 s10 fn /\
   fn_has_code s11 s12 fn /\ fn_has_code s12 s13 fn /\ fn_has_code s13 s14 fn` by
    metis_tac[fn_has_code_mid, fn_has_code_split, cs_extends_trans] >>
  `local_ptrs_reserved cenv s7 /\ local_ptrs_reserved cenv s11` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `cs_extends s7 s7a /\ cs_extends s7a s8 /\
   cs_extends s11 s11a /\ cs_extends s11a s12` by
    metis_tac[compile_expr_extends, ci_mono_compile_ifexp_arm, ci_mono_def, pairTheory.SND] >>
  `fn_has_code s7 s7a fn /\ fn_has_code s7a s8 fn /\
   fn_has_code s11 s11a fn /\ fn_has_code s11a s12 fn` by
    metis_tac[fn_has_code_split] >>
  Cases_on `sel`
  >- (qexistsl_tac [`cond_op`,`s1`,`s5`,`s6`,`tl`,`el`,`xl`,`rv`,
                   `s7`,`av`,`s7a`,`aop`,`s8`,`s9`,`s10`] >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`cond_op`,`s1`,`s5`,`s6`,`tl`,`el`,`xl`,`rv`,
               `s11`,`bv`,`s11a`,`bop`,`s12`,`s13`,`s14`] >> simp[] >> metis_tac[]
QED
