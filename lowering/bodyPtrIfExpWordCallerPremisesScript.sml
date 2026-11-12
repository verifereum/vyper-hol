Theory bodyPtrIfExpWordCallerPremises
Ancestors
  exprSimIfExp exprSimOperators exprLoweringProps fragExec compileEnv
  bodyPtrIfExpWord bodyPtrIfExpWordTyping bodyPtrIfExpWordPrefix
  exprSimDefs loweringPosts vyperState vyperInterpreter exprSimUnwrap bodyPtrPreds gasSummaryComposePtr

Theorem ifexp_word_code_layout:
  is_word_type t /\ compile_expr cenv ty (IfExp t c a b) st = (vv,st') /\
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
    unwrap_value cenv av sea = (aop,sx) /\
    emit_inst ASSIGN [aop] [rv] sx = ((),sy) /\
    emit_inst JMP [Label xl] [] sy = ((),sz) /\
    se.cs_current_bb = (if sel then tl else el) /\ se.cs_current_insts = [] /\
    st'.cs_current_bb = xl /\ st'.cs_current_insts = [] /\ vv = StackValue t (Var rv) /\
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
  gvs[ifexp_word_arm_compile] >>
  `cs_extends s7 s7a /\ cs_extends s7a s8 /\
   cs_extends s11 s11a /\ cs_extends s11a s12` by
    metis_tac[compile_expr_extends, unwrap_value_extends] >>
  `fn_has_code s7 s7a fn /\ fn_has_code s7a s8 fn /\
   fn_has_code s11 s11a fn /\ fn_has_code s11a s12 fn` by
    metis_tac[fn_has_code_split] >>
  Cases_on `sel`
  >- (qexistsl_tac [`s5`,`s6`,`s7.cs_current_bb`,`s11.cs_current_bb`,
                   `s7`,`av`,`s7a`,`aop`,`s8`,`s9`,`s10`] >> simp[]) >>
  qexistsl_tac [`s5`,`s6`,`s7.cs_current_bb`,`s11.cs_current_bb`,
               `s11`,`bv`,`s11a`,`bop`,`s12`,`s13`,`s14`] >> simp[]
QED

Theorem ifexp_marked_condition_arm_body:
  (!s raw st. eval_expr cx c s = (INL raw,st) ==> body_expr_ptr_ok cx a) /\
  (!s raw st. eval_expr cx c s = (INL raw,st) ==> body_expr_ptr_ok cx b) /\
  gas_marked_exec_ptr D (ctx,fn) PG
    (bind (eval_expr cx c) (read_result cx)) (es,s0,G0,tn0)
    marks (INL v) mid G tn r ==>
  body_expr_ptr_ok cx a /\ body_expr_ptr_ok cx b
Proof
  strip_tac >>
  `bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  gvs[bind_def, AllCaseEqs()] >> metis_tac[]
QED
