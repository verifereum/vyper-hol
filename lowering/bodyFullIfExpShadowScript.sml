(* The code layout of a ternary, for its compilation and its gas shadow's
   compilation together: the selected arm's and the condition's code on
   both sides, at shadow-related compiler states. *)
Theory bodyFullIfExpShadow
Ancestors
  gasShadow gasShadowState exprSimIfExp exprLoweringProps exprLowering
  emitHelperProps fragExec compileEnv loweringPosts vyperAST loweringStateRelDefs

Theorem lowered_value_type_gas_shadow[local]:
  lowered_value_type ce (gas_shadow_expr e) = lowered_value_type ce e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, lowered_value_type_def,
    gas_shadow_builtin_def, expr_type_def, listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  rpt (CASE_TAC >> gvs[lowered_value_type_def, expr_type_def,
    listTheory.MAP_MAP_o, combinTheory.o_DEF])
  >- (Cases_on `b` >> gvs[lowered_value_type_def, expr_type_def,
        listTheory.MAP_MAP_o, combinTheory.o_DEF])
  >- (Cases_on `t0` >> gvs[lowered_value_type_def, expr_type_def,
        listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
      Cases_on `l` >> simp[ETA_THM])
  >> Cases_on `c` >> simp[lowered_value_type_def, expr_type_def]
QED

Theorem gas_shadow_call[local]:
  gas_shadow_compiles f g /\ gas_shadow_state s ss /\
  f s = (v,u) /\ g ss = (w,su) ==>
  w = v /\ gas_shadow_state u su
Proof
  simp[gas_shadow_compiles_def] >> metis_tac[pairTheory.FST, pairTheory.SND]
QED

(* compile_expr_ifexp_states with the fresh names of its labels and result
   variable. *)
Theorem compile_expr_ifexp_layout[local]:
  !cenv ty t c a b st vv st'.
    compile_expr cenv ty (IfExp t c a b) st = (vv, st') /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) ==>
    ?cond_op s1 rv tl el xl s5 s6 x6 s7 av s7a aop s8 s9 s10 x10 s11 bv s11a bop s12 s13
     s14 x14 s2 s3 s4.
      fresh_var s1 = (rv,s2) /\
      fresh_label "then" s2 = (tl,s3) /\
      fresh_label "else" s3 = (el,s4) /\
      fresh_label "exit" s4 = (xl,s5) /\
      lower_value compile_expr cenv (BaseT BoolT) c st = (cond_op, s1) /\
      emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
      new_block tl s6 = (x6, s7) /\
      compile_expr cenv ty a s7 = (av, s7a) /\
      compile_ifexp_arm cenv t (lowered_value_type cenv a) av s7a = (aop, s8) /\
      emit_inst ASSIGN [aop] [rv] s8 = ((), s9) /\
      emit_inst JMP [Label xl] [] s9 = ((), s10) /\
      new_block el s10 = (x10, s11) /\
      compile_expr cenv ty b s11 = (bv, s11a) /\
      compile_ifexp_arm cenv t (lowered_value_type cenv b) bv s11a = (bop, s12) /\
      emit_inst ASSIGN [bop] [rv] s12 = ((), s13) /\
      emit_inst JMP [Label xl] [] s13 = ((), s14) /\
      new_block xl s14 = (x14, st') /\
      vv = (if is_word_type t then StackValue t (Var rv)
            else LocatedValue t (mk_ptr (Var rv) LocMemory)) /\
      s5.cs_current_bb = s1.cs_current_bb /\
      s5.cs_current_insts = s1.cs_current_insts /\
      s7.cs_current_bb = tl /\ s11.cs_current_bb = el /\
      st'.cs_current_bb = xl /\ s7.cs_current_insts = [] /\
      s11.cs_current_insts = [] /\ st'.cs_current_insts = [] /\
      cs_extends st s1 /\ cs_extends s1 s5 /\ cs_extends s7 s8 /\
      cs_extends s7 s11 /\ cs_extends s11 s12 /\ cs_extends s11 st' /\
      cs_extends s1 st' /\
      st.cs_next_var <= s1.cs_next_var /\ st.cs_next_id <= s1.cs_next_id /\
      s1.cs_next_var <= s7.cs_next_var /\ s1.cs_next_id <= s7.cs_next_id /\
      s1.cs_next_var <= s11.cs_next_var /\ s1.cs_next_id <= s11.cs_next_id /\
      s8.cs_next_id <= st'.cs_next_id /\ s12.cs_next_id <= st'.cs_next_id /\
      !x. not_fresh_at st x ==> x <> rv
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_expr_ifexp >> strip_tac >>
  qpat_x_assum `!st sb op. lower_value _ _ (BaseT BoolT) c _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  imp_res_tac (CONJUNCT1 compile_expr_grows) >>
  qspecl_then [`cenv`, `t`, `lowered_value_type cenv a`, `av`, `s7a`]
    mp_tac ci_mono_compile_ifexp_arm >>
  qspecl_then [`cenv`, `t`, `lowered_value_type cenv b`, `bv`, `s11a`]
    mp_tac ci_mono_compile_ifexp_arm >>
  simp[ci_mono_def] >> rpt strip_tac >>
  `cs_extends s7 s8 /\ s7.cs_next_var <= s8.cs_next_var /\
   s7.cs_next_id <= s8.cs_next_id /\
   cs_extends s11 s12 /\ s11.cs_next_var <= s12.cs_next_var /\
   s11.cs_next_id <= s12.cs_next_id` by
    (metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  imp_res_tac fresh_label_props >> imp_res_tac emit_inst_extends >>
  `cs_extends s1 s2` by metis_tac[cs_extends_fresh_var] >>
  `cs_extends s2 s3 /\ cs_extends s3 s4 /\ cs_extends s4 s5` by
     metis_tac[cs_extends_fresh_label] >>
  `cs_extends s5 s6 /\ cs_extends s8 s9 /\ cs_extends s9 s10 /\
   cs_extends s12 s13 /\ cs_extends s13 s14` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s6 s7 /\ cs_extends s10 s11 /\ cs_extends s14 st'` by
    metis_tac[cs_extends_new_block] >>
  `Abbrev (rv = STRING #"%" (toString s1.cs_next_var)) /\
   s2.cs_next_var = s1.cs_next_var + 1 /\ s2.cs_next_id = s1.cs_next_id /\
   s2.cs_current_bb = s1.cs_current_bb /\
   s2.cs_current_insts = s1.cs_current_insts /\ s2.cs_blocks = s1.cs_blocks` by
    (qpat_assum `fresh_var s1 = _` mp_tac >>
     pure_rewrite_tac[fresh_var_def, pairTheory.PAIR_EQ] >>
     strip_tac >> gvs[markerTheory.Abbrev_def]) >>
  `!x. not_fresh_at st x ==> x <> rv` by
    (fs[markerTheory.Abbrev_def] >> rw[not_fresh_at_def] >>
     first_x_assum (qspec_then `s1.cs_next_var` mp_tac) >> simp[]) >>
  `s7.cs_next_var = s2.cs_next_var /\ s7.cs_next_id = s1.cs_next_id + 1 /\
   s11.cs_next_var = s10.cs_next_var /\ s11.cs_next_id = s10.cs_next_id /\
   st'.cs_next_var = s14.cs_next_var /\ st'.cs_next_id = s14.cs_next_id /\
   s7.cs_current_insts = [] /\ s11.cs_current_insts = [] /\
   st'.cs_current_insts = [] /\ s7.cs_current_bb = tl /\
   s11.cs_current_bb = el /\ st'.cs_current_bb = xl` by
    (imp_res_tac new_block_props >> simp[]) >>
  `cs_extends s1 s5 /\ cs_extends s7 s11 /\ cs_extends s11 st'` by
    metis_tac[cs_extends_trans] >>
  `cs_extends s1 st'` by metis_tac[cs_extends_trans] >>
  qexistsl_tac [`s6`, `x6`,
                `s7`, `av`, `s7a`, `aop`, `s8`, `s9`, `s10`, `x10`, `s11`, `bv`, `s11a`, `bop`, `s12`,
                `s13`, `s14`, `x14`] >>
  simp[] >>
  qpat_x_assum `!x. not_fresh_at st x ==> x <> rv` (qspec_then `rv` mp_tac) >>
  simp[]
QED

(* The three spine premises are instances of gasShadowCompile's
   gas_shadow_compile_expr, gas_shadow_compiles_lower_value and the
   arm helpers' shadow compilation (alloc buffer, unwrap, store). *)
Theorem ifexp_shadow_code_layout:
  compile_expr cenv ty (IfExp t c a b) st = (vv,st') /\
  compile_expr cenv ty (gas_shadow_expr (IfExp t c a b)) shadow_st =
    (vv,shadow_st') /\
  gas_shadow_state st shadow_st /\
  fn_has_code st st' func /\ fn_has_code shadow_st shadow_st' shadow_func /\
  local_ptrs_reserved cenv st /\
  (!ty' e. gas_shadow_compiles (compile_expr cenv ty' e)
             (compile_expr cenv ty' (gas_shadow_expr e))) /\
  (!ty' e. gas_shadow_compiles (lower_value compile_expr cenv ty' e)
             (lower_value compile_expr cenv ty' (gas_shadow_expr e))) /\
  (!rt at av. gas_shadow_compiles (compile_ifexp_arm cenv rt at av)
                (compile_ifexp_arm cenv rt at av)) ==>
  ?cop sc shadow_sc sj sn tl el xl rv se shadow_se av sea shadow_sea aop
   sx sy sz.
    lower_value compile_expr cenv (BaseT BoolT) c st = (cop,sc) /\
    lower_value compile_expr cenv (BaseT BoolT) (gas_shadow_expr c)
      shadow_st = (cop,shadow_sc) /\
    gas_shadow_state sc shadow_sc /\
    emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
    sj.cs_current_bb = sc.cs_current_bb /\
    sj.cs_current_insts = sc.cs_current_insts /\
    compile_expr cenv ty (if sel then a else b) se = (av,sea) /\
    compile_expr cenv ty (gas_shadow_expr (if sel then a else b)) shadow_se =
      (av,shadow_sea) /\
    gas_shadow_state se shadow_se /\ gas_shadow_state sea shadow_sea /\
    compile_ifexp_arm cenv t (lowered_value_type cenv (if sel then a else b))
      av sea = (aop,sx) /\
    emit_inst ASSIGN [aop] [rv] sx = ((),sy) /\
    emit_inst JMP [Label xl] [] sy = ((),sz) /\
    se.cs_current_bb = (if sel then tl else el) /\ se.cs_current_insts = [] /\
    st'.cs_current_bb = xl /\ st'.cs_current_insts = [] /\
    vv = (if is_word_type t then StackValue t (Var rv)
          else LocatedValue t (mk_ptr (Var rv) LocMemory)) /\
    fn_has_code st sc func /\ fn_has_code shadow_st shadow_sc shadow_func /\
    fn_has_code sj sn func /\
    fn_has_code se sea func /\ fn_has_code shadow_se shadow_sea shadow_func /\
    fn_has_code sea sx func /\
    fn_has_code sx sy func /\ fn_has_code sy sz func /\
    local_ptrs_reserved cenv se /\ cs_extends sc st' /\ cs_extends se sx /\
    st.cs_next_var <= sc.cs_next_var /\ st.cs_next_id <= sc.cs_next_id /\
    sc.cs_next_var <= se.cs_next_var /\ sc.cs_next_id <= se.cs_next_id /\
    se.cs_next_var <= sea.cs_next_var /\ se.cs_next_id <= sea.cs_next_id /\
    sx.cs_next_id <= st'.cs_next_id /\ (!x. not_fresh_at st x ==> x <> rv)
Proof
  strip_tac >>
  qpat_assum `compile_expr _ _ (IfExp _ _ _ _) st = _`
    (mp_then (Pos hd) mp_tac compile_expr_ifexp_layout) >>
  (impl_tac >- metis_tac[CONJUNCT2 compile_expr_grows]) >> strip_tac >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
  (fn th => mp_then Any (qx_choosel_then
    [`hc`,`h1`,`hr`,`h2`,`ht`,`h3`,`he`,`h4`,`hx`,`h5`,`h6`,`hu6`,
     `h7`,`hv`,`h7a`,`hop`,`h8`,`h9`,`h10`,`hu10`,`h11`,`hw`,`h11a`,
     `hbp`,`h12`,`h13`,`h14`,`hu14`] strip_assume_tac) compile_expr_ifexp
      (SRULE[gas_shadow_expr_def] th)) >>
  `hc = cond_op /\ gas_shadow_state s1 h1` by metis_tac[gas_shadow_call] >>
  `hr = rv /\ gas_shadow_state s2 h2` by
    metis_tac[gas_shadow_call, gas_shadow_compiles_fresh_var] >>
  `ht = tl /\ gas_shadow_state s3 h3` by
    metis_tac[gas_shadow_call, gas_shadow_compiles_fresh_label] >>
  `he = el /\ gas_shadow_state s4 h4` by
    metis_tac[gas_shadow_call, gas_shadow_compiles_fresh_label] >>
  `hx = xl /\ gas_shadow_state s5 h5` by
    metis_tac[gas_shadow_call, gas_shadow_compiles_fresh_label] >>
  `gas_shadow_state s6 h6` by
    metis_tac[gas_shadow_call, gas_shadow_compiles_emit_inst] >>
  `gas_shadow_state s7 h7` by
    metis_tac[gas_shadow_call, gas_shadow_compiles_new_block] >>
  `hv = av /\ gas_shadow_state s7a h7a` by metis_tac[gas_shadow_call] >>
  fs[lowered_value_type_gas_shadow] >>
  `hop = aop /\ gas_shadow_state s8 h8` by metis_tac[gas_shadow_call] >>
  `gas_shadow_state s9 h9` by
    metis_tac[gas_shadow_call, gas_shadow_compiles_emit_inst] >>
  `gas_shadow_state s10 h10` by
    metis_tac[gas_shadow_call, gas_shadow_compiles_emit_inst] >>
  `gas_shadow_state s11 h11` by
    metis_tac[gas_shadow_call, gas_shadow_compiles_new_block] >>
  `hw = bv /\ gas_shadow_state s11a h11a` by metis_tac[gas_shadow_call] >>
  imp_res_tac (CONJUNCT1 compile_expr_grows) >>
  imp_res_tac (CONJUNCT2 compile_expr_grows) >>
  `cs_extends s7a s8 /\ cs_extends s11a s12` by
    metis_tac[ci_mono_compile_ifexp_arm, ci_mono_def, pairTheory.SND] >>
  `cs_extends s5 s6 /\ cs_extends s8 s9 /\ cs_extends s9 s10 /\
   cs_extends s12 s13 /\ cs_extends s13 s14` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s6 s7 /\ cs_extends s10 s11 /\ cs_extends s14 st'` by
    metis_tac[cs_extends_new_block] >>
  `fn_has_code st s1 func /\ fn_has_code s5 s6 func /\
   fn_has_code s7 s7a func /\ fn_has_code s7a s8 func /\
   fn_has_code s8 s9 func /\ fn_has_code s9 s10 func /\
   fn_has_code s11 s11a func /\ fn_has_code s11a s12 func /\
   fn_has_code s12 s13 func /\ fn_has_code s13 s14 func` by
    metis_tac[fn_has_code_mid, fn_has_code_split, cs_extends_trans] >>
  `local_ptrs_reserved cenv s7 /\ local_ptrs_reserved cenv s11` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `cs_extends h1 h2 /\ cs_extends h2 h3 /\ cs_extends h3 h4 /\
   cs_extends h4 h5` by
    metis_tac[cs_extends_fresh_var, cs_extends_fresh_label] >>
  `cs_extends h5 h6 /\ cs_extends h8 h9 /\ cs_extends h9 h10 /\
   cs_extends h12 h13 /\ cs_extends h13 h14` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends h6 h7 /\ cs_extends h10 h11 /\ cs_extends h14 shadow_st'` by
    metis_tac[cs_extends_new_block] >>
  `cs_extends h7a h8 /\ cs_extends h11a h12` by
    metis_tac[ci_mono_compile_ifexp_arm, ci_mono_def, pairTheory.SND] >>
  `cs_extends h11 shadow_st'` by metis_tac[cs_extends_trans] >>
  `cs_extends h7 shadow_st'` by metis_tac[cs_extends_trans] >>
  `cs_extends h1 shadow_st'` by metis_tac[cs_extends_trans] >>
  `fn_has_code shadow_st h1 shadow_func /\
   fn_has_code h7 h7a shadow_func /\ fn_has_code h11 h11a shadow_func` by
    metis_tac[fn_has_code_mid, fn_has_code_split, cs_extends_trans] >>
  Cases_on `sel`
  >- (qexistsl_tac [`s5`,`s6`,`tl`,`el`,`rv`,`s7`,`h7`,`av`,`s7a`,
        `h7a`,`aop`,`s8`,`s9`,`s10`] >> simp[]) >>
  qexistsl_tac [`s5`,`s6`,`tl`,`el`,`rv`,`s11`,`h11`,`bv`,`s11a`,
        `h11a`,`bop`,`s12`,`s13`,`s14`] >> simp[]
QED
