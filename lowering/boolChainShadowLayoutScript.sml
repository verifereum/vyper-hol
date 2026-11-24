(* Pair the two compiled tests before dividing their code into head and tail. *)
Theory boolChainShadowLayout
Ancestors
  gasShadowCompileStmtHelpers gasShadowState bodyFullShared[qualified]
  exprLoweringProps exprLowering emitHelperProps fragExec compileEnv
  gasShadow vyperAST venomInst list pair boolChainCodeLayout
Libs
  pairLib

Theorem bool_chain_labels_shadow[local]:
  gas_shadow_compiles
    (if d then
       comp_bind (fresh_label "and_next") (\ln.
         comp_bind (fresh_label "and_false") (\ls. comp_return (ln,ls)))
     else
       comp_bind (fresh_label "or_true") (\ls.
         comp_bind (fresh_label "or_next") (\ln. comp_return (ln,ls))))
    (if d then
       comp_bind (fresh_label "and_next") (\ln.
         comp_bind (fresh_label "and_false") (\ls. comp_return (ln,ls)))
     else
       comp_bind (fresh_label "or_true") (\ls.
         comp_bind (fresh_label "or_next") (\ln. comp_return (ln,ls))))
Proof
  Cases_on `d` >> simp[] >>
  irule gas_shadow_compiles_bind >> simp[gas_shadow_compiles_fresh_label] >>
  gen_tac >> irule gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_fresh_label, gas_shadow_compiles_return]
QED

Theorem bool_chain_test_shadow_layout:
  compile_bool_chain_ops compile_expr cenv d rv xl (e::h::hs) sa = ((),sb) /\
  compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) d rv xl
    (MAP gas_shadow_expr (e::h::hs)) shadow_sa = ((),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?op sc shadow_sc sj sn ls ln ss sd se st shadow_st.
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,sc) /\
    lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT)
      (gas_shadow_expr e) shadow_sa = (op,shadow_sc) /\
    gas_shadow_state sc shadow_sc /\
    emit_inst JNZ [op; Label (if d then ln else ls); Label (if d then ls else ln)]
      [] sj = ((),sn) /\
    new_block ls sn = (sn.cs_current_bb,ss) /\
    emit_inst ASSIGN [Lit (if d then 0w else 1w)] [rv] ss = ((),sd) /\
    emit_inst JMP [Label xl] [] sd = ((),se) /\
    new_block ln se = (se.cs_current_bb,st) /\
    compile_bool_chain_ops compile_expr cenv d rv xl (h::hs) st = ((),sb) /\
    compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) d rv xl
      (MAP gas_shadow_expr (h::hs)) shadow_st = ((),shadow_sb) /\
    gas_shadow_state st shadow_st /\
    sj.cs_current_bb = sc.cs_current_bb /\
    sj.cs_current_insts = sc.cs_current_insts /\
    sj.cs_blocks = sc.cs_blocks /\
    sj.cs_next_id = sc.cs_next_id /\ sj.cs_next_var = sc.cs_next_var /\
    ss.cs_current_bb = ls /\ ss.cs_current_insts = [] /\
    st.cs_current_bb = ln /\ st.cs_current_insts = [] /\
    ci_mono sa sc /\ ci_mono sc sj /\ ci_mono sj sn /\
    ci_mono sn ss /\ ci_mono ss sd /\ ci_mono sd se /\
    ci_mono se st /\ ci_mono st sb /\
    fn_has_code sa sc func /\ fn_has_code sj sn func /\
    fn_has_code sn ss func /\ fn_has_code ss sd func /\
    fn_has_code sd se func /\ fn_has_code se st func /\
    fn_has_code st sb func /\
    fn_has_code shadow_sa shadow_sc shadow_func /\
    fn_has_code shadow_st shadow_sb shadow_func
Proof
  pure_rewrite_tac[MAP] >> strip_tac >>
  qpat_x_assum `compile_bool_chain_ops _ cenv _ _ _ _ sa = _`
    (strip_assume_tac o MATCH_MP bool_chain_test_layout_alloc) >>
  rename1 `lower_value _ cenv _ e sa = (op,sc)` >>
  rename1 `(if d then _ else _) sc = ((ln,ls),sj)` >>
  rename1 `emit_inst JNZ _ [] sj = (_,sn)` >>
  rename1 `new_block ls sn = (_,ss)` >>
  rename1 `emit_inst ASSIGN [_] [rv] ss = (_,sd)` >>
  rename1 `emit_inst JMP [Label xl] [] sd = (_,se)` >>
  rename1 `new_block ln se = (_,st)` >>
  qpat_x_assum `compile_bool_chain_ops _ _ _ _ _ _ shadow_sa = _`
    (strip_assume_tac o MATCH_MP bool_chain_test_layout_alloc) >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (sop,shadow_sc)` >>
  rename1 `(if d then _ else _) shadow_sc = ((shadow_ln,shadow_ls),shadow_sj)` >>
  rename1 `emit_inst JNZ _ [] shadow_sj = (_,shadow_sn)` >>
  rename1 `new_block shadow_ls shadow_sn = (_,shadow_ss)` >>
  rename1 `emit_inst ASSIGN [_] [rv] shadow_ss = (_,shadow_sd)` >>
  rename1 `emit_inst JMP [Label xl] [] shadow_sd = (_,shadow_se)` >>
  rename1 `new_block shadow_ln shadow_se = (_,shadow_st)` >>
  qpat_x_assum `!fn. fn_has_code sa sb fn ==> _`
    (qspec_then `func` (drule_then strip_assume_tac)) >>
  qpat_x_assum `!fn. fn_has_code shadow_sa shadow_sb fn ==> _`
    (qspec_then `shadow_func` (drule_then strip_assume_tac)) >>
  `sop = op /\ gas_shadow_state sc shadow_sc` by
    (mp_then (Pos hd) (drule_all o GEN_ALL) bodyFullSharedTheory.gas_shadow_step
       gas_shadow_stmt_lower_value_env >> simp[]) >>
  `shadow_ln = ln /\ shadow_ls = ls /\ gas_shadow_state sj shadow_sj` by
    (mp_then (Pos hd) mp_tac bodyFullSharedTheory.gas_shadow_step bool_chain_labels_shadow >>
     disch_then drule_all >> simp[]) >>
  qpat_x_assum `sop = op` SUBST_ALL_TAC >>
  qpat_x_assum `shadow_ln = ln` SUBST_ALL_TAC >>
  qpat_x_assum `shadow_ls = ls` SUBST_ALL_TAC >>
  (* Match each emitted compiler operation at its related entry. *)
  map_every (fn (q,corr) => q by
    (mp_then (Pos hd) (drule_all o GEN_ALL) bodyFullSharedTheory.gas_shadow_step corr >> simp[]))
    [(`gas_shadow_state sn shadow_sn`, gas_shadow_compiles_emit_inst),
     (`gas_shadow_state ss shadow_ss`, gas_shadow_compiles_new_block),
     (`gas_shadow_state sd shadow_sd`, gas_shadow_compiles_emit_inst),
     (`gas_shadow_state se shadow_se`, gas_shadow_compiles_emit_inst),
     (`gas_shadow_state st shadow_st`, gas_shadow_compiles_new_block)] >>
  qexistsl_tac [`op`, `sc`, `shadow_sc`, `sj`, `sn`, `ls`, `ln`,
                `ss`, `sd`, `se`, `st`, `shadow_st`] >>
  simp[]
QED
