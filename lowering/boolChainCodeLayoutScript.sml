Theory boolChainCodeLayout
Ancestors
  exprSimHypsDefs exprBopLowering exprLoweringProps boolChainOpsCong
  ctorCallFreeBoolChain fragExec emitHelperProps loweringStateRelDefs
  list arithmetic pair exprCallBounds vyperAST compileEnv exprLowering
Libs
  pairLib

(* The recursion guard of builtin dispatch admits every extracted operand. *)
Theorem bool_chain_dispatch_callback[local]:
  compile_bool_chain_ops
    (expr_child_callback (cenv_defaults_size cenv + (expr_size e + 1))
                         compile_expr)
    cenv d rv xl (bool_chain_operands d k e) =
  compile_bool_chain_ops compile_expr cenv d rv xl (bool_chain_operands d k e)
Proof
  irule compile_bool_chain_ops_lower_value_cong >> rpt strip_tac >>
  irule lower_value_child_call >>
  drule bool_chain_operand_size >> decide_tac
QED

Theorem bool_chain_root_layout:
  compile_expr cenv ty (Builtin ann (BoolChain d n) [e]) sa = (vv,sb) ==>
  ?rv sr xl sg sf old.
    fresh_var sa = (rv,sr) /\
    fresh_label "bool_exit" sr = (xl,sg) /\
    compile_bool_chain_ops compile_expr cenv d rv xl
      (bool_chain_operands d (n - 1) e) sg = ((),sf) /\
    new_block xl sf = (old,sb) /\
    vv = StackValue ann (Var rv) /\
    sg.cs_current_bb = sa.cs_current_bb /\
    sg.cs_current_insts = sa.cs_current_insts /\
    sg.cs_blocks = sa.cs_blocks /\
    sg.cs_next_id = sa.cs_next_id /\
    sg.cs_next_var = sa.cs_next_var + 1 /\
    ~not_fresh_at sa rv /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
    ci_mono sa sg /\ ci_mono sg sf /\ ci_mono sf sb /\
    (!fn. fn_has_code sa sb fn ==>
       fn_has_code sg sf fn /\ fn_has_code sf sb fn)
Proof
  `~names_builtin (BoolChain d n) [e]` by (Cases_on `e` >> simp[names_builtin_def]) >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once compile_builtin_dispatch_component_eq, bool_chain_dispatch_callback] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rename1 `fresh_var sa = (rv,sr)` >>
  rename1 `fresh_label "bool_exit" sr = (xl,sg)` >>
  rename1 `new_block xl sf = (old,sb)` >>
  `ci_mono sa sg` by
    (irule ci_mono_trans >> qexists `sr` >> conj_tac
     >- (qspec_then `sa` mp_tac ci_mono_fresh_var >> simp[]) >>
     qspecl_then [`"bool_exit"`, `sr`] mp_tac ci_mono_fresh_label >> simp[]) >>
  `ci_mono sg sf` by
    (`ci_mono sg (SND (compile_bool_chain_ops compile_expr cenv d rv xl
                        (bool_chain_operands d (n - 1) e) sg))`
      by simp[ci_mono_compile_bool_chain_ops, ci_mono_lower_value_compile_expr] >>
     gvs[]) >>
  `ci_mono sf sb` by
    (qspecl_then [`xl`, `sf`] mp_tac ci_mono_new_block >> simp[]) >>
  `!fn. fn_has_code sa sb fn ==> fn_has_code sg sf fn /\ fn_has_code sf sb fn` by
    (rpt strip_tac >> fs[ci_mono_def] >>
     metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl]) >>
  drule_then strip_assume_tac fresh_label_props >>
  drule_then strip_assume_tac new_block_props >>
  qexistsl_tac [`sf`, `old`] >> simp[] >>
  qpat_x_assum `fresh_var sa = _` mp_tac >>
  simp[fresh_var_def, not_fresh_at_def] >> strip_tac >> gvs[] >>
  metis_tac[LESS_EQ_REFL]
QED

Theorem bool_chain_singleton_layout:
  compile_bool_chain_ops compile_expr cenv d rv xl [e] sa = ((),sb) ==>
  ?op sc sd.
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,sc) /\
    emit_inst ASSIGN [op] [rv] sc = ((),sd) /\
    emit_inst JMP [Label xl] [] sd = ((),sb) /\
    ci_mono sa sc /\ ci_mono sc sd /\ ci_mono sd sb /\
    (!fn. fn_has_code sa sb fn ==>
       fn_has_code sa sc fn /\ fn_has_code sc sd fn /\ fn_has_code sd sb fn)
Proof
  simp[Once compile_bool_chain_ops_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `lower_value _ _ _ _ sa = (op,sc)` >>
  rename1 `emit_inst ASSIGN [op] [rv] sc = (_,sd)` >>
  `ci_mono sa sc` by
    (qspecl_then [`cenv`, `BaseT BoolT`, `e`, `sa`] mp_tac
       ci_mono_lower_value_compile_expr >> simp[]) >>
  `ci_mono sc sd` by
    (qspecl_then [`ASSIGN`, `[op]`, `[rv]`, `sc`] mp_tac ci_mono_emit_inst >> simp[]) >>
  `ci_mono sd sb` by
    (qspecl_then [`JMP`, `[Label xl]`, `[]`, `sd`] mp_tac ci_mono_emit_inst >> simp[]) >>
  simp[] >> rpt strip_tac >> fs[ci_mono_def] >>
  metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl]
QED

(* Allocating the two branch labels changes neither the PC nor the instruction
   and variable counters. The allocation order is different in each arm. *)
Theorem bool_chain_test_labels_layout[local]:
  (if d then
     comp_bind (fresh_label "and_next") (\ln.
       comp_bind (fresh_label "and_false") (\ls. comp_return (ln,ls)))
   else
     comp_bind (fresh_label "or_true") (\ls.
       comp_bind (fresh_label "or_next") (\ln. comp_return (ln,ls)))) sc = ((ln,ls),sj) ==>
  sj.cs_current_bb = sc.cs_current_bb /\
  sj.cs_current_insts = sc.cs_current_insts /\
  sj.cs_blocks = sc.cs_blocks /\
  sj.cs_next_id = sc.cs_next_id /\ sj.cs_next_var = sc.cs_next_var
Proof
  Cases_on `d` >> simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  imp_res_tac fresh_label_props >> gvs[]
QED

Theorem bool_chain_test_layout_alloc:
  compile_bool_chain_ops compile_expr cenv d rv xl (e::h::hs) sa = ((),sb) ==>
  ?op sc sj sn ls ln ss sd se st.
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,sc) /\
    (if d then
       comp_bind (fresh_label "and_next") (\ln.
         comp_bind (fresh_label "and_false") (\ls. comp_return (ln,ls)))
     else
       comp_bind (fresh_label "or_true") (\ls.
         comp_bind (fresh_label "or_next") (\ln. comp_return (ln,ls)))) sc =
      ((ln,ls),sj) /\
    emit_inst JNZ [op; Label (if d then ln else ls); Label (if d then ls else ln)]
      [] sj = ((),sn) /\
    new_block ls sn = (sn.cs_current_bb,ss) /\
    emit_inst ASSIGN [Lit (if d then 0w else 1w)] [rv] ss = ((),sd) /\
    emit_inst JMP [Label xl] [] sd = ((),se) /\
    new_block ln se = (se.cs_current_bb,st) /\
    compile_bool_chain_ops compile_expr cenv d rv xl (h::hs) st = ((),sb) /\
    sj.cs_current_bb = sc.cs_current_bb /\
    sj.cs_current_insts = sc.cs_current_insts /\
    sj.cs_blocks = sc.cs_blocks /\
    sj.cs_next_id = sc.cs_next_id /\ sj.cs_next_var = sc.cs_next_var /\
    ss.cs_current_bb = ls /\ ss.cs_current_insts = [] /\
    st.cs_current_bb = ln /\ st.cs_current_insts = [] /\
    ci_mono sa sc /\ ci_mono sc sj /\ ci_mono sj sn /\
    ci_mono sn ss /\ ci_mono ss sd /\ ci_mono sd se /\
    ci_mono se st /\ ci_mono st sb /\
    (!fn. fn_has_code sa sb fn ==>
       fn_has_code sa sc fn /\ fn_has_code sj sn fn /\
       fn_has_code sn ss fn /\ fn_has_code ss sd fn /\
       fn_has_code sd se fn /\ fn_has_code se st fn /\ fn_has_code st sb fn)
Proof
  simp[Once compile_bool_chain_ops_def, comp_ignore_bind_def] >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >>
  rename1 `(if d then _ else _) _ = (label_pair,_)` >>
  Cases_on `label_pair` >> gvs[] >> simp[comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `lower_value _ _ _ _ sa = (op,sc)` >>
  rename1 `emit_inst JNZ _ [] sj = (_,sn)` >>
  rename1 `new_block ls sn = (_,ss)` >>
  rename1 `emit_inst ASSIGN [_] [rv] ss = (_,sd)` >>
  rename1 `emit_inst JMP [Label xl] [] sd = (_,se)` >>
  rename1 `new_block ln se = (_,st)` >>
  drule_then strip_assume_tac bool_chain_test_labels_layout >>
  `ci_mono sa sc` by
    (qspecl_then [`cenv`, `BaseT BoolT`, `e`, `sa`] mp_tac
       ci_mono_lower_value_compile_expr >> simp[]) >>
  `ci_mono sc sj` by (simp[ci_mono_def] >> irule cs_extends_same_block >> simp[]) >>
  `ci_mono sj sn` by
    (qspecl_then [`JNZ`, `if d then [op; Label ln; Label ls]
                               else [op; Label ls; Label ln]`, `[]`, `sj`]
       mp_tac ci_mono_emit_inst >> simp[]) >>
  `ci_mono sn ss` by (qspecl_then [`ls`, `sn`] mp_tac ci_mono_new_block >> simp[]) >>
  `ci_mono ss sd` by
    (qspecl_then [`ASSIGN`, `[Lit (if d then 0w else 1w)]`, `[rv]`, `ss`]
       mp_tac ci_mono_emit_inst >> simp[]) >>
  `ci_mono sd se` by
    (qspecl_then [`JMP`, `[Label xl]`, `[]`, `sd`] mp_tac ci_mono_emit_inst >> simp[]) >>
  `ci_mono se st` by (qspecl_then [`ln`, `se`] mp_tac ci_mono_new_block >> simp[]) >>
  `ci_mono st sb` by
    (`ci_mono st (SND (compile_bool_chain_ops compile_expr cenv d rv xl (h::hs) st))`
      by simp[ci_mono_compile_bool_chain_ops, ci_mono_lower_value_compile_expr] >> gvs[]) >>
  `!fn. fn_has_code sa sb fn ==>
       fn_has_code sa sc fn /\ fn_has_code sj sn fn /\
       fn_has_code sn ss fn /\ fn_has_code ss sd fn /\
       fn_has_code sd se fn /\ fn_has_code se st fn /\ fn_has_code st sb fn` by
    (gen_tac >> strip_tac >> fs[ci_mono_def] >>
     map_every (fn (q,m) => q by (irule cs_extends_trans >> qexists m >> simp[]))
       [(`cs_extends se sb`,`st`), (`cs_extends sd sb`,`se`),
        (`cs_extends ss sb`,`sd`), (`cs_extends sn sb`,`ss`),
        (`cs_extends sj sb`,`sn`), (`cs_extends sc sb`,`sj`),
        (`cs_extends sa sj`,`sc`), (`cs_extends sa sn`,`sj`),
        (`cs_extends sa ss`,`sn`), (`cs_extends sa sd`,`ss`),
        (`cs_extends sa se`,`sd`), (`cs_extends sa st`,`se`)] >>
     rpt conj_tac >> irule fn_has_code_mid >> simp[] >>
     qexistsl_tac [`sb`, `sa`] >> simp[cs_extends_refl]) >>
  imp_res_tac new_block_props >>
  qexistsl_tac [`sn`, `ss`, `sd`, `se`, `st`] >>
  Cases_on `d` >> gvs[]
QED

Theorem bool_chain_test_layout:
  compile_bool_chain_ops compile_expr cenv d rv xl (e::h::hs) sa = ((),sb) ==>
  ?op sc sj sn ls ln ss sd se st.
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,sc) /\
    emit_inst JNZ [op; Label (if d then ln else ls); Label (if d then ls else ln)]
      [] sj = ((),sn) /\
    new_block ls sn = (sn.cs_current_bb,ss) /\
    emit_inst ASSIGN [Lit (if d then 0w else 1w)] [rv] ss = ((),sd) /\
    emit_inst JMP [Label xl] [] sd = ((),se) /\
    new_block ln se = (se.cs_current_bb,st) /\
    compile_bool_chain_ops compile_expr cenv d rv xl (h::hs) st = ((),sb) /\
    sj.cs_current_bb = sc.cs_current_bb /\
    sj.cs_current_insts = sc.cs_current_insts /\
    sj.cs_blocks = sc.cs_blocks /\
    sj.cs_next_id = sc.cs_next_id /\ sj.cs_next_var = sc.cs_next_var /\
    ss.cs_current_bb = ls /\ ss.cs_current_insts = [] /\
    st.cs_current_bb = ln /\ st.cs_current_insts = [] /\
    ci_mono sa sc /\ ci_mono sc sj /\ ci_mono sj sn /\
    ci_mono sn ss /\ ci_mono ss sd /\ ci_mono sd se /\
    ci_mono se st /\ ci_mono st sb /\
    (!fn. fn_has_code sa sb fn ==>
       fn_has_code sa sc fn /\ fn_has_code sj sn fn /\
       fn_has_code sn ss fn /\ fn_has_code ss sd fn /\
       fn_has_code sd se fn /\ fn_has_code se st fn /\ fn_has_code st sb fn)
Proof
  strip_tac >> drule_then strip_assume_tac bool_chain_test_layout_alloc >>
  rename1 `lower_value _ _ _ _ sa = (op,sc)` >>
  rename1 `emit_inst JNZ _ [] sj = (_,sn)` >>
  rename1 `new_block ls sn = (_,ss)` >>
  rename1 `emit_inst ASSIGN [_] [rv] ss = (_,sd)` >>
  rename1 `emit_inst JMP [Label xl] [] sd = (_,se)` >>
  rename1 `new_block ln se = (_,st)` >>
  qexistsl_tac [`op`, `sc`, `sj`, `sn`, `ls`, `ln`, `ss`, `sd`, `se`, `st`] >>
  simp[]
QED
