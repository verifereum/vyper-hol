Theory exprListSplitProps
Ancestors
  vyperInterpreter vyperState list
  exprSimWordArgs[qualified,ignore_grammar]

Theorem expr_list_ok_append_split:
  !P Q.
    (!cx. P cx []) /\
    (!cx e es.
      P cx (e::es) <=>
        Q cx e /\
        ((?st tv mid st' v en.
            eval_expr cx e st = (INL tv,mid) /\
            read_result cx tv st' = (INL v,en)) ==>
          P cx es)) ==>
    !xs ys cx. P cx (xs ++ ys) ==>
      P cx xs /\
      (!st vs en. eval_exprs cx xs st = (INL vs,en) ==> P cx ys)
Proof
  rpt gen_tac >> strip_tac >>
  Induct >- simp[exprSimWordArgsTheory.eval_exprs_nil] >>
  rpt gen_tac >> rewrite_tac[APPEND] >>
  qpat_x_assum `!cx e es. P cx (e::es) <=> _`
    (fn cons_ok => once_rewrite_tac[cons_ok]) >>
  strip_tac >> conj_tac
  >- (simp[] >> metis_tac[]) >>
  rpt gen_tac >>
  simp[Once exprSimWordArgsTheory.eval_exprs_cons_action, bind_def,
       return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> metis_tac[]
QED
