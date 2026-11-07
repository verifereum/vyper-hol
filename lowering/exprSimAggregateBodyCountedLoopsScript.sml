Theory exprSimAggregateBodyCountedLoops
Ancestors
  exprSimAggregateBodyCountedChildren exprSimAggregateLoops exprLowering
  compileEnv exprLoweringProps emitHelper list
Libs
  monadsyntax

Theorem aggregate_tuple_body_cons_compile:
  compile_make_tuple compile_expr ce (e::args) buf off sa = (out,sb) ==>
  ?vv sm dst sn op su st.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    unwrap_value ce vv sn = (op,su) /\
    compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e)
      su = ((),st) /\
    compile_make_tuple compile_expr ce args buf
      (off + type_memory_bytes ce (expr_type e)) st = (out,sb)
Proof
  simp[Once compile_make_tuple_def, comp_bind_def] >>
  rpt (pairarg_tac >> fs[]) >> rpt strip_tac >> gvs[] >>
  gvs[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> Cases_on `v'` >> metis_tac[]
QED

