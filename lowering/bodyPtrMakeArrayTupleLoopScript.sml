(* Compilation boundary for the counted literal loop.  Keep the source
   type of each store: the operational cons handles capacity widening. *)
Theory bodyPtrMakeArrayTupleLoop
Ancestors
  bodyPtrMakeArrayConsOutcome exprLowering exprLoweringProps emitHelperProps
  compileEnv context

Theorem literal_tuple_cons_compile:
  compile_make_tuple compile_expr ce (e::args) (Var root) off sa = (out,sb) ==>
  ?vv sm dst sn op su ss.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
    unwrap_value ce vv sn = (op,su) /\
    compile_store_memory ce op (Var dst) (expr_type e) (lowered_value_type ce e) su = ((),ss) /\
    compile_make_tuple compile_expr ce args (Var root)
      (off+type_memory_bytes ce (expr_type e)) ss = (out,sb)
Proof
  simp[Once compile_make_tuple_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> gvs[] >>
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  metis_tac[]
QED
