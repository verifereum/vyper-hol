Theory bodyPtrIfExpReannotation
Ancestors
  exprLowering exprCallbackContracts

(* Internal calls select their result representation from the callee's declared
   return type. Neither use-site annotation nor external-call default is read. *)
Theorem ifexp_compile_intcall_annotation:
  !cfn ce rt rt' a b id args drv drv' st.
    compile_call cfn ce rt a (IntCall id) args drv st =
    compile_call cfn ce rt' b (IntCall id) args drv' st
Proof
  simp[compile_call_def]
QED

Theorem ifexp_compile_expr_intcall_annotation:
  !ce rt rt' a b id args drv drv' st.
    compile_expr ce rt (Call a (IntCall id) args drv) st =
    compile_expr ce rt' (Call b (IntCall id) args drv') st
Proof
  rpt gen_tac >>
  pure_once_rewrite_tac[compile_expr_component_eq] >>
  simp_tac (srw_ss()) [LET_THM, Excl "expr_size_def"] >>
  pure_rewrite_tac[compile_call_child_calls] >>
  metis_tac[ifexp_compile_intcall_annotation]
QED
