Theory s1PrefixBoolChainExtArgDomain
Ancestors
  exprCallBounds vyperInterpreter vyperAST list rich_list

(* A demanded argument need not itself succeed. Successes of the earlier
   windows and of preceding elements within this window are independent. *)
Definition bool_chain_ext_arg_def:
  bool_chain_ext_arg cx h a <=>
    ?ann stat skip fname ats rt opts args dr ys pre post.
      h = Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr /\
      ys = pre ++ a::post /\
      EVERY (\b. ?s tv t s1 v t1.
        eval_expr cx b s = (INL tv,t) /\
        read_result cx tv s1 = (INL v,t1)) pre /\
      (ys = TAKE 1 args \/
       (ys = TAKE (LENGTH ats) (DROP 1 args) /\
        (?st vs mid. eval_exprs cx (TAKE 1 args) st = (INL vs,mid))) \/
       (ys = DROP (1 + LENGTH ats) args /\
        (?st vs mid. eval_exprs cx (TAKE 1 args) st = (INL vs,mid)) /\
        (?src vs ee.
          eval_exprs cx (TAKE (LENGTH ats) (DROP 1 args)) src = (INL vs,ee))))
End

Theorem bool_chain_ext_arg_smaller:
  bool_chain_ext_arg cx h a ==> expr_size a < expr_size h
Proof
  rw[bool_chain_ext_arg_def] >> irule expr_call_arg_bound >>
  metis_tac[MEM_APPEND, MEM, MEM_TAKE, MEM_DROP_IMP]
QED
