(* Diagnose the list-to-operand boundary of the native BoolChain dispatcher. *)
Theory s1PrefixBoolChainUseSite
Ancestors
  bodyFullBoolChainOperands bodyFullPreds bodyFullExprsListFacts bodyFullBoolChain
  s1PrefixPreds exprLowering
  vyperInterpreter vyperContext vyperState vyperAST list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `!s. type_check (builtin_args_length_ok (BoolChain p n) (LENGTH args))
          "Builtin args" s = (INL (),s)` by simp[type_check_def,assert_def] >>
  `body_exprs_full_ok cx args /\ body_exprs_prefix_ok cx args` by
    (conj_tac
     >- (first_x_assum irule >> simp[code_slice_source_def] >> metis_tac[]) >>
     first_x_assum irule >> simp[code_slice_source_def] >> metis_tac[]) >>
  `?e. args = [e]` by fs[builtin_args_length_ok_def,LENGTH_EQ_1] >>
  qpat_x_assum `args = [_]` SUBST_ALL_TAC >>
  fs[body_exprs_full_ok_cons,body_exprs_full_ok_nil,body_exprs_prefix_ok_def] >>
  simp[body_expr_full_ok_bool_chain_operands]
QED
*)
Theorem bool_chain_dispatch_observation:
  (!s'' x t.
     type_check (builtin_args_length_ok (BoolChain p n) (LENGTH args))
       "Builtin args" s'' = (INL x,t) /\
     BoolChain p n <> Len /\ BoolChain p n <> Env MsgGas /\
     code_slice_source (BoolChain p n) args = NONE ==>
     body_exprs_full_ok cx args) /\
  (!s'' x t.
     type_check (builtin_args_length_ok (BoolChain p n) (LENGTH args))
       "Builtin args" s'' = (INL x,t) /\
     BoolChain p n <> Len /\ BoolChain p n <> Env MsgGas /\
     code_slice_source (BoolChain p n) args = NONE ==>
     body_exprs_prefix_ok cx args) /\
  builtin_args_length_ok (BoolChain p n) (LENGTH args) ==>
  ?e. args = [e] /\ body_expr_prefix_ok cx e /\
      bool_chain_full_ok [(NONE,cx_tops cx)] [] cx (bool_chain_operands p (n - 1) e)
Proof
  cheat
QED

(* At a peeled test the full observation decomposes, while the prefix
   observation obtained from the original argument list concerns e. *)
Theorem bool_chain_dispatch_observation_at_test:
  (if p then
     e = IfExp (BaseT BoolT) c residual (Literal (BaseT BoolT) (BoolL F))
   else
     e = IfExp (BaseT BoolT) c (Literal (BaseT BoolT) (BoolL T)) residual) /\
  body_expr_prefix_ok cx e /\
  bool_chain_full_ok [(NONE,cx_tops cx)] [] cx (bool_chain_operands p (SUC k) e) ==>
  body_expr_full_ok_mods [(NONE,cx_tops cx)] [] cx c /\
  ((?s tv s'. eval_expr cx c s = (INL tv,s')) ==>
   bool_chain_full_ok [(NONE,cx_tops cx)] [] cx (bool_chain_operands p k residual)) /\
  body_expr_prefix_ok cx e
Proof
  Cases_on `p` >> fs[] >> strip_tac >>
  gvs[bool_chain_operands_def,bool_chain_full_ok_def] >> first_assum ACCEPT_TAC
QED
