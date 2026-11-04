(* Concrete operator prefixes, after both operands have been evaluated. *)
Theory exprBopSimDefs
Ancestors
  exprSimDefs compileEnv exprBopLowering gasSummary venomExecSemantics
  vyperInterpreter valueEncoding pair

Definition bop_result_def:
  bop_result cx ann bop tys v1 v2 (es:evaluation_state) =
    case evaluate_builtin cx es.accounts ann (Bop bop) tys [v1; v2] of
      INL v => INL v
    | INR e => INR (Error e)
End

Definition binop_frag_words_def:
  binop_frag_words ctx func cenv cx bop ty ann bl el tys v1 v2 w1 w2 es0 <=>
    !sa sb x y op s0.
      compile_binop bop x y ty bl el sa = (op, sb) /\
      expr_res_ok (bop_result cx ann bop tys v1 v2 es0) /\
      (!z. x = Var z ==> not_fresh_at sa z) /\
      (!z. y = Var z ==> not_fresh_at sa z) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      stmt_state_rel ctx func cenv cx es0 s0 /\
      eval_operand x s0 = SOME w1 /\ eval_operand y s0 = SOME w2 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?r. gas_marked_path F ctx func s0 0 r /\
        ((?s v. r = OK s /\
                 bop_result cx ann bop tys v1 v2 es0 = INL v /\
                 word_value v /\
                 stmt_state_rel ctx func cenv cx es0 s /\
                 eval_operand op s = SOME (val_to_w256 v) /\
                 (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                        lookup_var z s = SOME w) /\
                 (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                          FLOOKUP s.vs_allocas aid = SOME b) /\
                 s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
                 s.vs_current_bb = sb.cs_current_bb /\
                 s.vs_inst_idx = LENGTH sb.cs_current_insts) \/
         (exit_result r /\ expr_exit (bop_result cx ann bop tys v1 v2 es0) r))
End

Definition binop_frag_def:
  binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0 <=>
    binop_frag_words ctx func cenv cx bop ty ann bl el tys v1 v2
      (val_to_w256 v1) (val_to_w256 v2) es0
End
