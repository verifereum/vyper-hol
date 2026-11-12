(* Actual counted paths for unary operator prefixes. *)
Theory exprUnopSimDefs
Ancestors
  exprSimDefs compileEnv gasSummary venomExecSemantics
  vyperInterpreter valueEncoding

Definition unop_frag_def:
  unop_frag ctx func cenv cx f w1 t res es0 <=>
    !sa sb x op s0.
      f x sa = (op, sb) /\ expr_res_ok res /\
      (!z. x = Var z ==> not_fresh_at sa z) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      stmt_state_rel ctx func cenv cx es0 s0 /\
      eval_operand x s0 = SOME w1 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?r. gas_marked_path F ctx func s0 0 r /\
        ((?s v. r = OK s /\ res = INL v /\
                 stmt_state_rel ctx func cenv cx es0 s /\
                 expr_val_rel cx t v op s /\
                 (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                        lookup_var z s = SOME w) /\
                 (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                          FLOOKUP s.vs_allocas aid = SOME b) /\
                 s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
                 s.vs_current_bb = sb.cs_current_bb /\
                 s.vs_inst_idx = LENGTH sb.cs_current_insts) \/
         (exit_result r /\ expr_exit res r))
End
