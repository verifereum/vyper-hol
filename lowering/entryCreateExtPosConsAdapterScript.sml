(* Canonical positional cons rule and its explicit scope adapter. *)
Theory entryCreateExtPosConsAdapter
Ancestors
  entryCreateExtPosConsScope

Definition extcall_pos_cons_rule_def:
  extcall_pos_cons_rule DF lo E C f PG tops cx st0 <=>
    !a m b e xs es s G tn P Q.
      (!marks. create_operand_focus_scope a m E C f s marks ==>
               create_operand_focus_scope a b E C f s marks) /\
      (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
                 create_operand_full_scope a b E C f s marks r) /\
      (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
          create_operand_focus_scope m b E C f t right ==>
          create_operand_focus_scope a b E C f s (left ++ right)) /\
      (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
          create_operand_full_scope m b E C f t right r ==>
          create_operand_full_scope a b E C f s (left ++ right) r) /\
      scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
        (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) P (create_operand_exit_post C cx) /\
      (!H r ee G1 tn1 t. P H r ee G1 tn1 t ==> ?v. r = INL v) /\
      (!obs marks v mid G1 tn1 t.
        bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
          (INL v,mid with gas_obs := []) /\
        (?H. valid_horizon cx st0 H mid.storage_trace) /\
        (!H. valid_horizon cx st0 H mid.storage_trace ==>
          P H (INL v) (mid with gas_obs := []) G1 tn1 t /\
          gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) marks (OK t,G1,tn1)) ==>
        scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
          (bind (eval_exprs cx xs) (\vs. return (v::vs))) (mid with gas_obs := [],t,G1,tn1) Q
          (create_operand_exit_post C cx)) ==>
      scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
        (eval_exprs cx (e::xs)) (es,s,G,tn) Q (create_operand_exit_post C cx)
End

Theorem extcall_pos_cons_rule_from_pos_cons_scope_mixed:
  extcall_pos_cons_rule DF lo E C f PG tops cx st0
Proof
  pure_rewrite_tac[extcall_pos_cons_rule_def] >>
  ACCEPT_TAC (Q.GENL [`a`, `m`, `b`, `e`, `xs`, `es`, `s`, `G`, `tn`, `P`, `Q`]
    pos_cons_scope_mixed)
QED
