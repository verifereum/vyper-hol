(* Obligation: cmp_flip preserves block execution up to dead variables. *)
Theory aoCmpFlipObligation
Ancestors
  algebraicOptDefs stateEquiv execEquivProps venomExecSemantics

Theorem ao_cmp_flip_block_sim:
  !mid dfg fn1 lbl bb1 bb' fuel ctx s1 s2.
    let dead = ao_cmp_flip_dead_vars dfg fn1 in
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    lookup_block lbl (ao_cmp_flip_function mid dfg fn1).fn_blocks = SOME bb' /\
    state_equiv dead s1 s2 /\ s1.vs_inst_idx = 0 ==>
    lift_result (state_equiv dead) (execution_equiv dead)
      (execution_equiv dead)
      (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb' s2)
Proof
  cheat
QED
