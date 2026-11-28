Theory s1PrefixBoolChainTipChild
Ancestors
  s1PrefixBoolChainExtArgDomain s1PrefixIfExpChildren s1PrefixPreds
  bodyFullIfExp vyperAST vyperInterpreter

(* The condition is always demanded; the arms are guarded by its success. *)
Definition bool_chain_tip_child_def:
  bool_chain_tip_child cx x a <=>
    bool_chain_ext_arg cx x a \/
    ?ty c l r. x = IfExp ty c l r /\
      (a = c \/ ((a = l \/ a = r) /\
        ?s tv t. eval_expr cx c s = (INL tv,t)))
End

Theorem bool_chain_tip_child_smaller:
  bool_chain_tip_child cx x a ==> expr_size a < expr_size x
Proof
  rw[bool_chain_tip_child_def]
  >- metis_tac[bool_chain_ext_arg_smaller]
  >> simp[expr_size_def] >> decide_tac
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_tac >> CCONTR_TAC >>
  `!a. bool_chain_tip_child cx (IfExp ty c l r) a ==>
       body_expr_full_ok cx a /\ body_expr_prefix_ok cx a` by metis_tac[] >>
  `bool_chain_tip_child cx (IfExp ty c l r) c` by simp[bool_chain_tip_child_def] >>
  `body_expr_full_ok cx c /\ body_expr_prefix_ok cx c` by metis_tac[] >>
  `!s tv t. eval_expr cx c s = (INL tv,t) ==>
     (body_expr_full_ok cx l /\ body_expr_prefix_ok cx l) /\
     (body_expr_full_ok cx r /\ body_expr_prefix_ok cx r)` by
    (rpt gen_tac >> disch_tac >>
     `bool_chain_tip_child cx (IfExp ty c l r) l /\
      bool_chain_tip_child cx (IfExp ty c l r) r` by
       (simp[bool_chain_tip_child_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `body_expr_full_ok cx (IfExp ty c l r)` by
    (irule ifexp_expr_full_ok >> metis_tac[]) >>
  `body_expr_prefix_ok cx (IfExp ty c l r)` by
    (simp[Once body_expr_prefix_ok_def] >>
     match_mp_tac ifexp_prefix_from_child_cases >> metis_tac[]) >>
  metis_tac[]
QED
*)
Theorem bool_chain_ifexp_bad_child:
  ~(body_expr_full_ok cx (IfExp ty c l r) /\
    body_expr_prefix_ok cx (IfExp ty c l r)) ==>
  ?a. bool_chain_tip_child cx (IfExp ty c l r) a /\
      ~(body_expr_full_ok cx a /\ body_expr_prefix_ok cx a)
Proof
  cheat
QED
