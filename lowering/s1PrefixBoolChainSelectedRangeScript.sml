(* Native Range-loop case for a selected internal-call body. *)
Theory s1PrefixBoolChainSelectedRange
Ancestors
  s1PrefixPreds s1PrefixForRange bodyFullForFrame bodyFullForHandlers

val _ = Parse.hide "body";

Theorem bool_chain_selected_range_stmt_prefix:
  !cx id typ e1 e2 n body.
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx (Range e1 e2) s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx (Range e1 e2) s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_prefix_ok cx tyv id body vs) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx (Range e1 e2)) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_prefix_ok cx (Range e1 e2)) ==>
  body_stmt_prefix_ok cx (For id typ (Range e1 e2) n body)
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[body_stmt_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  irule compile_for_range_frag_prefix >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  FIRST [rpt gen_tac >> MATCH_ACCEPT_TAC for_full_frame_compose,
         rpt gen_tac >> MATCH_ACCEPT_TAC for_full_frame_pop,
         ACCEPT_TAC for_body_cleanup_full,
         simp[] >> MATCH_ACCEPT_TAC (SRULE [] for_full_exit_scopes_gas_obs),
         qexistsl [`bindings`,`env`,`env'`,`tops`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC]
QED
