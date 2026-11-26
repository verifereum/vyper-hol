(* Full and prefix child contracts for the guarded ExtCall argument windows. *)
Theory s1PrefixBoolChainExtArgWindows
Ancestors
  s1PrefixPreds bodyFullPreds bodyFullExprsListFacts vyperInterpreter list

Theorem bool_chain_guarded_expr_list_ok[local]:
  (!pre a post.
    xs = pre ++ a::post /\
    EVERY (\b. ?s tv t s1 v t1. eval_expr cx b s = (INL tv,t) /\
                               read_result cx tv s1 = (INL v,t1)) pre ==>
    body_expr_full_ok cx a /\ body_expr_prefix_ok cx a) ==>
  body_exprs_full_ok cx xs /\ body_exprs_prefix_ok cx xs
Proof
  Induct_on `xs`
  >- simp[body_exprs_full_ok_nil, body_exprs_prefix_ok_def] >>
  qx_gen_tac `h` >>
  disch_tac >>
  qpat_assum `!pre a post. _` (qspecl_then [`[]`, `h`, `xs`] mp_tac) >>
  simp[] >> strip_tac >>
  `(?s tv t s1 v t1. eval_expr cx h s = (INL tv,t) /\
                   read_result cx tv s1 = (INL v,t1)) ==>
   body_exprs_full_ok cx xs /\ body_exprs_prefix_ok cx xs` by
    (disch_tac >> first_x_assum irule >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!pre a post. _`
       (qspecl_then [`h::pre`, `a`, `post`] mp_tac) >>
     simp[]) >>
  simp[body_exprs_full_ok_cons, body_exprs_prefix_ok_def] >>
  metis_tac[]
QED

Theorem bool_chain_extcall_guarded_windows:
  (!pre a post.
    TAKE 1 args = pre ++ a::post /\
    EVERY (\b. ?s tv t s1 v t1. eval_expr cx b s = (INL tv,t) /\
                               read_result cx tv s1 = (INL v,t1)) pre ==>
    body_expr_full_ok cx a /\ body_expr_prefix_ok cx a) /\
  (!st target mid. eval_exprs cx (TAKE 1 args) st = (INL target,mid) ==>
    !pre a post.
      TAKE (LENGTH ats) (DROP 1 args) = pre ++ a::post /\
      EVERY (\b. ?s tv t s1 v t1. eval_expr cx b s = (INL tv,t) /\
                                 read_result cx tv s1 = (INL v,t1)) pre ==>
      body_expr_full_ok cx a /\ body_expr_prefix_ok cx a) /\
  (!st target mid src vs fin.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    eval_exprs cx (TAKE (LENGTH ats) (DROP 1 args)) src = (INL vs,fin) ==>
    !pre a post.
      DROP (1 + LENGTH ats) args = pre ++ a::post /\
      EVERY (\b. ?s tv t s1 v t1. eval_expr cx b s = (INL tv,t) /\
                                 read_result cx tv s1 = (INL v,t1)) pre ==>
      body_expr_full_ok cx a /\ body_expr_prefix_ok cx a) ==>
  (body_exprs_full_ok cx (TAKE 1 args) /\
   body_exprs_prefix_ok cx (TAKE 1 args)) /\
  (!st target mid. eval_exprs cx (TAKE 1 args) st = (INL target,mid) ==>
    body_exprs_full_ok cx (TAKE (LENGTH ats) (DROP 1 args)) /\
    body_exprs_prefix_ok cx (TAKE (LENGTH ats) (DROP 1 args))) /\
  (!st target mid src vs fin.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    eval_exprs cx (TAKE (LENGTH ats) (DROP 1 args)) src = (INL vs,fin) ==>
    body_exprs_full_ok cx (DROP (1 + LENGTH ats) args) /\
    body_exprs_prefix_ok cx (DROP (1 + LENGTH ats) args))
Proof
  strip_tac >> conj_tac
  >- (match_mp_tac (GEN_ALL bool_chain_guarded_expr_list_ok) >> first_assum ACCEPT_TAC) >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  match_mp_tac (GEN_ALL bool_chain_guarded_expr_list_ok) >> metis_tac[]
QED
