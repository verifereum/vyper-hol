(* Discharge the statement cases in the guarded rank induction. *)
Theory s1PrefixBoolChainGuardedRankInduction
Ancestors
  s1PrefixBoolChainGuardedRankCore s1PrefixBoolChainSelectedStmtCasePorts

Theorem bool_chain_guarded_rank_induction:
  (!cx h. ~(?ann nid args dr. h = Call ann (IntCall nid) args dr) /\
     (!a. expr_size a < expr_size h ==> body_expr_prefix_ok cx a) ==>
     body_expr_prefix_ok cx h) ==>
  (!rank cx ann src name es dr.
     LENGTH (remcode cx) <= rank /\
     (!a. expr_size a < expr_size (Call ann (IntCall (src,name)) es dr) ==>
        body_expr_prefix_ok cx a) /\
     (!c a. LENGTH (remcode c) < rank ==> body_expr_prefix_ok c a) /\
     (!c ys. LENGTH (remcode c) < rank /\
        (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
           stmts_loop_calls_ok [(NONE,ts)] ys) ==>
        body_stmts_prefix_ok c ys) ==>
     body_expr_prefix_ok cx (Call ann (IntCall (src,name)) es dr)) ==>
  !rank:num.
    (!cx h. LENGTH (remcode cx) <= rank ==> body_expr_prefix_ok cx h) /\
    (!cx ss. LENGTH (remcode cx) <= rank /\
       (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
          stmts_loop_calls_ok [(NONE,tops)] ss) ==>
       body_stmts_prefix_ok cx ss)
Proof
  mp_tac bool_chain_guarded_rank_core >>
  rewrite_tac[bool_chain_selected_stmt_case_ports]
QED
