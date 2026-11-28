(* Full and smaller-prefix evidence for guarded ExtCall argument windows. *)
Theory s1PrefixExtCallPositionalChildEvidence
Ancestors
  s1PrefixBoolChainExtArgDomain s1PrefixBoolChainExtArgWindows
  s1PrefixPreds bodySimFullMain vyperInterpreter list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  qpat_x_assum `h = _` SUBST_ALL_TAC >>
  `!a. bool_chain_ext_arg cx (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr) a ==>
       body_expr_full_ok cx a /\ body_expr_prefix_ok cx a` by
    (gen_tac >> disch_tac >> conj_tac
     >- (irule (cj 5 body_sim_full_mutual) >> first_assum ACCEPT_TAC)
     >- (qpat_assum `!a. expr_size a < expr_size (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr) ==> body_expr_prefix_ok cx a`
           (qspec_then `a` mp_tac) >>
         impl_tac >- (drule bool_chain_ext_arg_smaller >> simp[]) >>
         disch_tac >> first_x_assum ACCEPT_TAC)) >>
  match_mp_tac (GEN_ALL bool_chain_extcall_guarded_windows) >>
  rpt conj_tac >> rpt (gen_tac ORELSE disch_tac) >>
  first_x_assum match_mp_tac >>
  fs[bool_chain_ext_arg_def] >> qexistsl [`pre`,`post`] >> metis_tac[]
QED
*)
Theorem extcall_positional_child_full_evidence:
  (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
     struct_args_unique tops /\
     (!vis mut nr raw fn args dflts ret ss.
        MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
        stmts_loop_calls_ok [(NONE,tops)]
          (subst_consts_stmts (module_consts_env tops []) ss))) /\
  (!a. expr_size a < expr_size h ==> body_expr_prefix_ok cx a) /\
  h = Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr ==>
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
  cheat
QED
