(* Smaller-rank prefix induction hypotheses for the body and defaults of a callee. *)
Theory s1PrefixIntCallRank
Ancestors
  s1PrefixPreds s1PrefixStmtZero bodySimFullMain constSubst gasContext
  vyperContext vyperInterpreter vyperAST alist list
  vyperTypeContract[qualified,ignore_grammar]

Theorem intcall_callee_prefix_ih:
  LENGTH (remcode cx) <= rank /\
  (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
          struct_args_unique tops /\
          (!vis mut nr raw f a ds rt ss.
             MEM (FunctionDecl vis mut nr raw f a ds rt ss) tops ==>
             stmts_loop_calls_ok [(NONE,tops)]
               (subst_consts_stmts (module_consts_env tops []) ss))) /\
  (!m. m < rank ==> !c ys. LENGTH (remcode c) <= m /\
       (!tops. ALOOKUP c.sources c.txn.target = SOME [(NONE,tops)] ==>
               struct_args_unique tops /\
               (!vis mut nr raw f a ds rt ss.
                  MEM (FunctionDecl vis mut nr raw f a ds rt ss) tops ==>
                  stmts_loop_calls_ok [(NONE,tops)]
                    (subst_consts_stmts (module_consts_env tops []) ss)) /\
               stmts_loop_calls_ok [(NONE,tops)] ys) ==>
       body_stmts_prefix_ok c ys) /\
  (!m. m < rank ==> !c xs. LENGTH (remcode c) <= m /\
       (!tops. ALOOKUP c.sources c.txn.target = SOME [(NONE,tops)] ==>
               struct_args_unique tops /\
               (!vis mut nr raw f a ds rt ss.
                  MEM (FunctionDecl vis mut nr raw f a ds rt ss) tops ==>
                  stmts_loop_calls_ok [(NONE,tops)]
                    (subst_consts_stmts (module_consts_env tops []) ss))) ==>
       body_exprs_prefix_ok c xs)
  ==>
  !ts mut nr args dflts ret ss.
    ~MEM (src,fn) cx.stk /\ get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
    body_stmts_prefix_ok (cx with stk updated_by CONS (src,fn))
      (subst_consts_stmts (module_consts_env (cx_tops cx) []) ss) /\
    body_exprs_prefix_ok (cx with stk updated_by CONS (src,fn))
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
        (subst_consts_exprs (module_consts_env (cx_tops cx) []) dflts))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `(dflts,ss) = ([],[])`
  >- gvs[subst_consts_stmt_def, subst_consts_expr_def, body_exprs_prefix_ok_def,
         body_stmts_prefix_ok_def, stmt_frag_nil_prefix] >>
  `LENGTH (remcode (cx with stk updated_by CONS (src,fn))) < rank` by
    (drule_all callable_remcode_decreases >> decide_tac) >>
  conj_tac
  >- (qpat_assum `!m. m < rank ==> !c ys. _ ==> body_stmts_prefix_ok c ys`
        (drule_then irule) >> simp[] >> gen_tac >> strip_tac >>
      qpat_assum `!tops. ALOOKUP cx.sources _ = SOME _ ==> _`
        (qspec_then `tops` mp_tac) >> simp[] >> strip_tac >>
      `cx_tops cx = tops` by fs[cx_tops_def, get_module_code_def, ALOOKUP_def] >>
      asm_rewrite_tac[] >> irule callable_body_loop_calls_ok >> metis_tac[]) >>
  qpat_assum `!m. m < rank ==> !c xs. _ ==> body_exprs_prefix_ok c xs`
    (drule_then irule) >> simp[] >> gen_tac >> strip_tac >>
  qpat_assum `!tops. ALOOKUP cx.sources _ = SOME _ ==> _`
    (qspec_then `tops` mp_tac) >> simp[]
QED
