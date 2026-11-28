(* Smaller-rank prefix induction hypotheses for the body and defaults of a callee. *)
Theory s1PrefixIntCallRank
Ancestors
  bodyCallLiveness s1PrefixPreds s1PrefixStmtZero bodySimFullMain constSubst gasContext
  vyperContext vyperInterpreter vyperAST alist list
  vyperTypeContract[qualified,ignore_grammar]

Theorem intcall_callee_prefix_ih:
  LENGTH (remcode cx) <= rank /\
  (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
          IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
          struct_args_unique tops /\
          (!vis mut nr raw f a ds rt ss.
             MEM (FunctionDecl vis mut nr raw f a ds rt ss) tops ==>
             stmts_loop_calls_ok [(NONE,tops)]
               (subst_consts_stmts (module_consts_env tops []) ss))) /\
  (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
     MEM (src,fn) (vyperTypeContract$linked_live_functions [(NONE,tops)] [])) /\
  (!m. m < rank ==> !c ys. LENGTH (remcode c) <= m /\
       (!tops. ALOOKUP c.sources c.txn.target = SOME [(NONE,tops)] ==>
               IS_SOME (vyperTypeContract$check_contract F c.layouts c.txn.target [(NONE,tops)]) /\
               struct_args_unique tops /\
               (!vis mut nr raw f a ds rt ss.
                  MEM (FunctionDecl vis mut nr raw f a ds rt ss) tops ==>
                  stmts_loop_calls_ok [(NONE,tops)]
                    (subst_consts_stmts (module_consts_env tops []) ss)) /\
               EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                 (vyperTypeCallGraph$int_calls_stmts ys) /\
               stmts_loop_calls_ok [(NONE,tops)] ys) ==>
       body_stmts_prefix_ok c ys) /\
  (!m. m < rank ==> !c xs. LENGTH (remcode c) <= m /\
       (!tops. ALOOKUP c.sources c.txn.target = SOME [(NONE,tops)] ==>
               IS_SOME (vyperTypeContract$check_contract F c.layouts c.txn.target [(NONE,tops)]) /\
               struct_args_unique tops /\
               (!vis mut nr raw f a ds rt ss.
                  MEM (FunctionDecl vis mut nr raw f a ds rt ss) tops ==>
                  stmts_loop_calls_ok [(NONE,tops)]
                    (subst_consts_stmts (module_consts_env tops []) ss)) /\
               EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                 (vyperTypeCallGraph$int_calls_exprs xs)) ==>
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
  qabbrev_tac `pushed = cx with stk updated_by CONS (src,fn)` >>
  `!tops. ALOOKUP pushed.sources pushed.txn.target = SOME [(NONE,tops)] ==>
    IS_SOME (vyperTypeContract$check_contract F pushed.layouts pushed.txn.target [(NONE,tops)]) /\
    struct_args_unique tops /\
    (!vis mut nr raw f a ds rt body.
       MEM (FunctionDecl vis mut nr raw f a ds rt body) tops ==>
       stmts_loop_calls_ok [(NONE,tops)]
         (subst_consts_stmts (module_consts_env tops []) body)) /\
    EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
      (vyperTypeCallGraph$int_calls_stmts (subst_consts_stmts (module_consts_env (cx_tops cx) []) ss)) /\
    stmts_loop_calls_ok [(NONE,tops)] (subst_consts_stmts (module_consts_env (cx_tops cx) []) ss) /\
    (!n. EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
      (vyperTypeCallGraph$int_calls_exprs
        (DROP n (subst_consts_exprs (module_consts_env (cx_tops cx) []) dflts))))` by
    (simp[Abbr `pushed`] >> rpt strip_tac >>
     qpat_assum `!tops. ALOOKUP cx.sources _ = SOME _ ==> IS_SOME _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!tops. ALOOKUP cx.sources _ = SOME _ ==> MEM _ _`
       (drule_then assume_tac) >>
     TRY (res_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
     `cx_tops cx = tops` by fs[cx_tops_def, get_module_code_def, ALOOKUP_def] >>
     asm_rewrite_tac[] >>
     TRY (drule_all_then ACCEPT_TAC callable_body_loop_calls_ok >> NO_TAC) >>
     Cases_on `src` >> gvs[get_module_code_def, ALOOKUP_def, optionTheory.IS_SOME_EXISTS] >>
     drule_all_then strip_assume_tac callable_compiled_calls_live >>
     TRY (res_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
     qpat_assum `!n. EVERY _ (vyperTypeCallGraph$int_calls_exprs (DROP n _))`
       (qspec_then `n` ACCEPT_TAC)) >>
  conj_tac
  >- (qpat_assum `!m. m < rank ==> !c ys. _ ==> body_stmts_prefix_ok c ys`
        (drule_then irule) >> simp[] >> gen_tac >> disch_tac >>
      qpat_assum `!tops. ALOOKUP pushed.sources _ = SOME _ ==> _`
        (drule_then strip_assume_tac) >> simp[] >> first_assum ACCEPT_TAC) >>
  qpat_assum `!m. m < rank ==> !c xs. _ ==> body_exprs_prefix_ok c xs`
    (drule_then irule) >> simp[] >> gen_tac >> disch_tac >>
      qpat_assum `!tops. ALOOKUP pushed.sources _ = SOME _ ==> _`
        (drule_then strip_assume_tac) >> simp[] >> first_assum ACCEPT_TAC
QED
