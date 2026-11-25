(* Rank descent or request-free callee actions after a successful lookup. *)
Theory s1PrefixBoolChainCallRankBase
Ancestors
  bodySimFullMain s1PrefixFrame constSubst gasContext vyperContext
  vyperInterpreter vyperState vyperStorageTrace
  bodyLoopCalls bodyFullPreds typedCopyProducer vyperTypeContract alist list

Theorem bool_chain_lookup_rank_or_empty_prefixes:
  ~MEM (src,fn) cx.stk /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
  LENGTH (remcode (cx with stk updated_by CONS (src,fn))) < LENGTH (remcode cx) \/
  (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
     (subst_consts_exprs (module_consts_env (cx_tops cx) []) dflts) = [] /\
   subst_consts_stmts (module_consts_env (cx_tops cx) []) ss = [] /\
   (!DF lo explicit ctx f PG st0 ee z J tm. ~z.vs_halted ==>
      gas_prefix_full (DF,lo,explicit,ctx,f,PG)
        (cx with stk updated_by CONS (src,fn)) st0
        (eval_exprs (cx with stk updated_by CONS (src,fn))
          (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
            (subst_consts_exprs (module_consts_env (cx_tops cx) []) dflts)))
        (ee,z,J,tm)) /\
   (!DF lo explicit ctx f PG st0 ee z J tm. ~z.vs_halted ==>
      gas_prefix_full (DF,lo,explicit,ctx,f,PG)
        (cx with stk updated_by CONS (src,fn)) st0
        (eval_stmts (cx with stk updated_by CONS (src,fn))
          (subst_consts_stmts (module_consts_env (cx_tops cx) []) ss))
        (ee,z,J,tm)))
Proof
  strip_tac >> Cases_on `(dflts,ss) = ([],[])`
  >- (disj2_tac >> gvs[subst_consts_expr_def, subst_consts_stmt_def] >>
      conj_tac >> rpt strip_tac >> irule gas_prefix_full_no_outcome >>
      simp[evaluate_storage_trace_frame, Once evaluate_def, return_def]) >>
  disj1_tac >> drule_all callable_remcode_decreases >> simp[]
QED

Theorem selected_port_checker_guards:
  body_const_cells_agree [(NONE,tops)] cx env es ==>
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  struct_args_unique tops /\
  (!vis mut nr raw fn args ds ret ss.
     MEM (FunctionDecl vis mut nr raw fn args ds ret ss) tops ==>
     stmts_loop_calls_ok [(NONE,tops)]
       (subst_consts_stmts (module_consts_env tops []) ss))
Proof
  simp[body_const_cells_agree_def] >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (drule checked_contract_struct_args_unique >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule checked_subst_consts_loop_calls_ok >>
  disch_then irule >>
  drule checked_module_loop_calls_ok >> strip_tac >>
  gvs[alistTheory.ALOOKUP_def] >> metis_tac[]
QED
