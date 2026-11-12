Theory bodyPtrIntCallResultsBoundary
Ancestors bodyPtrPreds vyperInterpreter vyperState exprLowering
  context compileEnv fragGasPathPtr bodyPtrIntCallEntryContracts
  bodyPtrIntCallConfinement stmtFragPtr exprSimWordArgs gasCount
  bodyPtrDefs gasSummary venomState

Theorem intcall_successful_results_ptr_children:
  !es cx s raws t.
    body_results_ptr_ok cx es /\
    eval_expr_results cx es s = (INL raws,t) ==>
    EVERY (body_expr_ptr_ok cx) es
Proof
  Induct_on `es` >> simp[body_results_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  metis_tac[]
QED

(* Both empty argument phases leave the compiler and the counted runtime
   state untouched.  This is also the base case when flags/types are empty. *)
Theorem intcall_empty_argument_phases:
  ~s.vs_halted ==>
  compile_multi_vvs compile_expr ce [] sa = ([],sa) /\
  compile_stage_intcall_args ce [] flags tys sa = ([],sa) /\
  eval_expr_results cx [] es = (INL [],es) /\
  gas_path_ptr D lo ctx fn PG G tn s 0 G tn (OK s)
Proof
  simp[compile_multi_vvs_def, compile_stage_intcall_args_def,
       comp_return_def, Once evaluate_def, return_def] >>
  strip_tac >> irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem intcall_empty_results_ptr_outcome:
  stmt_state_rel ctx fn ce cx es s /\ ghost_inv d ce cx es G tn s /\
  ~s.vs_halted ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (eval_expr_results cx []) (es,s,G,tn)
    (\res ee H un t.
      res = INL [] /\ ee = es with gas_obs := [] /\
      H = G /\ un = tn /\ t = s /\
      stmt_state_rel ctx fn ce cx ee t /\ ghost_inv d ce cx ee H un t /\
      ghost_kept ce es sa G tn s H un /\ pure_frame ce fn es sa s t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
                  FLOOKUP t.vs_allocas aid = SOME site))
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> simp[gas_outcome_ptr_def] >> qexists_tac `[]` >>
  disj1_tac >> simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL []`, `es`, `G`, `tn`, `OK s`] >>
  simp[Once evaluate_def, return_def, gas_explicit_def,
       ghost_inv_gas_obs, ghost_kept_def] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem intcall_empty_staging_ptr_frame:
  compile_stage_intcall_args ce [] flags tys sa = (ops,sb) /\
  stmt_state_rel ctx fn ce cx ee s /\ ghost_inv d ce cx ee G tn s /\
  ~s.vs_halted ==>
  ?H un t argv.
    gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 H un (OK t) /\
    sb = sa /\ t = s /\ H = G /\ un = tn /\ ops = [] /\ argv = [] /\
    eval_operands ops t = SOME argv /\
    stmt_state_rel ctx fn ce cx ee t /\ ghost_inv d ce cx ee H un t /\
    ghost_kept ce ee sa G tn s H un /\ pure_frame ce fn ee sa s t /\
    intcall_owned_sites 0 sa.cs_next_id ops H t /\
    EVERY (\op. !site. op_prov H op = SOME site ==>
      intcall_site_outside (intcall_protected ce ee sa s) site) ops
Proof
  simp[compile_stage_intcall_args_def, comp_return_def] >> strip_tac >>
  simp[eval_operands_def, ghost_kept_def, intcall_owned_sites_def] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED
