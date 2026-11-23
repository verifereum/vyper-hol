(*
 * The full body induction: bodySimPtrMainAt's body_sim_ptr_mutual_at over
 * bodyFullPreds's predicates, from bodyFullCases's cases, so a frame's
 * statements, statement lists and expressions simulate with source GAS
 * origins, memory bounds and pointer ghosts at one witness, for runtime
 * and constructor frames alike.
 *
 * TOP-LEVEL:
 *   body_sim_full_mutual -- the ten predicates, by evaluate_ind
 *   body_stmts_sim_full -- the statement-list judgment it gives
 *)
Theory bodySimFullMain
Ancestors bodyFullShadowBodyInv bodyFullRaiseCustomError bodyFullAssertCustomError
  bodyFullCases bodyFullCreateHeld bodyFullIf bodyFullExprStmt bodyFullExits bodyFullPreds bodySimFull gasShadow bodySim supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeCallGraph typedCopyMetadata alist list
  vyperTypeContract[qualified,ignore_grammar] constSubst bodyLoopCalls
  contractInvContextProps
  bodyFullPredsMods bodyFullPostsMods bodyFullZeroCasesMods bodyInvSplit constSubstMods
  bodyQualifiedStmtSupport

val _ = Parse.hide "body";

val body_ind = evaluate_ind
  |> Q.SPECL [
       `\cx s. LENGTH (remcode cx) <= rank /\
                 (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmt_loop_calls_ok [(NONE,tops)] s) ==>
          body_stmt_full_ok cx s`,
       `\cx ss. LENGTH (remcode cx) <= rank /\
                 (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] ss) ==>
          body_stmts_full_ok cx ss`,
       `\cx it. LENGTH (remcode cx) <= rank /\
                 (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
          body_iterator_full_ok cx it`,
       `\cx tyv nm body vs. LENGTH (remcode cx) <= rank /\
                 (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] body) ==>
          body_for_full_ok cx tyv nm body vs`,
       `\cx e. LENGTH (remcode cx) <= rank /\
                 (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
          body_expr_full_ok cx e`,
       `\cx es. LENGTH (remcode cx) <= rank /\
                 (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
          body_exprs_full_ok cx es`,
       `\cx t. LENGTH (remcode cx) <= rank /\
                 (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
          body_base_target_full_ok cx t`,
       `\cx t. LENGTH (remcode cx) <= rank /\
                 (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
          body_base_target_full_ok cx t`,
       `\cx g v. LENGTH (remcode cx) <= rank /\
                 (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
          body_tuple_target_full_ok cx g v`,
       `\cx gs vs. LENGTH (remcode cx) <= rank /\
                 (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
          body_tuple_targets_full_ok cx gs vs`]
  |> CONV_RULE (DEPTH_CONV BETA_CONV);

val full_case_simps =
  [push_function_def, return_def, vyperContextTheory.evaluation_context_accfupds,
   pairTheory.PAIR_EQ, sumTheory.INL_11];

fun full_case th =
  rpt strip_tac >> full_simp_tac bool_ss full_case_simps >>
  irule (SIMP_RULE bool_ss full_case_simps th) >>
  asm_rewrite_tac[] >> metis_tac[];

Theorem body_raise_custom_case_full:
  !cx err.
    (!id positional kwargs tops params es.
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_full_ok cx es) ==>
    body_stmt_full_ok cx (Raise (RaiseCustomError err))
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[body_stmt_full_ok_def] >> rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.SPECL [`cx`,`err`,`DF`,`lo`,`d`,`PG`,
    `tops`,`bindings`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,`cenv`,
    `env`,`env'`,`ret_ty`,`lctx`,`RetQ`,`es`] compile_raise_custom_frag_full) >>
  asm_rewrite_tac[]
QED

Theorem body_assert_custom_case_full:
  !cx e err.
    (!s tv t id positional kwargs tops params es.
       eval_expr cx e s = (INL tv,t) /\
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_full_ok cx es) /\
    body_expr_full_ok cx e ==>
    body_stmt_full_ok cx (Assert e (AssertCustomError err))
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[body_stmt_full_ok_def] >> rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.SPECL [`cx`,`e`,`err`,`DF`,`lo`,`d`,`PG`,
    `tops`,`bindings`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,`cenv`,
    `env`,`env'`,`ret_ty`,`lctx`,`RetQ`,`es`] compile_assert_custom_frag_full_from_raise) >>
  asm_rewrite_tac[] >>
  rpt strip_tac >> irule body_raise_custom_case_full >> metis_tac[]
QED

Theorem callable_body_loop_calls_ok[local]:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy name ts = SOME (mut,nr,args,dflts,ret,ss) /\
  (!vis fm fr raw fn fa fd ft body.
     MEM (FunctionDecl vis fm fr raw fn fa fd ft body) tops ==>
     stmts_loop_calls_ok [(NONE,tops)]
       (subst_consts_stmts (module_consts_env tops []) body)) ==>
  stmts_loop_calls_ok [(NONE,tops)]
    (subst_consts_stmts (module_consts_env tops []) ss)
Proof
  rpt strip_tac >>
  Cases_on `src` >> gvs[vyperContextTheory.get_module_code_def, alistTheory.ALOOKUP_def] >>
  drule vyperTypeCallStackSoundnessTheory.lookup_callable_function_SOME_decompose >>
  simp[] >> rpt strip_tac >>
  gvs[subst_consts_stmt_def, vyperTypeContractTheory.stmt_loop_calls_ok_def] >>
  metis_tac[]
QED

fun full_loop_case th =
  let val simps = vyperTypeContractTheory.stmt_loop_calls_ok_def :: full_case_simps in
    rpt strip_tac >> full_simp_tac bool_ss simps >>
    irule (SIMP_RULE bool_ss simps th) >>
    asm_rewrite_tac[] >> metis_tac[]
  end;

Theorem callable_remcode_decreases[local]:
  ~MEM (src,fn) cx.stk /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) /\
  (dflts,ss) <> ([],[]) ==>
  LENGTH (remcode (cx with stk updated_by CONS (src,fn))) < LENGTH (remcode cx)
Proof
  strip_tac >>
  drule_all_then (qspec_then `src` assume_tac) lookup_callable_function_eq_ALOOKUP_module_fns >>
  fs[vyperContextTheory.get_module_code_def, AllCaseEqs()] >>
  drule_all ALOOKUP_FLAT_MAP_module_fns >> strip_tac >>
  qabbrev_tac `all_fns = FLAT (MAP (\(sid,tl). module_fns sid tl) mods)` >>
  `MEM ((src,fn),(dflts,ss)) all_fns` by
    (irule alistTheory.ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
  `FILTER (\((sid,f),ss). ~MEM (sid,f) ((src,fn)::cx.stk)) all_fns =
     FILTER (\(k,ss). k <> (src,fn))
       (FILTER (\((sid,f),ss). ~MEM (sid,f) cx.stk) all_fns)` by
    (simp[rich_listTheory.FILTER_FILTER] >> AP_THM_TAC >> AP_TERM_TAC >>
     simp[FUN_EQ_THM, pairTheory.FORALL_PROD]) >>
  simp[remcode_def, GSYM markerTheory.Abbrev_def] >>
  qpat_assum `FILTER _ all_fns = FILTER _ (FILTER _ all_fns)`
    (once_rewrite_tac o single o SIMP_RULE (srw_ss()) []) >>
  irule rich_listTheory.LENGTH_FILTER_LESS >>
  simp[EXISTS_MEM, MEM_FILTER] >>
  qexists_tac `((src,fn),(dflts,ss))` >> simp[]
QED

fun without_smaller_rank tac =
  qpat_x_assum `!m:num. m < rank ==> _` (K ALL_TAC) >> tac;

Theorem body_sim_full_mutual_ranked[local]:
  !rank:num. ^(snd (dest_imp (concl body_ind)))
Proof
  completeInduct_on `rank` >>
  mp_tac body_ind >> impl_tac
  >- (rpt conj_tac
      >- without_smaller_rank (full_case body_pass_case_full)
      >- without_smaller_rank (full_case body_continue_case_full)
      >- without_smaller_rank (full_case body_break_case_full)
      >- without_smaller_rank (full_case body_return_none_case_full)
      >- without_smaller_rank (full_case body_return_case_full)
      >- without_smaller_rank (full_case body_raise_bare_case_full)
      >- without_smaller_rank (full_case body_raise_unreachable_case_full)
      >- without_smaller_rank (full_case body_raise_reason_case_full)
      >- without_smaller_rank (full_case body_raise_custom_case_full)
      >- without_smaller_rank (full_case body_assert_case_full)
      >- without_smaller_rank (full_case body_assert_unreachable_case_full)
      >- without_smaller_rank (full_case body_assert_reason_case_full)
      >- without_smaller_rank (full_case body_assert_custom_case_full)
      >- without_smaller_rank (full_case body_log_case_full)
      >- without_smaller_rank (full_case body_annassign_case_full)
      >- without_smaller_rank (full_case body_append_case_full)
      >- without_smaller_rank (full_case body_assign_case_full)
      >- without_smaller_rank (full_case body_assign_tuple_case_full)
      >- without_smaller_rank (full_case body_augassign_case_full)
      >- without_smaller_rank (full_loop_case body_if_case_full)
      >- without_smaller_rank (full_loop_case body_for_case_full)
      >- without_smaller_rank (full_case body_expr_stmt_case_full)
      >- without_smaller_rank (full_case body_stmts_nil_case_full)
      >- without_smaller_rank (full_loop_case body_stmts_cons_case_full)
      >- without_smaller_rank (simp[body_iterator_full_ok_def])
      >- without_smaller_rank (rpt strip_tac >> fs[] >> rw[body_iterator_full_ok_def] >> metis_tac[])
      >- without_smaller_rank (simp[body_for_full_ok_def])
      >- without_smaller_rank (rpt strip_tac >> fs[] >> rw[body_for_full_ok_def] >> first_x_assum irule >> simp[push_scope_with_var_def, return_def] >> metis_tac[])
      >- without_smaller_rank (rpt strip_tac >> irule body_expr_full_ok_leaf >> simp[])
      >- without_smaller_rank (rpt strip_tac >> irule body_expr_full_ok_leaf >> simp[])
      >- without_smaller_rank (rpt strip_tac >> irule body_expr_full_ok_leaf >> simp[])
      >- without_smaller_rank (full_case body_ifexp_case_full)
      >- without_smaller_rank (rpt strip_tac >> irule body_expr_full_ok_leaf >> simp[])
      >- without_smaller_rank (full_case body_structlit_case_full)
      >- without_smaller_rank (full_case body_subscript_case_full)
      >- without_smaller_rank (full_case body_attribute_case_full)
      >- without_smaller_rank (full_case body_builtin_case_full)
      >- without_smaller_rank (full_case body_pop_case_full)
      >- without_smaller_rank (full_case body_type_builtin_case_full)
      >- without_smaller_rank (full_case body_send_case_full)
      >- without_smaller_rank (full_case body_extcall_case_full)
      >- suspend "intcall"
      >- without_smaller_rank (full_case body_raw_call_case_full)
      >- without_smaller_rank (full_case body_raw_call_calldata_case_full)
      >- without_smaller_rank (full_case body_raw_log_case_full)
      >- without_smaller_rank (full_case body_raw_revert_case_full)
      >- without_smaller_rank (full_case body_selfdestruct_case_full)
      >- without_smaller_rank (rpt gen_tac >> Cases_on `kind` >>
          rpt strip_tac >> full_simp_tac bool_ss full_case_simps >>
          FIRST [irule create_minimal_proxy_expr_full_ok,
                 irule create_copy_expr_full_ok,
                 irule create_blueprint_expr_full_ok,
                 irule raw_create_expr_full_ok] >>
          asm_rewrite_tac[] >> metis_tac[])
      >- without_smaller_rank (simp[body_exprs_full_ok_def])
      >- without_smaller_rank (rpt strip_tac >> fs[] >> rw[body_exprs_full_ok_def] >> metis_tac[])
      >- without_smaller_rank (simp[body_base_target_full_ok_def])
      >- without_smaller_rank (simp[body_base_target_full_ok_def])
      >- without_smaller_rank (simp[body_base_target_full_ok_def])
      >- without_smaller_rank (rpt strip_tac >> fs[] >> rw[body_base_target_full_ok_def] >> metis_tac[])
      >- without_smaller_rank (simp[])
      >- without_smaller_rank (simp[body_tuple_target_full_ok_def])
      >- without_smaller_rank
           (simp[body_tuple_target_full_ok_def] >> rpt strip_tac >> metis_tac[])
      >- without_smaller_rank (simp[body_tuple_target_full_ok_def])
      >- without_smaller_rank (rpt strip_tac >> fs[] >> rw[body_tuple_target_full_ok_def] >> metis_tac[])
      >- without_smaller_rank (simp[body_tuple_target_full_ok_def])
      >> without_smaller_rank (simp[body_tuple_target_full_ok_def])) >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_sim_full_mutual_ranked[intcall]:
  rpt strip_tac >> full_simp_tac bool_ss full_case_simps >>
  irule (SIMP_RULE bool_ss full_case_simps body_intcall_case_full) >>
  conj_tac
  >- (qpat_x_assum `!m:num. m < rank ==> _` kall_tac >>
      rpt gen_tac >> strip_tac >> gvs[] >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `(dflts,ss) = ([],[])`
  >- gvs[subst_consts_stmt_def, subst_consts_expr_def,
          body_stmts_nil_case_full, body_exprs_full_ok_def] >>
  `LENGTH (remcode (cx with stk updated_by CONS (src_id_opt,fn))) < rank` by
    (drule_all callable_remcode_decreases >> decide_tac) >>
  qpat_x_assum `!m:num. m < rank ==> _` (drule_then strip_assume_tac) >>
  conj_tac
  >- (first_x_assum irule >> simp[] >> gen_tac >> strip_tac >>
      qpat_assum `!tops. ALOOKUP cx.sources _ = SOME _ ==> _`
        (qspec_then `tops` mp_tac) >> simp[] >> strip_tac >>
      `cx_tops cx = tops` by
        fs[gasContextTheory.cx_tops_def, vyperContextTheory.get_module_code_def,
           alistTheory.ALOOKUP_def] >>
      asm_rewrite_tac[] >>
      irule callable_body_loop_calls_ok >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> gen_tac >> strip_tac >>
  qpat_assum `!tops. ALOOKUP cx.sources _ = SOME _ ==> _`
    (qspec_then `tops` mp_tac) >> simp[]
QED

Finalise body_sim_full_mutual_ranked

Theorem body_sim_full_mutual:
  (!cx s. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmt_loop_calls_ok [(NONE,tops)] s) ==>
    body_stmt_full_ok cx s) /\
  (!cx ss. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] ss) ==>
    body_stmts_full_ok cx ss) /\
  (!cx it. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_iterator_full_ok cx it) /\
  (!cx tyv nm body vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] body) ==>
    body_for_full_ok cx tyv nm body vs) /\
  (!cx e. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_expr_full_ok cx e) /\
  (!cx es. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_exprs_full_ok cx es) /\
  (!cx t. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_base_target_full_ok cx t) /\
  (!cx g v. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_tuple_target_full_ok cx g v) /\
  (!cx gs vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_tuple_targets_full_ok cx gs vs)
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  qspec_then `LENGTH (remcode cx)` mp_tac body_sim_full_mutual_ranked >>
  strip_tac >> first_x_assum irule >> asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem body_stmts_sim_full:
  !DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv cx env env'
   ret_ty lctx RetQ ss es.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\ struct_args_unique tops /\
    supported_stmts tops bindings ss /\
    (!vis mut nr raw fn args dflts ret body.
       MEM (FunctionDecl vis mut nr raw fn args dflts ret body) tops ==>
       stmts_loop_calls_ok [(NONE,tops)] body) /\
    stmts_loop_calls_ok [(NONE,tops)] ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    stmts_exprs_ok cenv ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss)
      (stmts_env (gas_shadow_env T cenv) lctx ret_ty (MAP gas_shadow_stmt ss))
      (eval_stmts cx ss) es
Proof
  rpt strip_tac >>
  `!vis mut nr raw fn args dflts ret body.
      MEM (FunctionDecl vis mut nr raw fn args dflts ret body) tops ==>
      stmts_loop_calls_ok [(NONE,tops)] (subst_consts_stmts (module_consts_env tops []) body)` by
    (qpat_assum `body_const_cells_agree _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_def]) >>
     `cx_tops cx = tops` by fs[alistTheory.ALOOKUP_def] >>
     rpt strip_tac >>
     drule checked_subst_consts_loop_calls_ok >>
     simp[] >> disch_then irule >> gvs[] >> metis_tac[]) >>
  `!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
        struct_args_unique ts /\
        (!vis mut nr raw fn args dflts ret body.
           MEM (FunctionDecl vis mut nr raw fn args dflts ret body) ts ==>
           stmts_loop_calls_ok [(NONE,ts)]
             (subst_consts_stmts (module_consts_env ts []) body)) /\
        stmts_loop_calls_ok [(NONE,ts)] ss` by (drule_then assume_tac body_inv_contract >>
          drule_then assume_tac contract_inv_singleton_source_modules >>
          simp[] >> first_assum ACCEPT_TAC) >>
  metis_tac[body_sim_full_mutual, body_stmts_full_ok_def]
QED

(* The linked induction follows calls reachable from the main and exported
   entry points, with each function's constants already substituted. *)
val linked_body_guard =
  ``ALOOKUP cx.sources cx.txn.target = SOME mods /\
    vyperTypeContract$exports_ok cx.layouts cx.txn.target mods exps /\
    EVERY (struct_args_unique o SND) mods /\
    (!src tops vis mut nr raw fn args dflts ret ss.
       ALOOKUP mods src = SOME tops /\
       MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
       stmts_loop_calls_ok mods
         (subst_consts_stmts_mods (consts_env_mods mods) ss))``;

val linked_calls_live =
  ``\calls. EVERY (\k. MEM k (vyperTypeContract$linked_live_functions mods exps)) calls``;

fun linked_body_ind rank_guard =
  evaluate_ind
  |> Q.SPECL [
       `\cx s. ^rank_guard /\ ^linked_body_guard /\
         qualified_stmt_decls_ok mods s /\
         ^linked_calls_live (int_calls_stmt s) /\ stmt_loop_calls_ok mods s ==>
         body_stmt_full_ok_mods mods exps cx s`,
       `\cx ss. ^rank_guard /\ ^linked_body_guard /\
         qualified_stmts_decls_ok mods ss /\
         ^linked_calls_live (int_calls_stmts ss) /\ stmts_loop_calls_ok mods ss ==>
         body_stmts_full_ok_mods mods exps cx ss`,
       `\cx it. ^rank_guard /\ ^linked_body_guard /\
         ^linked_calls_live (int_calls_iterator it) ==>
         body_iterator_full_ok_mods mods exps cx it`,
       `\cx tyv nm body vs. ^rank_guard /\ ^linked_body_guard /\
         qualified_stmts_decls_ok mods body /\
         ^linked_calls_live (int_calls_stmts body) /\ stmts_loop_calls_ok mods body ==>
         body_for_full_ok_mods mods exps cx tyv nm body vs`,
       `\cx e. ^rank_guard /\ ^linked_body_guard /\
         ^linked_calls_live (int_calls_expr e) ==>
         body_expr_full_ok_mods mods exps cx e`,
       `\cx es. ^rank_guard /\ ^linked_body_guard /\
         ^linked_calls_live (int_calls_exprs es) ==>
         body_exprs_full_ok_mods mods exps cx es`,
       `\cx t. ^rank_guard /\ ^linked_body_guard /\
         ^linked_calls_live (int_calls_target t) ==>
         body_base_target_full_ok_mods mods exps cx t`,
       `\cx t. ^rank_guard /\ ^linked_body_guard /\
         ^linked_calls_live (int_calls_target t) ==>
         body_base_target_full_ok_mods mods exps cx t`,
       `\cx g v. ^rank_guard /\ ^linked_body_guard /\
         ^linked_calls_live (int_calls_atarget g) ==>
         body_tuple_target_full_ok_mods mods exps cx g v`,
       `\cx gs vs. ^rank_guard /\ ^linked_body_guard /\
         ^linked_calls_live (int_calls_atargets gs) ==>
         body_tuple_targets_full_ok_mods mods exps cx gs vs`]
  |> CONV_RULE (DEPTH_CONV BETA_CONV);

val ranked_linked_body_ind = linked_body_ind ``LENGTH (remcode cx) <= rank``;

Theorem body_sim_full_mutual_ranked_mods:
  !mods exps rank:num. ^(snd (dest_imp (concl ranked_linked_body_ind)))
Proof
  cheat
QED

Theorem body_sim_full_mutual_mods:
  !mods exps. ^(simpLib.SIMP_CONV bool_ss []
    (snd (dest_imp (concl (linked_body_ind boolSyntax.T)))) |> concl |> rhs)
Proof
  rpt gen_tac >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  qmatch_asmsub_rename_tac `ALOOKUP cx.sources cx.txn.target` >>
  qspecl_then [`mods`, `exps`, `LENGTH (remcode cx)`] strip_assume_tac
    body_sim_full_mutual_ranked_mods >>
  first_x_assum irule >> asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem body_stmts_sim_full_mods:
  !DF lo d PG mods exps src tops bindings ctx shadow_ctx func shadow_func
    cenv cx env env' ret_ty lctx RetQ ss es.
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    vyperTypeContract$exports_ok cx.layouts cx.txn.target mods exps /\
    EVERY (struct_args_unique o SND) mods /\
    supported_stmts tops bindings ss /\
    (!sid ts vis mut nr raw fn args dflts ret body.
       ALOOKUP mods sid = SOME ts /\
       MEM (FunctionDecl vis mut nr raw fn args dflts ret body) ts ==>
       stmts_loop_calls_ok mods
         (subst_consts_stmts_mods (consts_env_mods mods) body)) /\
    qualified_stmts_decls_ok mods ss /\
    stmts_loop_calls_ok mods ss /\
    EVERY (\k. MEM k (vyperTypeContract$linked_live_functions mods exps))
      (int_calls_stmts ss) /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       EXISTS (occurs_abi_decode_target target o SND) mods) /\
    body_const_cells_agree_mods mods cx env es /\
    expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    stmts_exprs_ok cenv ss /\
    ~supported_stmts_expr_exists (unallocated_bare_global_root cenv env) ss /\
    (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
                (vyperSubscriptOverlap$accesses_stmts ss) /\
           IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
           IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_full_mods mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss)
      (stmts_env (gas_shadow_env T cenv) lctx ret_ty (MAP gas_shadow_stmt ss))
      (eval_stmts cx ss) es
Proof
  rpt gen_tac >> strip_tac >>
  `ALOOKUP cx.sources cx.txn.target = SOME mods` by
    drule_then ACCEPT_TAC body_const_cells_agree_mods_sources >>
  `body_stmts_full_ok_mods mods exps cx ss` by
    (irule (cj 2 (Q.SPECL [`mods`, `exps`] body_sim_full_mutual_mods)) >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `body_stmts_full_ok_mods _ _ _ _`
    (mp_tac o Q.SPECL [`DF`, `lo`, `d`, `PG`, `src`, `tops`, `bindings`,
        `ctx`, `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `env'`,
        `ret_ty`, `lctx`, `RetQ`, `es`] o
     REWRITE_RULE [body_stmts_full_ok_mods_def]) >>
  asm_rewrite_tac[]
QED
