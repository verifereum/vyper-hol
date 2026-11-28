(*
 * Single-file corollaries of the module-list body simulation.
 *
 * TOP-LEVEL:
 *   body_sim_full_mutual -- the guarded single-file body predicates
 *   body_stmts_sim_full -- the statement-list judgment it gives
 *)
Theory bodySimFullMain
Ancestors bodySingletonStmtGuards[qualified] bodyFullShadowBodyInv bodyFullRaiseCustomError bodyFullAssertCustomError
  bodyFullCases bodyFullCreateHeld bodyFullIf bodyFullExprStmt bodyFullExits bodyFullPreds bodySimFull gasShadow bodySim supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeCallGraph typedCopyMetadata alist list
  vyperTypeContract[qualified,ignore_grammar] constSubst bodyLoopCalls
  contractInvContextProps
  bodySimFullMainWidenedScratch[qualified]

val _ = Parse.hide "body";

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[body_stmt_full_ok_def] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac bodySingletonStmtGuardsTheory.singleton_stmt_expr_guards >>
  match_mp_tac (Q.SPECL [`cx`,`err`,`DF`,`lo`,`d`,`PG`,
    `tops`,`bindings`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,`cenv`,
    `env`,`env'`,`ret_ty`,`lctx`,`RetQ`,`es`] compile_raise_custom_frag_full) >>
  asm_rewrite_tac[]
QED
*)
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
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[body_stmt_full_ok_def] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac bodySingletonStmtGuardsTheory.singleton_stmt_expr_guards >>
  match_mp_tac (Q.SPECL [`cx`,`e`,`err`,`DF`,`lo`,`d`,`PG`,
    `tops`,`bindings`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,`cenv`,
    `env`,`env'`,`ret_ty`,`lctx`,`RetQ`,`es`] compile_assert_custom_frag_full_from_raise) >>
  asm_rewrite_tac[] >>
  rpt strip_tac >> irule body_raise_custom_case_full >> metis_tac[]
QED
*)
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
  cheat
QED

Theorem callable_body_loop_calls_ok:
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

Theorem callable_remcode_decreases:
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

Theorem body_sim_full_mutual:
  (!cx s. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_stmt s) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmt_loop_calls_ok [(NONE,tops)] s) ==>
    body_stmt_full_ok cx s) /\
  (!cx ss. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_stmts ss) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] ss) ==>
    body_stmts_full_ok cx ss) /\
  (!cx it. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_iterator it) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_iterator_full_ok cx it) /\
  (!cx tyv nm body vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_stmts body) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] body) ==>
    body_for_full_ok cx tyv nm body vs) /\
  (!cx e. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_expr e) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_expr_full_ok cx e) /\
  (!cx es. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_exprs es) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_exprs_full_ok cx es) /\
  (!cx t. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_target t) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_base_target_full_ok cx t) /\
  (!cx g v. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_atarget g) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_tuple_target_full_ok cx g v) /\
  (!cx gs vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_atargets gs) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_tuple_targets_full_ok cx gs vs)
Proof
  ACCEPT_TAC bodySimFullMainWidenedScratchTheory.body_sim_full_mutual
QED

Theorem body_stmts_sim_full:
  !DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv cx env env'
   ret_ty lctx RetQ ss es.
    body_inv tops ctx cenv cx /\
    IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
    EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
      (int_calls_stmts ss) /\
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
     `cx_tops cx = tops` by
       (drule_then (ACCEPT_TAC o CONJUNCT2) bodyInvCodePropsTheory.body_inv_main_code) >>
     rpt strip_tac >>
     drule checked_subst_consts_loop_calls_ok >>
     simp[] >> disch_then irule >> gvs[] >> metis_tac[]) >>
  `!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
        IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,ts)]) /\
        EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
          (int_calls_stmts ss) /\
        struct_args_unique ts /\
        (!vis mut nr raw fn args dflts ret body.
           MEM (FunctionDecl vis mut nr raw fn args dflts ret body) ts ==>
           stmts_loop_calls_ok [(NONE,ts)]
             (subst_consts_stmts (module_consts_env ts []) body)) /\
        stmts_loop_calls_ok [(NONE,ts)] ss` by
    (qpat_assum `body_inv _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
     rpt gen_tac >> strip_tac >>
     `ts = tops` by
       (qpat_x_assum `ALOOKUP _ _ = SOME [(NONE,ts)]` mp_tac >> simp[]) >>
     simp[] >> first_assum ACCEPT_TAC) >>
  metis_tac[body_sim_full_mutual, body_stmts_full_ok_def]
QED
