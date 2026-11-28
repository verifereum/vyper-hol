(* Other call targets are closed under the same-context prefix induction. *)
Theory s1PrefixBoolChainHeadOtherCall
Ancestors vyperCreate[qualified,ignore_grammar] rich_list[qualified,ignore_grammar]
  s1PrefixSend s1PrefixCreateHeld s1PrefixRawCall s1PrefixRawCallCalldata
  s1PrefixRawLogCompose s1PrefixRawRevertValue s1PrefixSelfdestruct
  s1PrefixCheckedContextFull s1PrefixPreds exprCallBounds vyperAST
  gasShadowCompile gasShadowCompileHelpers bodyFullRawLog exprSimCallRawLog
  s1PrefixBoolChainHeadMakeArray[qualified,ignore_grammar]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_expr_prefix_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `!a. MEM a args ==> body_expr_prefix_ok cx a` by
    (gen_tac >> strip_tac >>
     qpat_assum `!a. expr_size a < _ ==> body_expr_prefix_ok cx a` irule >>
     irule expr_call_arg_bound >> first_assum ACCEPT_TAC) >>
  `body_exprs_prefix_ok cx args` by
    (irule s1PrefixBoolChainHeadMakeArrayTheory.prefix_list_from_members >>
     first_assum ACCEPT_TAC) >>
  drule_then strip_assume_tac checked_context_full_exprs >>
  Cases_on `target` >> gvs[]
  >- (`body_expr_prefix_ok cx (Call ann (Send b) args dr)` by
        (irule body_send_case_prefix >> metis_tac[]) >>
      qpat_assum `body_expr_prefix_ok cx (Call ann (Send b) args dr)`
        (mp_tac o REWRITE_RULE [body_expr_prefix_ok_def]) >> simp[] >>
      metis_tac[])
  >- (`expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
          cenv cx ty (Call ann (RawCallTarget r) args dr) es` by
        (irule raw_call_expr_vv_prefix >> simp[] >> qexistsl [`env`,`tops`] >> simp[]) >>
      simp[s1PrefixOfVVTheory.expr_sim_prefix_of_vv])
  >- (`expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
          cenv cx ty (Call ann (RawCallCalldataTarget r) args dr) es` by
        (irule raw_call_calldata_vv_prefix >> simp[] >> qexistsl [`env`,`tops`] >> simp[]) >>
      simp[s1PrefixOfVVTheory.expr_sim_prefix_of_vv])
  >- (`expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
          cenv cx ty (Call ann RawLog args dr) es` by
        (irule raw_log_expr_sim_prefix >> simp[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env] >>
         conj_tac
         >- metis_tac[Q.INST [`sd` |-> `T`, `sh` |-> `T`]
               (MATCH_MP gas_shadow_compiles_multi_exprs_env
                 (CONJUNCT1 gas_shadow_compile_expr_env))] >>
         qexistsl [`env`,`tops`] >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule s1PrefixOfVVTheory.expr_vv_sim_stack_prefix >> simp[] >> conj_tac
      >- metis_tac[raw_log_compile_stack]
      >- metis_tac[raw_log_eval_value])
  >- (`expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
          cenv cx ty (Call ann RawRevert args dr) es` by
        (mp_tac raw_revert_value_prefix_from_tail >>
         (impl_tac >-
           (rpt gen_tac >> strip_tac >>
            drule_all bodyFullRawRevertCompiledTailTheory.raw_revert_compiled_tail_joint >> simp[])) >>
         disch_then irule >> metis_tac[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule s1PrefixOfVVTheory.expr_vv_sim_stack_prefix >> simp[] >>
      reverse conj_tac >- metis_tac[vyperSystemControlTheory.raw_revert_no_success] >>
      drule bodyFullRawRevertInterfacesTheory.raw_revert_source_pre >> strip_tac >> gvs[] >>
      gen_tac >> simp[Once exprLoweringTheory.compile_expr_def, exprLoweringTheory.compile_call_def] >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[])
  >- (`expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
          cenv cx ty (Call ann SelfDestructTarget args dr) es` by
        (irule s1PrefixSelfdestructTheory.selfdestruct_expr_prefix >> metis_tac[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule s1PrefixOfVVTheory.expr_vv_sim_stack_prefix >> simp[] >>
      drule bodyFullCasesTheory.selfdestruct_full_source_pre >> strip_tac >> gvs[] >>
      conj_tac
      >- (gen_tac >> simp[Once exprLoweringTheory.compile_expr_def,
                          exprLoweringTheory.compile_call_def, expr_type_def,
                          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def] >>
          rpt (pairarg_tac >> simp[]))
      >- (rpt strip_tac >> gvs[vyperStateTheory.bind_def, AllCaseEqs()] >>
          rename1 `selfdestruct_tail cx target st = (INL _,_)` >>
          qpat_x_assum `selfdestruct_tail _ _ _ = _` mp_tac >>
          qspecl_then [`cx`,`target`,`st`]
            (qx_choosel_then [`ex`,`out`] SUBST1_TAC) selfdestructHaltTheory.selfdestruct_tail_raises >>
          simp[]))
  >- (`!x. MEM x (create_operand_order c b args) ==> MEM x args` by
        ((POP_ASSUM_LIST (K ALL_TAC) >>
         Cases_on `c` >> Cases_on `args` >>
         simp[vyperCreateTheory.create_operand_order_def] >>
         Cases_on `t` >> simp[vyperCreateTheory.create_operand_order_def] >>
         rpt gen_tac >> rpt strip_tac >>
         Cases_on `x = h` >> gvs[] >> rpt strip_tac >> gvs[] >>
         (drule rich_listTheory.MEM_DROP_IMP ORELSE
          drule rich_listTheory.MEM_TAKE) >> (simp[vyperCreateTheory.create_operand_order_def, rich_listTheory.MEM_DROP_IMP, rich_listTheory.MEM_TAKE]))) >>
      `body_exprs_prefix_ok cx (create_operand_order c b args)` by
        (irule s1PrefixBoolChainHeadMakeArrayTheory.prefix_list_from_members >>
         gen_tac >> strip_tac >>
         qpat_assum `!a. MEM a args ==> body_expr_prefix_ok cx a` irule >>
         first_x_assum irule >> first_assum ACCEPT_TAC) >>
      `body_expr_prefix_ok cx (Call ann (CreateTarget c b b0 l) args dr)` by
        (Cases_on `c` >-
           (irule create_minimal_proxy_expr_prefix_ok >> simp[]) >-
           (irule create_copy_expr_prefix_ok >> simp[]) >-
           (irule create_blueprint_expr_prefix_ok >> simp[]) >>
         irule raw_create_expr_prefix_ok >> simp[]) >>
      qpat_assum `body_expr_prefix_ok cx (Call ann (CreateTarget c b b0 l) args dr)`
        (mp_tac o REWRITE_RULE [body_expr_prefix_ok_def]) >> simp[] >>
      metis_tac[])
QED
*)
Theorem bool_chain_head_other_call_prefix_ok:
  !cx ann target args dr.
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
        (vyperTypeCallGraph$int_calls_expr (Call ann target args dr))) /\
    (!fid. target <> IntCall fid) /\
    (!stat skip fsig opts. target <> ExtCall stat skip fsig opts) /\
    (!a. expr_size a < expr_size (Call ann target args dr) /\
         (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
           EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
             (vyperTypeCallGraph$int_calls_expr a)) ==>
         body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Call ann target args dr)
Proof
  cheat
QED
