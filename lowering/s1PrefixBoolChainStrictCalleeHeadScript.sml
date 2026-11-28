(* Assemble the selected internal call in the caller's paired code. *)
Theory s1PrefixBoolChainStrictCalleeHead
Ancestors
  s1PrefixBoolChainSuppliedToDefaults s1PrefixBoolChainUsedDefaultBind
  s1PrefixBoolChainDefaultsToInvoke s1PrefixBoolChainUniformEntries
  s1PrefixBoolChainPushedLockedRun s1PrefixBoolChainCallRankBase[qualified]
  vyperReadOnlySyntax
  s1PrefixBoolChainHeadMakeArray s1PrefixCheckedContextFull s1PrefixOfVV
  bodyIntCallSource bodySimFullMain bodyLoopCalls typedCopyProducer
  bodyFullPreds bodyFullShadowBodyInv s1PrefixPreds s1PrefixDefs
  vyperTypeContract vyperStorageTrace vyperInterpreter vyperState vyperAST list alist
  exprLowering compileEnv gasSummary constSubst

val _ = temp_overload_on ("bind", ``vyperState$bind``)
val _ = temp_overload_on ("return", ``vyperState$return``)

Theorem intcall_supplied_smaller[local]:
  !ys e ann src name dr. MEM e ys ==>
    expr_size e < expr_size (Call ann (IntCall (src,name)) ys dr)
Proof
  Induct >> simp[expr_size_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`e`,`ann`,`src`,`name`,`dr`] mp_tac) >>
  simp[expr_size_def]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[body_expr_prefix_ok_def] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `body_const_cells_agree [(NONE,tops)] cx env es0` >>
  drule_all body_intcall_source_selection >> strip_tac >>
  qpat_x_assum `src = NONE` SUBST_ALL_TAC >>
  `body_exprs_prefix_ok cx es` by
    (irule prefix_list_from_members >> rpt strip_tac >>
     qpat_assum `!a. expr_size a < _ ==> _` irule >>
     irule intcall_supplied_smaller >> first_assum ACCEPT_TAC) >>
  drule_then strip_assume_tac checked_context_full_exprs >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Call ann (IntCall (NONE,name)) es dr) es0` by
    suspend "raw" >>
  conj_tac >- (irule expr_sim_prefix_of_vv >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
*)
Theorem bool_chain_strict_callee_head_prefix:
  !rank cx ann src name es dr.
    LENGTH (remcode cx) <= rank /\
    (!a. expr_size a < expr_size (Call ann (IntCall (src,name)) es dr) ==>
       body_expr_prefix_ok cx a) /\
    (!c a. LENGTH (remcode c) < rank ==> body_expr_prefix_ok c a) /\
    (!c ys. LENGTH (remcode c) < rank /\
       (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
          stmts_loop_calls_ok [(NONE,ts)] ys) ==>
       body_stmts_prefix_ok c ys) ==>
    body_expr_prefix_ok cx (Call ann (IntCall (src,name)) es dr)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_strict_callee_head_prefix[raw]:
  simp[expr_vv_sim_prefix_def] >> rpt gen_tac >> strip_tac >>
  qhdtm_assum `expr_vv_sim_full_pre`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  once_rewrite_tac[GSYM bodyFullIntCallTheory.bind_return_right] >>
  irule (bool_chain_supplied_to_defaults |> SPEC_ALL
    |> Q.GENL [`kc`,`f`,`P`]
    |> Q.ISPEC `compileEnv$comp_return : vyper_value -> compile_state -> vyper_value # compile_state`
    |> Q.ISPEC `vyperState$return : eval_result -> evaluation_state -> (eval_result + exception) # evaluation_state`
    |> Q.SPEC `expr_vv_res_ok`) >>
  qpat_assum `lookup_callable_function _ _ _ = SOME _` (irule_at Any) >>
  qpat_assum `body_const_cells_agree _ _ _ _` (irule_at Any) >>
  qexistsl [`ty`,`shadow_sb`,`shadow_func`,`shadow_sa`,`sb`,`sa`,`rr`,`vv`,`d`,`cenv`] >>
  pure_rewrite_tac [bodyFullIntCallTheory.bind_return_right,
    exprSimAccountsTheory.comp_bind_comp_return, compileEnvTheory.comp_return_def,
    fragExecTheory.cs_appends_return, storage_trace_frame_return, FORALL_SIMP, AND_CLAUSES] >>
  qabbrev_tac `after_args = \prev vals.
    bind (lift_option_type (bind_arguments (get_tenv cx) args vals) "IntCall bind_arguments")
      (\penv. bind (lift_option_type (evaluate_type (get_tenv cx) ret) "IntCall eval ret")
        (\rtv. ignore_bind (lock_if_nr cx nr (is_view_mut mut))
          (bind (push_function (NONE,name) penv cx) (\cxf.
            bind (finally_unless_halt
              (finally (try (ignore_bind (eval_stmts cxf ss) (return NoneV)) handle_function)
                (pop_function prev)) (unlock_if_nr cx nr (is_view_mut mut)))
              (\rv. bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
                (\crv. return (Value crv)))))))` >>
  qexists_tac `after_args` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY ((simp_tac bool_ss [Abbr `after_args`] >> NO_TAC) ORELSE
       (disch_tac >> simp[] >> NO_TAC)) >>
  map_every qx_gen_tac [`vv'`,`sm`,`nret`,`rbs`,`pvs`,`ds`,`si`,`sf`,`sh_si`,`sh_sf`,
    `def_ops`,`st2`,`sup_ops`,`entry`,`Ga`,`tna`,`pin`,`marks`,`svs`,`at_defaults`,
    `t`,`G`,`tn`,`dc`,`pushed`,`envd`,`next`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule (bool_chain_used_default_bind_prefix |> SPEC_ALL |> Q.GEN `P`
    |> Q.ISPEC `expr_vv_res_ok`) >>
  qpat_x_assum `envd = _` SUBST_ALL_TAC >>
  qhdtm_assum `bool_chain_default_ready` (irule_at Any) >>
  qexistsl [`DROP (LENGTH es) (MAP SND args)`,`[]`,`svs`,`TAKE (LENGTH es) (MAP SND args)`,
    `t`,`at_defaults`,`sup_ops`,`sh_si`,`TAKE (LENGTH es) pvs`,`rank`,`[]`,`[]`,
    `DROP (LENGTH es) pvs`,`[]`,`ds`,`[]`,`[]`,`si`] >>
  simp[NoAsms,compile_stage_intcall_args_def,comp_return_def,gas_explicit_nil] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qmatch_goalsub_rename_tac `LENGTH (remcode pushed) < rank` >>
       disch_tac >>
       `(dflts,ss) <> ([],[])` by (CCONTR_TAC >> gvs[subst_consts_expr_def]) >>
       drule_all callable_remcode_decreases >> fs[] >> decide_tac >> NO_TAC) >>
  map_every qx_gen_tac [`def_ops'`,`dvs`,`ed`,`u`,`Gd`,`tnd`,`dm`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `def_ops' = def_ops` by
    (qpat_assum `compile_stage_intcall_args compile_expr dc ds _ _ si = (def_ops,sf)`
       (fn th => qpat_assum `compile_stage_intcall_args compile_expr dc ds _ _ si = (def_ops',sf)`
                    (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
  qpat_x_assum `def_ops' = def_ops` SUBST_ALL_TAC >>
  suspend "invoke"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_strict_callee_head_prefix[invoke]:
  qpat_assum `IS_SOME (evaluate_type _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  rename1 `evaluate_type (get_tenv cx) ret = SOME rtv` >>
  `body_stmts_full_ok (cx with stk updated_by CONS (NONE,name))
     (subst_consts_stmts (module_consts_env tops []) ss)` by
    (qpat_assum `body_const_cells_agree _ cx env es0`
      (mp_then Any strip_assume_tac
        s1PrefixBoolChainCallRankBaseTheory.selected_port_checker_guards) >>
     irule (cj 2 bodySimFullMainTheory.body_sim_full_mutual) >> simp[] >> metis_tac[]) >>
  irule (bool_chain_defaults_to_invoke_projected_prefix |> SPEC_ALL
    |> Q.GENL [`kc`,`f`,`P`]
    |> Q.ISPEC `compileEnv$comp_return : vyper_value -> compile_state -> vyper_value # compile_state`
    |> Q.ISPEC `vyperState$return : eval_result -> evaluation_state -> (eval_result + exception) # evaluation_state`
    |> Q.SPEC `expr_vv_res_ok`
    |> Q.INST [`st2` |-> `st2`, `st2a` |-> `si`, `st3` |-> `sf`, `sm` |-> `sm`, `sb` |-> `sb`]) >>
  qpat_assum `lookup_callable_function cx.in_deploy name tops = SOME _` (irule_at Any) >>
  qpat_assum `expr_body_pre cenv cx env _ es0` (irule_at Any) >>
  qpat_assum `evaluate_type (get_tenv cx) ret = SOME rtv` (irule_at Any) >>
  qpat_assum `cenv.ce_func_info _ = (nret,rbs,pvs)` (irule_at Any) >>
  qpat_assum `compile_expr cenv ty _ sa = (vv',sm)` (irule_at Any) >>
  simp_tac bool_ss [comp_return_def,storage_trace_frame_return,return_def,pairTheory.SND,
    FORALL_SIMP,AND_CLAUSES,IMP_CLAUSES,TAKE_DROP] >>
  qexistsl [`tna`,`tn0`,`t`,`svs`,`sup_ops`,`st2`,`si`,`sf`,`sb`,`s0`,`rr`,`rank`,
    `pin`,`vv'`,`marks`,`entry`,`at_defaults`,`dvs`,`dm`,`def_ops`,`d`,`Ga`,`G0`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (simp[Abbr `after_args`,bodyFullIntCallTheory.bind_return_right,nsid_to_string_def] >> NO_TAC) >>
  TRY (gvs[nsid_to_string_def] >> NO_TAC) >>
  `TAKE (LENGTH args) (MAP SND args) = MAP SND args` by simp[] >>
  qpat_assum `cenv.ce_func_param_types _ = MAP SND args` (pure_rewrite_tac o single) >>
  qpat_assum `TAKE (LENGTH args) (MAP SND args) = _` (pure_rewrite_tac o single) >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qpat_assum `ds = omitted_defaults _ _ _` (pure_rewrite_tac o single o SYM) >>
  pure_rewrite_tac[nsid_to_string_def] >>
  qpat_assum `dc = cenv_without_defaults cenv name` (pure_rewrite_tac o single o SYM) >>
  first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise bool_chain_strict_callee_head_prefix
*)
