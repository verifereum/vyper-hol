(* Piece of bodySimCallCases.body_intcall_case. *)

Theory bodySimCallIntcall
Ancestors
  bodyIntCallSeams bodyIntCallSource bodySimExprCases exprSimHypsDefs exprSimDefs
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph exprSimSend exprLowering context
  exprSimUnwrap exprSimMemoryRead
  exprSimMemorySource exprSimProps exprLoweringProps gasOutcome gasSummary
  gasSummaryCompose gasExemptCert gasContext fragGasPath fragGasMode fragExec
  venomState compileEnv exprSimUnwrapProps

(* The IHs at a supported callee (body_intcall_source_selection): not
   nonreentrant, no defaults, as many arguments as parameters. *)
Theorem intcall_results_ih[local]:
  !cx src_id_opt fn es ts mut args ret ss.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') ==>
       body_results_ok cx es) /\
    get_module_code cx src_id_opt = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (mut,F,args,[],ret,ss) /\
    LENGTH es = LENGTH args /\ ~MEM (src_id_opt,fn) cx.stk ==>
    body_results_ok cx es
Proof
  rpt strip_tac >> first_x_assum irule >>
  simp[type_check_def, assert_def, lift_option_type_def, return_def]
QED

Theorem intcall_body_ih[local]:
  !cx src_id_opt fn es ts mut args ret ss s1 results t1 s2 vs t2 penv rtv.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7' prev
         t'5' s'8' dflt_vs t'6' s'9' vs t'7' all_tenv s'10' env t'8' s'11' rtv
         t'9' is_view s'12' x'' t'10' s'13' cxf t'11'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_expr_results cx es s'6' = (INL results,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       finally
         (ignore_bind (set_scopes [FEMPTY]) (eval_exprs cxd needed_dflts))
         (set_scopes prev) s'8' = (INL dflt_vs,t'6') /\
       read_results cx results s'9' = (INL vs,t'7') /\
       all_tenv = get_tenv cx /\
       lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
         "IntCall bind_arguments" s'10' = (INL env,t'8') /\
       lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'11' =
       (INL rtv,t'9') /\ (is_view <=> is_view_mut mut) /\
       lock_if_nr cx nr is_view s'12' = (INL x'',t'10') /\
       push_function (src_id_opt,fn) env cx s'13' = (INL cxf,t'11') ==>
       body_stmts_ok cxf body') /\
    get_module_code cx src_id_opt = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (mut,F,args,[],ret,ss) /\
    LENGTH es = LENGTH args /\ ~MEM (src_id_opt,fn) cx.stk /\
    eval_expr_results cx es s1 = (INL results,t1) /\
    read_results cx results s2 = (INL vs,t2) /\
    bind_arguments (get_tenv cx) args vs = SOME penv /\
    evaluate_type (get_tenv cx) ret = SOME rtv ==>
    body_stmts_ok (cx with stk updated_by CONS (src_id_opt,fn)) ss
Proof
  rpt strip_tac >> first_x_assum irule >>
  simp[type_check_def, assert_def, lift_option_type_def, return_def,
       get_scopes_def, finally_def, ignore_bind_def, bind_def,
       set_scopes_def, lock_if_nr_def, push_function_def,
       Once evaluate_def] >>
  qexistsl_tac [`penv`,`results`,`s1`,`s2`,`s2`,`t1`,`t2`,`s2`,`vs`] >>
  simp[return_def]
QED

Theorem compile_expr_intcall_location[local]:
  !cenv ty ann src name args dflt sa vv sb.
    compile_expr cenv ty (Call ann (IntCall (src,name)) args dflt) sa =
      (vv,sb) ==>
    ((?t op. vv = StackValue t op) \/
     (?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory))
Proof
  rpt gen_tac >> simp[compile_expr_call, compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[AllCaseEqs(), base_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem expr_sim_of_vv_sim_stack_memory[local]:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es /\
    (!sa vv sm. compile_expr cenv ty e sa = (vv,sm) ==>
      ((?t op. vv = StackValue t op) \/
       (?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory))) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv,sm)` >>
  simp[] >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >> simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_at_def]
      >- (`~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          qpat_x_assum `!sa vv sm. compile_expr _ _ _ _ = _ ==> _` drule >>
          strip_tac >> gvs[]
          >- (gvs[unwrap_value_def, comp_return_def] >>
              `?v. read_result cx tv (es_end with gas_obs := []) =
                   (INL v,es_end with gas_obs := [])` by
                gvs[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def] >>
              `vv_post ctx func cenv cx e es sa sb s0
                (es_end with gas_obs := []) (Value v) (StackValue t' op) t` by
                metis_tac[vv_post_read_result] >>
              qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK t`] >>
              simp[] >> conj_tac
              >- (drule read_result_gas_obs >> strip_tac >>
                  gvs[gas_marked_exec_def, vyperStateTheory.bind_def]) >>
              metis_tac[expr_post_of_vv_post_stack]) >>
          drule_all unwrap_memory_marked_read >> simp[] >> strip_tac >>
          qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK u`] >>
          simp[] >>
          `marks = marks ++ []` by simp[] >>
          pop_assum SUBST1_TAC >> irule gas_marked_exec_bind_normal >>
          goal_assum drule >> simp[]) >>
      Cases_on `res`
      >- (Cases_on `r` >> gvs[expr_exit_def]) >>
      rename1 `expr_exit (INR exc) r` >>
      `expr_res_ok (INR exc : value + exception)` by
        (Cases_on `exc` >> Cases_on `r` >>
         gvs[expr_exit_def, expr_res_ok_def, AllCaseEqs()] >>
         Cases_on `e'` >> gvs[expr_exit_def, expr_res_ok_def]) >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      simp[GSYM expr_exit_exception_transport] >>
      irule gas_marked_exec_bind_exception >> goal_assum drule) >>
  disj2_tac >> metis_tac[force_exempt_cert]
QED

(* A widened internal call is laid out at the callee's return type.
   Its stack/memory result needs no post-value/annotation equality to force. *)
Theorem intcall_sim_case_widened:
  !ctx func cenv cx ann src name es dflt.
    post_value_type cenv (Call ann (IntCall (src,name)) es dflt) <>
      expr_type (Call ann (IntCall (src,name)) es dflt) /\
    expr_vv_case F ctx func cenv cx (Call ann (IntCall (src,name)) es dflt) ==>
    expr_sim_case F ctx func cenv cx (Call ann (IntCall (src,name)) es dflt)
Proof
  pure_rewrite_tac[expr_sim_case_def, expr_vv_case_def] >>
  rpt strip_tac >> irule expr_sim_of_vv_sim_stack_memory >>
  conj_tac >- metis_tac[compile_expr_intcall_location] >>
  metis_tac[]
QED

(* GAP (#638 the call step): the INVOKE of an internal call.  The IHs
   give the arguments' judgments (body_results_ok), the defaults' at the
   callee's stack (body_exprs_ok), and the callee body's (body_stmts_ok
   at cxf, the callee's context after push_function).  The step:
   - compile_call: intCallStep's compile_call_intcall_shape, the INVOKE
     label by intCallLookup's compile_call_intcall_label (body_inv gives
     its premises), and the callee's code in ctx by
     lower_vyper_runtime_unit_internal_lookup;
   - the arguments: the IH, then intCallArgs' stage_mem_arg_frag for
     the staged memory arguments;
   - the callee's entry: intCallCallee's compile_internal_prologue_entry
     gives stmt_state_rel at the callee's start, at
     vs with scopes := [env];
   - the callee's body: the IH at the callee's compile env, with RetQ
     intret_q (stack returns) or intret_mem_q (memory returns), whose
     frame_ret_ok stmtSimReturn's compile_return_word_int_frag and
     compile_return_tuple_int_frag and intCallReturnMem's
     compile_internal_return_memory_frag give;
   - the return: intCallStep's frag_exec_invoke_intret, intCallReturn's
     eval_expr_intcall_return (source) and invoke_intret_state_rel
     (Venom), with intCallFrame's callee_writes_above for the caller's
     live regions, and intCallResult's store_multi_results_frag for
     stack results.
   Left (the push transfer): the callee body's premises at its entry:
   body_inv (whose target conjunct needs the callee's compile env at the
   unit's policy target, as set_*_package_target installs it) and
   expr_sim_inv for the callee's compile env and env at cxf, and
   frame_ret_ok for the internal return; and that the callee
   body's code in ctx is stmts_env's in that compile env.
   ce_locals_declared there is bodySimEntry's internal_entry_declared and
   ce_locals_declared_params, for an env that has the parameters; the
   body's locals_alloc_ok and stmt_exprs_ok's alloc_limits_stmt come from
   fn_allocs_ok_body. *)
Theorem intcall_body_expr_ok:
  !cx v16 src_id_opt fn es v17.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7' prev
         t'5' s'8' dflt_vs t'6' s'9' vs t'7' all_tenv s'10' env t'8' s'11' rtv
         t'9' is_view s'12' x'' t'10' s'13' cxf t'11'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_expr_results cx es s'6' = (INL results,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       finally
         (ignore_bind (set_scopes [FEMPTY]) (eval_exprs cxd needed_dflts))
         (set_scopes prev) s'8' = (INL dflt_vs,t'6') /\
       read_results cx results s'9' = (INL vs,t'7') /\
       all_tenv = get_tenv cx /\
       lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
         "IntCall bind_arguments" s'10' = (INL env,t'8') /\
       lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'11' =
       (INL rtv,t'9') /\ (is_view <=> is_view_mut mut) /\
       lock_if_nr cx nr is_view s'12' = (INL x'',t'10') /\
       push_function (src_id_opt,fn) env cx s'13' = (INL cxf,t'11') ==>
       body_stmts_ok cxf body') /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7' prev
         t'5' s'8' x'' t'6'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_expr_results cx es s'6' = (INL results,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       set_scopes [FEMPTY] s'8' = (INL x'',t'6') ==>
       body_exprs_ok cxd needed_dflts) /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') ==>
       body_results_ok cx es) ==>
    body_expr_ok cx (Call v16 (IntCall (src_id_opt,fn)) es v17)
Proof
  rpt strip_tac >> irule body_expr_ok_of_case >> rpt gen_tac >> strip_tac >>
  `expr_vv_case F ctx func cenv cx (Call v16 (IntCall (src_id_opt,fn)) es v17)`
    suffices_by
      (strip_tac >> conj_tac >- (
         Cases_on `post_value_type cenv (Call v16 (IntCall (src_id_opt,fn)) es v17) =
                   expr_type (Call v16 (IntCall (src_id_opt,fn)) es v17)`
         >- (irule expr_sim_case_of_vv >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
         irule intcall_sim_case_widened >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
       first_assum ACCEPT_TAC) >>
  simp[expr_vv_case_def] >> rpt gen_tac >> strip_tac >>
  rename1 `expr_body_pre cenv cx tenv _ es0` >>
  drule_all body_intcall_source_selection >> strip_tac >>
  `~MEM (src_id_opt,fn) cx.stk ==> body_results_ok cx es` by
    (strip_tac >> drule intcall_results_ih >> disch_then drule_all >> simp[]) >>
  `!s1 results t1 s2 vs t2 penv rtv.
     ~MEM (src_id_opt,fn) cx.stk /\
     eval_expr_results cx es s1 = (INL results,t1) /\
     read_results cx results s2 = (INL vs,t2) /\
     bind_arguments (get_tenv cx) args vs = SOME penv /\
     evaluate_type (get_tenv cx) ret = SOME rtv ==>
     body_stmts_ok (cx with stk updated_by CONS (src_id_opt,fn)) ss` by
    (rpt strip_tac >> drule intcall_body_ih >> disch_then drule_all >>
     simp[]) >>
  gvs[] >>
  simp[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  `?nrc nrbs npvs.
     cenv.ce_func_info (nsid_to_string (NONE,fn)) = (nrc,nrbs,npvs)`
    by metis_tac[pairTheory.ABS_PAIR_THM] >>
  irule intcall_args_frame_setup >> simp[] >>
  qexistsl_tac [`args`,`cenv`,`mut`,`ret`,`rr`,`sa`,`sb`,`ss`,`tenv`,`tops`,
                `ty`,`vv`] >>
  simp[] >> rpt strip_tac >>
  qspecl_then [`tops`,`ctx`,`func`,`cenv`,`cx`,`tenv`,`ty`,`v16`,`fn`,`es`,
               `v17`,`es0`,`sa`,`sb`,`vv`,`s0`,`mut`,`args`,`ret`,`ss`,`rr`,
               `prev`,`penv`,`rtv`,`es1`,`t`,`nrc`,`nrbs`,`npvs`]
    mp_tac intcall_return_restore >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      drule intcall_entry_source >> strip_tac >>
      `body_stmts_ok (cx with stk updated_by CONS (NONE,fn)) ss` by
        metis_tac[] >>
      drule_all intcall_callee_body_sim >> simp[]) >>
  simp[]
QED
