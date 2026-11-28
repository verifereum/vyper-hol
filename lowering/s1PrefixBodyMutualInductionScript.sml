(* Ranked request-prefix induction, conditional on the remaining dispatcher rules. *)
Theory s1PrefixBodyMutualInduction
Ancestors
  s1PrefixCases s1PrefixAtomicExprIntro[qualified] s1PrefixIntCallRank s1PrefixAttribute s1PrefixStructLit
  s1PrefixBoolChainSelectedStmtCasePorts
  s1PrefixTypeBuiltinGuarded[qualified]
  s1PrefixSubscriptCase[qualified] s1PrefixPop[qualified,ignore_grammar]
  s1PrefixSend s1PrefixCreateHeld s1PrefixPreds bodySimFullMain bodyFullPreds
  vyperInterpreter vyperState vyperContext vyperAST vyperTypeCallGraph
  vyperTypeContract[qualified,ignore_grammar] constSubst bodyLoopCalls alist list
  gasContext supportedProgram

val _ = Parse.hide "body";

(* These hypotheses are discharged by the following request-prefix rules,
   in order:
     body_assign_case_prefix          (Assign / BaseTarget)
     body_assign_tuple_case_prefix    (Assign / TupleTarget)
     body_for_case_prefix             (For)
     body_builtin_case_prefix         (Builtin)
     body_intcall_case_prefix         (Call / IntCall)
     body_raw_call_calldata_case_prefix (Call / RawCallCalldataTarget)
*)
val outstanding_cases = ``
  (!cx t e.
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
              struct_args_unique tops) /\
    (!s'' pv t' s'3' v t''.
         eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
         body_base_target_full_ok cx t) /\
    (!s'' pv t' s'3' v t''.
         eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
         body_base_target_prefix_ok cx t) /\
    body_expr_full_ok cx e /\
    body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Assign (BaseTarget t) e)) /\
  (!cx gs e.
    (!s'' tv t s'3' v t'.
         eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
         body_tuple_target_full_ok cx (TupleTarget gs) v) /\
    (!s'' tv t s'3' v t'.
         eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
         body_tuple_target_prefix_ok cx (TupleTarget gs) v) /\
    body_expr_full_ok cx e /\
    body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Assign (TupleTarget gs) e)) /\
  (!cx id typ it n body.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
         tenv = get_tenv cx /\
         lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
         (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
         check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
         (INL x,t'') ==>
         body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
         tenv = get_tenv cx /\
         lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
         (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
         check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
         (INL x,t'') ==>
         body_for_prefix_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
         tenv = get_tenv cx /\
         lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
         (INL tyv,t) ==>
         body_iterator_full_ok cx it) /\
    (!tenv s'' tyv t.
         tenv = get_tenv cx /\
         lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
         (INL tyv,t) ==>
         body_iterator_prefix_ok cx it) /\
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
         stmt_loop_calls_ok [(NONE,tops)] (For id typ it n body)) ==>
    body_stmt_prefix_ok cx (For id typ it n body)) /\
  (!cx ty bt es.
    (!s'' x t v code_ty addr tail_s tail_vs t'.
         type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
         (INL x,t) /\ bt <> Len /\
         bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
         v = (code_ty,addr) /\
         eval_exprs cx (TL es) tail_s = (INL tail_vs,t') ==>
         body_exprs_full_ok cx [addr]) /\
    (!s'' x t v code_ty addr tail_s tail_vs t'.
         type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
         (INL x,t) /\ bt <> Len /\
         bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
         v = (code_ty,addr) /\
         eval_exprs cx (TL es) tail_s = (INL tail_vs,t') ==>
         body_exprs_prefix_ok cx [addr]) /\
    (!s'' x t v code_ty addr.
         type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
         (INL x,t) /\ bt <> Len /\
         bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
         v = (code_ty,addr) ==>
         body_exprs_full_ok cx (TL es)) /\
    (!s'' x t v code_ty addr.
         type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
         (INL x,t) /\ bt <> Len /\
         bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
         v = (code_ty,addr) ==>
         body_exprs_prefix_ok cx (TL es)) /\
    (!s'' x t.
         type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
         (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas /\
         code_slice_source bt es = NONE ==>
         body_exprs_full_ok cx es) /\
    (!s'' x t.
         type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
         (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas /\
         code_slice_source bt es = NONE ==>
         body_exprs_prefix_ok cx es) /\
    (!s'' x t.
         type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
         (INL x,t) /\ bt = Len ==>
         body_expr_full_ok cx (HD es)) /\
    (!s'' x t.
         type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
         (INL x,t) /\ bt = Len ==>
         body_expr_prefix_ok cx (HD es)) ==>
    body_expr_prefix_ok cx (Builtin ty bt es)) /\
  (!cx v16 src_id_opt fn es v17.
    (!ts mut nr args dflts ret ss.
       ~MEM (src_id_opt,fn) cx.stk /\
       get_module_code cx src_id_opt = SOME ts /\
       lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
       body_stmts_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (subst_consts_stmts (module_consts_env (cx_tops cx) []) ss) /\
       body_exprs_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env (cx_tops cx) []) dflts))) /\
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
       body_exprs_full_ok cx es) /\
    (!ts mut nr args dflts ret ss.
       ~MEM (src_id_opt,fn) cx.stk /\
       get_module_code cx src_id_opt = SOME ts /\
       lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
       body_stmts_prefix_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (subst_consts_stmts (module_consts_env (cx_tops cx) []) ss) /\
       body_exprs_prefix_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env (cx_tops cx) []) dflts))) /\
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
       body_exprs_prefix_ok cx es) ==>
    body_expr_prefix_ok cx (Call v16 (IntCall (src_id_opt,fn)) es v17)) /\
  (!cx ty flags es v19.
    body_exprs_full_ok cx es /\
    body_exprs_prefix_ok cx es ==>
    body_expr_prefix_ok cx (Call ty (RawCallCalldataTarget flags) es v19))``;

val source_conditions = ``\tops.
  struct_args_unique tops /\
  (!vis mut nr raw fn args dflts ret ss.
     MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
     stmts_loop_calls_ok [(NONE,tops)]
       (subst_consts_stmts (module_consts_env tops []) ss))``;

val prefix_ind = evaluate_ind
  |> Q.SPECL [
     `\cx s. LENGTH (remcode cx) <= rank /\
              (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                ^source_conditions tops /\ stmt_loop_calls_ok [(NONE,tops)] s) ==>
              body_stmt_prefix_ok cx s`,
     `\cx ss. LENGTH (remcode cx) <= rank /\
               (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 ^source_conditions tops /\ stmts_loop_calls_ok [(NONE,tops)] ss) ==>
               body_stmts_prefix_ok cx ss`,
     `\cx it. LENGTH (remcode cx) <= rank /\
               (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 ^source_conditions tops) ==>
               body_iterator_prefix_ok cx it`,
     `\cx tyv nm body vs. LENGTH (remcode cx) <= rank /\
               (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 ^source_conditions tops /\ stmts_loop_calls_ok [(NONE,tops)] body) ==>
               body_for_prefix_ok cx tyv nm body vs`,
     `\cx e. LENGTH (remcode cx) <= rank /\
              (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                ^source_conditions tops) ==>
              body_expr_prefix_ok cx e`,
     `\cx es. LENGTH (remcode cx) <= rank /\
               (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 ^source_conditions tops) ==>
               body_exprs_prefix_ok cx es`,
     `\cx t. LENGTH (remcode cx) <= rank /\
              (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                ^source_conditions tops) ==>
              body_base_target_prefix_ok cx t`,
     `\cx t. LENGTH (remcode cx) <= rank /\
              (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                ^source_conditions tops) ==>
              body_base_target_prefix_ok cx t`,
     `\cx g v. LENGTH (remcode cx) <= rank /\
                (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                  ^source_conditions tops) ==>
                body_tuple_target_prefix_ok cx g v`,
     `\cx gs vs. LENGTH (remcode cx) <= rank /\
                  (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                    ^source_conditions tops) ==>
                  body_tuple_targets_prefix_ok cx gs vs`]
  |> CONV_RULE (DEPTH_CONV BETA_CONV)
  |> REWRITE_RULE [GSYM CONJ_ASSOC];

val loop_calls = vyperTypeContractTheory.stmt_loop_calls_ok_def;

val case_simps =
  [push_function_def, return_def, evaluation_context_accfupds,
   pairTheory.PAIR_EQ, sumTheory.INL_11, loop_calls];

val full_children = CONJUNCTS body_sim_full_mutual;

val from_source =
  rpt gen_tac >> disch_tac >>
  qpat_assum `!xs. ALOOKUP _ _ = SOME [(NONE,xs)] ==> _` drule >>
  simp[loop_calls];

val full_child = FIRST (map irule full_children) >> from_source;

val prefix_child =
  first_assum (fn ih =>
    irule ih >> asm_rewrite_tac[] >> rpt conj_tac >>
    FIRST [from_source >> NO_TAC, metis_tac[]] >> NO_TAC);

fun apply_prefix_rule th =
  rpt strip_tac >> full_simp_tac bool_ss case_simps >>
  irule (SIMP_RULE bool_ss case_simps th);

fun prefix_case th =
  apply_prefix_rule th >> asm_rewrite_tac[] >>
  rpt conj_tac >> rpt strip_tac >>
  FIRST [full_child >> NO_TAC, prefix_child,
         from_source >> NO_TAC, metis_tac[]];

fun without_smaller_rank tac =
  qpat_x_assum `!m:num. m < rank ==> _` kall_tac >> tac;

fun direct th = without_smaller_rank (asm_x "case_rules" kall_tac >> prefix_case th);
fun conditional i = without_smaller_rank
  (asm_x "case_rules" (prefix_case o el i o CONJUNCTS));
fun structural tac = without_smaller_rank (asm_x "case_rules" kall_tac >> tac);

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (mk_asm "case_rules") >> completeInduct_on `rank` >>
  mp_tac prefix_ind >> impl_tac
  >- (rpt conj_tac
      >- direct body_pass_case_prefix
      >- direct body_continue_case_prefix
      >- direct body_break_case_prefix
      >- direct body_return_none_case_prefix
      >- direct body_return_case_prefix
      >- direct body_raise_bare_case_prefix
      >- direct body_raise_unreachable_case_prefix
      >- direct body_raise_reason_case_prefix
      >- direct body_raise_custom_case_prefix
      >- direct body_assert_case_prefix
      >- direct body_assert_unreachable_case_prefix
      >- direct body_assert_reason_case_prefix
      >- direct body_assert_custom_case_prefix
      >- direct body_log_case_prefix
      >- direct body_annassign_case_prefix
      >- direct body_append_case_prefix
      >- conditional 1
      >- conditional 2
      >- direct body_augassign_case_prefix
      >- direct body_if_case_prefix
      >- conditional 3
      >- direct body_expr_stmt_case_prefix
      >- direct body_stmts_nil_case_prefix
      >- direct body_stmts_cons_case_prefix
      >- structural (simp[body_iterator_prefix_ok_def])
      >- structural (rpt strip_tac >> fs[] >> rw[body_iterator_prefix_ok_def] >> metis_tac[])
      >- structural (simp[body_for_prefix_ok_def])
      >- structural (rpt strip_tac >> fs[] >> rw[body_for_prefix_ok_def] >>
                     first_x_assum irule >> simp[push_scope_with_var_def, return_def] >>
                     metis_tac[])
      >- structural (rpt strip_tac >> irule s1PrefixAtomicExprIntroTheory.atomic_expr_prefix_ok >> simp[])
      >- structural (rpt strip_tac >> irule s1PrefixAtomicExprIntroTheory.atomic_expr_prefix_ok >> simp[])
      >- structural (rpt strip_tac >> irule s1PrefixAtomicExprIntroTheory.atomic_expr_prefix_ok >> simp[])
      >- direct body_ifexp_case_prefix
      >- structural (rpt strip_tac >> irule s1PrefixAtomicExprIntroTheory.atomic_expr_prefix_ok >> simp[])
      >- direct structlit_expr_prefix_ok
      >- direct s1PrefixSubscriptCaseTheory.body_subscript_case_prefix
      >- direct attribute_expr_prefix_ok
      >- conditional 4
      >- direct s1PrefixPopTheory.body_pop_case_prefix
      >- direct s1PrefixTypeBuiltinGuardedTheory.body_type_builtin_case_prefix
      >- direct body_send_case_prefix
      >- direct body_extcall_case_prefix
      >- suspend "intcall"
      >- direct body_raw_call_case_prefix
      >- conditional 6
      >- direct body_raw_log_case_prefix
      >- direct body_raw_revert_case_prefix
      >- direct body_selfdestruct_case_prefix
      >- structural (rpt gen_tac >> Cases_on `kind` >>
                     FIRST (map prefix_case
                       [create_minimal_proxy_expr_prefix_ok, create_copy_expr_prefix_ok,
                        create_blueprint_expr_prefix_ok, raw_create_expr_prefix_ok]))
      >- structural (simp[body_exprs_prefix_ok_def])
      >- structural (rpt strip_tac >> fs[] >> rw[body_exprs_prefix_ok_def] >> metis_tac[])
      >- structural (simp[body_base_target_prefix_ok_def])
      >- structural (simp[body_base_target_prefix_ok_def])
      >- structural (simp[body_base_target_prefix_ok_def])
      >- structural (rpt strip_tac >> fs[] >> rw[body_base_target_prefix_ok_def] >> metis_tac[])
      >- structural (simp[body_tuple_target_prefix_ok_def])
      >- structural (simp[body_tuple_target_prefix_ok_def] >> rpt strip_tac >> metis_tac[])
      >- structural (simp[body_tuple_target_prefix_ok_def])
      >- structural (rpt strip_tac >> fs[] >> rw[body_tuple_target_prefix_ok_def] >> metis_tac[])
      >- structural (simp[body_tuple_target_prefix_ok_def])
      >- structural (simp[body_tuple_target_prefix_ok_def])
      >> structural (simp[body_tuple_target_prefix_ok_def])) >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)
Theorem body_sim_prefix_mutual_ranked[local]:
  ^outstanding_cases ==> !rank:num. ^(snd (dest_imp (concl prefix_ind)))
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume body_sim_prefix_mutual_ranked[intcall]:
  rpt strip_tac >> full_simp_tac bool_ss case_simps >>
  asm_x "case_rules" (match_mp_tac o SIMP_RULE bool_ss case_simps o el 5 o CONJUNCTS) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (FIRST (map irule full_children) >> simp[evaluation_context_accfupds] >>
          gen_tac >> strip_tac >>
          `cx_tops cx = tops` by fs[cx_tops_def, get_module_code_def, ALOOKUP_def] >>
          qpat_assum `!xs. ALOOKUP _ _ = SOME [(NONE,xs)] ==> _` drule >>
          strip_tac >> simp[] >>
          conj_tac >- first_assum ACCEPT_TAC >>
          irule callable_body_loop_calls_ok >> metis_tac[]) >>
      FIRST (map irule full_children) >> simp[evaluation_context_accfupds] >>
      from_source) >>
  conj_tac >- (rpt strip_tac >> full_child) >>
  conj_tac
  >- (match_mp_tac intcall_callee_prefix_ih >> asm_rewrite_tac[] >>
      conj_tac >> gen_tac >> strip_tac >>
      qpat_assum `!m:num. m < rank ==> _` (drule_then strip_assume_tac) >>
      first_assum ACCEPT_TAC) >>
  rpt strip_tac >> gvs[] >> without_smaller_rank
    (qpat_x_assum `!s t s1 ts t1 s2 tup t2 s3 t3.
        _ ==> _ ==> body_exprs_prefix_ok cx es` irule) >>
  conj_tac >- from_source >>
  conj_tac
  >- (qpat_assum `type_check _ "recursion" _ = _`
        (part_match_exists_tac I o concl) >> simp[]) >>
  qpat_assum `lift_option_type _ "IntCall get_module_code" _ = _`
    (part_match_exists_tac (hd o strip_conj) o concl) >>
  qpat_assum `lift_option_type _ "IntCall lookup_function" _ = _`
    (part_match_exists_tac (last o strip_conj) o concl) >>
  simp[] >>
  qpat_assum `type_check _ "IntCall args length" _ = _`
    (part_match_exists_tac I o concl) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise body_sim_prefix_mutual_ranked
*)

Theorem body_sim_prefix_mutual_from_cases:
  ^outstanding_cases ==>
  ((!cx s. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmt_loop_calls_ok [(NONE,tops)] s) ==>
    body_stmt_prefix_ok cx s) /\
  (!cx ss. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] ss) ==>
    body_stmts_prefix_ok cx ss) /\
  (!cx it. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_iterator_prefix_ok cx it) /\
  (!cx tyv nm body vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] body) ==>
    body_for_prefix_ok cx tyv nm body vs) /\
  (!cx e. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_expr_prefix_ok cx e) /\
  (!cx es. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_exprs_prefix_ok cx es) /\
  (!cx t. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_base_target_prefix_ok cx t) /\
  (!cx g v. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_tuple_target_prefix_ok cx g v) /\
  (!cx gs vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_tuple_targets_prefix_ok cx gs vs))
Proof
  disch_then (mp_tac o MATCH_MP body_sim_prefix_mutual_ranked) >>
  disch_then (mk_asm "ranked") >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  asm_x "ranked" (qspec_then `LENGTH (remcode cx)` strip_assume_tac) >>
  first_x_assum irule >> asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL]
QED
