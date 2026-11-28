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
  gasContext supportedProgram s1PrefixSyntaxCalls bodyCallLiveness rich_list
  bodyStorageCases[qualified] vyperCreate[qualified]

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
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
        (vyperTypeCallGraph$int_calls_expr (Builtin ty bt es))) /\
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

val source_conditions = ``\cx tops.
  IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
  struct_args_unique tops /\
  (!vis mut nr raw fn args dflts ret ss.
     MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
     stmts_loop_calls_ok [(NONE,tops)]
       (subst_consts_stmts (module_consts_env tops []) ss))``;

val prefix_ind = evaluate_ind
  |> Q.SPECL [
     `\cx s. LENGTH (remcode cx) <= rank /\
              (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                ^source_conditions cx tops /\
                EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                  (vyperTypeCallGraph$int_calls_stmt s) /\ stmt_loop_calls_ok [(NONE,tops)] s) ==>
              body_stmt_prefix_ok cx s`,
     `\cx ss. LENGTH (remcode cx) <= rank /\
               (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 ^source_conditions cx tops /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_stmts ss) /\ stmts_loop_calls_ok [(NONE,tops)] ss) ==>
               body_stmts_prefix_ok cx ss`,
     `\cx it. LENGTH (remcode cx) <= rank /\
               (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 ^source_conditions cx tops /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_iterator it)) ==>
               body_iterator_prefix_ok cx it`,
     `\cx tyv nm body vs. LENGTH (remcode cx) <= rank /\
               (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 ^source_conditions cx tops /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_stmts body) /\ stmts_loop_calls_ok [(NONE,tops)] body) ==>
               body_for_prefix_ok cx tyv nm body vs`,
     `\cx e. LENGTH (remcode cx) <= rank /\
              (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                ^source_conditions cx tops /\
                EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                  (vyperTypeCallGraph$int_calls_expr e)) ==>
              body_expr_prefix_ok cx e`,
     `\cx es. LENGTH (remcode cx) <= rank /\
               (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 ^source_conditions cx tops /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_exprs es)) ==>
               body_exprs_prefix_ok cx es`,
     `\cx t. LENGTH (remcode cx) <= rank /\
              (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                ^source_conditions cx tops /\
                EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                  (vyperTypeCallGraph$int_calls_target t)) ==>
              body_base_target_prefix_ok cx t`,
     `\cx t. LENGTH (remcode cx) <= rank /\
              (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                ^source_conditions cx tops /\
                EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                  (vyperTypeCallGraph$int_calls_target t)) ==>
              body_base_target_prefix_ok cx t`,
     `\cx g v. LENGTH (remcode cx) <= rank /\
                (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                  ^source_conditions cx tops /\
                  EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                    (vyperTypeCallGraph$int_calls_atarget g)) ==>
                body_tuple_target_prefix_ok cx g v`,
     `\cx gs vs. LENGTH (remcode cx) <= rank /\
                  (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                    ^source_conditions cx tops /\
                    EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                      (vyperTypeCallGraph$int_calls_atargets gs)) ==>
                  body_tuple_targets_prefix_ok cx gs vs`]
  |> CONV_RULE (DEPTH_CONV BETA_CONV)
  |> REWRITE_RULE [GSYM CONJ_ASSOC];

val loop_calls = vyperTypeContractTheory.stmt_loop_calls_ok_def;

val case_simps =
  [push_function_def, return_def, evaluation_context_accfupds,
   pairTheory.PAIR_EQ, sumTheory.INL_11, loop_calls];

val full_children = CONJUNCTS body_sim_full_mutual;

val syntax_calls =
  [int_calls_stmt_def, int_calls_expr_def, int_calls_iterator_def,
   int_calls_atarget_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
   GSYM vyperTypeEvalProofsTheory.int_calls_exprs_MAP_SND, EVERY_APPEND];

Theorem int_calls_window[local]:
  EVERY P (int_calls_exprs xs) ==>
  EVERY P (int_calls_exprs (TAKE n xs)) /\
  EVERY P (int_calls_exprs (DROP n xs)) /\
  EVERY P (int_calls_exprs (TAKE m (DROP n xs)))
Proof
  simp[int_calls_exprs_members] >> metis_tac[MEM_TAKE, MEM_DROP_IMP]
QED

Theorem int_calls_create_operands[local]:
  EVERY P (int_calls_exprs es) ==>
  EVERY P (int_calls_exprs (create_operand_order kind has_salt es))
Proof
  Cases_on `kind` >> Cases_on `es` >>
  simp[vyperCreateTheory.create_operand_order_def,
       bodyStorageCasesTheory.body_exprs_main_calls_every,
       EVERY_APPEND, EVERY_TAKE, EVERY_DROP] >>
  Cases_on `t` >> simp[vyperCreateTheory.create_operand_order_def,
       EVERY_APPEND, EVERY_TAKE, EVERY_DROP]
QED

val operand_calls =
  int_calls_create_operands ::
  map (DISCH (lhand (concl int_calls_window))) (CONJUNCTS (UNDISCH int_calls_window));

val inherited_operand_calls =
  FIRST (map (fn th => match_mp_tac (GEN_ALL th) >> first_assum ACCEPT_TAC >> NO_TAC) operand_calls);

val from_source =
  TRY (rpt gen_tac >> disch_tac) >>
  qpat_assum `!xs. ALOOKUP _ _ = SOME [(NONE,xs)] ==> _`
    (drule_then strip_assume_tac) >>
  fs (loop_calls :: syntax_calls) >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY inherited_operand_calls >>
  TRY (drule_all_then (fn th => ACCEPT_TAC (CONJUNCT1 th) ORELSE
      ACCEPT_TAC (CONJUNCT2 th)) code_slice_source_calls >> NO_TAC) >>
  drule_all_then ACCEPT_TAC ordered_custom_error_calls;

val full_child = FIRST (map irule full_children) >> from_source;

val prefix_child =
  TRY (qpat_x_assum `err = CustomError _ _ _` SUBST_ALL_TAC) >>
  first_assum (fn ih =>
    irule ih >> asm_rewrite_tac[] >> rpt conj_tac >>
    TRY (from_source >> NO_TAC) >>
    rpt (goal_assum (drule_at Any)) >> fs[] >> NO_TAC);

fun apply_prefix_rule th =
  rpt strip_tac >> full_simp_tac bool_ss case_simps >>
  irule (SIMP_RULE bool_ss case_simps th);

fun prefix_case th =
  apply_prefix_rule th >> asm_rewrite_tac[] >>
  rpt conj_tac >> rpt strip_tac >>
  FIRST [full_child >> NO_TAC, prefix_child,
         from_source];

fun without_smaller_rank tac =
  qpat_x_assum `!m:num. m < rank ==> _` kall_tac >> tac;

fun direct th = without_smaller_rank (asm_x "case_rules" kall_tac >> prefix_case th);
fun conditional i = without_smaller_rank
  (asm_x "case_rules" (prefix_case o el i o CONJUNCTS));
fun structural tac = without_smaller_rank (asm_x "case_rules" kall_tac >> tac);

Theorem body_sim_prefix_mutual_ranked[local]:
  ^outstanding_cases ==> !rank:num. ^(snd (dest_imp (concl prefix_ind)))
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
      >- structural (simp[body_iterator_prefix_ok_def, int_calls_iterator_def] >> metis_tac[])
      >- structural (rpt strip_tac >> fs[] >> rw[body_iterator_prefix_ok_def] >>
                     metis_tac[int_calls_iterator_def, EVERY_APPEND])
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
      >- suspend "builtin"
      >- direct s1PrefixPopTheory.body_pop_case_prefix
      >- direct s1PrefixTypeBuiltinGuardedTheory.body_type_builtin_case_prefix
      >- direct body_send_case_prefix
      >- suspend "extcall"
      >- suspend "intcall"
      >- direct body_raw_call_case_prefix
      >- conditional 6
      >- direct body_raw_log_case_prefix
      >- direct body_raw_revert_case_prefix
      >- direct body_selfdestruct_case_prefix
      >- suspend "create"
      >- structural (simp[body_exprs_prefix_ok_def])
      >- structural (simp[body_exprs_prefix_ok_def, int_calls_expr_def, EVERY_APPEND] >>
                     rpt strip_tac >> metis_tac[])
      >- structural (simp[body_base_target_prefix_ok_def])
      >- structural (simp[body_base_target_prefix_ok_def])
      >- structural (simp[body_base_target_prefix_ok_def, int_calls_expr_def] >> metis_tac[])
      >- structural (simp[body_base_target_prefix_ok_def, int_calls_expr_def, EVERY_APPEND] >>
                     rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[])
      >- structural (simp[body_tuple_target_prefix_ok_def, int_calls_atarget_def] >> metis_tac[])
      >- structural (simp[body_tuple_target_prefix_ok_def, int_calls_atarget_def] >> metis_tac[])
      >- structural (simp[body_tuple_target_prefix_ok_def])
      >- structural (simp[body_tuple_target_prefix_ok_def, int_calls_atarget_def, EVERY_APPEND] >>
                     rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[])
      >- structural (simp[body_tuple_target_prefix_ok_def])
      >- structural (simp[body_tuple_target_prefix_ok_def])
      >> structural (simp[body_tuple_target_prefix_ok_def])) >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_sim_prefix_mutual_ranked[builtin]:
  without_smaller_rank (asm_x "case_rules"
    (apply_prefix_rule o el 4 o CONJUNCTS)) >>
  asm_rewrite_tac[] >>
  rpt conj_tac >> rpt strip_tac >>
  TRY (qpat_x_assum `(v : type # expr) = (code_ty,addr)` SUBST_ALL_TAC) >>
  TRY (qpat_assum `code_slice_source bt es = SOME (_,_)`
         (strip_assume_tac o REWRITE_RULE [code_slice_source_SOME]) >>
       gvs[code_slice_source_def, int_calls_expr_def, EVERY_APPEND]) >>
  TRY (qpat_x_assum `bt = Len` SUBST_ALL_TAC >>
       `LENGTH es = 1` by fs[type_check_def, assert_def, builtin_args_length_ok_def] >>
       gvs[LENGTH_EQ_1]) >>
  FIRST [full_child >> NO_TAC, prefix_child,
         from_source]
QED

Resume body_sim_prefix_mutual_ranked[extcall]:
  without_smaller_rank (asm_x "case_rules" kall_tac) >>
  apply_prefix_rule body_extcall_case_prefix >>
  asm_rewrite_tac[] >>
  rpt conj_tac >> rpt strip_tac >>
  FIRST [full_child >> NO_TAC, prefix_child]
QED

Resume body_sim_prefix_mutual_ranked[create]:
  without_smaller_rank (asm_x "case_rules" kall_tac) >>
  rpt gen_tac >> Cases_on `kind` >>
  FIRST (map apply_prefix_rule
    [create_minimal_proxy_expr_prefix_ok, create_copy_expr_prefix_ok,
     create_blueprint_expr_prefix_ok, raw_create_expr_prefix_ok]) >>
  asm_rewrite_tac[] >>
  rpt conj_tac >> rpt strip_tac >>
  FIRST [full_child >> NO_TAC, prefix_child]
QED

Resume body_sim_prefix_mutual_ranked[intcall]:
  rpt strip_tac >> full_simp_tac bool_ss case_simps >>
  asm_x "case_rules" (match_mp_tac o SIMP_RULE bool_ss case_simps o el 5 o CONJUNCTS) >>
  conj_tac
  >- (qpat_x_assum `!m:num. m < rank ==> _` kall_tac >>
       rpt gen_tac >> strip_tac >> conj_tac >>
       FIRST (map irule full_children) >> simp[evaluation_context_accfupds] >>
       gen_tac >> disch_tac >>
       qpat_assum `!xs. ALOOKUP cx.sources _ = SOME [(NONE,xs)] ==> _`
         (drule_then strip_assume_tac) >>
       qpat_x_assum `EVERY _ (int_calls_expr (Call _ (IntCall _) _ _))`
         (strip_assume_tac o SIMP_RULE bool_ss [int_calls_expr_def, EVERY_DEF]) >>
       `cx_tops cx = tops` by fs[cx_tops_def, get_module_code_def, ALOOKUP_def] >>
       asm_rewrite_tac[] >> rpt conj_tac >>
       TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
       TRY (drule_all_then ACCEPT_TAC callable_body_loop_calls_ok_singleton >> NO_TAC) >>
       Cases_on `src_id_opt` >>
       gvs[get_module_code_def, ALOOKUP_def, optionTheory.IS_SOME_EXISTS] >>
       drule_all_then strip_assume_tac callable_compiled_calls_live >>
       TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
       qpat_assum `!n. EVERY _ (int_calls_exprs (DROP n _))` irule >>
       simp[]) >>
  conj_tac >- without_smaller_rank (rpt strip_tac >> full_child) >>
  conj_tac
  >- (match_mp_tac intcall_callee_prefix_ih >> asm_rewrite_tac[] >>
      conj_tac >- from_source >>
      conj_tac >- from_source >>
      conj_tac >> gen_tac >> disch_tac >>
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

Finalise body_sim_prefix_mutual_ranked

Theorem body_sim_prefix_mutual_from_cases:
  ^outstanding_cases ==>
  ((!cx s. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_stmt s) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmt_loop_calls_ok [(NONE,tops)] s) ==>
    body_stmt_prefix_ok cx s) /\
  (!cx ss. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_stmts ss) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] ss) ==>
    body_stmts_prefix_ok cx ss) /\
  (!cx it. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_iterator it) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_iterator_prefix_ok cx it) /\
  (!cx tyv nm body vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_stmts body) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] body) ==>
    body_for_prefix_ok cx tyv nm body vs) /\
  (!cx e. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_expr e) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_expr_prefix_ok cx e) /\
  (!cx es. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_exprs es) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_exprs_prefix_ok cx es) /\
  (!cx t. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_target t) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_base_target_prefix_ok cx t) /\
  (!cx g v. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_atarget g) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_tuple_target_prefix_ok cx g v) /\
  (!cx gs vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (vyperTypeCallGraph$int_calls_atargets gs) /\
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
  first_x_assum irule >> asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL] >>
  rpt strip_tac >> res_tac >> asm_rewrite_tac[]
QED
