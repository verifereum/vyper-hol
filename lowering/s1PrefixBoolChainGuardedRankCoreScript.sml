(* Rank induction for native operand prefixes, with closed case-rule ports. *)
Theory s1PrefixBoolChainGuardedRankCore
Ancestors
  s1PrefixPreds s1PrefixCheckedContextFull s1PrefixBoolChainHeadMakeArray
  bodySimFullMain bodyFullPreds bodyCallLiveness vyperTypeCallGraph s1PrefixSyntaxCalls vyperInterpreter vyperState vyperContext
  vyperAST vyperTypeContract[qualified,ignore_grammar] constSubst alist list

val _ = Parse.hide "body";

(* The exact statement rows of the prefix dispatcher. *)
val body_pass_case_prefix_port = ``!cx. body_stmt_prefix_ok cx Pass``;
val body_continue_case_prefix_port = ``!cx. body_stmt_prefix_ok cx Continue``;
val body_break_case_prefix_port = ``!cx. body_stmt_prefix_ok cx Break``;
val body_return_none_case_prefix_port = ``!cx. body_stmt_prefix_ok cx (Return NONE)``;
val body_return_case_prefix_port = ``
  !cx e. body_expr_full_ok cx e /\ body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Return (SOME e))``;
val body_raise_bare_case_prefix_port = ``!cx. body_stmt_prefix_ok cx (Raise RaiseBare)``;
val body_raise_unreachable_case_prefix_port = ``!cx. body_stmt_prefix_ok cx (Raise RaiseUnreachable)``;
val body_raise_reason_case_prefix_port = ``
  !cx e. body_expr_full_ok cx e /\ body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Raise (RaiseReason e))``;
val body_raise_custom_case_prefix_port = ``
  !cx err.
  (!id positional kwargs tops params es.
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_full_ok cx es) /\
  (!id positional kwargs tops params es.
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_prefix_ok cx es) ==>
  body_stmt_prefix_ok cx (Raise (RaiseCustomError err))``;
val body_assert_case_prefix_port = ``
  !cx e. body_expr_full_ok cx e /\ body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Assert e AssertBare)``;
val body_assert_unreachable_case_prefix_port = ``
  !cx e. body_expr_full_ok cx e /\ body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Assert e AssertUnreachable)``;
val body_assert_reason_case_prefix_port = ``
  !cx e se.
  (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_full_ok cx se) /\
  (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_prefix_ok cx se) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assert e (AssertReason se))``;
val body_assert_custom_case_prefix_port = ``
  !cx e err.
  (!s tv t id positional kwargs tops params es.
       eval_expr cx e s = (INL tv,t) /\
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_full_ok cx es) /\
  (!s tv t id positional kwargs tops params es.
       eval_expr cx e s = (INL tv,t) /\
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_prefix_ok cx es) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assert e (AssertCustomError err))``;
val body_log_case_prefix_port = ``
  !cx id es. body_exprs_full_ok cx es /\ body_exprs_prefix_ok cx es ==>
    body_stmt_prefix_ok cx (Log id es)``;
val body_annassign_case_prefix_port = ``
  !cx id typ e.
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_prefix_ok cx e) ==>
  body_stmt_prefix_ok cx (AnnAssign id typ e)``;
val body_append_case_prefix_port = ``
  !cx t e.
  (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_full_ok cx e) /\
  (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx t /\
  body_base_target_prefix_ok cx t ==>
  body_stmt_prefix_ok cx (Append t e)``;
val body_assign_case_prefix_port = ``
  !cx t e.
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
  body_stmt_prefix_ok cx (Assign (BaseTarget t) e)``;
val body_assign_tuple_case_prefix_port = ``
  !cx gs e.
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_prefix_ok cx (TupleTarget gs) v) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assign (TupleTarget gs) e)``;
val body_augassign_case_prefix_port = ``
  !cx ty t bop e.
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx t /\
  body_base_target_prefix_ok cx t ==>
  body_stmt_prefix_ok cx (AugAssign ty t bop e)``;
val body_if_case_prefix_port = ``
  !cx e ss1 ss2.
  (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_full_ok cx ss1) /\
  (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_prefix_ok cx ss1) /\
  (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_full_ok cx ss2) /\
  (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_prefix_ok cx ss2) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (If e ss1 ss2)``;
val body_for_case_prefix_port = ``
  !cx id typ it n body.
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
  body_stmt_prefix_ok cx (For id typ it n body)``;
val body_expr_stmt_case_prefix_port = ``
  !cx e. body_expr_full_ok cx e /\ body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Expr e)``;
val body_stmts_nil_case_prefix_port = ``!cx. body_stmts_prefix_ok cx []``;
val body_stmts_cons_case_prefix_port = ``
  !cx s ss.
  (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_full_ok cx ss) /\
  (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_prefix_ok cx ss) /\
  body_stmt_full_ok cx s /\
  body_stmt_prefix_ok cx s ==>
  body_stmts_prefix_ok cx (s::ss)``;

val stmt_ports =
  [body_pass_case_prefix_port, body_continue_case_prefix_port,
   body_break_case_prefix_port, body_return_none_case_prefix_port,
   body_return_case_prefix_port, body_raise_bare_case_prefix_port,
   body_raise_unreachable_case_prefix_port, body_raise_reason_case_prefix_port,
   body_raise_custom_case_prefix_port, body_assert_case_prefix_port,
   body_assert_unreachable_case_prefix_port, body_assert_reason_case_prefix_port,
   body_assert_custom_case_prefix_port, body_log_case_prefix_port,
   body_annassign_case_prefix_port, body_append_case_prefix_port,
   body_assign_case_prefix_port, body_assign_tuple_case_prefix_port,
   body_augassign_case_prefix_port, body_if_case_prefix_port,
   body_for_case_prefix_port, body_expr_stmt_case_prefix_port,
   body_stmts_nil_case_prefix_port, body_stmts_cons_case_prefix_port];

val same_step = ``
  !cx h. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
           EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
             (vyperTypeCallGraph$int_calls_expr h)) /\
         ~(?ann nid args dr. h = Call ann (IntCall nid) args dr) /\
    (!a. expr_size a < expr_size h /\
        (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
            (vyperTypeCallGraph$int_calls_expr a)) ==> body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx h``;

val selected_step = ``
  !rank cx ann src name es dr.
    LENGTH (remcode cx) <= rank /\
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
        (vyperTypeCallGraph$int_calls_expr (Call ann (IntCall (src,name)) es dr))) /\
    (!a. expr_size a < expr_size (Call ann (IntCall (src,name)) es dr) /\
       (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
         EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
           (vyperTypeCallGraph$int_calls_expr a)) ==>
       body_expr_prefix_ok cx a) /\
    (!c a. LENGTH (remcode c) < rank /\
       (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
            (vyperTypeCallGraph$int_calls_expr a)) ==> body_expr_prefix_ok c a) /\
    (!c ys. LENGTH (remcode c) < rank /\
       (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
            (vyperTypeCallGraph$int_calls_stmts ys) /\
          stmts_loop_calls_ok [(NONE,ts)] ys) ==>
       body_stmts_prefix_ok c ys) ==>
    body_expr_prefix_ok cx (Call ann (IntCall (src,name)) es dr)``;

Theorem ranked_expr_step[local]:
  ^same_step ==> ^selected_step ==>
  ((!c a. LENGTH (remcode c) < rank /\
       (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
            (vyperTypeCallGraph$int_calls_expr a)) ==> body_expr_prefix_ok c a) /\
   (!c ys. LENGTH (remcode c) < rank /\
      (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
         EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
           (vyperTypeCallGraph$int_calls_stmts ys) /\
         stmts_loop_calls_ok [(NONE,ts)] ys) ==>
      body_stmts_prefix_ok c ys)) ==>
  !cx h. LENGTH (remcode cx) <= rank /\
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
       EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
         (vyperTypeCallGraph$int_calls_expr h)) ==> body_expr_prefix_ok cx h
Proof
  disch_then (mk_asm "same_step") >> disch_then (mk_asm "selected_step") >>
  strip_tac >> rpt strip_tac >> completeInduct_on `expr_size h` >>
  rpt strip_tac >>
  Cases_on `?ann nid args dr. h = Call ann (IntCall nid) args dr`
  >- (gvs[] >> PairCases_on `nid` >>
      asm "selected_step" irule >>
      conj_tac
      >- (qx_gen_tac `a` >> strip_tac >>
          qpat_assum `!m:num. m < _ ==> _` (qspec_then `expr_size a` mp_tac) >>
          gvs[] >> decide_tac) >>
      simp[] >> qexists_tac `rank` >> simp[]) >>
  asm "same_step" irule >> conj_tac
  >- (qx_gen_tac `a` >> strip_tac >>
      qpat_assum `!m:num. m < _ ==> _` (qspec_then `expr_size a` mp_tac) >> gvs[]) >>
  simp[] >> metis_tac[]
QED

val checked_source = ``\cx. !ts.
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
  IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,ts)]) /\
  struct_args_unique ts /\
  (!vis mut nr raw fn args dflts ret ss.
    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) ts ==>
    stmts_loop_calls_ok [(NONE,ts)] (subst_consts_stmts (module_consts_env ts []) ss))``;

val stmt_ind = evaluate_ind |> Q.SPECL [
  `\cx s. LENGTH (remcode cx) <= rank /\ ^checked_source cx /\
          (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
                EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
                  (vyperTypeCallGraph$int_calls_stmt s) /\
                stmt_loop_calls_ok [(NONE,ts)] s) ==> body_stmt_prefix_ok cx s`,
  `\cx ss. LENGTH (remcode cx) <= rank /\ ^checked_source cx /\
           (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
                   (vyperTypeCallGraph$int_calls_stmts ss) /\
                 stmts_loop_calls_ok [(NONE,ts)] ss) ==> body_stmts_prefix_ok cx ss`,
  `\cx it. LENGTH (remcode cx) <= rank /\ ^checked_source cx /\
       (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
         EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
           (vyperTypeCallGraph$int_calls_iterator it)) ==> body_iterator_prefix_ok cx it`,
  `\cx ty nm ss vs. LENGTH (remcode cx) <= rank /\ ^checked_source cx /\
                    (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
                          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
                            (vyperTypeCallGraph$int_calls_stmts ss) /\
                          stmts_loop_calls_ok [(NONE,ts)] ss) ==>
                    body_for_prefix_ok cx ty nm ss vs`,
  `\(cx:evaluation_context) (e:expr). T`,
  `\(cx:evaluation_context) (es:expr list). T`,
  `\cx t. LENGTH (remcode cx) <= rank /\ ^checked_source cx /\
       (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
         EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
           (vyperTypeCallGraph$int_calls_target t)) ==> body_base_target_prefix_ok cx t`,
  `\cx t. LENGTH (remcode cx) <= rank /\ ^checked_source cx /\
       (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
         EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
           (vyperTypeCallGraph$int_calls_target t)) ==> body_base_target_prefix_ok cx t`,
  `\cx g v. LENGTH (remcode cx) <= rank /\ ^checked_source cx /\
       (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
         EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
           (vyperTypeCallGraph$int_calls_atarget g)) ==> body_tuple_target_prefix_ok cx g v`,
  `\cx gs vs. LENGTH (remcode cx) <= rank /\ ^checked_source cx /\
       (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
         EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
           (vyperTypeCallGraph$int_calls_atargets gs)) ==> body_tuple_targets_prefix_ok cx gs vs`]
  |> CONV_RULE (DEPTH_CONV BETA_CONV)
  |> REWRITE_RULE [GSYM CONJ_ASSOC];

val loop_calls = vyperTypeContractTheory.stmt_loop_calls_ok_def;
val syntax_calls =
  [int_calls_stmt_def, int_calls_expr_def, int_calls_iterator_def,
   int_calls_atarget_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
   EVERY_APPEND];
val stmt_simps = [push_function_def, return_def, evaluation_context_accfupds,
                  pairTheory.PAIR_EQ, sumTheory.INL_11, loop_calls];

fun stmt_row port =
  asm_x "stmt_ports" (fn th =>
    rpt strip_tac >> full_simp_tac bool_ss stmt_simps >>
    irule (SIMP_RULE bool_ss stmt_simps
      (first (fn t => aconv (concl t) port) (CONJUNCTS th)))) >>
  asm_rewrite_tac[] >> rpt conj_tac >> rpt strip_tac >>
  FIRST [first_assum ACCEPT_TAC,
         (FIRST (map irule (CONJUNCTS body_sim_full_mutual)) >>
          rpt strip_tac >> res_tac >> fs[loop_calls] >> NO_TAC),
         ALL_TAC] >>
  TRY (FIRST (map irule (CONJUNCTS body_sim_full_mutual))) >>
  rpt strip_tac >> res_tac >> fs (syntax_calls @ [loop_calls]) >>
  metis_tac[ordered_custom_error_calls];

Theorem ranked_stmt_step[local]:
  ^(list_mk_conj stmt_ports) ==>
  (!cx h. LENGTH (remcode cx) <= rank /\
       (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
            (vyperTypeCallGraph$int_calls_expr h)) ==> body_expr_prefix_ok cx h) ==>
  !cx ss. LENGTH (remcode cx) <= rank /\
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
       EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
         (vyperTypeCallGraph$int_calls_stmts ss) /\
       stmts_loop_calls_ok [(NONE,tops)] ss) ==> body_stmts_prefix_ok cx ss
Proof
  disch_then (mk_asm "stmt_ports") >> strip_tac >>
  `!cx es. LENGTH (remcode cx) <= rank /\
     (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
            (int_calls_exprs es)) ==> body_exprs_prefix_ok cx es` by
    (rpt strip_tac >> irule prefix_list_from_members >> rpt strip_tac >>
     qpat_assum `!cx h. LENGTH _ <= rank /\ _ ==> _` irule >>
     simp[] >> rpt strip_tac >> res_tac >>
     fs[int_calls_exprs_members] >> metis_tac[]) >>
  mp_tac stmt_ind >> impl_tac
  >- (rpt conj_tac
      >- stmt_row body_pass_case_prefix_port
      >- stmt_row body_continue_case_prefix_port
      >- stmt_row body_break_case_prefix_port
      >- stmt_row body_return_none_case_prefix_port
      >- stmt_row body_return_case_prefix_port
      >- stmt_row body_raise_bare_case_prefix_port
      >- stmt_row body_raise_unreachable_case_prefix_port
      >- stmt_row body_raise_reason_case_prefix_port
      >- stmt_row body_raise_custom_case_prefix_port
      >- stmt_row body_assert_case_prefix_port
      >- stmt_row body_assert_unreachable_case_prefix_port
      >- stmt_row body_assert_reason_case_prefix_port
      >- stmt_row body_assert_custom_case_prefix_port
      >- stmt_row body_log_case_prefix_port
      >- stmt_row body_annassign_case_prefix_port
      >- stmt_row body_append_case_prefix_port
      >- stmt_row body_assign_case_prefix_port
      >- stmt_row body_assign_tuple_case_prefix_port
      >- stmt_row body_augassign_case_prefix_port
      >- stmt_row body_if_case_prefix_port
      >- stmt_row body_for_case_prefix_port
      >- stmt_row body_expr_stmt_case_prefix_port
      >- stmt_row body_stmts_nil_case_prefix_port
      >- stmt_row body_stmts_cons_case_prefix_port
      >- (simp[body_iterator_prefix_ok_def, int_calls_iterator_def] >> metis_tac[])
      >- (rpt strip_tac >> fs[] >> rw[body_iterator_prefix_ok_def] >> metis_tac[int_calls_iterator_def, EVERY_APPEND])
      >- simp[body_for_prefix_ok_def]
      >- (rpt strip_tac >> fs[] >> rw[body_for_prefix_ok_def] >>
          first_x_assum irule >> simp[push_scope_with_var_def, return_def] >> metis_tac[])
      >- simp[body_base_target_prefix_ok_def]
      >- simp[body_base_target_prefix_ok_def]
      >- (simp[body_base_target_prefix_ok_def, int_calls_expr_def] >> metis_tac[])
      >- (simp[body_base_target_prefix_ok_def, int_calls_expr_def, EVERY_APPEND] >>
          rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[])
      >- (simp[body_tuple_target_prefix_ok_def, int_calls_atarget_def] >> metis_tac[])
      >- (simp[body_tuple_target_prefix_ok_def, int_calls_atarget_def] >> metis_tac[])
      >- simp[body_tuple_target_prefix_ok_def]
      >- (simp[body_tuple_target_prefix_ok_def, int_calls_atarget_def, EVERY_APPEND] >>
          rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[])
      >- simp[body_tuple_target_prefix_ok_def]
      >- simp[body_tuple_target_prefix_ok_def]
      >> simp[body_tuple_target_prefix_ok_def]) >>
  disch_then (assume_tac o cj 2) >> rpt strip_tac >>
  reverse (Cases_on `?tops env es. body_const_cells_agree [(NONE,tops)] cx env es`)
  >- (simp[body_stmts_prefix_ok_def] >> rpt strip_tac >> metis_tac[]) >>
  qpat_x_assum `?tops env es. _` strip_assume_tac >>
  drule_then assume_tac checked_context_full_guards >>
  drule_then assume_tac body_const_cells_agree_runtime_check >>
  fs[body_const_cells_agree_def] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem bool_chain_guarded_rank_core:
  ^(list_mk_conj stmt_ports) ==> ^same_step ==> ^selected_step ==>
  !rank:num.
    (!cx h. LENGTH (remcode cx) <= rank /\
       (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
            (vyperTypeCallGraph$int_calls_expr h)) ==> body_expr_prefix_ok cx h) /\
    (!cx ss. LENGTH (remcode cx) <= rank /\
       (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
            (vyperTypeCallGraph$int_calls_stmts ss) /\
          stmts_loop_calls_ok [(NONE,tops)] ss) ==>
       body_stmts_prefix_ok cx ss)
Proof
  disch_then (mk_asm "stmt_ports") >>
  disch_then (mk_asm "same_step") >> disch_then (mk_asm "selected_step") >>
  completeInduct_on `rank` >> conj_asm1_tac
  >- (asm_x "same_step" assume_tac >> asm_x "selected_step" assume_tac >>
      mp_tac (Q.INST [`rank` |-> `rank`] ranked_expr_step) >> asm_rewrite_tac[] >>
      impl_tac >- (conj_tac >> rpt strip_tac >>
        qpat_assum `!m:num. m < rank ==> _` (drule_then strip_assume_tac) >> simp[]) >>
      simp[]) >>
  asm_x "stmt_ports" assume_tac >>
  mp_tac (Q.INST [`rank` |-> `rank`] ranked_stmt_step) >> asm_rewrite_tac[]
QED
