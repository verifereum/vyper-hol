open HolKernel boolLib bossLib Parse intLib wordsLib cv_transLib blastLib;
open finite_mapTheory vyperAstTheory vyperVmTheory vyperTestTheory;

val () = new_theory "vyperDemo";

Definition demo_ast_def:
  demo_ast = [
    pubvar "creator" address;
    pubvar "goal" uint256;
    pubmap "contributions" address (Type uint256);
    pubvar "total_contributions" uint256;
    pubvar "goal_reached" bool;
    pubmap "refund_claimed" address (Type bool);
    pubvar "is_active" bool;
    deploy_def "__init__" [("goal_amount", uint256)] NoneT [
      AssignSelf "creator" msg_sender;
      AssignSelf "goal" (Name "goal_amount");
      AssignSelf "is_active" (lb T)
    ];
    pay_def "contribute" [] NoneT [
      Assert (self_ "is_active") "Not active";
      AugAssign (SubscriptTarget (GlobalNameTarget "contributions")
                                 msg_sender)
                Add msg_value;
      AugAssign (GlobalNameTarget "total_contributions")
                Add msg_value;
      AssignSelf "goal_reached"
        (not (self_ "goal" < self_ "total_contributions"))
    ];
    def "end_campaign" [] NoneT [
      Assert (msg_sender == self_ "creator") "Only creator";
      AssignSelf "is_active" (lb F)
    ];
    def "refund" [] NoneT [
      Assert (not (self_ "is_active")) "Still active";
      Assert (not (self_ "goal_reached")) "Goal was reached";
      If (li 0 < Subscript (self_ "contributions") msg_sender)
        [Expr $ Call Send [msg_sender; Subscript (self_ "contributions") msg_sender]]
        []
    ];
    def "withdraw" [] NoneT [
      Assert (not (self_ "is_active")) "Still active";
      Assert (not (self_ "goal_reached")) "Goal was reached";
      Assert (msg_sender == self_ "creator") "Only creator";
      Expr $ Call Send [self_ "creator"; self_balance]
    ]
  ]
End

(* TODO: why doesn't this work later?
val () = cv_trans_deep_embedding EVAL demo_ast_def;
*)
val () = cv_auto_trans demo_ast_def;

val deployer = “0x42w: address”
val contract = “0x0123w: address”

Definition deploy_demo_def:
  deploy_demo =
  let deployer = ^deployer in
  let addr = ^contract in
  let goal_amount = 10 ** 18 in
  let deploy_tx = transaction deployer addr "__init__" [IntV &goal_amount] 0 in
    OUTL $ load_contract initial_machine_state deploy_tx demo_ast
End

val deploy_demo_pre_def = cv_auto_trans_pre deploy_demo_def;

fun mk_eval_match eval pat tm = let
  val t1 = find_term (can $ match_term pat) tm
  val th = eval t1
in PURE_REWRITE_CONV [th] tm end

val cv_eval_match = mk_eval_match cv_eval
val eval_match = mk_eval_match EVAL

Theorem deploy_demo_pre[cv_pre]:
  deploy_demo_pre
Proof
  rw[deploy_demo_pre_def, load_contract_def]
  \\ CONV_TAC(cv_eval_match“lookup_function _ _ _”)
  \\ rw[]
  \\ CONV_TAC(cv_eval_match“step_external_function _ _ _ _ _”)
  \\ rw[]
QED

Theorem deploy_demo_eq = cv_eval “deploy_demo”

Theorem demo_check_end_campaign_other:
  tx = <| sender := addr; target := ^contract;
          value := 0; args := [];
          function_name := "end_campaign" |>
  ==>
  FST $ external_call deploy_demo tx =
  if addr = ^deployer then INL NoneV
  else INR "Assertion Failed: Only creator"
Proof
  rw[]
  >- CONV_TAC cv_eval
  \\ rewrite_tac[deploy_demo_eq]
  \\ rewrite_tac[GSYM demo_ast_def]
  \\ simp[external_call_def]
  \\ qmatch_goalsub_abbrev_tac`contract _ gbs`
  \\ simp[external_call_contract_def]
  \\ CONV_TAC(cv_eval_match “lookup_function _ _ _”)
  \\ simp[step_external_function_def]
  \\ CONV_TAC(cv_eval_match “bind_arguments _ _”)
  \\ simp[]
  \\ CONV_TAC(cv_eval_match “initial_function_context _ _ _”)
  \\ simp[Once step_stmt_till_exception_def,
          initial_execution_context_def,
          exception_raised_def]
  \\ CONV_TAC(eval_match “step_stmt _”) \\ rewrite_tac[GSYM demo_ast_def]
  \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
  \\ CONV_TAC(eval_match “step_stmt _”) \\ rewrite_tac[GSYM demo_ast_def]
  \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
  \\ CONV_TAC(eval_match “step_stmt _”) \\ rewrite_tac[GSYM demo_ast_def]
  \\ qmatch_goalsub_abbrev_tac`BuiltinK Eq [addrv]`
  \\ `addrv = AddressV addr` by (unabbrev_all_tac \\ EVAL_TAC)
  \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
  \\ qunabbrev_tac`gbs`
  \\ CONV_TAC(eval_match “step_stmt _”) \\ rewrite_tac[GSYM demo_ast_def]
  \\ qmatch_goalsub_abbrev_tac`contract _ gbs`
  \\ qmatch_goalsub_abbrev_tac`BoolV b`
  \\ `b = (addr = 66w)` by ( unabbrev_all_tac \\ BBLAST_TAC )
  \\ `¬b` by rw[]
  \\ BasicProvers.VAR_EQ_TAC
  \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
  \\ CONV_TAC(eval_match “step_stmt _”) \\ rewrite_tac[GSYM demo_ast_def]
  \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
  \\ CONV_TAC cv_eval
QED

Theorem lookup_function_demo_ast:
  lookup_function fn vis demo_ast = SOME x
  ⇒
  fn ∈ {
    "creator";
    "contributions";
    "total_contributions";
    "refund_claimed";
    "is_active";
    "goal_reached";
    "goal";
    "contribute";
    "end_campaign";
    "refund";
    "withdraw"
  } ∧ vis = External
  ∨ vis = Deploy
Proof
  Cases_on`vis`
  \\ EVAL_TAC
  \\ rw[]
QED

Theorem bind_arguments_nil_SOME[simp]:
  bind_arguments [] args = SOME env ⇔ args = [] ∧ env = FEMPTY
Proof
  Cases_on`args` \\ rw[bind_arguments_def]
QED

val step_stmt_pat = “step_stmt _”
val option_case_pat = “option_CASE opt”
val some_pat = “SOME x”
val value_pat = “Value v”

val step_tac =
  (
    qmatch_goalsub_abbrev_tac ‘toplevel_value_CASE x’
    \\ reverse (Cases_on ‘x’)
    >- (
      simp[Once step_stmt_till_exception_def, exception_raised_def]
      \\ CONV_TAC(eval_match step_stmt_pat)
      \\ simp[Once step_stmt_till_exception_def, exception_raised_def] )
    \\ simp[]
  ) ORELSE
  (
    qmatch_goalsub_abbrev_tac ‘SOME (x:toplevel_value)’
    \\ (fn g as (asl, _) =>
          (if total (fn asl =>
              asl |> hd |> rand |> lhs |>
              dest_var |> #1 |> equal "x"  ) asl = SOME true
           then NO_TAC else ALL_TAC) g)
    \\ reverse (Cases_on ‘x’)
    >- (
      simp[Once step_stmt_till_exception_def, exception_raised_def]
      \\ CONV_TAC(eval_match step_stmt_pat)
      \\ simp[Once step_stmt_till_exception_def, exception_raised_def] )
  ) ORELSE
  (
    qmatch_goalsub_abbrev_tac ‘option_CASE opt’
    \\ Cases_on ‘opt’
    >- (
      simp[Once step_stmt_till_exception_def, exception_raised_def]
      \\ CONV_TAC(eval_match step_stmt_pat)
      \\ simp[Once step_stmt_till_exception_def, exception_raised_def] )
    \\ simp[]
  ) ORELSE
  (
    qmatch_goalsub_abbrev_tac ‘evaluate_builtin _ Not [v]’
    \\ Cases_on`v`
    \\ CONV_TAC(eval_match “step_stmt _”)
    \\ rw[Once step_stmt_till_exception_def, exception_raised_def]
    \\ CONV_TAC(eval_match “step_stmt _”)
    \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
    \\ gvs[]
  ) ORELSE
  (
    CONV_TAC(eval_match step_stmt_pat)
    \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
  )

Theorem demo_cannot_become_active:
  ALOOKUP ms0.contracts addr = SOME ctr0 ∧
  ctr0.src = demo_ast ∧
  FLOOKUP ctr0.globals (string_to_num "is_active") = SOME (Value (BoolV F)) ∧
  external_call ms0 tx = (res, ms1)
  ⇒
  ∃ctr1.
    ALOOKUP ms1.contracts addr = SOME ctr1 ∧
    FLOOKUP ctr1.globals (string_to_num "is_active") = SOME (Value (BoolV F))
Proof
  rw[external_call_def, CaseEq"prod", CaseEq"option"]
  \\ rw[]
  \\ gvs[external_call_contract_def, CaseEq"option", CaseEq"prod"]
  \\ drule lookup_function_demo_ast
  \\ simp[]
  \\ strip_tac
  \\ qhdtm_x_assum`lookup_function`mp_tac
  \\ gvs[]
  \\ CONV_TAC(cv_eval_match “lookup_function _ _ _”) \\ rw[]
  \\ qhdtm_x_assum`step_external_function`mp_tac
  \\ simp[step_external_function_def, CaseEq"option"]
  \\ strip_tac \\ gvs[]
  \\ CONV_TAC(cv_eval_match “initial_function_context _ _ _”)
  \\ simp[Once step_stmt_till_exception_def,
          initial_execution_context_def,
          exception_raised_def]
  >- rpt step_tac
  >- rpt step_tac
  >- rpt step_tac
  >- rpt step_tac
  >- rpt step_tac
  >- ( rename1 ‘tx.function_name = "contribute"’
    \\ ntac 5 step_tac
    \\ Cases_on`v` \\ simp[]
    \\ Cases_on`b` \\ simp[]
    \\ qhdtm_x_assum`FLOOKUP`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ strip_tac \\ gs[])
  >- ( rename1 ‘tx.function_name = "end_campaign"’
    \\ ntac 3 step_tac
    \\ qmatch_goalsub_abbrev_tac`BuiltinK Eq [sender]`
    \\ ntac 3 step_tac
    \\ qunabbrev_tac`sender` \\ Cases_on`v` \\ rw[evaluate_builtin_def]
    \\ TRY (step_tac \\ NO_TAC)
    \\ qmatch_goalsub_abbrev_tac`BoolV bb`
    \\ CONV_TAC(eval_match “step_stmt _”)
    \\ reverse (Cases_on`bb`)
    >- rw[Once step_stmt_till_exception_def, exception_raised_def]
    \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
    \\ ntac 10 step_tac
    \\ rw[FLOOKUP_UPDATE] )
  >- ( rename1 ‘tx.function_name = "refund"’
    \\ ntac 18 step_tac
    \\ Cases_on`x`
    >- (
      simp[Once step_stmt_till_exception_def, exception_raised_def]
      \\ CONV_TAC(eval_match “step_stmt _”)
      \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
      \\ CONV_TAC(eval_match “step_stmt _”)
      \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
    )
    \\ ntac 3 step_tac
    \\ Cases_on`v`
    \\ CONV_TAC(eval_match “step_stmt _”)
    \\ rw[Once step_stmt_till_exception_def, exception_raised_def]
    \\ gvs[]
    \\ rpt step_tac )
  >- ( rename1 ‘tx.function_name = "withdraw"’
    \\ ntac 18 step_tac
    \\ Cases_on`v`
    \\ CONV_TAC(eval_match “step_stmt _”)
    \\ rw[Once step_stmt_till_exception_def, exception_raised_def]
    \\ gvs[]
    \\ rpt step_tac )
QED

val () = export_theory();
