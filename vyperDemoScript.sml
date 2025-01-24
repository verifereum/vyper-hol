open HolKernel boolLib bossLib Parse intLib wordsLib cv_transLib;
open vyperAstTheory vyperVmTheory vyperTestTheory;

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
      Expr $ Call Send [self_ "creator"; self_ "balance" (* TODO *)]
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

fun cv_eval_match pat tm = let
  val t1 = find_term (can $ match_term pat) tm
  val th = cv_eval t1
in PURE_REWRITE_CONV [th] tm end

Theorem deploy_demo_pre[cv_pre]:
  deploy_demo_pre
Proof
  rw[deploy_demo_pre_def, load_contract_def]
  \\ CONV_TAC(cv_eval_match“lookup_function _ _ _”)
  \\ rw[]
  \\ CONV_TAC(cv_eval_match“step_external_function _ _ _ _”)
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
  \\ simp[external_call_def]
  \\ rewrite_tac[Once deploy_demo_eq]
  \\ qmatch_goalsub_abbrev_tac`contract src gbs`
  \\ simp[external_call_contract_def]
  \\ qunabbrev_tac`src`
  \\ CONV_TAC(cv_eval_match “lookup_function _ _ _”)
  \\ qmatch_goalsub_abbrev_tac`contract src gbs`
  \\ simp[step_external_function_def]
  \\ CONV_TAC(cv_eval_match “bind_arguments _ _”)
  \\ simp[]
  \\ CONV_TAC(cv_eval_match “initial_function_context _ _ _”)
  \\ simp[Once step_stmt_till_exception_def]
  \\ simp[Once initial_execution_context_def, exception_raised_def]
  \\ simp[Once initial_execution_context_def]
  \\ simp[Once step_stmt_def, set_stmt_def]
  \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
  \\ simp[Once step_stmt_def, set_stmt_def]
  \\ simp[step_expr_def]
  \\ CONV_TAC(cv_eval_match “AssertK _ _”)
  \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
  \\ simp[Once step_stmt_def, set_stmt_def]
  \\ simp[step_expr_def]
  \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
  \\ simp[Once step_stmt_def, set_stmt_def]
  \\ simp[step_expr_def]
  \\ qunabbrev_tac`gbs`
  \\ CONV_TAC(cv_eval_match “FLOOKUP _ _”)
  \\ simp[evaluate_builtin_def]
  \\ qmatch_goalsub_abbrev_tac`contract src gbs`
  \\ qmatch_goalsub_abbrev_tac`BoolV b`
  \\ `b = (addr = 66w)` by cheat (* word_to_bytes_word_of_bytes_20 *)
  \\ gvs[Abbr`b`]
  \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
  \\ simp[Once step_stmt_def, set_stmt_def, raise_def]
  \\ simp[Once step_stmt_till_exception_def, exception_raised_def]
  \\ CONV_TAC cv_eval
QED

val () = export_theory();
