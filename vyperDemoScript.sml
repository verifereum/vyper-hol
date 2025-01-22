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

val () = cv_trans_deep_embedding EVAL demo_ast_def;

val () = export_theory();
