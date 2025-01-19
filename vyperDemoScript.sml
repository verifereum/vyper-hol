open HolKernel boolLib bossLib Parse intLib wordsLib cv_transLib;
open vyperAstTheory vyperVmTheory vyperTestTheory;

val () = new_theory "vyperDemo";

Definition demo_ast_def:
  demo_ast = [
    pubvar "creator" address;
    pubvar "goal" uint256;
    HashMapDecl Public "contributions" address (Type uint256);
    pubvar "total_contributions" uint256;
    pubvar "goal_reached" bool;
    HashMapDecl Public "refund_claimed" address (Type bool);
    pubvar "is_active" bool;
    FunctionDef Deploy Nonpayable "__init__" [("goal_amount", uint256)] NoneT [
      AssignSelf "creator" msg_sender;
      AssignSelf "goal" (Name "goal_amount");
      AssignSelf "is_active" (Literal (BoolL T))
    ];
    FunctionDef External Payable "contribute" [] NoneT [
      Assert (GlobalName "is_active") "Not active";
      AugAssign (SubscriptTarget (GlobalNameTarget "contributions")
                                 msg_sender)
                Add msg_value;
      AugAssign (GlobalNameTarget "total_contributions")
                Add msg_value;
      AssignSelf "goal_reached"
        (not (GlobalName "goal" < GlobalName "total_contributions"))
    ];
    defun "end_campaign" [] NoneT [
      Assert (msg_sender == GlobalName "creator") "Only creator";
      AssignSelf "is_active" (Literal (BoolL F))
    ];
    defun "refund" [] NoneT [
      Assert (not (GlobalName "is_active")) "Still active";
      Assert (not (GlobalName "goal_reached")) "Goal was reached";
      If (intlit 0 < Subscript (GlobalName "contributions") msg_sender)
      [(* TODO: send *)] []
    ];
    defun "withdraw" [] NoneT [
      Assert (not (GlobalName "is_active")) "Still active";
      Assert (not (GlobalName "goal_reached")) "Goal was reached";
      Assert (msg_sender == GlobalName "creator") "Only creator"
      (* TODO: send *)
    ]
  ]
End

val () = export_theory();
