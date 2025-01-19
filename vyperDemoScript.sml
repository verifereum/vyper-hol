open HolKernel boolLib bossLib Parse intLib wordsLib cv_transLib;
open vyperAstTheory vyperVmTheory vyperTestTheory;

val () = new_theory "vyperDemo";

Definition demo_ast_def:
  demo_ast = [
    VariableDecl Public Storage "creator" address;
    VariableDecl Public Storage "goal" uint256;
    HashMapDecl Public "contributions" address (Type uint256);
    VariableDecl Public Storage "total_contributions" uint256;
    VariableDecl Public Storage "goal_reached" (BaseT BoolT);
    HashMapDecl Public "refund_claimed" address (Type (BaseT BoolT));
    VariableDecl Public Storage "is_active" (BaseT BoolT);
    FunctionDef Deploy Nonpayable "__init__" [("goal_amount", uint256)] VoidT [
      Assign (BaseTarget (GlobalNameTarget "creator")) (Builtin (Msg Sender) []);
      Assign (BaseTarget (GlobalNameTarget "goal")) (Name "goal_amount");
      Assign (BaseTarget (GlobalNameTarget "is_active")) (Literal (BoolL T))
    ];
    FunctionDef External Payable "contribute" [] VoidT [
      Assert (GlobalName "is_active") "Not active";
      AugAssign (SubscriptTarget (GlobalNameTarget "contributions")
                                 (Builtin (Msg Sender) []))
                Add (Builtin (Msg ValueSent) []);
      AugAssign (GlobalNameTarget "total_contributions")
                Add (Builtin (Msg ValueSent) []);
      Assign (BaseTarget (GlobalNameTarget "goal_reached"))
        (Builtin Not [
           Builtin Lt [GlobalName "goal"; GlobalName "total_contributions"]
         ])
    ]
  ]
End

val () = export_theory();
