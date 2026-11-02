(* TOP-LEVEL: conservative syntactic purity test shared by the interpreter
   proofs and lowering. Calls and Pop may change state; nested occurrences
   propagate through every expression constructor that can contain them.
   msg.gas is impure because it consumes a gas reading. *)
Theory vyperExprEffects
Ancestors
  vyperAST list pair

Definition pure_expr_def:
  pure_expr (Name _ _) = T /\
  pure_expr (TopLevelName _ _) = T /\
  pure_expr (FlagMember _ _ _) = T /\
  pure_expr (Literal _ _) = T /\
  pure_expr (IfExp _ e1 e2 e3) = (pure_expr e1 /\ pure_expr e2 /\ pure_expr e3) /\
  pure_expr (StructLit _ _ kes) = EVERY pure_expr (MAP SND kes) /\
  pure_expr (Subscript _ e1 e2) = (pure_expr e1 /\ pure_expr e2) /\
  pure_expr (Attribute _ e _) = pure_expr e /\
  pure_expr (Builtin _ bt es) = (bt <> Env MsgGas /\ EVERY pure_expr es) /\
  pure_expr (TypeBuiltin _ _ _ es) = EVERY pure_expr es /\
  pure_expr _ = F
Termination
  WF_REL_TAC `measure expr_size` >> rw[] >>
  Induct_on `kes` >> rw[] >> PairCases_on `h` >> rw[] >> res_tac >> simp[]
End
