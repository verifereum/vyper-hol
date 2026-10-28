(* TOP-LEVEL: conservative syntactic purity test shared by the interpreter
   proofs and lowering. Calls and Pop may change state; nested occurrences
   propagate through every expression constructor that can contain them. *)
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
  pure_expr (Builtin _ _ es) = EVERY pure_expr es /\
  pure_expr (TypeBuiltin _ _ _ es) = EVERY pure_expr es /\
  pure_expr _ = F
Termination
  WF_REL_TAC `measure expr_size` >> rw[] >>
  Induct_on `kes` >> rw[] >> PairCases_on `h` >> rw[] >> res_tac >> simp[]
End

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed expression effect theorem: " ^ name)
  end) (DB.thms "vyperExprEffects")
