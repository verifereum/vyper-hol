Theory vyperPopTypingTest
Ancestors
  vyperTypeSystem finite_map
Libs
  wordsLib

Definition pop_typing_env_def:
  pop_typing_env env = env with <|
    type_defs := FEMPTY;
    var_types := FEMPTY |+ ("local", ArrayT (BaseT (UintT 256)) (Dynamic 2));
    var_assignable := FEMPTY |+ ("local", T);
    bare_globals := FEMPTY |+
      ((NONE,"imm"), ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 2)) (Dynamic 2));
    bare_global_assignable := FEMPTY |+
      ((NONE,"imm"), ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 2)) (Dynamic 2));
    toplevel_vtypes := FEMPTY |+
      ((NONE,"store"), Type (ArrayT (BaseT (UintT 256)) (Dynamic 2))) |+
      ((NONE,"imm"), Type
        (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 2)) (Dynamic 2))) |>
End

(* An immutable is an assignable initialization target, but cannot be popped
   directly even in a constructor. *)
Theorem root_immutable_pop_rejected:
  type_place_target (pop_typing_env env) (TopLevelNameTarget (NONE,"imm")) =
    SOME (Type (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 2)) (Dynamic 2))) /\
  ~well_typed_expr (pop_typing_env env)
    (Pop (ArrayT (BaseT (UintT 256)) (Dynamic 2))
      (TopLevelNameTarget (NONE,"imm")))
Proof
  EVAL_TAC >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED

(* Static-map transfer also covers incomplete metadata before the bare-global
   and top-level maps have been populated. Initialization-only assignability
   must not make root pop valid there. *)
Theorem root_pop_rejects_initialization_only_metadata:
  ~well_typed_expr
    (pop_typing_env env with <|bare_globals := FEMPTY; toplevel_vtypes := FEMPTY|>)
    (Pop (ArrayT (BaseT (UintT 256)) (Dynamic 2))
      (TopLevelNameTarget (NONE,"imm")))
Proof
  EVAL_TAC >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem local_and_storage_pop_accepted:
  well_typed_expr (pop_typing_env env)
    (Pop (BaseT (UintT 256)) (NameTarget "local")) /\
  well_typed_expr (pop_typing_env env)
    (Pop (BaseT (UintT 256)) (TopLevelNameTarget (NONE,"store")))
Proof
  EVAL_TAC >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem nested_immutable_pop_typing_preserved:
  well_typed_expr (pop_typing_env env)
    (Pop (BaseT (UintT 256))
      (SubscriptTarget (TopLevelNameTarget (NONE,"imm"))
        (Literal (BaseT (UintT 256)) (IntL 0))))
Proof
  EVAL_TAC >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED
