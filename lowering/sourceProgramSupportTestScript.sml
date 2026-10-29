(* #543 remainder regressions: redundant gates are removed, local tuple
   reads (including nested places) are admitted, and independent type/layout
   boundaries remain. No claim about unrelated whitelist clauses. *)
Theory sourceProgramSupportTest
Ancestors
  sourceProgramSupport sourceStmtSupport sourceExprSupport sourceBuiltinSupport
  supportedProgram supportedStmts supportedExprs supportedExprForms supportedTypes
  supportedDecls supportedNames supportedExprTraverse supportedStmtTraverse
  vyperTypeContract vyperTypeSystem vyperAST list integer finite_map

val () = computeLib.add_funs
  [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``];

Theorem remainder_method_id_gate_removed:
  source_expr_remainder tops (Builtin (BaseT (BytesT (Fixed 4))) MethodId []) /\
  ~supported_expr tops (Builtin (BaseT (BytesT (Fixed 4))) MethodId []) /\
  ~well_typed_expr env (Builtin (BaseT (BytesT (Fixed 4))) MethodId [])
Proof
  simp[source_expr_remainder_def, source_pure_expr_remainder_def,
       source_builtin_remainder_def, supported_expr_def, supported_pure_expr_def,
       supported_effect_expr_def, supported_builtin_form_def, typed_method_id_rejected]
QED

Theorem remainder_power_gate_removed:
  source_pure_expr_remainder tops
    (Builtin (BaseT (UintT 256)) (Bop Exp)
      [Name (BaseT (UintT 256)) "a"; Name (BaseT (UintT 256)) "b"]) /\
  ~supported_pure_expr tops
    (Builtin (BaseT (UintT 256)) (Bop Exp)
      [Name (BaseT (UintT 256)) "a"; Name (BaseT (UintT 256)) "b"])
Proof
  EVAL_TAC
QED

Theorem remainder_augassign_gate_removed:
  source_stmt_remainder tops [("a",BaseT (UintT 256))]
    (AugAssign (BaseT (UintT 256)) (NameTarget "a") Exp
      (Name (BaseT (UintT 256)) "b")) /\
  ~supported_stmt tops [("a",BaseT (UintT 256))]
    (AugAssign (BaseT (UintT 256)) (NameTarget "a") Exp
      (Name (BaseT (UintT 256)) "b"))
Proof
  EVAL_TAC
QED

Theorem remainder_local_tuple_supported:
  source_expr_remainder tops
    (Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT BoolT; BaseT (UintT 256)]) "t")
      (Literal (BaseT (UintT 256)) (IntL 1)))
Proof
  EVAL_TAC
QED

(* Nested tuple components use supported_place_type, not the flat tuple gate. *)
Theorem remainder_nested_local_tuple_supported:
  source_expr_remainder tops
    (Subscript (BaseT (UintT 256))
      (Subscript (ArrayT (BaseT (UintT 256)) (Fixed 2))
        (Name (TupleT [ArrayT (BaseT (UintT 256)) (Fixed 2)]) "t")
        (Literal (BaseT (UintT 256)) (IntL 0)))
      (Literal (BaseT (UintT 256)) (IntL 1)))
Proof
  EVAL_TAC
QED

(* Even when the selected field is bool, an unsupported bytes20 sibling
   prevents this tuple from being a supported local place. *)
Theorem remainder_local_tuple_unsupported_component_rejected:
  ~source_expr_remainder tops
    (Subscript (BaseT BoolT)
      (Name (TupleT [BaseT BoolT; BaseT (BytesT (Fixed 20))]) "t")
      (Literal (BaseT (UintT 256)) (IntL 0)))
Proof
  EVAL_TAC
QED

Definition source_support_local_tuple_tops_def:
  source_support_local_tuple_tops =
    [FunctionDecl External Nonpayable F F "f"
      [("t",TupleT [BaseT BoolT; BaseT (UintT 256)])] [] (BaseT (UintT 256))
      [Return (SOME (Subscript (BaseT (UintT 256))
        (Name (TupleT [BaseT BoolT; BaseT (UintT 256)]) "t")
        (Literal (BaseT (UintT 256)) (IntL 1))))]]
End

Theorem local_tuple_program_checked_remainder:
  source_program_remainder source_support_local_tuple_tops /\
  (?art. check_contract T [] (0w:address)
    [(NONE,source_support_local_tuple_tops)] = SOME art)
Proof
  EVAL_TAC >> simp[]
QED

Theorem local_tuple_program_supported_by_replacement:
  supported_program source_support_local_tuple_tops
Proof
  strip_assume_tac local_tuple_program_checked_remainder >>
  drule checked_remainder_supported_program >> simp[]
QED

Definition source_support_power_tops_def:
  source_support_power_tops =
    [FunctionDecl External Nonpayable F F "f" [("a",BaseT (UintT 256))] []
      (BaseT (UintT 256))
      [Return (SOME (Builtin (BaseT (UintT 256)) (Bop Exp)
        [Name (BaseT (UintT 256)) "a"; Literal (BaseT (UintT 256)) (IntL 2)]))]]
End

Theorem power_program_remainder_nonvacuous:
  source_program_remainder source_support_power_tops
Proof
  EVAL_TAC
QED

Theorem power_program_checked:
  ?art. check_contract T [] (0w:address) [(NONE,source_support_power_tops)] = SOME art
Proof
  EVAL_TAC >> simp[]
QED

Theorem power_program_supported_by_replacement:
  supported_program source_support_power_tops
Proof
  strip_assume_tac power_program_checked >>
  drule checked_remainder_supported_program >>
  simp[power_program_remainder_nonvacuous]
QED

Definition source_support_aug_tops_def:
  source_support_aug_tops =
    [FunctionDecl External Nonpayable F F "f" [("a",BaseT (UintT 256))] []
      (BaseT (UintT 256))
      [If (Literal (BaseT BoolT) (BoolL T))
        [AugAssign (BaseT (UintT 256)) (NameTarget "a") Exp
          (Literal (BaseT (UintT 256)) (IntL 2))] [];
       Return (SOME (Name (BaseT (UintT 256)) "a"))]]
End

Theorem recursive_aug_program_checked_remainder:
  source_program_remainder source_support_aug_tops /\
  (?art. check_contract T [] (0w:address) [(NONE,source_support_aug_tops)] = SOME art)
Proof
  EVAL_TAC >> simp[FLOOKUP_UPDATE]
QED

Theorem recursive_aug_program_supported_by_replacement:
  supported_program source_support_aug_tops
Proof
  strip_assume_tac recursive_aug_program_checked_remainder >>
  drule checked_remainder_supported_program >> simp[]
QED

(* Body expression support does not discharge the declared return layout. *)
Theorem remainder_return_layout_retained:
  source_function_body_remainder [] External
    [("a",ArrayT (BaseT (UintT 256)) (Dynamic 1))]
    [Return (SOME (Name (ArrayT (BaseT (UintT 256)) (Dynamic 1)) "a"))] /\
  ~source_declaration_body_remainder []
    (FunctionDecl External Nonpayable F F "f"
      [("a",ArrayT (BaseT (UintT 256)) (Dynamic 1))] []
      (ArrayT (BaseT (UintT 256)) (Dynamic 2))
      [Return (SOME (Name (ArrayT (BaseT (UintT 256)) (Dynamic 1)) "a"))])
Proof
  EVAL_TAC
QED

Theorem remainder_custom_error_rejected:
  ~source_declaration_body_remainder tops (ErrorDecl name fields) /\
  ~source_program_remainder [ErrorDecl name fields] /\
  ~supported_program [ErrorDecl name fields]
Proof
  simp[source_declaration_body_remainder_def, source_program_remainder_def,
       supported_program_def, supported_declaration_headers_def,
       supported_declaration_header_def]
QED

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source program remainder test kernel audit: " ^ name) end)
  (DB.thms "sourceProgramSupportTest");
