(* #543 remainder regression contracts: actual removal of the redundant
   gates, continued admission of ordinary expressions, and retained tuple
   base-shape rejection. No claim about unrelated whitelist clauses. *)
Theory sourceProgramSupportTest
Ancestors
  sourceProgramSupport sourceStmtSupport sourceExprSupport sourceBuiltinSupport
  supportedProgram supportedStmts supportedExprs supportedExprForms supportedTypes
  supportedDecls supportedNames supportedExprTraverse supportedStmtTraverse
  vyperTypeContract vyperTypeSystem vyperAST list integer finite_map

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

Theorem remainder_local_tuple_still_rejected:
  ~source_expr_remainder tops
    (Subscript ty (Name (TupleT ts) name) index)
Proof
  simp[source_expr_remainder_def, source_pure_expr_remainder_def,
       source_effect_expr_remainder_def]
QED

Theorem remainder_program_tuple_still_rejected:
  ~source_program_remainder
    [FunctionDecl External mut nr rr name args defaults ret
      [Return (SOME (Subscript ty (Name (TupleT ts) local_name) index))]]
Proof
  simp[source_program_remainder_def, source_declaration_body_remainder_def,
       source_function_body_remainder_def, source_stmt_remainder_def,
       remainder_local_tuple_still_rejected]
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

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source program remainder test kernel audit: " ^ name) end)
  (DB.thms "sourceProgramSupportTest");
