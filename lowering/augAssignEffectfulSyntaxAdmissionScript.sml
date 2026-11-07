(* Static fragment checks for the concrete source witness. *)
Theory augAssignEffectfulSyntaxAdmission
Ancestors
  augAssignEffectfulSourceWitness supportedStmts exprSimHypsDefs targetPlaceSim
  supportedTypes supportedTargets supportedExprForms

Theorem effaug_index_syntax:
  supported_expr effaug_tops effaug_index /\
  byte_widths_expr effaug_index /\ int_calls_expr effaug_index = []
Proof
  EVAL_TAC >> simp[]
QED

Theorem effaug_rhs_syntax:
  supported_expr effaug_tops (Literal (BaseT (UintT 8)) (IntL 1)) /\
  byte_widths_expr (Literal (BaseT (UintT 8)) (IntL 1)) /\
  int_calls_expr (Literal (BaseT (UintT 8)) (IntL 1)) = []
Proof
  EVAL_TAC >> simp[]
QED

Theorem effaug_stmt_unsupported:
  ~supported_stmt effaug_tops [] effaug_stmt
Proof
  EVAL_TAC >> simp[]
QED

(* Storage aggregates require full-word leaves, excluding this Uint8 root. *)
Theorem effaug_storage_type_rejected:
  ~supported_storage_type effaug_tops effaug_array_ty /\
  ~supported_place_root effaug_tops (NONE,"a")
Proof
  EVAL_TAC >> simp[]
QED

Theorem effaug_target_rejected:
  supported_target_info effaug_tops []
    (SubscriptTarget
      (SubscriptTarget (TopLevelNameTarget (NONE,"a"))
        (Literal (BaseT (UintT 256)) (IntL 0))) effaug_index) = NONE
Proof
  EVAL_TAC >> simp[]
QED
