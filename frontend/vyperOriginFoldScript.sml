Theory vyperOriginFold
Ancestors
  vyperAST vyperPinFold
Libs
  cv_transLib

(* Comparisons need the JSON source classes. The pin leaves bytes32
   bitwise operations, shifts and inversion to runtime. *)
Definition origin_fold_builtin_def:
  origin_fold_builtin ty b es =
    case b of
    | Bop bop =>
        if MEM bop [Eq; NotEq] then Builtin ty b es
        else if MEM bop [And; Or; XOr; ShL; ShR] then
          (case es of
           | [Literal _ (IntL _); Literal _ (IntL _)] => pin_fold_builtin ty b es
           | _ => Builtin ty b es)
        else pin_fold_builtin ty b es
    | Not =>
        (case es of
         | [Literal _ (BoolL _)] => pin_fold_builtin ty b es
         | [Literal _ (IntL _)] => pin_fold_builtin ty b es
         | _ => Builtin ty b es)
    | _ => pin_fold_builtin ty b es
End

val () = cv_auto_trans origin_fold_builtin_def;

Theorem origin_fold_builtin_type[local,simp]:
  expr_type (origin_fold_builtin ty b es) = ty
Proof
  Cases_on `b` >> simp[origin_fold_builtin_def] >>
  rw[] >> BasicProvers.every_case_tac >> simp[expr_type_def]
QED

(* Source-approved selectors and equalities reduce before this traversal. *)
Definition origin_fold_value_def[nocompute]:
  origin_fold_value (Builtin ty b es) =
    origin_fold_builtin ty b (origin_fold_values es) /\
  origin_fold_value (TypeBuiltin (BaseT bt) MaxValue typ []) =
    pin_fold_expr (TypeBuiltin (BaseT bt) MaxValue typ []) /\
  origin_fold_value (TypeBuiltin (BaseT bt) MinValue typ []) =
    pin_fold_expr (TypeBuiltin (BaseT bt) MinValue typ []) /\
  origin_fold_value (TypeBuiltin (BaseT bt) Epsilon typ []) =
    pin_fold_expr (TypeBuiltin (BaseT bt) Epsilon typ []) /\
  origin_fold_value e = e /\
  origin_fold_values [] = [] /\
  origin_fold_values (e::es) = origin_fold_value e :: origin_fold_values es
End

val () = cv_auto_trans origin_fold_value_def;

Theorem origin_fold_value_literal[simp]:
  origin_fold_value (Literal ty l) = Literal ty l
Proof
  simp[origin_fold_value_def]
QED

Theorem origin_fold_value_type[simp]:
  expr_type (origin_fold_value e) = expr_type e
Proof
  qsuff_tac `(!e. expr_type (origin_fold_value e) = expr_type e) /\
             (!es. MAP expr_type (origin_fold_values es) = MAP expr_type es)`
  >- simp[] >>
  ho_match_mp_tac origin_fold_value_ind >>
  rw[origin_fold_value_def, expr_type_def]
QED
