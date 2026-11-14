Theory vyperPinFold
Ancestors
  vyperConstEval vyperContext vyperValueOperation vyperAST list option
Libs
  cv_transLib

Definition is_int_literal_def:
  is_int_literal (Literal _ (IntL _)) = T /\
  is_int_literal _ = F
End

val () = cv_auto_trans is_int_literal_def;

Definition pin_constant_literal_def:
  pin_constant_literal (DecimalV i) = SOME (DecimalL i) /\
  pin_constant_literal v = constant_literal v
End

val () = cv_auto_trans pin_constant_literal_def;

Definition pin_literal_values_def:
  pin_literal_values [] = SOME [] /\
  pin_literal_values (Literal ty l :: es) =
    OPTION_MAP (CONS (evaluate_literal l)) (pin_literal_values es) /\
  pin_literal_values _ = NONE
End

val () = cv_auto_trans pin_literal_values_def;

Definition pin_foldable_builtin_def:
  pin_foldable_builtin (Bop b) =
    (~MEM b [In; NotIn; UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv]) /\
  pin_foldable_builtin Not = T /\
  pin_foldable_builtin Neg = T /\
  pin_foldable_builtin Abs = T /\
  pin_foldable_builtin (AsWeiValue _) = T /\
  pin_foldable_builtin Floor = T /\
  pin_foldable_builtin Ceil = T /\
  pin_foldable_builtin AddMod = T /\
  pin_foldable_builtin MulMod = T /\
  pin_foldable_builtin PowMod256 = T /\
  pin_foldable_builtin (Uint2Str _) = T /\
  pin_foldable_builtin Keccak256 = T /\
  pin_foldable_builtin MethodId = T /\
  pin_foldable_builtin _ = F
End

val () = cv_auto_trans pin_foldable_builtin_def;

Definition pin_fold_result_def:
  pin_fold_result ty original r =
    case r of
    | INL v =>
        (case pin_constant_literal v of
         | SOME l => Literal ty l
         | NONE => original)
    | INR err => original
End

val () = cv_auto_trans pin_fold_result_def;

Definition pin_fold_builtin_def:
  pin_fold_builtin (BaseT bt) b es =
    (let original = Builtin (BaseT bt) b es in
    case (b,es) of
    | (Len,[Literal _ (BytesL bs)]) =>
        Literal (BaseT bt) (IntL (&(LENGTH bs)))
    | (Len,[Literal _ (StringL s)]) =>
        Literal (BaseT bt) (IntL (&(LENGTH s)))
    | _ =>
        if ~pin_foldable_builtin b \/
           ~builtin_args_length_ok b (LENGTH es) \/
           ~EVERY (\e. ?bt. expr_type e = BaseT bt) es then original
        else case pin_literal_values es of
             | NONE => original
             | SOME vs => pin_fold_result (BaseT bt) original
                 (evaluate_builtin empty_evaluation_context empty_accounts
                   (BaseT bt) b (MAP expr_type es) vs)) /\
  pin_fold_builtin ty b es = Builtin ty b es
End

Triviality pin_base_type_case:
  (?bt. ty = BaseT bt) = (case ty of BaseT _ => T | _ => F)
Proof
  Cases_on `ty` >> simp[]
QED

val () = cv_auto_trans (REWRITE_RULE [pin_base_type_case] pin_fold_builtin_def);

(* The array guards ensure that selecting a member cannot discard an
   unevaluated effect, failure or type lookup. *)
Definition pin_literal_tree_def:
  pin_literal_tree (Literal ty l) = T /\
  pin_literal_tree (Builtin ty (MakeArray (SOME elem) bd) es) =
    (ty = ArrayT elem bd /\
     IS_SOME (evaluate_type FEMPTY (ArrayT elem bd)) /\
     compatible_bound bd (LENGTH es) /\
     EVERY (\e. expr_type e = elem) es /\ pin_literal_trees es) /\
  pin_literal_tree _ = F /\
  pin_literal_trees [] = T /\
  pin_literal_trees (e::es) =
    (pin_literal_tree e /\ pin_literal_trees es)
End

val () = cv_auto_trans pin_literal_tree_def;

Definition pin_fold_subscript_def:
  pin_fold_subscript ty base index =
    case (base,index) of
    | (Builtin aty (MakeArray (SOME elem) bd) es,
       Literal ity (IntL i)) =>
        if pin_literal_tree base /\ ty = elem /\
           0 <= i /\ Num i < LENGTH es
        then EL (Num i) es
        else Subscript ty base index
    | _ => Subscript ty base index
End

val pin_fold_subscript_pre_def =
  cv_auto_trans_pre "pin_fold_subscript_pre" pin_fold_subscript_def;

Theorem pin_fold_subscript_pre[cv_pre]:
  pin_fold_subscript_pre ty arr index
Proof
  rw[pin_fold_subscript_pre_def, AllCaseEqs()]
QED

Definition pin_fold_expr_def[nocompute]:
  pin_fold_expr (Builtin ty b es) =
    pin_fold_builtin ty b (pin_fold_exprs es) /\
  pin_fold_expr (TypeBuiltin (BaseT bt) MaxValue typ []) =
    pin_fold_result (BaseT bt)
      (TypeBuiltin (BaseT bt) MaxValue typ []) (evaluate_max_value typ) /\
  pin_fold_expr (TypeBuiltin (BaseT bt) MinValue typ []) =
    pin_fold_result (BaseT bt)
      (TypeBuiltin (BaseT bt) MinValue typ []) (evaluate_min_value typ) /\
  pin_fold_expr (TypeBuiltin (BaseT bt) Epsilon typ []) =
    pin_fold_result (BaseT bt)
      (TypeBuiltin (BaseT bt) Epsilon typ [])
      (evaluate_type_builtin empty_evaluation_context Epsilon typ [] []) /\
  pin_fold_expr (Subscript ty base index) =
    pin_fold_subscript ty (pin_fold_expr base) (pin_fold_expr index) /\
  pin_fold_expr e = e /\
  pin_fold_exprs [] = [] /\
  pin_fold_exprs (e::es) = pin_fold_expr e :: pin_fold_exprs es
End

val () = cv_auto_trans pin_fold_expr_def;

Theorem pin_fold_literal[simp]:
  pin_fold_expr (Literal ty l) = Literal ty l
Proof
  simp[pin_fold_expr_def]
QED

Theorem pin_fold_result_type:
  expr_type original = ty ==>
  expr_type (pin_fold_result ty original r) = ty
Proof
  rw[pin_fold_result_def] >> BasicProvers.every_case_tac >> simp[expr_type_def]
QED

Theorem pin_fold_builtin_type[simp]:
  expr_type (pin_fold_builtin ty b es) = ty
Proof
  Cases_on `ty` >>
  rw[pin_fold_builtin_def] >> BasicProvers.every_case_tac >>
  simp[expr_type_def, pin_fold_result_type]
QED

Theorem pin_fold_subscript_type[simp]:
  expr_type (pin_fold_subscript ty arr index) = ty
Proof
  rw[pin_fold_subscript_def] >> BasicProvers.every_case_tac >>
  gvs[expr_type_def] >>
  gvs[pin_literal_tree_def] >>
  gvs[EVERY_EL] >> first_x_assum irule >> simp[]
QED

Theorem pin_fold_expr_type[simp]:
  expr_type (pin_fold_expr e) = expr_type e
Proof
  qsuff_tac `(!e. expr_type (pin_fold_expr e) = expr_type e) /\
             (!es. MAP expr_type (pin_fold_exprs es) = MAP expr_type es)`
  >- simp[] >>
  ho_match_mp_tac pin_fold_expr_ind >>
  rw[pin_fold_expr_def, expr_type_def, pin_fold_result_type]
QED

Theorem is_int_literal_iff:
  is_int_literal e <=> ?ty i. e = Literal ty (IntL i)
Proof
  Cases_on `e` >> simp[is_int_literal_def] >>
  rename1 `Literal ty l` >> Cases_on `l` >> simp[is_int_literal_def]
QED

