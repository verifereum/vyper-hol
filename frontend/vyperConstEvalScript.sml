Theory vyperConstEval
Ancestors
  vyperEvalPureExpr vyperContext vyperState vyperValue vyperAST
  vyperValueOperation
Libs
  cv_transLib

(* Compile-time values of source expressions, computed with the interpreter's
   own literal and builtin operations. Only operations that read neither the
   runtime context nor the state are admitted. Decimal values are left to
   runtime evaluation. *)
Definition closed_builtin_def:
  closed_builtin (Bop bop) = (bop <> In /\ bop <> NotIn) /\
  closed_builtin Not = T /\
  closed_builtin Neg = T /\
  closed_builtin MethodId = T /\
  closed_builtin _ = F
End

(* Not in EVAL's rewrites: method_id hashes with Keccak, which rewriting
   evaluates far too slowly. vyperConstEvalLib has EVAL compute eval_constant
   with cv_eval instead. *)
Definition eval_constant_def[nocompute]:
  eval_constant (Literal (BaseT bt) l) =
    (if bt = DecimalT then NONE else SOME (evaluate_literal l)) /\
  eval_constant (Builtin (BaseT bt) b es) =
    (if bt = DecimalT \/ ~closed_builtin b \/
        ~builtin_args_length_ok b (LENGTH es) then NONE
     else case eval_constants es of
          | NONE => NONE
          | SOME vs =>
              (case evaluate_builtin empty_evaluation_context empty_accounts
                      (BaseT bt) b (MAP expr_type es) vs of
               | INL v => SOME v
               | INR _ => NONE)) /\
  eval_constant (TypeBuiltin (BaseT bt) MaxValue typ []) =
    (if bt = DecimalT then NONE
     else case evaluate_max_value typ of INL v => SOME v | INR _ => NONE) /\
  eval_constant (TypeBuiltin (BaseT bt) MinValue typ []) =
    (if bt = DecimalT then NONE
     else case evaluate_min_value typ of INL v => SOME v | INR _ => NONE) /\
  eval_constant _ = NONE /\
  eval_constants [] = SOME [] /\
  eval_constants (e::es) =
    (case (eval_constant e, eval_constants es) of
     | (SOME v, SOME vs) => SOME (v::vs)
     | _ => NONE)
End

val () = cv_auto_trans eval_constant_def;

(* The literal a computed value is written back as. *)
Definition constant_literal_def:
  constant_literal (IntV i) = SOME (IntL i) /\
  constant_literal (BoolV b) = SOME (BoolL b) /\
  constant_literal (StringV s) = SOME (StringL s) /\
  constant_literal (BytesV bs) = SOME (BytesL bs) /\
  constant_literal _ = NONE
End

Theorem constant_literal_evaluate:
  constant_literal v = SOME l ==> evaluate_literal l = v
Proof
  Cases_on `v` >> rw[constant_literal_def] >> simp[evaluate_literal_def]
QED

Theorem evaluate_builtin_closed[local]:
  closed_builtin b /\ EVERY (\t. ?bt. t = BaseT bt) tys ==>
  evaluate_builtin cx acc (BaseT bt) b tys vs =
  evaluate_builtin empty_evaluation_context empty_accounts (BaseT bt) b tys vs
Proof
  Cases_on `b` >> rw[closed_builtin_def] >>
  simp[evaluate_builtin_def, evaluate_type_def] >>
  Cases_on `tys` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[evaluate_type_def]
QED

Theorem eval_constant_pure:
  (!e v. eval_constant e = SOME v ==>
     (?bt. expr_type e = BaseT bt) /\
     !cx st. eval_pure_expr cx st e = SOME (Value v)) /\
  (!es vs. eval_constants es = SOME vs ==>
     EVERY (\t. ?bt. t = BaseT bt) (MAP expr_type es) /\
     !cx st. eval_pure_exprs cx st es = SOME vs)
Proof
  ho_match_mp_tac eval_constant_ind >>
  rw[eval_constant_def, AllCaseEqs()] >>
  gvs[expr_type_def, eval_pure_expr_def, evaluate_literal_def,
      read_result_def, return_def, evaluate_type_builtin_def,
      type_builtin_args_length_ok_def] >>
  `b <> Len /\ b <> Bop In /\ b <> Bop NotIn` by
    (Cases_on `b` >> gvs[closed_builtin_def]) >>
  gvs[] >>
  drule_all evaluate_builtin_closed >> simp[]
QED

(* A computed value is what the interpreter returns in any context and state,
   leaving the state unchanged. *)
Theorem eval_constant_sound:
  eval_constant e = SOME v ==>
  eval_expr cx e st = (INL (Value v), st)
Proof
  strip_tac >> irule eval_pure_expr_to_eval_expr_some >>
  drule (cj 1 eval_constant_pure) >> simp[]
QED
