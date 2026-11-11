Theory vyperConstEval
Ancestors
  vyperInterpreter vyperContext vyperState vyperValue vyperAST
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
