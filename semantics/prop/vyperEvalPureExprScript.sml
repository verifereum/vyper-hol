Theory vyperEvalPureExpr

Ancestors
  vyperPureExpr vyperLookup

(* ===== eval_pure_expr / eval_pure_exprs ===== *)
(*
  eval_pure_expr  : cx -> st -> expr -> toplevel_value option
  eval_pure_exprs : cx -> st -> expr list -> value list option

  eval_pure_expr evaluates a pure expression, returning a toplevel_value
  (which may be a Value, ArrayRef, or HashMapRef).

  eval_pure_exprs evaluates a list of pure expressions, materialising
  each result to a value (reading from storage if needed).
*)

Definition eval_pure_expr_def:
  (* Base cases *)
  eval_pure_expr cx st (Name id) =
    OPTION_MAP Value (lookup_scoped_var st id) ∧

  eval_pure_expr cx st (TopLevelName nsid) =
    (case eval_expr cx (TopLevelName nsid) st of
     | (INL tv, _) => SOME tv
     | _ => NONE) ∧

  eval_pure_expr cx st (FlagMember nsid mid) =
    lookup_flag_member cx nsid mid ∧

  eval_pure_expr cx st (Literal l) =
    SOME (Value (evaluate_literal l)) ∧

  (* Conditional *)
  eval_pure_expr cx st (IfExp cond et ef) =
    (case eval_pure_expr cx st cond of
     | SOME (Value (BoolV T)) => eval_pure_expr cx st et
     | SOME (Value (BoolV F)) => eval_pure_expr cx st ef
     | _ => NONE) ∧

  (* Struct literal *)
  eval_pure_expr cx st (StructLit src kes) =
    (case eval_pure_exprs cx st (MAP SND kes) of
     | SOME vs => SOME (Value (StructV (ZIP (MAP FST kes, vs))))
     | NONE => NONE) ∧

  (* Subscript *)
  eval_pure_expr cx st (Subscript e1 e2) =
    (case eval_pure_expr cx st e1 of
     | SOME tv1 =>
       (case eval_pure_expr cx st e2 of
        | SOME (Value v2) =>
          (case check_array_bounds cx tv1 v2 st of
           | (INL _, _) =>
             (case evaluate_subscript (get_tenv cx) tv1 v2 of
              | INL (INL tv) => SOME tv
              | INL (INR (is_transient, slot, tv)) =>
                (case read_storage_slot cx is_transient slot tv st of
                 | (INL v, _) => SOME (Value v)
                 | _ => NONE)
              | INR _ => NONE)
           | _ => NONE)
        | _ => NONE)
     | NONE => NONE) ∧

  (* Attribute access *)
  eval_pure_expr cx st (Attribute e id) =
    (case eval_pure_expr cx st e of
     | SOME (Value sv) =>
       (case evaluate_attribute sv id of
        | INL v => SOME (Value v)
        | INR _ => NONE)
     | _ => NONE) ∧

  (* General builtins *)
  eval_pure_expr cx st (Builtin bt es) =
    (case eval_pure_exprs cx st es of
     | SOME vs =>
       (case evaluate_builtin cx st.accounts bt vs of
        | INL v => SOME (Value v)
        | INR _ => NONE)
     | NONE => NONE) ∧

  (* General type builtins *)
  eval_pure_expr cx st (TypeBuiltin tb typ es) =
    (case eval_pure_exprs cx st es of
     | SOME vs =>
       (case evaluate_type_builtin cx tb typ vs of
        | INL v => SOME (Value v)
        | INR _ => NONE)
     | NONE => NONE) ∧

  (* Non-pure expressions *)
  eval_pure_expr cx st _ = NONE ∧

  (* eval_pure_exprs: evaluate list, materialising each result *)
  eval_pure_exprs cx st [] = SOME [] ∧

  eval_pure_exprs cx st (e::es) =
    (case eval_pure_expr cx st e of
     | SOME tv =>
       (case materialise cx tv st of
        | (INL v, _) =>
          (case eval_pure_exprs cx st es of
           | SOME vs => SOME (v::vs)
           | NONE => NONE)
        | _ => NONE)
     | NONE => NONE)
Termination
  WF_REL_TAC `measure (sum_size
    (\(cx:evaluation_context, st:evaluation_state, e). expr_size e)
    (\(cx:evaluation_context, st:evaluation_state, es).
       list_size expr_size es))` >>
  rpt gen_tac >>
  Induct_on `kes` >>
  simp[pairTheory.FORALL_PROD, basicSizeTheory.pair_size_def]
End

(* Convenience wrapper: evaluate pure expression to value *)
Definition eval_pure_value_def:
  eval_pure_value cx st e =
    (case eval_pure_expr cx st e of
     | SOME tv =>
       (case materialise cx tv st of
        | (INL v, _) => SOME v
        | _ => NONE)
     | NONE => NONE)
End
