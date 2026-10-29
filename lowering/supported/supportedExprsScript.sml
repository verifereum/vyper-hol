(* P is recursively pure. E additionally admits effects along place paths.
   TOP-LEVEL: supported_pure_expr, supported_pure_exprs,
   supported_effect_expr, supported_expr. Helpers: supported_pure_fields.
   Storage aggregate values retain their declared type during traversal. Source
   typing remains separate; this does not interpret or evaluate expressions. *)
Theory supportedExprs
Ancestors
  supportedExprForms supportedTypes supportedDecls vyperAST list pair

Definition supported_pure_expr_def:
  supported_pure_expr tops (Name ty name) = T /\
  supported_pure_expr tops (Literal ty lit) = T /\
  supported_pure_expr tops (TopLevelName ty id) =
    supported_storage_value tops id ty /\
  supported_pure_expr tops (FlagMember ty id member) = F /\
  (* A non-word ternary is a PHI of two memory pointers (#561: a14-01,
     a10-04).  Tuple ternaries have no parity witness. *)
  supported_pure_expr tops (IfExp ty c a b) =
    (supported_value_type tops ty /\ ~supported_tuple_type ty /\
     supported_pure_expr tops c /\
     supported_pure_expr tops a /\ supported_pure_expr tops b) /\
  supported_pure_expr tops (StructLit ty id fields) =
    (supported_main_nsid id /\ supported_struct_elements tops ty fields /\
     supported_pure_fields tops fields) /\
  supported_pure_expr tops (Subscript ty base key) =
    (supported_place_type tops ty /\ supported_subscript_place tops base /\
     supported_place_expr tops base /\ supported_pure_expr tops key) /\
  supported_pure_expr tops (Attribute ty base field) =
    (supported_place_type tops ty /\ supported_field_place tops (expr_type base) field /\
     supported_place_expr tops base) /\
  supported_pure_expr tops (Builtin ty blt es) =
    (supported_builtin_form tops ty blt es /\ supported_pure_exprs tops es) /\
  supported_pure_expr tops (TypeBuiltin ty blt target es) =
    (supported_type_builtin_form tops ty blt target es /\ supported_pure_exprs tops es) /\
  supported_pure_expr tops (Pop ty target) = F /\
  supported_pure_expr tops (Call ty target es default) = F /\
  supported_pure_exprs tops [] = T /\
  supported_pure_exprs tops (e::es) =
    (supported_pure_expr tops e /\ supported_pure_exprs tops es) /\
  supported_pure_fields tops [] = T /\
  supported_pure_fields tops ((name,e)::fields) =
    (supported_pure_expr tops e /\ supported_pure_fields tops fields) /\
  supported_place_expr tops (Name ty name) = supported_place_type tops ty /\
  supported_place_expr tops (TopLevelName ty id) = supported_place_root tops id /\
  supported_place_expr tops (Subscript ty base key) =
    (supported_subscript_place tops base /\ supported_place_expr tops base /\
     supported_pure_expr tops key) /\
  supported_place_expr tops (Attribute ty base field) =
    (supported_field_place tops (expr_type base) field /\ supported_place_expr tops base) /\
  supported_place_expr tops e = supported_pure_expr tops e
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, e) => 3 * expr_size e
    | INR (INL (_, es)) => 3 * list_size expr_size es
    | INR (INR (INL (_, fields))) =>
        3 * list_size (pair_size (list_size char_size) expr_size) fields
    | INR (INR (INR (_, e))) => 3 * expr_size e + 1)` >>
  simp[expr_size_def, listTheory.list_size_def,
       basicSizeTheory.pair_size_def]
End

Definition supported_effect_expr_def:
  supported_effect_expr tops (Call ty (IntCall id) args NONE) =
    (IS_SOME (supported_function_decl tops id Internal) /\
     (* Internal struct memory-return handling is deferred to #545. *)
     (case ty of StructT _ => F | _ => T) /\
     supported_pure_exprs tops args) /\
  (* Operands: target :: positional args ++ keyword operands in source
     order. Every operand is pure, so lowering default_return_value= before
     the call matches the semantics, which evaluates it there too. *)
  supported_effect_expr tops
    (Call ty (ExtCall static_call skip_check (name, arg_types, ret) opts) args NONE) =
    (EVERY supported_word_type arg_types /\
     supported_external_return_type tops ret /\
     ALL_DISTINCT opts /\ (static_call ==> ~MEM EKValue opts) /\
     LENGTH args = 1 + LENGTH arg_types + LENGTH opts /\
     supported_pure_exprs tops args) /\
  supported_effect_expr tops (Call NoneT (Send F) [a; v] NONE) =
    (supported_pure_expr tops a /\ supported_pure_expr tops v) /\
  supported_effect_expr tops (Call NoneT (Send T) [a; v; g] NONE) =
    (supported_pure_expr tops a /\ supported_pure_expr tops v /\
     supported_pure_expr tops g) /\
  supported_effect_expr tops (Pop ty (TopLevelNameTarget id)) =
    supported_storage_dynamic_array tops id /\
  supported_effect_expr tops (Subscript ty base key) =
    (supported_place_type tops ty /\ supported_subscript_place tops base /\
     ((supported_place_expr tops base /\ supported_effect_expr tops key) \/
      (supported_effect_place_expr tops base /\
       (supported_pure_expr tops key \/ supported_effect_expr tops key)))) /\
  supported_effect_expr tops (Attribute ty base field) =
    (supported_place_type tops ty /\ supported_field_place tops (expr_type base) field /\
     supported_effect_place_expr tops base) /\
  supported_effect_expr tops e = F /\
  supported_effect_place_expr tops (Subscript ty base key) =
    (supported_subscript_place tops base /\
     ((supported_place_expr tops base /\ supported_effect_expr tops key) \/
      (supported_effect_place_expr tops base /\
       (supported_pure_expr tops key \/ supported_effect_expr tops key)))) /\
  supported_effect_place_expr tops (Attribute ty base field) =
    (supported_field_place tops (expr_type base) field /\
     supported_effect_place_expr tops base) /\
  supported_effect_place_expr tops e = F
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, e) => expr_size e
    | INR (_, e) => expr_size e)` >> simp[expr_size_def]
End

Definition supported_expr_def:
  supported_expr tops e <=>
    supported_pure_expr tops e \/ supported_effect_expr tops e
End

(* ===== Consumer boundary contracts ===== *)

Theorem supported_pure_call_pop_rejected:
  ~supported_pure_expr tops (Call ty target args default) /\
  ~supported_pure_expr tops (Pop ty target2)
Proof
  simp[supported_pure_expr_def]
QED

Theorem supported_external_call_contract:
  supported_effect_expr tops
    (Call ty (ExtCall static_call skip_check (name, arg_types, ret) opts) args
       NONE) <=>
  EVERY supported_word_type arg_types /\
  supported_external_return_type tops ret /\
  ALL_DISTINCT opts /\ (static_call ==> ~MEM EKValue opts) /\
  LENGTH args = 1 + LENGTH arg_types + LENGTH opts /\
  supported_pure_exprs tops args
Proof
  simp[supported_effect_expr_def]
QED

Theorem supported_call_default_rejected:
  ~supported_expr tops (Call ty target args (SOME default))
Proof
  Cases_on `target` >>
  simp[supported_expr_def, supported_effect_expr_def, supported_pure_expr_def] >>
  BasicProvers.every_case_tac >> simp[]
QED

Theorem supported_pure_exprs_every:
  supported_pure_exprs tops es <=> EVERY (supported_pure_expr tops) es
Proof
  Induct_on `es` >> simp[supported_pure_expr_def]
QED

Theorem supported_pure_fields_every:
  supported_pure_fields tops fields <=>
    EVERY (supported_pure_expr tops o SND) fields
Proof
  Induct_on `fields` >> simp[supported_pure_expr_def] >>
  Cases_on `h` >> simp[supported_pure_expr_def]
QED
