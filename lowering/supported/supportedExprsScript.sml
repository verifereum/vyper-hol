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
  supported_pure_expr tops (IfExp ty c a b) =
    (supported_word_type ty /\ supported_pure_expr tops c /\
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
    (supported_type_builtin_form ty blt target es /\ supported_pure_exprs tops es) /\
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
    | INR (INL (_, es)) => 3 * expr4_size es
    | INR (INR (INL (_, fields))) => 3 * expr1_size fields
    | INR (INR (INR (_, e))) => 3 * expr_size e + 1)` >>
  simp[expr_size_def]
End

(* The source semantics evaluates a default_return_value only when the callee
   returns no data, the lowering evaluates it before the call (until #553's
   a06-07). Both agree when the default is a literal or a name. *)
Definition supported_external_default_def:
  supported_external_default tops NONE = T /\
  supported_external_default tops (SOME e) =
    ((case e of Literal _ _ => T | Name _ _ => T | _ => F) /\
     supported_pure_expr tops e)
End

Definition supported_effect_expr_def:
  supported_effect_expr tops (Call ty (IntCall id) args NONE) =
    (IS_SOME (supported_function_decl tops id Internal) /\
     (* Internal struct memory-return handling is deferred to #545. *)
     (case ty of StructT _ => F | _ => T) /\
     supported_pure_exprs tops args) /\
  supported_effect_expr tops
    (Call ty (ExtCall static_call skip_check (name, arg_types, ret)) args default) =
    (EVERY supported_word_type arg_types /\
     supported_external_return_type tops ret /\
     LENGTH args = LENGTH arg_types + (if static_call then 1 else 2) /\
     supported_pure_exprs tops args /\ supported_external_default tops default) /\
  supported_effect_expr tops (Call ty Send args default) =
    (ty = NoneT /\ default = NONE /\ LENGTH args = 2 /\
     supported_pure_exprs tops args) /\
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
    (Call ty (ExtCall static_call skip_check (name, arg_types, ret)) args default) <=>
  EVERY supported_word_type arg_types /\
  supported_external_return_type tops ret /\
  LENGTH args = LENGTH arg_types + (if static_call then 1 else 2) /\
  supported_pure_exprs tops args /\
  supported_external_default tops default
Proof
  simp[supported_effect_expr_def]
QED

Theorem supported_external_default_contract:
  supported_external_default tops (SOME e) <=>
  ((?ty l. e = Literal ty l) \/ (?ty n. e = Name ty n)) /\
  supported_pure_expr tops e
Proof
  Cases_on `e` >> simp[supported_external_default_def]
QED

Theorem supported_call_default_rejected:
  (!static_call skip_check sig. target <> ExtCall static_call skip_check sig) ==>
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
