(* PLAN 5.6: P is recursively pure; E is effectful only at the root.
   TOP-LEVEL: supported_pure_expr, supported_pure_exprs,
   supported_effect_expr, supported_expr. Helpers: supported_pure_fields.
   Storage aggregate bases are places, not standalone P values. Source
   typing remains separate; this does not interpret or evaluate expressions. *)
Theory supportedExprs
Ancestors
  supportedExprForms supportedTypes supportedDecls vyperAST list pair

Definition supported_pure_expr_def:
  supported_pure_expr tops (Name ty name) = T /\
  supported_pure_expr tops (Literal ty lit) = T /\
  supported_pure_expr tops (TopLevelName ty id) =
    (supported_storage_scalar tops id ty \/
     supported_immutable_type tops id = SOME ty) /\
  supported_pure_expr tops (FlagMember ty id member) = F /\
  (* A non-word ternary is a PHI of two memory pointers (#561: a14-01,
     a10-04).  Tuple ternaries have no parity witness. *)
  supported_pure_expr tops (IfExp ty c a b) =
    (supported_value_type tops ty /\ ~supported_tuple_type ty /\
     supported_pure_expr tops c /\
     supported_pure_expr tops a /\ supported_pure_expr tops b) /\
  supported_pure_expr tops (StructLit ty id fields) =
    (supported_main_nsid id /\ supported_value_type tops ty /\
     supported_pure_fields tops fields) /\
  supported_pure_expr tops (Subscript ty base key) =
    ((case base of
        TopLevelName bt id => supported_subscript_base tops id
      | _ => F) /\ supported_pure_expr tops key) /\
  supported_pure_expr tops (Attribute ty base field) =
    (case base of
       TopLevelName bt id => supported_storage_field_read tops id field
     | _ => F) /\
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
    (supported_pure_expr tops e /\ supported_pure_fields tops fields)
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, e) => expr_size e
    | INR (INL (_, es)) => expr4_size es
    | INR (INR (_, fields)) => expr1_size fields)` >>
  simp[expr_size_def] >>
  qsuff_tac
    `(!es. expr4_size es = list_size expr_size es) /\
     (!fields. expr1_size fields =
       list_size (pair_size (list_size char_size) expr_size) fields)`
  >- (strip_tac >> asm_rewrite_tac[] >> DECIDE_TAC) >>
  conj_tac >> Induct >>
  simp[expr_size_def, listTheory.list_size_def, basicSizeTheory.pair_size_def] >>
  Cases >> simp[expr_size_def, basicSizeTheory.pair_size_def]
End

Definition supported_effect_expr_def:
  supported_effect_expr tops e <=>
    case e of
      Call ty (IntCall id) args NONE =>
        IS_SOME (supported_function_decl tops id Internal) /\
        supported_pure_exprs tops args
    (* Operands: target :: positional args ++ keyword operands in source
       order. Every operand is pure, so lowering default_return_value= before
       the call matches the semantics, which evaluates it there too. *)
    | Call ty (ExtCall is_static skip_check (name, arg_types, ret) opts) args NONE =>
        EVERY supported_word_type arg_types /\
        supported_external_return_type tops ret /\
        ALL_DISTINCT opts /\ (is_static ==> ~MEM EKValue opts) /\
        LENGTH args = 1 + LENGTH arg_types + LENGTH opts /\
        supported_pure_exprs tops args
    | Call NoneT (Send F) [a; v] NONE =>
        supported_pure_expr tops a /\ supported_pure_expr tops v
    | Call NoneT (Send T) [a; v; g] NONE =>
        supported_pure_expr tops a /\ supported_pure_expr tops v /\
        supported_pure_expr tops g
    | Pop ty (TopLevelNameTarget id) =>
        supported_storage_dynamic_array tops id
    | _ => F
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
    (Call ty (ExtCall is_static skip_check (name, arg_types, ret) opts) args
       NONE) <=>
  EVERY supported_word_type arg_types /\
  supported_external_return_type tops ret /\
  ALL_DISTINCT opts /\ (is_static ==> ~MEM EKValue opts) /\
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
