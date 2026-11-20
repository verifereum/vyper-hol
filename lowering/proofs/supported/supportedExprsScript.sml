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
    (supported_storage_value tops id ty \/
     supported_immutable_type tops id = SOME ty) /\
  supported_pure_expr tops (FlagMember ty id member) = T /\
  (* A non-word ternary is a PHI of two memory pointers (#561: a14-01,
     a10-04).  Tuple ternaries have no parity witness. *)
  (* SCRATCH SEQ-8389: ternaries of every type *)
  supported_pure_expr tops (IfExp ty c a b) =
    (supported_pure_expr tops c /\
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
  (* SCRATCH SEQ-8389: effects below the root, every call target and pop *)
  supported_pure_expr tops (Pop ty target) = T /\
  supported_pure_expr tops (Call ty target es default) =
    ((case target of
        IntCall id => IS_SOME (supported_function_decl tops id Internal)
      | _ => T) /\
     supported_pure_exprs tops es /\
     (case default of NONE => T | SOME d => supported_pure_expr tops d)) /\
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
       basicSizeTheory.pair_size_def, basicSizeTheory.option_size_def]
End

(* SCRATCH SEQ-8389: the effect-free fragment of supported_pure_expr (its
   arms before the widening let calls and pops below the root).  Pure-
   expression lemmas the widening makes false are restated over it, and
   their callers split on it. *)
Definition supported_effect_free_expr_def:
  supported_effect_free_expr tops (Name ty name) = T /\
  supported_effect_free_expr tops (Literal ty lit) = T /\
  supported_effect_free_expr tops (TopLevelName ty id) =
    (supported_storage_value tops id ty \/
     supported_immutable_type tops id = SOME ty) /\
  supported_effect_free_expr tops (FlagMember ty id member) = T /\
  (* A non-word ternary is a PHI of two memory pointers (#561: a14-01,
     a10-04).  Tuple ternaries have no parity witness. *)
  (* SCRATCH SEQ-8389: ternaries of every type *)
  supported_effect_free_expr tops (IfExp ty c a b) =
    (supported_effect_free_expr tops c /\
     supported_effect_free_expr tops a /\ supported_effect_free_expr tops b) /\
  supported_effect_free_expr tops (StructLit ty id fields) =
    (supported_main_nsid id /\ supported_struct_elements tops ty fields /\
     supported_effect_free_fields tops fields) /\
  supported_effect_free_expr tops (Subscript ty base key) =
    (supported_place_type tops ty /\ supported_subscript_place tops base /\
     supported_effect_free_place_expr tops base /\ supported_effect_free_expr tops key) /\
  supported_effect_free_expr tops (Attribute ty base field) =
    (supported_place_type tops ty /\ supported_field_place tops (expr_type base) field /\
     supported_effect_free_place_expr tops base) /\
  supported_effect_free_expr tops (Builtin ty blt es) =
    (supported_builtin_form tops ty blt es /\ supported_effect_free_exprs tops es) /\
  supported_effect_free_expr tops (TypeBuiltin ty blt target es) =
    (supported_type_builtin_form tops ty blt target es /\ supported_effect_free_exprs tops es) /\
  supported_effect_free_expr tops (Pop ty target) = F /\
  supported_effect_free_expr tops (Call ty target es default) = F /\
  supported_effect_free_exprs tops [] = T /\
  supported_effect_free_exprs tops (e::es) =
    (supported_effect_free_expr tops e /\ supported_effect_free_exprs tops es) /\
  supported_effect_free_fields tops [] = T /\
  supported_effect_free_fields tops ((name,e)::fields) =
    (supported_effect_free_expr tops e /\ supported_effect_free_fields tops fields) /\
  supported_effect_free_place_expr tops (Name ty name) = supported_place_type tops ty /\
  supported_effect_free_place_expr tops (TopLevelName ty id) = supported_place_root tops id /\
  supported_effect_free_place_expr tops (Subscript ty base key) =
    (supported_subscript_place tops base /\ supported_effect_free_place_expr tops base /\
     supported_effect_free_expr tops key) /\
  supported_effect_free_place_expr tops (Attribute ty base field) =
    (supported_field_place tops (expr_type base) field /\ supported_effect_free_place_expr tops base) /\
  supported_effect_free_place_expr tops e = supported_effect_free_expr tops e
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

(* SCRATCH SEQ-8389: the effect-free fragment is a fragment *)
Theorem supported_effect_free_pure:
  (!tops e. supported_effect_free_expr tops e ==> supported_pure_expr tops e) /\
  (!tops es. supported_effect_free_exprs tops es ==> supported_pure_exprs tops es) /\
  (!tops fields. supported_effect_free_fields tops fields ==>
     supported_pure_fields tops fields) /\
  (!tops e. supported_effect_free_place_expr tops e ==> supported_place_expr tops e)
Proof
  ho_match_mp_tac supported_effect_free_expr_ind >> rw[] >>
  gvs[supported_effect_free_expr_def, supported_pure_expr_def]
QED

Definition supported_effect_expr_def:
  (* SCRATCH SEQ-8389: struct returns and defaults *)
  supported_effect_expr tops (Call ty (IntCall id) args default) =
    (IS_SOME (supported_function_decl tops id Internal) /\
     supported_pure_exprs tops args /\
     (case default of NONE => T | SOME d => supported_pure_expr tops d)) /\
  (* Operands: target :: positional args ++ keyword operands in source
     order. Every operand is pure, so lowering default_return_value= before
     the call matches the semantics, which evaluates it there too. *)
  supported_effect_expr tops
    (Call ty (ExtCall static_call skip_check (name, arg_types, ret) opts) args default) =
    (* SCRATCH SEQ-8389: every argument and return type, value= on staticcall *)
    (supported_external_return_type tops ret /\
     ALL_DISTINCT opts /\
     LENGTH args = 1 + LENGTH arg_types + LENGTH opts /\
     supported_pure_exprs tops args /\
     (case default of NONE => T | SOME d => supported_pure_expr tops d)) /\
  supported_effect_expr tops (Call NoneT (Send F) [a; v] NONE) =
    (supported_pure_expr tops a /\ supported_pure_expr tops v) /\
  supported_effect_expr tops (Call NoneT (Send T) [a; v; g] NONE) =
    (supported_pure_expr tops a /\ supported_pure_expr tops v /\
     supported_pure_expr tops g) /\
  (* SCRATCH SEQ-8389: pop on every target *)
  supported_effect_expr tops (Pop ty target) = T /\
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

(* SCRATCH SEQ-8389: effects at the root only, with the arms the gate had
   before the widening (internal calls without defaults or struct returns,
   word-argument external calls, storage pops) over effect-free operands.
   Effect lemmas the widening makes false are restated over it, and their
   callers split on it. *)
Definition supported_root_effect_expr_def:
  supported_root_effect_expr tops (Call ty (IntCall id) args NONE) =
    (IS_SOME (supported_function_decl tops id Internal) /\
     (* Internal struct memory-return handling is deferred to #545. *)
     (case ty of StructT _ => F | _ => T) /\
     supported_effect_free_exprs tops args) /\
  (* Operands: target :: positional args ++ keyword operands in source
     order. Every operand is pure, so lowering default_return_value= before
     the call matches the semantics, which evaluates it there too. *)
  supported_root_effect_expr tops
    (Call ty (ExtCall static_call skip_check (name, arg_types, ret) opts) args NONE) =
    (EVERY supported_word_type arg_types /\
     supported_external_return_type tops ret /\
     ALL_DISTINCT opts /\ (static_call ==> ~MEM EKValue opts) /\
     LENGTH args = 1 + LENGTH arg_types + LENGTH opts /\
     supported_effect_free_exprs tops args) /\
  supported_root_effect_expr tops (Call NoneT (Send F) [a; v] NONE) =
    (supported_effect_free_expr tops a /\ supported_effect_free_expr tops v) /\
  supported_root_effect_expr tops (Call NoneT (Send T) [a; v; g] NONE) =
    (supported_effect_free_expr tops a /\ supported_effect_free_expr tops v /\
     supported_effect_free_expr tops g) /\
  supported_root_effect_expr tops (Pop ty (TopLevelNameTarget id)) =
    supported_storage_dynamic_array tops id /\
  supported_root_effect_expr tops (Subscript ty base key) =
    (supported_place_type tops ty /\ supported_subscript_place tops base /\
     ((supported_effect_free_place_expr tops base /\ supported_root_effect_expr tops key) \/
      (supported_root_effect_place_expr tops base /\
       (supported_effect_free_expr tops key \/ supported_root_effect_expr tops key)))) /\
  supported_root_effect_expr tops (Attribute ty base field) =
    (supported_place_type tops ty /\ supported_field_place tops (expr_type base) field /\
     supported_root_effect_place_expr tops base) /\
  supported_root_effect_expr tops e = F /\
  supported_root_effect_place_expr tops (Subscript ty base key) =
    (supported_subscript_place tops base /\
     ((supported_effect_free_place_expr tops base /\ supported_root_effect_expr tops key) \/
      (supported_root_effect_place_expr tops base /\
       (supported_effect_free_expr tops key \/ supported_root_effect_expr tops key)))) /\
  supported_root_effect_place_expr tops (Attribute ty base field) =
    (supported_field_place tops (expr_type base) field /\
     supported_root_effect_place_expr tops base) /\
  supported_root_effect_place_expr tops e = F
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, e) => expr_size e
    | INR (_, e) => expr_size e)` >> simp[expr_size_def]
End

Definition supported_root_expr_def:
  supported_root_expr tops e <=>
    supported_effect_free_expr tops e \/ supported_root_effect_expr tops e
End

(* SCRATCH SEQ-8389: the root-effect fragment is a fragment *)
Theorem supported_root_effect_effect:
  (!tops e. supported_root_effect_expr tops e ==> supported_effect_expr tops e) /\
  (!tops e. supported_root_effect_place_expr tops e ==>
     supported_effect_place_expr tops e)
Proof
  ho_match_mp_tac supported_root_effect_expr_ind >> rw[] >>
  gvs[supported_root_effect_expr_def, supported_effect_expr_def] >>
  metis_tac[supported_effect_free_pure]
QED

Theorem supported_root_expr_supported:
  supported_root_expr tops e ==> supported_expr tops e
Proof
  rw[supported_root_expr_def, supported_expr_def] >>
  metis_tac[supported_effect_free_pure, supported_root_effect_effect]
QED

(* ===== Consumer boundary contracts ===== *)

(* SCRATCH SEQ-8389 DELETED: false under the widened gate (it pinned an exclusion); no theorem uses it
  Theorem supported_pure_call_pop_rejected:
    ~supported_pure_expr tops (Call ty target args default) /\
    ~supported_pure_expr tops (Pop ty target2)
  Proof
    simp[supported_pure_expr_def]
  QED
*)

Theorem supported_external_call_contract:
  supported_effect_expr tops
    (Call ty (ExtCall static_call skip_check (name, arg_types, ret) opts) args
       NONE) <=>
  (* SCRATCH SEQ-8389: restated to the widened definition *)
  supported_external_return_type tops ret /\
  ALL_DISTINCT opts /\
  LENGTH args = 1 + LENGTH arg_types + LENGTH opts /\
  supported_pure_exprs tops args
Proof
  simp[supported_effect_expr_def]
QED

(* SCRATCH SEQ-8389 DELETED: false under the widened gate (it pinned an exclusion); no theorem uses it
  Theorem supported_call_default_rejected:
    ~supported_expr tops (Call ty target args (SOME default))
  Proof
    Cases_on `target` >>
    simp[supported_expr_def, supported_effect_expr_def, supported_pure_expr_def] >>
    BasicProvers.every_case_tac >> simp[]
  QED
*)

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
