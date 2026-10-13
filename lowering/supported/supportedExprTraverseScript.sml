(* Reusable syntactic occurrence traversal, including default returns and
   Pop target indices even in unsupported expressions. Not an evaluator.
   TOP-LEVEL: supported_expr_exists, supported_target_exists,
   supported_exprs_exists, supported_opt_exists, supported_fields_exists;
   expr_has_effect, expr_has_internal_call, target_has_internal_call,
   expr_has_dynamic_decode, target_has_dynamic_decode. *)
Theory supportedExprTraverse
Ancestors
  supportedExprs vyperAST vyperABI vyperContext list pair

Definition supported_expr_exists_def:
  supported_expr_exists p (Name ty name) = p (Name ty name) /\
  supported_expr_exists p (Literal ty lit) = p (Literal ty lit) /\
  supported_expr_exists p (TopLevelName ty id) = p (TopLevelName ty id) /\
  supported_expr_exists p (FlagMember ty id field) = p (FlagMember ty id field) /\
  supported_expr_exists p (IfExp ty c a b) =
    (p (IfExp ty c a b) \/ supported_expr_exists p c \/
      supported_expr_exists p a \/ supported_expr_exists p b) /\
  supported_expr_exists p (StructLit ty id fields) =
    (p (StructLit ty id fields) \/ supported_fields_exists p fields) /\
  supported_expr_exists p (Subscript ty base key) =
    (p (Subscript ty base key) \/ supported_expr_exists p base \/
      supported_expr_exists p key) /\
  supported_expr_exists p (Attribute ty base field) =
    (p (Attribute ty base field) \/ supported_expr_exists p base) /\
  supported_expr_exists p (Builtin ty blt es) =
    (p (Builtin ty blt es) \/ supported_exprs_exists p es) /\
  supported_expr_exists p (TypeBuiltin ty blt target es) =
    (p (TypeBuiltin ty blt target es) \/ supported_exprs_exists p es) /\
  supported_expr_exists p (Pop ty target) =
    (p (Pop ty target) \/ supported_target_exists p target) /\
  supported_expr_exists p (Call ty target es default) =
    (p (Call ty target es default) \/ supported_exprs_exists p es \/
      supported_opt_exists p default) /\
  supported_target_exists p (NameTarget name) = F /\
  supported_target_exists p (TopLevelNameTarget id) = F /\
  supported_target_exists p (SubscriptTarget target key) =
    (supported_target_exists p target \/ supported_expr_exists p key) /\
  supported_target_exists p (AttributeTarget target field) =
    supported_target_exists p target /\
  supported_exprs_exists p [] = F /\
  supported_exprs_exists p (e::es) =
    (supported_expr_exists p e \/ supported_exprs_exists p es) /\
  supported_opt_exists p NONE = F /\
  supported_opt_exists p (SOME e) = supported_expr_exists p e /\
  supported_fields_exists p [] = F /\
  supported_fields_exists p ((name,e)::fields) =
    (supported_expr_exists p e \/ supported_fields_exists p fields)
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, e) => expr_size e
    | INR (INL (_, target)) => base_assignment_target_size target
    | INR (INR (INL (_, es))) => expr4_size es
    | INR (INR (INR (INL (_, opt)))) => expr3_size opt
    | INR (INR (INR (INR (_, fields)))) => expr1_size fields)` >>
  simp[expr_size_def] >>
  qsuff_tac
    `(!es. expr4_size es = list_size expr_size es) /\
     (!opt. expr3_size opt = option_size expr_size opt) /\
     (!fields. expr1_size fields =
       list_size (pair_size (list_size char_size) expr_size) fields)`
  >- (strip_tac >> asm_rewrite_tac[] >> DECIDE_TAC) >>
  rpt conj_tac >>
  TRY (Induct >> simp[expr_size_def, listTheory.list_size_def,
    basicSizeTheory.pair_size_def]) >>
  Cases >> simp[expr_size_def, basicSizeTheory.option_size_def]
End

Definition expr_effect_root_def:
  expr_effect_root (Call ty target es default) = T /\
  expr_effect_root (Pop ty target) = T /\
  expr_effect_root _ = F
End

Definition expr_internal_call_root_def:
  expr_internal_call_root (Call ty (IntCall id) es default) = T /\
  expr_internal_call_root _ = F
End

(* Reuses the source ABI dynamic-type test, including declared structs and
   recursive type environments. No second dynamic-type interpretation. *)
Definition expr_dynamic_decode_root_def:
  expr_dynamic_decode_root tops (TypeBuiltin ty (AbiDecode unwrap) target es) =
    vyper_is_dynamic (type_env tops) target /\
  expr_dynamic_decode_root tops _ = F
End

Definition expr_has_effect_def:
  expr_has_effect e <=> supported_expr_exists expr_effect_root e
End

Definition expr_has_internal_call_def:
  expr_has_internal_call e <=> supported_expr_exists expr_internal_call_root e
End

Definition target_has_internal_call_def:
  target_has_internal_call target <=>
    supported_target_exists expr_internal_call_root target
End

Definition expr_has_dynamic_decode_def:
  expr_has_dynamic_decode tops e <=>
    supported_expr_exists (expr_dynamic_decode_root tops) e
End

Definition target_has_dynamic_decode_def:
  target_has_dynamic_decode tops target <=>
    supported_target_exists (expr_dynamic_decode_root tops) target
End

Theorem supported_expr_exists_mono:
  (!p e. !q. (!x. p x ==> q x) /\ supported_expr_exists p e ==>
      supported_expr_exists q e) /\
  (!p target. !q. (!x. p x ==> q x) /\ supported_target_exists p target ==>
      supported_target_exists q target) /\
  (!p es. !q. (!x. p x ==> q x) /\ supported_exprs_exists p es ==>
      supported_exprs_exists q es) /\
  (!p opt. !q. (!x. p x ==> q x) /\ supported_opt_exists p opt ==>
      supported_opt_exists q opt) /\
  (!p fields. !q. (!x. p x ==> q x) /\ supported_fields_exists p fields ==>
      supported_fields_exists q fields)
Proof
  ho_match_mp_tac supported_expr_exists_ind >>
  rw[supported_expr_exists_def] >> metis_tac[]
QED

Theorem supported_expr_exists_root:
  p e ==> supported_expr_exists p e
Proof
  Cases_on `e` >> simp[supported_expr_exists_def]
QED

Theorem supported_exprs_exists_every:
  supported_exprs_exists p es <=> EXISTS (supported_expr_exists p) es
Proof
  Induct_on `es` >> simp[supported_expr_exists_def]
QED

Theorem supported_fields_exists_every:
  supported_fields_exists p fields <=>
    EXISTS (supported_expr_exists p o SND) fields
Proof
  Induct_on `fields` >> simp[supported_expr_exists_def] >>
  Cases_on `h` >> simp[supported_expr_exists_def]
QED

Theorem supported_pure_no_effect:
  (!tops e. supported_pure_expr tops e ==>
      ~supported_expr_exists expr_effect_root e) /\
  (!tops es. supported_pure_exprs tops es ==>
      ~supported_exprs_exists expr_effect_root es) /\
  (!tops fields. supported_pure_fields tops fields ==>
      ~supported_fields_exists expr_effect_root fields)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  simp[supported_pure_expr_def, supported_expr_exists_def, expr_effect_root_def] >>
  rpt conj_tac >> rpt gen_tac >>
  TRY (Cases_on `base`) >>
  simp[supported_pure_expr_def, supported_expr_exists_def, expr_effect_root_def]
QED

Theorem supported_pure_expr_effect_free:
  supported_pure_expr tops e ==> ~expr_has_effect e
Proof
  strip_tac >> simp[expr_has_effect_def] >>
  irule (CONJUNCT1 supported_pure_no_effect) >>
  qexists_tac `tops` >> simp[]
QED

Theorem supported_effect_root:
  supported_effect_expr tops e ==> expr_effect_root e
Proof
  Cases_on `e` >> simp[supported_effect_expr_def, expr_effect_root_def] >>
  rename1 `Call ty target args default` >>
  Cases_on `target` >> Cases_on `default` >>
  simp[expr_effect_root_def]
QED

Theorem expr_internal_call_is_effect:
  expr_has_internal_call e ==> expr_has_effect e
Proof
  rw[expr_has_internal_call_def, expr_has_effect_def] >>
  irule (CONJUNCT1 supported_expr_exists_mono) >>
  qexists_tac `expr_internal_call_root` >> simp[] >>
  Cases >> simp[expr_internal_call_root_def, expr_effect_root_def] >>
  rename1 `Call ty target args default` >> Cases_on `target` >>
  simp[expr_internal_call_root_def, expr_effect_root_def]
QED

Theorem supported_pure_no_internal_call:
  supported_pure_expr tops e ==> ~expr_has_internal_call e
Proof
  metis_tac[supported_pure_expr_effect_free, expr_internal_call_is_effect]
QED

Theorem supported_effect_expr_has_effect:
  supported_effect_expr tops e ==> expr_has_effect e
Proof
  strip_tac >> simp[expr_has_effect_def] >>
  irule supported_expr_exists_root >>
  drule supported_effect_root >> simp[]
QED

Theorem supported_effect_classification:
  supported_expr tops e /\ expr_has_effect e <=> supported_effect_expr tops e
Proof
  metis_tac[supported_expr_def, supported_pure_expr_effect_free,
    supported_effect_expr_has_effect]
QED
