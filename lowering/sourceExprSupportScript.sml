(* #543: transparent expression remainder, including nested pure/effect
   places. Only the builtin MethodId/Exp gates differ from supportedExprs;
   checker-derived equivalence includes intermediate storage map places. *)
Theory sourceExprSupport
Ancestors
  sourceBuiltinSupport supportedExprs supportedExprForms supportedTypes
  supportedDecls vyperTypeSystem vyperAST list pair option

Definition source_pure_expr_remainder_def:
  source_pure_expr_remainder tops (Name ty name) = T /\
  source_pure_expr_remainder tops (Literal ty lit) = T /\
  source_pure_expr_remainder tops (TopLevelName ty id) =
    supported_storage_value tops id ty /\
  source_pure_expr_remainder tops (FlagMember ty id member) = F /\
  source_pure_expr_remainder tops (IfExp ty c a b) =
    (supported_value_type tops ty /\ ~supported_tuple_type ty /\
     source_pure_expr_remainder tops c /\
     source_pure_expr_remainder tops a /\ source_pure_expr_remainder tops b) /\
  source_pure_expr_remainder tops (StructLit ty id fields) =
    (supported_main_nsid id /\ supported_struct_elements tops ty fields /\
     source_pure_fields_remainder tops fields) /\
  source_pure_expr_remainder tops (Subscript ty base key) =
    (supported_place_type tops ty /\ supported_subscript_place tops base /\
     source_place_expr_remainder tops base /\ source_pure_expr_remainder tops key) /\
  source_pure_expr_remainder tops (Attribute ty base field) =
    (supported_place_type tops ty /\ supported_field_place tops (expr_type base) field /\
     source_place_expr_remainder tops base) /\
  source_pure_expr_remainder tops (Builtin ty blt es) =
    (source_builtin_remainder tops ty blt es /\
     source_pure_exprs_remainder tops es) /\
  source_pure_expr_remainder tops (TypeBuiltin ty blt target es) =
    (supported_type_builtin_form tops ty blt target es /\
     source_pure_exprs_remainder tops es) /\
  source_pure_expr_remainder tops (Pop ty target) = F /\
  source_pure_expr_remainder tops (Call ty target es default) = F /\
  source_pure_exprs_remainder tops [] = T /\
  source_pure_exprs_remainder tops (e::es) =
    (source_pure_expr_remainder tops e /\ source_pure_exprs_remainder tops es) /\
  source_pure_fields_remainder tops [] = T /\
  source_pure_fields_remainder tops ((name,e)::fields) =
    (source_pure_expr_remainder tops e /\ source_pure_fields_remainder tops fields) /\
  source_place_expr_remainder tops (Name ty name) = supported_place_type tops ty /\
  source_place_expr_remainder tops (TopLevelName ty id) = supported_place_root tops id /\
  source_place_expr_remainder tops (Subscript ty base key) =
    (supported_subscript_place tops base /\ source_place_expr_remainder tops base /\
     source_pure_expr_remainder tops key) /\
  source_place_expr_remainder tops (Attribute ty base field) =
    (supported_field_place tops (expr_type base) field /\ source_place_expr_remainder tops base) /\
  source_place_expr_remainder tops e = source_pure_expr_remainder tops e
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, e) => 3 * expr_size e
    | INR (INL (_, es)) => 3 * expr4_size es
    | INR (INR (INL (_, fields))) => 3 * expr1_size fields
    | INR (INR (INR (_, e))) => 3 * expr_size e + 1)` >>
  simp[expr_size_def]
End

(* A map-valued intermediate base is checked by type_place_expr rather than
   well_typed_expr. Both routes check the key and recursively check the base. *)
Theorem checked_remainder_subscript_children:
  (well_typed_expr env (Subscript ty base_e key) \/
   IS_SOME (type_place_expr env (Subscript ty base_e key))) ==>
  (well_typed_expr env base_e \/ IS_SOME (type_place_expr env base_e)) /\
  well_typed_expr env key
Proof
  strip_tac
  >- (gvs[Once well_typed_expr_def] >> metis_tac[]) >>
  qpat_x_assum `IS_SOME _` mp_tac >>
  simp[Once well_typed_expr_def, IS_SOME_EXISTS, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem checked_pure_place_remainders:
  (!tops e. !env.
    (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
    (source_pure_expr_remainder tops e <=> supported_pure_expr tops e)) /\
  (!tops es. !env. well_typed_exprs env es ==>
    (source_pure_exprs_remainder tops es <=> supported_pure_exprs tops es)) /\
  (!tops fields. !env. well_typed_named_exprs env fields ==>
    (source_pure_fields_remainder tops fields <=> supported_pure_fields tops fields)) /\
  (!tops e. !env.
    (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
    (source_place_expr_remainder tops e <=> supported_place_expr tops e))
Proof
  ho_match_mp_tac source_pure_expr_remainder_ind >> rw[] >>
  imp_res_tac (REWRITE_RULE [DISJ_IMP_THM] checked_remainder_subscript_children) >>
  TRY (drule typed_builtin_remainder >> strip_tac) >>
  fs[source_pure_expr_remainder_def, supported_pure_expr_def,
     Once well_typed_expr_def, IS_SOME_EXISTS] >> metis_tac[]
QED

Theorem checked_pure_remainder:
  (!tops e. !env. well_typed_expr env e ==>
    (source_pure_expr_remainder tops e <=> supported_pure_expr tops e)) /\
  (!tops es. !env. well_typed_exprs env es ==>
    (source_pure_exprs_remainder tops es <=> supported_pure_exprs tops es)) /\
  (!tops fields. !env. well_typed_named_exprs env fields ==>
    (source_pure_fields_remainder tops fields <=> supported_pure_fields tops fields))
Proof
  metis_tac[checked_pure_place_remainders]
QED

Definition source_effect_expr_remainder_def:
  source_effect_expr_remainder tops (Call ty (IntCall id) args NONE) =
    (IS_SOME (supported_function_decl tops id Internal) /\
     (case ty of StructT _ => F | _ => T) /\
     source_pure_exprs_remainder tops args) /\
  source_effect_expr_remainder tops
    (Call ty (ExtCall static_call skip_check (name, arg_types, ret) opts) args NONE) =
    (EVERY supported_word_type arg_types /\
     supported_external_return_type tops ret /\
     ALL_DISTINCT opts /\ (static_call ==> ~MEM EKValue opts) /\
     LENGTH args = 1 + LENGTH arg_types + LENGTH opts /\
     source_pure_exprs_remainder tops args) /\
  source_effect_expr_remainder tops (Call NoneT (Send F) [a; v] NONE) =
    (source_pure_expr_remainder tops a /\ source_pure_expr_remainder tops v) /\
  source_effect_expr_remainder tops (Call NoneT (Send T) [a; v; g] NONE) =
    (source_pure_expr_remainder tops a /\ source_pure_expr_remainder tops v /\
     source_pure_expr_remainder tops g) /\
  source_effect_expr_remainder tops (Pop ty (TopLevelNameTarget id)) =
    supported_storage_dynamic_array tops id /\
  source_effect_expr_remainder tops (Subscript ty base key) =
    (supported_place_type tops ty /\ supported_subscript_place tops base /\
     ((source_place_expr_remainder tops base /\ source_effect_expr_remainder tops key) \/
      (source_effect_place_expr_remainder tops base /\
       (source_pure_expr_remainder tops key \/ source_effect_expr_remainder tops key)))) /\
  source_effect_expr_remainder tops (Attribute ty base field) =
    (supported_place_type tops ty /\ supported_field_place tops (expr_type base) field /\
     source_effect_place_expr_remainder tops base) /\
  source_effect_expr_remainder tops e = F /\
  source_effect_place_expr_remainder tops (Subscript ty base key) =
    (supported_subscript_place tops base /\
     ((source_place_expr_remainder tops base /\ source_effect_expr_remainder tops key) \/
      (source_effect_place_expr_remainder tops base /\
       (source_pure_expr_remainder tops key \/ source_effect_expr_remainder tops key)))) /\
  source_effect_place_expr_remainder tops (Attribute ty base field) =
    (supported_field_place tops (expr_type base) field /\
     source_effect_place_expr_remainder tops base) /\
  source_effect_place_expr_remainder tops e = F
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, e) => expr_size e
    | INR (_, e) => expr_size e)` >> simp[expr_size_def]
End

Definition source_expr_remainder_def:
  source_expr_remainder tops e <=>
    source_pure_expr_remainder tops e \/ source_effect_expr_remainder tops e
End

Theorem checked_effect_place_remainders:
  (!tops e. !env.
    (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
    (source_effect_expr_remainder tops e <=> supported_effect_expr tops e)) /\
  (!tops e. !env.
    (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
    (source_effect_place_expr_remainder tops e <=> supported_effect_place_expr tops e))
Proof
  ho_match_mp_tac source_effect_expr_remainder_ind >> rw[] >>
  imp_res_tac (REWRITE_RULE [DISJ_IMP_THM] checked_remainder_subscript_children) >>
  rpt (qpat_x_assum `!env'. _` (qspec_then `env` assume_tac)) >>
  fs[source_effect_expr_remainder_def, supported_effect_expr_def,
     Once well_typed_expr_def, IS_SOME_EXISTS] >>
  imp_res_tac (REWRITE_RULE [DISJ_IMP_THM, IS_SOME_EXISTS]
    checked_pure_place_remainders) >> simp[] >>
  TRY (rename1 `well_typed_expr env (Call ty (IntCall id) args NONE)` >>
       Cases_on `id` >> fs[Once well_typed_expr_def] >>
       imp_res_tac checked_pure_remainder >> simp[]) >>
  fs[well_typed_expr_def] >>
  imp_res_tac (REWRITE_RULE [DISJ_IMP_THM, IS_SOME_EXISTS]
    checked_pure_place_remainders) >> simp[] >> metis_tac[]
QED

Theorem checked_effect_remainder:
  well_typed_expr env e ==>
  (source_effect_expr_remainder tops e <=> supported_effect_expr tops e)
Proof
  metis_tac[checked_effect_place_remainders]
QED

Theorem checked_expr_remainder:
  well_typed_expr env e ==>
  (source_expr_remainder tops e <=> supported_expr tops e)
Proof
  simp[source_expr_remainder_def, supported_expr_def] >>
  metis_tac[checked_pure_remainder, checked_effect_remainder]
QED

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source expression support kernel audit: " ^ name) end)
  (DB.thms "sourceExprSupport");
